(*|
==============================================
 A few exercises to get started with Rupicola
==============================================
|*)

From Coq Require Import Init.Byte.
From Rupicola Require Import Lib.Api Lib.Loops Lib.Arrays.
From bedrock2 Require Import BasicC64Semantics.

(*|
Compiling a new operator
========================

Bedrock2 defines `byte.and` and `byte.xor` but not `byte.or` or `byte.not`, and Rupicola doesn't have built-in support for these two operations.  Let's see how to add them: this exercise is about extending Rupicola's expression compiler, which is described in the supplementary material provided with the paper.

First, let's look at the definition of `byte.and`:
|*)

Print byte.and.

(*|
Based on that definition, adjust the definitions below to perform a logical `or` using `Z.lor` and a logical using `Z.lnot`.  The function `byte.of_Z` truncates, so you do not need to worry about additional non-zero high bits in the `lnot` case.
|*)

Definition byte_or (b1 b2: byte) : byte :=
  byte.of_Z (Z.lor (byte.unsigned b1) (byte.unsigned b2)).
Definition byte_not (b: byte) : byte :=
  byte.of_Z (Z.lnot (byte.unsigned b)).

(*|
Now let's write a program that uses these two.  Replace the `x00` parts of the program below so that it takes two byte values and a mask and returns the two values merged according to the mask, using `byte_or`, `byte.and`, and `byte_not`:
|*)

Definition combine (b1 b2: byte) (m: byte) :=
  let/n selected_b1 := byte.and b1 m in
  let/n selected_b2 := byte.and b2 (byte_not m) in
  let/n z := byte_or selected_b1 selected_b2 in
  z.

(*|
Here is a quick sanity check; the following `Compute` should return `xd4`, i.e. `"212"`.
|*)

Definition of_bits (bs: bool * bool * bool * bool * bool * bool * bool * bool) : byte :=
  let '(b0, b1, b2, b3, b4, b5, b6, b7) := bs in
  Byte.of_bits (b7, (b6, (b5, (b4, (b3, (b2, (b1, b0))))))).

Compute
  (* >>> b1 = 0b11010010 *)
  let b1 := of_bits (true , true, false, true,  false, false, true,  false) in
  (* >>> b2 = 0b01100100 *)
  let b2 := of_bits (false, true, true,  false, false, true,  false, false) in
  (* >>> m  = 0b11110000 *)
  let m  := of_bits (true , true, true,  true,  false, false, false, false) in
  (* >>> (b1 & m) | (b2 & ~m) *)
  combine b1 b2 m.

(*|
Fun fact: a (more!) efficient way to compute this same value is `b2 ^ ((b1 ^ b2) & m)`.  You can use that formula to check (or verify!) your own implementation.
|*)

Compute
  (* >>> b1 = 0b11010010 *)
  let b1 := of_bits (true , true, false, true,  false, false, true,  false) in
  (* >>> b2 = 0b01100100 *)
  let b2 := of_bits (false, true, true,  false, false, true,  false, false) in
  (* >>> m  = 0b11110000 *)
  let m  := of_bits (true , true, true,  true,  false, false, false, false) in
  (* >>> (b1 & m) | (b2 & ~m) *)
  byte.xor b2 (byte.and (byte.xor b1 b2) m).

(*|
Now, let's attempt to compile this function.  First, we need a "signature" for it: a pre-post-condition pair.  A template is below, but it needs to be edited: nothing says that the word-sized inputs `w1`, `w2`, and `m` of the function hold bytes, and nothing says how the function's output `z` relates to `w1`, `w2`, and `m`, either.

- Replace `True` after the `requires` part of the signature with two equations that connect `w1` and `b1` and `w2` and `b2` and `wm` and `m` using `word_of_byte`.

- Replace `True` after `ensures` with equalities that ensure that the program didn't produce output (an equality between the old trace `tr` and the new trace `tr'`), and that it didn't modify the memory (an equality between `mem` and `mem'`).
|*)

Print expr_compile_byte_and.

Instance spec_of_combine : spec_of "combine" :=
  fnspec! "combine" (w1 w2 wm: word) / (b1 b2 m: byte) ~> z,
    { requires tr mem :=
        w1 = word_of_byte b1 /\
        w2 = word_of_byte b2 /\
        wm = word_of_byte m;
      ensures tr' mem' :=
        tr' = tr /\
        mem' = mem /\
        z = word_of_byte (combine b1 b2 m) }.

(*|
This is enough to run the compiler:
|*)

Derive combine_br2fn SuchThat
       (defn! "combine"("b1", "b2", "m") ~> "z"
            { combine_br2fn },
        implements combine)
  As combine_br2fn_ok.
Proof.
  compile.

(*|
If you have not filled in the `True` part of `requires` above, Coq will give you a goal like this::

    DEXPR mem (map.of_list [("m", wm); ("b1", w1); ("b2", w2)]) ?e1 (word_of_byte b1)

… which means that Coq couldn't find an expression equal to `word_of_byte b1` in the context (notice how `"b1"` maps to `"w1"`, which should be equal to `word_of_byte b1`).

(These DEXPR goals are simplified compilation goals for expressions instead of statements.  The syntax is `DEXPR memory locals bedrock2-expression gallina-expression`)

Then, if you have completed the definition of `combine`, Rupicola will complain that it does not know how to compile `word_or` and `word_not`.  We need to provide lemma for both of them.
|*)

Abort.

(*|
Here is a simple tactic that may be helpful for the following two compilation lemmas:
|*)

Ltac cleanup :=
  repeat straightline;
  repeat simple eapply WeakestPrecondition_dexpr_expr; eauto.

(*|
And here is the compilation lemma that we want to prove for `or`.  If you get stuck in uninteresting lemmas about words, feel free to use `admit`, or draw inspiration from the proofs of `byte_morph_and` and `byte_unsigned_land` in `src/Lib/Core.v`:
|*)

Lemma expr_compile_byte_or {m l} (b1 b2 : byte) (e1 e2 : expr) :
  DEXPR m l e1 (word_of_byte b1) ->
  DEXPR m l e2 (word_of_byte b2) ->
  DEXPR (word := word) m l
        (expr.op bopname.or e1 e2)
        (word_of_byte (byte_or b1 b2)).
Proof.
  cleanup.
  apply word.unsigned_inj.
  rewrite word.unsigned_or_nowrap, !word.unsigned_of_Z, !wrap_byte_unsigned.
  unfold byte_or; rewrite byte.unsigned_of_Z.
  unfold byte.wrap; rewrite <- Z.land_ones.
  bitblast.Z.bitblast; rewrite !testbit_byte_unsigned_ge.
  all: lia.
Qed.

(*|
Can you fill in the lemma below for `not`?  Bedrock2 does not have `bopname.not`, but you can `xor` the number with `(expr.literal 255)` instead.

You may find the lemma `expr_compile_Z_literal` useful, but our solution does not use it: instead we have a 3-lines proof… can you find it?
|*)

Lemma expr_compile_byte_not {m l} (b : byte) (e : expr) :
  DEXPR m l e (word_of_byte b) ->
  DEXPR (word := word) m l
        (expr.op bopname.xor e (expr.literal 255))
        (word_of_byte (byte_not b)).
Proof.
  cleanup.
  instantiate (1 := (word.of_Z 255)); destruct b; reflexivity.
  reflexivity.
Qed.

(*|
We can then plug in these two lemmas as compiler hints, and finally complete the compilation:
|*)

#[export] Hint Extern 5 (DEXPR _ _ _ (word_of_byte (byte_or _ _))) =>
  simple eapply expr_compile_byte_or; shelve : expr_compiler.

#[export] Hint Extern 5 (DEXPR _ _ _ (word_of_byte (byte_not _))) =>
  simple eapply expr_compile_byte_not; shelve : expr_compiler.

Derive combine_br2fn SuchThat
       (defn! "combine"("b1", "b2", "m") ~> "z"
            { combine_br2fn },
        implements combine)
  As combine_br2fn_ok.
Proof.
  compile.
Qed.

(*|
And if you want to look at the generated code, you can simply print `combine_br2fn`:
|*)

Print combine_br2fn.

(*|
Or, "pretty"-printed to C:
|*)

Compute ToCString.c_func combine_br2fn.
