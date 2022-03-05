(*|
=============================================================
 A simple Rupicola example: converting a string to uppercase
=============================================================
|*)

From Coq.Strings Require Import String Ascii.

(*|
This file is a tutorial on specifying and compiling a simple function with Rupicola.  Concretely, we'll compile a function that converts an ASCII string to its uppercase counterpart.

We'll start with a specification: a Gallina function, written with no concerns of performance, capturing the behavior that we want.  In this case the specification is executable, but it does not even have to be.
|*)

Section Spec.
  Open Scope string_scope.

(*|
We start by specifying the uppercase operation on characters, using a case disjunction:
|*)

  Definition upchar_spec (c: ascii) :=
    match c with
    | "a" => "A" | "b" => "B" | "c" => "C" | "d" => "D"
    | "e" => "E" | "f" => "F" | "g" => "G" | "h" => "H"
    | "i" => "I" | "j" => "J" | "k" => "K" | "l" => "L"
    | "m" => "M" | "n" => "N" | "o" => "O" | "p" => "P"
    | "q" => "Q" | "r" => "R" | "s" => "S" | "t" => "T"
    | "u" => "U" | "v" => "V" | "w" => "W" | "x" => "X"
    | "y" => "Y" | "z" => "Z" | c => c
    end%char.

(*|
Then we specify uppercasing on string as the application of `upchar_spec` to each character in the string:
|*)

  Fixpoint string_map (f: ascii -> ascii) (s: String.string) :=
    match s with
    | EmptyString => EmptyString
    | String a s => String (f a) (string_map f s)
    end.

  Definition upstr_spec (s: string) :=
    string_map upchar_spec s.

(*|
Here is a concrete example:
|*)

  Compute upstr_spec "rupicola".
End Spec.

(*|
Now that we have a specification (a “high-level model”), we need a function implementation (a “low-level model”) to go with it.  That low-level model is still purely functional, but it is written in a restricted dialect of Coq that can be compiled efficiently to C.
|*)

From Coq.Strings Require Import Byte.
From Rupicola Require Import Lib.Api Lib.Loops Lib.Arrays.
From bedrock2 Require Import BasicC64Semantics.

Section Impl.

(*|
Let's start with characters.  We'll encode them using ASCII and represent them as bytes.  Given this choice, there is a much more efficient implementation of uppercasing: check if the character is lowercase by performing a range check, and apply a mask if it is.  This works because ASCII uppercase and lowercase alphabetic characters are at a constant offset from each other.  Even better, we need a single comparison, not two, by exploiting the wraparound semantics of subtraction.
|*)

  Definition upchar_impl (b: byte) :=
    if byte.wrap (byte.unsigned b - byte.unsigned "a"%byte) <? 26
    then byte.and b x5f else b.

(*|
We could make a smart argument as to why this property holds, but with only 256 cases in type `byte` it's tempting to just brute-force the problem: the proof below proves that this implementation matches the original `upchar_spec`, modulo conversion from character to byte:
|*)

  Lemma upchar_impl_ok b:
    byte_of_ascii (upchar_spec (ascii_of_byte b)) = upchar_impl b.
  Proof. destruct b; reflexivity. Qed.

(*|
Similarly, we can define a low-level model of `upstr_spec`.  This one uses a regular list map to apply `upchar_spec` to a list of bytes (using `upchar_spec` instead of `upchar_impl` here is a pedagogical choice to showcase rewrites later; using `upchar_impl` directly would have been perfectly fine as well).  The function `ListArray.map` is plain wrapper around the usual `List.map`; it is there only to guide the compiler.  Same for the `let/n s` part, which tells the compiler to place the results of the operation in a variable called `"s"`.
|*)

  Definition upstr_impl (s: list byte) :=
    let/n s := ListArray.map
                (fun b => byte_of_ascii (upchar_spec (ascii_of_byte b)))
                s in
    s.

(*|
Here again we can prove that our functional implementation matches our specification.  Since this implementation is pure, the proof is straightforward and does not involve low-level reasoning about state with explicit memories and separation logic predicates.
|*)

  Lemma string_map_is_map f s:
    string_map f s = string_of_list_ascii (List.map f (list_ascii_of_string s)).
  Proof. induction s; simpl; congruence. Qed.

  Lemma upstr_impl_ok bs:
    upstr_impl bs = list_byte_of_string (upstr_spec (string_of_list_byte bs)).
  Proof.
    unfold upstr_spec, upstr_impl, nlet, list_byte_of_string, string_of_list_byte.
    rewrite string_map_is_map, !list_ascii_of_string_of_list_ascii, !map_map;
      reflexivity.
  Qed.

  Lemma upstr_impl_ok' s:
    upstr_spec s = string_of_list_byte (upstr_impl (list_byte_of_string s)).
  Proof. rewrite upstr_impl_ok, !string_of_list_byte_of_string; reflexivity. Qed.
End Impl.

(*|
Now that we have our inputs to the compiler, we are ready to start the compilation process itself.  All that we need now is a specification of the low-level calling convention (how arguments are passed to the low-level program), and a compiler configuration (specifying which transformations to apply to the code).
|*)

Section Upstr.

(*|
First comes the calling convention.  It is described as a pre-postcondition pair, which together with the final program will form a Hoare triple.  The syntax is roughly like this::

   fnspec! <function name> <arguments> / <ghost variables>,
     { requires tr mem := <precondition>;
       ensures tr' mem' := <postcondition>; }

Below we have two arguments (a string pointer `s_ptr` and a length `wlen`), which are machine words and two ghost variables (a Gallina-level string `s` and a separation logic frame `R` — these are forall-quantified variables shared by the pre- and the postcondition).

The precondition of this program states that `wlen` contains the length of the string `s`; that the length of `s` is representable in a machine word (`< 2 ^ 64`), and that the memory `mem` contains the string `s` at address `s_ptr`.

The postcondition of the program is where our low-level model gets plugged in.  It states that the program's trace `tr'` is unchanged from the initial one `tr` (there is no I/O in this example), and it asserts that the new memory contains the result of updating `s` with `upstr_impl` at address `s_ptr`:
|*)

  Instance spec_of_upstr : spec_of "upstr" :=
    fnspec! "upstr" s_ptr wlen / (s : list byte) R,
      { requires tr mem :=
          wlen = word.of_Z (Z.of_nat (length s)) /\
          Z.of_nat (length s) < 2 ^ 64 /\
          (sizedlistarray_value AccessByte (length s) s_ptr s * R)%sep mem;
        ensures tr' mem' :=
          tr' = tr /\
          (sizedlistarray_value AccessByte (length s) s_ptr (upstr_impl s) * R)%sep mem' }.

(*|
With that done, all we need is to pull in the relevant compiler parts.  The tactic `compile` below applies lemmas found in a various databases, including `compiler` (for statements), `expr_compiler` (for expressions), `compiler_side_conditions` (for preconditions of compilation lemmas), and `compiler_cleanup` for miscellaneous cleanups.

The two `Import` commands below pull in additional compilation lemmas into these databases; without the compiler would stop halfway and complain loudly.
|*)

  Import LoopCompiler.
  Import SizedListArrayCompiler.

(*|
Similarly, the following two commands teach the compiler how to make progress when it encounters unsupported symbols `upchar_spec` and `upchar_impl`: the first, a rewrite rule, causes the compiler to replace `upchar_spec` with `upchar_impl`; the second allows the compiler to peek into the definition of `upchar_impl` and continue compilation from there.
|*)

  Hint Rewrite upchar_impl_ok : compiler_cleanup.
  Hint Unfold upchar_impl : compiler_cleanup.

(*|
Finally, a call to generic linear arithmetic solver handles side-conditions arising from array bounds checks:
|*)

  Hint Extern 10 => lia : compiler_side_conditions.

(*|
With that we are ready to compile!  We give the signature of the function (the name of its arguments) and use Coq's `Derive` command to generate a pair of a Bedrock2 function `upstr_br2fn` and its proof `upstr_br2fn_ok`.  The notation `defn!` resolves the calling convention of `"upstr"` by looking up the typeclass instance `spec_of_upstr` defined above.
|*)

  Derive upstr_br2fn SuchThat
      (defn! "upstr" ("s", "len") { upstr_br2fn },
       implements upstr_impl)
    As upstr_br2fn_ok.
  Proof.
    Time compile.
  Time Qed.
End Upstr.

(*|
The result is a piece of Bedrock2 code:
|*)

From bedrock2 Require Import NotationsCustomEntry.
Compute upstr_br2fn.

(*|
And, thanks to the proximity of Bedrock2 to C, we can easily pretty-print the result to C (but note that this final pretty-printing stage is unverified; for a fully verified pipeline we would want to use Bedrock2's verified compiler to RISCV assembly).
|*)

Compute ToCString.c_func upstr_br2fn.

(*|
The following can be ignored; it is an entry point for our benchmarking code to automatically pull the C code out of this Coq file.
|*)

Definition upstr_cbytes := Eval vm_compute in
  list_byte_of_string (ToCString.c_module [upstr_br2fn]).
