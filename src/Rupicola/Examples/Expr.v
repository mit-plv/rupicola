Require Import Rupicola.Lib.Api.

Section with_parameters.
  Context {width: Z} {BW: Bitwidth width}.
  Local Notation word := (bits width).
  Context {mem: map.map word Byte.byte}.
  Context {locals: map.map String.string word}.
  Context {ext_spec: bedrock2.Semantics.ExtSpec}.
  Context {mem_ok : map.ok mem}.
  Context {locals_ok : map.ok locals}.
  Context {ext_spec_ok : Semantics.ext_spec.ok ext_spec}.

  Definition example (x: word) (y: word) :=
    let/n x := Zmod.and (Zmod.add y Zmod.one)
                       (Zmod.xor (Zmod.add (Zmod.sub x y) x)
                                 Zmod.zero) in
    x.

  Implicit Type R : mem -> Prop.
  Instance spec_of_example : spec_of "example" :=
    fnspec! "example" (x y: word) ~> z,
    { requires tr mem := True;
      ensures tr' mem' :=
        tr = tr' /\
        mem = mem' /\
        z = example x y }.

  Derive example_br2fn SuchThat
         (defn! "example"("x", "y") ~> "x"
              { example_br2fn },
          implements example)
         As example_br2fn_ok.
  Proof.
    compile.
  Qed.

  Definition exZ (x: Z) (y: Z) :=
    let t := y + x in
    let t1 := ((1 - x) * (Z.land y 1) - x) * (Z.land y 1) in
    let/n t1 := t1 - (Z.lxor (Z.lxor 0 1) (Z.lxor 0 t)) in
    let t2 := ((y + 3) - (1 - y)) * (y + 3) in
    let/n t2 := Z.lor x (t * 3 + 1) in
    let t3 := t - (Z.lxor (Z.lxor t 1) 1) in
    let t3 := (1 - t3) * (((1 - t3) * (y + t3)) + t3) in
    let/n t3 := Z.lor (Z.lor x (t3 * 3 + 1)) (Z.lxor 0 (t3 * 3 + 1)) in
    let t4 := (Z.land (y + 1) (Z.lxor (t - y + t) 0)) in
    let/n t4 := Z.lor (1 + t4) (1 - t4) in
    let t5 := 3 * ((t + 8) + (t - 8)) in
    let/n x := t1 + t2 - t3 + t4 - t5 in
    x.

  Instance spec_of_exZ : spec_of "exZ" :=
    fnspec! "exZ" (x y: word) ~> z,
    { requires tr mem := True;
      ensures tr' mem' :=
        tr = tr' /\
        mem = mem' /\
        z = bits.of_Z width (exZ (Zmod.unsigned x) (Zmod.unsigned y)) }.

  Derive exZ_br2fn SuchThat
         (defn! "exZ"("x", "y") ~> "x"
              { exZ_br2fn },
          implements exZ)
         As exZ_br2fn_ok.
  Proof.
    compile.
  Qed.

  (* Compute exZ_br2fn. *)

  Fixpoint overwrite_chain (n: nat) (w0 w1: word) :=
    match n with
    | O => w1
    | S n => let/n w1 := Zmod.add w0 w1 in
            overwrite_chain n w0 w1
    end.

  Definition chain (w0: word) :=
    Eval simpl in
    let/n w1 := Zmod.one in
    overwrite_chain 5 w0 w1.

  Instance spec_of_chain : spec_of "chain" :=
    fnspec! "chain" (w0: word) ~> w1,
    { requires tr mem := True;
      ensures tr' mem' :=
        tr = tr' /\
        mem = mem' /\
        w1 = chain w0 }.

  Derive chain_br2fn SuchThat
         (defn! "chain"("w0") ~> "w1"
              { chain_br2fn },
          implements chain)
         As chain_br2fn_ok.
  Proof.
    compile.
  Qed.

  (* Compute chain_br2fn. *)
End with_parameters.
