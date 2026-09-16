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

  Implicit Type R : mem -> Prop.

  Section Tail.
    Definition min (x y : word) :=
      let/n c := Semantics.ltu x y in
      if c then
        let/n r := x in r
      else
        let/n r := y in r.

    Instance spec_of_min : spec_of "min" :=
      fnspec! "min" (x y: word) ~> z,
      { requires tr mem := True;
        ensures tr' mem' := tr = tr' /\ mem = mem' /\ z = min x y }.

    Derive min_br2fn SuchThat
           (defn! "min"("x", "y") ~> "r"
                { min_br2fn },
            implements min)
           As min_br2fn_ok.
    Proof.
      compile.
    Qed.
  End Tail.

  Section Body.
    Definition minm (x y : word) :=
      let/n r := if Semantics.ltu x y
                then x
                else Zmod.add y Zmod.one in
      let/n r := Zmod.sub r Zmod.one in
      r.

    Instance spec_of_minm : spec_of "minm" :=
      fnspec! "minm" (x y: word) / R ~> z,
      { requires tr mem := R mem;
        ensures tr' mem' := tr = tr' /\ R mem' /\ z = minm x y }. (* TODO explain why not mem' = mem *)

    Derive minm_br2fn SuchThat
           (defn! "minm"("x", "y") ~> "r"
                { minm_br2fn },
            implements minm)
           As minm_br2fn_ok.
    Proof.
      compile.
    Qed.
  End Body.
End with_parameters.
