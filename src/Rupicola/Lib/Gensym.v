From Coq Require Import
     String Numbers.DecimalString.

Definition _gs (gs_prefix prefix: string) (n: nat) :=
  (gs_prefix ++ prefix ++
   match n with
   | 0 => ""
   | S n => NilEmpty.string_of_uint (Nat.to_uint n)
   end)%string.

Definition gs {prefix: string} {n: nat} (str: string) :=
  str.

Ltac gensym_next locals prefix n :=
  match locals with
  | context[gs prefix n] => gensym_next locals prefix (S n)
  | _ => n
  end.

Ltac gensym_prefix :=
  constr:("_gs_"%string).

Ltac gensym locals prefix :=
  let n0 := match locals with
           | context[gs prefix ?n] => constr:(S n)
           | _ => constr:(0%nat)
           end in
  let n := gensym_next locals prefix n0 in
  let gs_prefix := gensym_prefix in
  let str := constr:(_gs gs_prefix prefix n) in
  let str := (eval vm_compute in str) in
  constr:(@gs prefix n str).

#[export] Hint Unfold gs : solve_map_get_goal.
