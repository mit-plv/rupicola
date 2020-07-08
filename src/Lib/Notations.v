Require Import Rupicola.Lib.Core.
Require Import Rupicola.Lib.IdentParsing.

Notation "'let/d'  x  :=  val  'in'  body" :=
  (dlet val (fun x => body)) (at level 4).

Definition nlet {A P} (var: string) (val : A) (body : forall a : A, P a) : P val :=
  let x := val in body x.

Notation "'let/n' x 'as' nm := val 'in' body" :=
  (nlet nm val (fun x => body))
    (at level 200, x ident, body at level 200,
     format "'let/n'  x  'as'  nm  :=  val  'in' '//' body",
     only printing).

Notation "'let/n' x := val 'in' body" :=
  (nlet (binder_to_string val x) val (fun x => body))
    (at level 200, x ident, body at level 200,
     only parsing).

Check (let/n x := 1 in let/n x := x + 1 in x).

(* TODO: figure out recursive notation for this *)
Notation
      "'let/d' '''(' x , y ')' := val 'in' body" :=
  (dlet val
        (fun v =>
           let x := fst v in
           let y := snd v in
           body))
    (at level 4, only parsing).
Notation
      "'let/d' '''(' x , y , z ')' := val 'in' body" :=
  (dlet val
        (fun v =>
           let x := fst (fst v) in
           let y := snd (fst v) in
           let z := snd v in
           body))
    (at level 4, only parsing).

Infix "~>" := scalar (at level 40, only parsing).

Notation "[[ locals ]]" := ({| value := locals; _value_ok := _ |}) (only printing).

Definition postcondition_func
           {semantics : Semantics.parameters} {T : Type}
           (spec : T -> Semantics.trace -> list word -> Semantics.mem -> Prop)
           (gallina_rets : T)
           R
  : Semantics.trace -> Semantics.mem -> list word -> Prop :=
  (fun (tr' : Semantics.trace) (mem' : Semantics.mem) (rets : list word) =>
     sep (spec gallina_rets tr' rets) R mem').

Definition postcondition_func_norets
           {semantics : Semantics.parameters} {T}
           (spec : T -> Semantics.trace -> list word -> Semantics.mem -> Prop)
           (gallina_rets : T)
           R
  : Semantics.trace -> Semantics.mem -> list word -> Prop :=
  (fun (tr' : Semantics.trace) (mem' : Semantics.mem) (rets : list word) =>
     (emp (rets = nil) * (spec gallina_rets tr' rets) * R)%sep mem').

Definition postcondition_cmd
           {semantics : Semantics.parameters} {T}
           (retvars : list string)
           (spec : T -> Semantics.trace -> list word -> Semantics.mem -> Prop)
           (gallina_rets : T)
  : Semantics.trace -> Semantics.mem -> Semantics.locals -> Prop :=
  fun tr' mem' locals' =>
    exists rets,
      map.getmany_of_list locals' retvars = Some rets
      /\ spec gallina_rets tr' rets mem'.

Notation "'find' body 'from' gallina_impl 'implementing' spec 'with-locals-sep' locals 'and-memory-sep' mem 'and-trace' tr 'and-functions' fns" :=
  (forall m l,
      locals l ->
      mem m ->
      WeakestPrecondition.cmd
        (WeakestPrecondition.call fns)
        body tr m l
        (spec gallina_impl)) (at level 0).

Check
  (forall fns tr (Rl : _ -> Prop) (Rm : _ -> Prop),
   find cmd.skip
   from (tt)
   implementing (fun _ : unit =>
                   fun tr' mem' locals' =>
                     tr = tr' /\ Rm mem' /\ Rl locals')
   with-locals-sep Rl
   and-memory-sep Rm
   and-trace tr
   and-functions fns).
Print WeakestPrecondition.call.

Notation "'find-function' body 'from' gallina_impl 'implementing' spec 'and-returning' retvars 'and-memory-sep' mem 'and-trace' tr 'and-functions' fns" :=
  (forall m l,
      locals l ->
      mem m ->
      WeakestPrecondition.cmd
        (WeakestPrecondition.call fns)
        body tr m l
        (postcondition_cmd retvars spec gallina_impl)) (at level 0).


Notation "'liftexists' x .. y ',' P" :=
  (Lift1Prop.ex1
     (fun x =>
        ..
          (Lift1Prop.ex1
             (fun y => P)) .. ))
    (x binder, y binder, only parsing, at level 199).

(* precondition is more permissively handled than postcondition in order to
   non-separation-logic (or multiple separation-logic) preconditions *)
Notation "'forall!' x .. y ',' pre '===>' fname '@' args 'returns' retvars '===>' post" :=
(fun functions =>
   (forall x,
       .. (forall y,
              forall R tr mem,
                pre R mem ->
                WeakestPrecondition.call
                  functions fname tr mem args
                  (postcondition_func post retvars)) ..))
     (x binder, y binder, only parsing, at level 199).

Example spec_example_withrets {semantics : Semantics.parameters}
  : spec_of "example" :=
  (forall! (pa : address) (a b : word),
      (sep (pa ~> a))
        ===>
        "example" @ [pa; b] returns ["r"]
        ===>
        (fun tr mem locals =>
           liftexists x R,
           (emp ((Var "r" x * R)%sep locals)
                * (pa ~> x)%sep) mem
           emp (r = [x]) * (pa ~> x))%sep).
Example spec_example_norets {semantics : Semantics.parameters}
  : spec_of "example" :=
     (forall! (pa : address) (a b : word),
         (sep (pa ~> a))
           ===>
           "example" @ [pa; b] returns r
           ===>
           (emp (r = []) * (pa ~> word.add a b))%sep).

(* shorthand for no return values *)
Notation "'forall!' x .. y ',' pre '===>' fname '@' args '===>' post" :=
(fun functions =>
   (forall x,
       .. (forall y,
              forall R tr mem,
                pre R mem ->
                WeakestPrecondition.call
                  functions fname tr mem args
                  (postcondition_func_norets post R tr)) ..))
     (x binder, y binder, only parsing, at level 199).

(* N.B. postconditions with no return values still need to take in an argument
   for return values to make types line up. However, the shorthand notation inserts
   a clause to the postcondition saying the return values are nil, so the
   postcondition does not need to ensure this. *)
Example spec_example_norets_short {semantics : Semantics.parameters}
  : spec_of "example" :=
  (forall! (pa : address) (a b : word),
      (sep (pa ~> a))
        ===>
        "example" @ [pa; b]
        ===>
        (fun _ => pa ~> word.add a b)%sep).

(* unify short and long notations for functions without return values (fails if
   spec_example_norets and spec_example_norets_short are not equivalent) *)
Compute (let x := ltac:(unify @spec_example_norets @spec_example_norets_short) in x).
