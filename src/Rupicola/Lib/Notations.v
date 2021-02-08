Require Import Rupicola.Lib.Core.
Require Import Rupicola.Lib.IdentParsing.

Notation "'let/d' x := val 'in' body" :=
  (dlet val (fun x => body))
    (at level 200, x ident, body at level 200,
     format "'let/d'  x  :=  val  'in' '//' body").

(* TODO: figure out recursive notation for this *)
Notation
      "'let/d' '''(' x , y ')' := val 'in' body" :=
  (dlet val
        (fun v =>
           let x := fst v in
           let y := snd v in
           body))
    (at level 200, only parsing).
Notation
      "'let/d' '''(' x , y , z ')' := val 'in' body" :=
  (dlet val
        (fun v =>
           let x := fst (fst v) in
           let y := snd (fst v) in
           let z := snd v in
           body))
    (at level 200, only parsing).

Definition nlet {A P} (vars: list string) (val : A) (body : forall a : A, P a) : P val :=
  let x := val in body x.

(* FIXME Error: Anomaly "Uncaught exception Failure("hd")." until 8.13 *)
(* Notation "'let/n' x := val 'in' body" := *)
(*   (nlet [_] val (fun x => body)) *)
(*     (at level 200, x ident, body at level 200, *)
(*      format "'let/n'  x  :=  val  'in' '//' body", *)
(*      only printing). *)

Notation "'let/n' x 'as' nm := val 'in' body" :=
  (nlet (P := fun _ => _) (* Force non-dependent type *)
        [nm] val (fun x => body))
    (at level 200, x ident, body at level 200,
     format "'let/n'  x  'as'  nm  :=  val  'in' '//' body").

Notation "'let/n' x := val 'in' body" :=
  (nlet (P := fun _ => _) (* Force non-dependent type *)
        [IdentParsing.TC.ident_to_string x]
        val (fun x => body))
    (at level 200, x ident, body at level 200,
     only parsing).

(* Notation "'let/n' ( x , y ) := val 'in' body" := *)
(*   (nlet [_; _] val (fun '(x, y) => body)) *)
(*     (at level 200, x ident, body at level 200, *)
(*      format "'let/n'  ( x ,  y )  :=  val  'in' '//' body", *)
(*      only printing). *)

Notation "'let/n' ( x , y ) 'as' ( nx , ny ) := val 'in' body" :=
  (nlet (P := fun _ => _) (* Force non-dependent type *)
        [nx; ny] val (fun '(x, y) => body))
    (at level 200, x ident, body at level 200,
     format "'let/n'  ( x ,  y )  'as'  ( nx ,  ny )  :=  val  'in' '//' body").

Notation "'let/n' ( x , y ) := val 'in' body" :=
  (nlet (P := fun _ => _) (* Force non-dependent type *)
        [IdentParsing.TC.ident_to_string x;
         IdentParsing.TC.ident_to_string y]
        val (fun '(x, y) => body))
    (at level 200, x ident, y ident, body at level 200,
     only parsing).

Infix "~>" := scalar (at level 40, only parsing).

Notation "[[ locals ]]" := ({| value := locals; _value_ok := _ |}) (only printing).

Definition postcondition_func
           {semantics : Semantics.parameters}
           (spec : list word -> Semantics.mem -> Prop)
           R tr :=
  (fun (tr' : Semantics.trace) (mem' : Semantics.mem) (rets : list word) =>
     tr = tr'
     /\ sep (spec rets) R mem').

Definition postcondition_func_norets
           {semantics : Semantics.parameters} spec R tr :=
  postcondition_func (fun r => sep (emp (r = nil)) (spec r)) R tr.

(* TODO: see if all uses of locals_post can be rephrased using retvars *)
Definition postcondition_cmd
           {semantics : Semantics.parameters}
           locals_post spec retvars R tr :=
  (fun (tr' : Semantics.trace) (mem' : Semantics.mem)
       (locals : Semantics.locals) =>
     tr = tr'
     /\ locals_post locals
     /\ exists rets,
         map.getmany_of_list locals retvars = Some rets
         /\ sep (spec rets) R mem').

Notation "'find' body 'implementing' spec 'and-returning' retvars 'and-locals-post' locals_post 'with-locals' locals 'and-memory' mem 'and-trace' tr 'and-rest' R 'and-functions' fns" :=
  (WeakestPrecondition.cmd
     (WeakestPrecondition.call fns)
     body tr mem locals
     (postcondition_cmd locals_post spec retvars R tr)) (at level 0).

Notation "'liftexists' x .. y ',' P" :=
  (Lift1Prop.ex1
     (fun x =>
        ..
          (Lift1Prop.ex1
             (fun y => P)) .. ))
    (x binder, y binder, only parsing, at level 199).

(* precondition is more permissively handled than postcondition in order to
   non-separation-logic (or multiple separation-logic) preconditions *)
Notation "'forall!' x .. y ',' pre '===>' fname '@' args 'returns' rets '===>' post" :=
(fun functions =>
   (forall x,
       .. (forall y,
              forall R tr mem,
                pre R mem ->
                WeakestPrecondition.call
                  functions fname tr mem args
                  (postcondition_func (fun rets => post) R tr)) ..))
     (x binder, y binder, only parsing, at level 199).

Example spec_example_withrets {semantics : Semantics.parameters}
  : spec_of "example" :=
  (forall! (pa : address) (a b : word),
      (sep (pa ~> a))
        ===>
        "example" @ [pa; b] returns r
        ===>
        (liftexists x, emp (r = [x]) * (pa ~> x))%sep).
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
