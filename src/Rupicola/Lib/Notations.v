Require Import Rupicola.Lib.Core.
Require Import Rupicola.Lib.Monads.
Require Import Rupicola.Lib.IdentParsing.
Require Import Rupicola.Lib.Tactics.

Notation "'let/d' x := val 'in' body" :=
  (dlet val (fun x => body))
    (at level 200, x ident, body at level 200,
     format "'[hv' 'let/d'  x  :=  val  'in' '//' body ']'").

Notation "'let/d' f a0 .. an := val 'in' body" :=
  (dlet (fun a0 => .. (fun an => val) ..) (fun f => body))
    (at level 200, f ident, a0 binder, an binder, body at level 200,
     format "'[hv' 'let/d'  f  a0  ..  an  :=  val  'in' '//' body ']'").

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

Notation nlet_eq_k P v :=
  (forall x, x = v -> P x).

(* FIXME use `x binder` or `x name` instead of `x ident`? *)

(* FIXME Error: Anomaly "Uncaught exception Failure("hd")." until 8.13 *)
(* Notation "'let/n' x := val 'in' body" := *)
(*   (nlet [_] val (fun x => body)) *)
(*     (at level 200, x ident, body at level 200, *)
(*      format "'[hv' 'let/n'  x  :=  val  'in' '//' body ']'", *)
(*      only printing). *)

Notation "'let/n' x 'as' nm := val 'in' body" :=
  (nlet [nm] val (fun x => body))
    (at level 200, x ident, body at level 200,
     format "'[hv' 'let/n'  x  'as'  nm  :=  val  'in' '//' body ']'").

Notation "'let/n' x 'as' nm 'eq:' Heq := val 'in' body" :=
  (nlet_eq [nm] val (fun x Heq => body))
    (at level 200, x ident, body at level 200,
     format "'[hv' 'let/n'  x  'as'  nm  'eq:' Heq  :=  val  'in' '//' body ']'").

Notation "'let/n' x := val 'in' body" :=
  (nlet [IdentParsing.TC.ident_to_string x] val (fun x => body))
    (at level 200, x ident, body at level 200,
     only parsing).

Notation "'let/n' x 'eq:' Heq := val 'in' body" :=
  (nlet_eq [IdentParsing.TC.ident_to_string x] val (fun x Heq => body))
    (at level 200, x ident, body at level 200,
     only parsing).

(* Notation "'let/n' ( x , y ) := val 'in' body" := *)
(*   (nlet [_; _] val (fun '(x, y) => body)) *)
(*     (at level 200, x ident, body at level 200, *)
(*      format "'[hv' 'let/n'  ( x ,  y )  :=  val  'in' '//' body ']'", *)
(*      only printing). *)

Notation "'let/n' ( x , y ) 'as' ( nx , ny ) := val 'in' body" :=
  (nlet [nx; ny] val (fun xy => let (x, y) := xy in body))
    (at level 200, x ident, body at level 200,
     format "'[hv' 'let/n'  ( x ,  y )  'as'  ( nx ,  ny )  :=  val  'in' '//' body ']'").

Notation "'let/n' ( x , y ) 'as' ( nx , ny ) 'eq:' Heq := val 'in' body" :=
  (nlet [nx; ny] val (fun xy Heq => let (x, y) := xy in body))
    (at level 200, x ident, body at level 200,
     format "'[hv' 'let/n'  ( x ,  y )  'as'  ( nx ,  ny )  'eq:' Heq  :=  val  'in' '//' body ']'").

Notation "'let/n' ( x , y ) 'eq:' Heq := val 'in' body" :=
  (nlet_eq [IdentParsing.TC.ident_to_string x;
           IdentParsing.TC.ident_to_string y]
           val (fun xy Heq => let (x, y) := xy in body))
    (at level 200, x ident, y ident, body at level 200,
     only parsing).

Notation "'let/n' ( x , y ) := val 'in' body" :=
  (nlet [IdentParsing.TC.ident_to_string x;
        IdentParsing.TC.ident_to_string y]
        val (fun xy => let (x, y) := xy in body))
    (at level 200, x ident, y ident, body at level 200,
     only parsing).

(* FIXME generalize using a '\< … \> pattern *)

Notation "'let/n' ( x , y , z ) 'as' ( nx , ny , nz ) := val 'in' body" :=
  (nlet [nx; ny; nz] val (fun xyz => let '\< x, y, z \> := xyz in body))
    (at level 200, x ident, body at level 200,
     format "'[hv' 'let/n'  ( x ,  y ,  z )  'as'  ( nx ,  ny ,  nz )  :=  val  'in' '//' body ']'").

Notation "'let/n' ( x , y , z ) 'as' ( nx , ny , nz ) 'eq:' Heq := val 'in' body" :=
  (nlet [nx; ny; nz] val (fun xyz Heq => let '\< x, y, z \> := xyz in body))
    (at level 200, x ident, body at level 200,
     format "'[hv' 'let/n'  ( x ,  y ,  z )  'as'  ( nx ,  ny ,  nz )  'eq:' Heq  :=  val  'in' '//' body ']'").

Notation "'let/n' ( x , y , z ) 'eq:' Heq := val 'in' body" :=
  (nlet_eq [IdentParsing.TC.ident_to_string x;
           IdentParsing.TC.ident_to_string y;
           IdentParsing.TC.ident_to_string z]
           val (fun xyz Heq => let '\< x, y, z \> := xyz in body))
    (at level 200, x ident, y ident, body at level 200,
     only parsing).

Notation "'let/n' ( x , y , z ) := val 'in' body" :=
  (nlet [IdentParsing.TC.ident_to_string x;
        IdentParsing.TC.ident_to_string y;
        IdentParsing.TC.ident_to_string z]
        val (fun xyz => let '\< x, y, z \> := xyz in body))
    (at level 200, x ident, y ident, body at level 200,
     only parsing).

Notation "'call!' x" := (Free.Call x) (x at level 200, at level 10).

Notation "'let/!' x 'as' nm := val 'in' body" :=
  (mbindn [nm] val (fun x => body))
    (at level 200, x ident, body at level 200,
     format "'[hv' 'let/!'  x  'as'  nm  :=  val  'in' '//' body ']'").

Notation "'let/!' x := val 'in' body" :=
  (mbindn [IdentParsing.TC.ident_to_string x] val (fun x => body))
    (at level 200, x ident, body at level 200,
     only parsing).

(* FIXME add a notation for loops? *)

Infix "~>" := scalar (at level 40, only parsing).

Declare Custom Entry maps.

Notation "x  =>  y" :=
  (map.put map.empty x y)
    (in custom maps at level 80,
        x constr at level 0, y constr at level 80,
        no associativity).

Notation "z ; x  =>  y" :=
  (map.put z x y)
    (in custom maps at level 82,
        x constr at level 0, y constr at level 80,
        z custom maps, left associativity).

Notation "… x" :=
  (x)
    (in custom maps at level 80, x constr at level 80).

Declare Scope maps_scope.
Delimit Scope maps_scope with maps.
Notation "#{  x  }#" := (x) (at level 0, x custom maps at level 200) : maps_scope.
Open Scope maps_scope.

Notation "[[ locals ]]" := {| value := locals; _value_ok := _ |} (only printing).

Notation "<{ 'Trace' := tr ; 'Memory' := mem ; 'Locals' := locals ; 'Functions' := functions }> cmd <{ post }>" :=
  (WeakestPrecondition.cmd
     (WeakestPrecondition.call functions)
     cmd tr mem locals post)
    (at level 0,
     format "'[v' <{  '[v' 'Trace'  :=  '[hv' tr ']' ; '//' 'Memory'  :=  '[hv' mem ']' ; '//' 'Locals'  :=  '[hv' locals ']' ; '//' 'Functions'  :=  '[hv' functions ']' ']'  }> '//' cmd '//' <{  '[hv' post ']'  }> ']'").

Notation "'liftexists' x .. y ',' P" :=
  (Lift1Prop.ex1
     (fun x =>
        ..
          (Lift1Prop.ex1
             (fun y => P)) .. ))
    (x binder, y binder, only parsing, at level 199).

Infix "⋆" := sep (at level 40, left associativity).
Infix "&&&" := unsep (at level 50, left associativity). (* 50 binds less tightly than ⋆ *)

Notation "'fnspec!' name a0 .. an '/' g0 .. gn '~>' r0 .. rn ',' '{' 'requires' tr mem := pre ';' 'ensures' tr' mem' ':=' post '}'" :=
  (fun functions =>
     (forall a0,
        .. (forall an,
              (forall g0,
                  .. (forall gn,
                         (forall tr mem,
                             pre%Z ->
                             WeakestPrecondition.call
                               functions name tr mem (cons a0 .. (cons an nil) ..)
                               (fun tr' mem' rets =>
                                  (exists r0,
                                      .. (exists rn,
                                             rets = (cons r0 .. (cons rn nil) ..) /\
                                             post%Z) ..)))) ..)) ..))
    (at level 200,
     name at level 0,
     a0 binder, an binder,
     g0 binder, gn binder,
     r0 closed binder, rn closed binder,
     tr ident, tr' ident, mem ident, mem' ident,
     pre at level 200,
     post at level 200).

Notation "'fnspec!' name a0 .. an '/' g0 .. gn ',' '{' 'requires' tr mem := pre ';' 'ensures' tr' mem' ':=' post '}'" :=
  (fun functions =>
     (forall a0,
        .. (forall an,
              (forall g0,
                  .. (forall gn,
                         (forall tr mem,
                             pre%Z%sep ->
                             WeakestPrecondition.call
                               functions name tr mem (cons a0 .. (cons an nil) ..)
                               (fun tr' mem' rets =>
                                  rets = nil /\ post%Z%sep))) ..)) ..))
    (at level 200,
     name at level 0,
     a0 binder, an binder,
     g0 binder, gn binder,
     tr ident, tr' ident, mem ident, mem' ident,
     pre at level 200,
     post at level 200).

Notation "'fnspec!' name a0 .. an '~>' r0 .. rn ',' '{' 'requires' tr mem := pre ';' 'ensures' tr' mem' ':=' post '}'" :=
  (fun functions =>
     (forall a0,
        .. (forall an,
               (forall tr mem,
                   pre%Z ->
                   WeakestPrecondition.call
                     functions name tr mem (cons a0 .. (cons an nil) ..)
                     (fun tr' mem' rets =>
                        (exists r0,
                            .. (exists rn,
                                   rets = (cons r0 .. (cons rn nil) ..) /\
                                   post%Z) ..)))) ..))
    (at level 200,
     name at level 0,
     a0 binder, an binder,
     r0 closed binder, rn closed binder,
     tr ident, tr' ident, mem ident, mem' ident,
     pre at level 200,
     post at level 200).

Notation "'fnspec!' name '~>' r0 .. rn ',' '{' 'requires' tr mem := pre ';' 'ensures' tr' mem' ':=' post '}'" :=
  (fun functions =>
     (forall tr mem,
         pre%Z ->
         WeakestPrecondition.call
           functions name tr mem nil
           (fun tr' mem' rets =>
              (exists r0,
                  .. (exists rn,
                         rets = (cons r0 .. (cons rn nil) ..) /\
                         post%Z) ..))))
    (at level 200,
     name at level 0,
     r0 closed binder, rn closed binder,
     tr ident, tr' ident, mem ident, mem' ident,
     pre at level 200,
     post at level 200).

Notation "'fnspec!' name a0 .. an ',' '{' 'requires' tr mem := pre ';' 'ensures' tr' mem' ':=' post '}'" :=
  (fun functions =>
     (forall a0,
        .. (forall an,
               (forall tr mem,
                   pre%Z%sep ->
                   WeakestPrecondition.call
                     functions name tr mem (cons a0 .. (cons an nil) ..)
                     (fun tr' mem' rets =>
                        rets = nil /\ post%Z%sep))) ..))
    (at level 200,
     name at level 0,
     a0 binder, an binder,
     tr ident, tr' ident, mem ident, mem' ident,
     pre at level 200,
     post at level 200).

Notation "'fnspec!' name '/' g0 .. gn ',' '{' 'requires' tr mem := pre ';' 'ensures' tr' mem' rets ':=' post '}'" :=
  (fun functions =>
     (forall g0,
         .. (forall gn,
                (forall tr mem,
                    pre%Z ->
                    WeakestPrecondition.call
                      functions name tr mem []
                      (fun tr' mem' rets => post%Z))) ..))
    (at level 200,
     name at level 0,
     g0 binder, gn binder,
     tr ident, tr' ident, mem ident, mem' ident,
     pre at level 200,
     post at level 200).

Notation "'fnspec!' name a0 .. an '/' g0 .. gn ',' '{' 'requires' tr mem := pre ';' 'ensures' tr' mem' rets ':=' post '}'" :=
  (fun functions =>
     (forall a0,
        .. (forall an,
              (forall g0,
                  .. (forall gn,
                         (forall tr mem,
                             pre%Z ->
                             WeakestPrecondition.call
                               functions name tr mem (cons a0 .. (cons an nil) ..)
                               (fun tr' mem' rets => post%Z))) ..)) ..))
    (at level 200,
     name at level 0,
     a0 binder, an binder,
     g0 binder, gn binder,
     tr ident, tr' ident, mem ident, mem' ident,
     pre at level 200,
     post at level 200).

Notation "'fnspec!' name a0 .. an ',' '{' 'requires' tr mem := pre ';' 'ensures' tr' mem' rets ':=' post '}'" :=
  (fun functions =>
     (forall a0,
        .. (forall an,
               (forall tr mem,
                   pre%Z ->
                   WeakestPrecondition.call
                     functions name tr mem (cons a0 .. (cons an nil) ..)
                     (fun tr' mem' rets => post%Z))) ..))
    (at level 200,
     name at level 0,
     a0 binder, an binder,
     tr ident, tr' ident, mem ident, mem' ident,
     pre at level 200,
     post at level 200).

Declare Custom Entry defn_spec.

Record _defn_spec_sig :=
  { _defn_args: list string;
    _defn_rets: list string }.

Record _defn_spec {A: Type} :=
  { _defn_name: string;
    _defn_sig: _defn_spec_sig;
    _defn_bedrock: cmd;
    _defn_gallina: A;
    _defn_calls: list string }.

Declare Custom Entry defn_spec_commas.

Notation "a0 , .. , an" :=
  (cons a0 .. (cons an []) ..)
    (in custom defn_spec_commas at level 0,
        a0 constr at level 0, an constr at level 0).

Declare Custom Entry defn_spec_args.

Notation "'()'" :=
  [] (in custom defn_spec_args at level 0).

Notation "'(' ')'" :=
  [] (in custom defn_spec_args at level 0).

Notation "'(' args ')'" :=
  args (in custom defn_spec_args at level 0,
           args custom defn_spec_commas at level 0).

Declare Custom Entry defn_spec_sig.

Notation "args  '~>'  rets" :=
  {| _defn_args := args; _defn_rets := rets |}
    (in custom defn_spec_sig at level 0,
        args custom defn_spec_args at level 0,
        rets custom defn_spec_commas at level 0).

Notation "args" :=
  {| _defn_args := args; _defn_rets := [] |}
    (in custom defn_spec_sig at level 0,
        args custom defn_spec_args at level 0).

Notation "name sig  {  body  } ,  'implements'  fn" :=
  {| _defn_name := name;
     _defn_sig := sig;
     _defn_bedrock := match body return cmd with body => body end;
     _defn_gallina := fn;
     _defn_calls := [] |}
    (in custom defn_spec at level 10,
        name constr at level 0,
        sig custom defn_spec_sig at level 0,
        body constr at level 200,
        fn constr at level 0,
        no associativity).

Notation "name sig  {  body  } ,  'implements'  fn  'using'  fns" :=
  {| _defn_name := name;
     _defn_sig := sig;
     _defn_bedrock := match body return cmd with body => body end;
     _defn_gallina := fn;
     _defn_calls := fns |}
    (in custom defn_spec at level 10,
        name constr at level 0,
        sig custom defn_spec_sig at level 0,
        body constr at level 200,
        fn constr at level 0,
        fns constr at level 0,
        no associativity).

Definition __rupicola_program_marker {A} (a: A) := True.

Notation "defn! spec" :=
  (match spec with
   | spec_constr =>
     (* This match typechecks `spec` before passing it to Ltac, yielding much
        better error messages when `spec` isn't a valid term. *)
     ltac:(lazymatch (eval red in spec_constr) with
           | {| _defn_name := ?name; _defn_sig := {| _defn_args := ?args; _defn_rets := ?rets |};
                _defn_bedrock := ?bedrock; _defn_gallina := ?gallina;
                _defn_calls := ?calls |} =>
             let proc := constr:((name, (args, rets, bedrock))) in
             let goal := Rupicola.Lib.Tactics.program_logic_goal_for_function proc calls in
             exact (__rupicola_program_marker gallina -> goal)
           end)
   end)
    (at level 0, spec custom defn_spec at level 200, only parsing).
