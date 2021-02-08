Require Import Rupicola.Lib.Core.
Require Import Rupicola.Lib.Notations.
Require Export Rupicola.Lib.Gensym.
Require Import Rupicola.Lib.Tactics.

Section with_semantics.
  Context {semantics : Semantics.parameters}
          {semantics_ok : Semantics.parameters_ok _}.

  Lemma compile_skip :
    forall (locals: Semantics.locals) (mem: Semantics.mem)
      tr functions (pred: predicate),
      pred tr mem locals  ->
      (<{ Trace := tr;
          Memory := mem;
          Locals := locals;
          Functions := functions }>
       cmd.skip
       <{ pred }>).
  Proof.
    intros.
    repeat straightline.
    assumption.
  Qed.

  Lemma compile_word_of_Z_constant :
    forall (locals: Semantics.locals) (mem: Semantics.mem)
      tr functions T (pred: T -> predicate) (z: Z) k k_impl,
    forall var,
      let v := word.of_Z z in
      (let v := v in
       <{ Trace := tr;
          Memory := mem;
          Locals := map.put locals var v;
          Functions := functions }>
       k_impl
       <{ pred (k v) }>) ->
      <{ Trace := tr;
         Memory := mem;
         Locals := locals;
         Functions := functions }>
      cmd.seq (cmd.set var (expr.literal z)) k_impl
      <{ pred (nlet [var] v k) }>.
  Proof. repeat straightline; eassumption. Qed.

  Lemma compile_Z_constant :
    forall (locals: Semantics.locals) (mem: Semantics.mem)
      tr functions T (pred: T -> predicate) z k k_impl,
    forall var,
      let v := z in
      (let v := v in
       <{ Trace := tr;
          Memory := mem;
          Locals := map.put locals var (word.of_Z v);
          Functions := functions }>
       k_impl
       <{ pred (k v) }>) ->
      <{ Trace := tr;
         Memory := mem;
         Locals := locals;
         Functions := functions }>
      cmd.seq (cmd.set var (expr.literal z)) k_impl
      <{ pred (nlet [var] v k) }>.
  Proof. repeat straightline; eassumption. Qed.

  Lemma compile_nat_constant :
    forall (locals: Semantics.locals) (mem: Semantics.mem)
      tr functions T (pred: T -> predicate) n k k_impl,
    forall var,
      let v := n in
      (let v := v in
       <{ Trace := tr;
          Memory := mem;
          Locals := map.put locals var (word.of_Z (Z.of_nat v));
          Functions := functions }>
       k_impl
       <{ pred (k v) }>) ->
      <{ Trace := tr;
         Memory := mem;
         Locals := locals;
         Functions := functions }>
      cmd.seq (cmd.set var (expr.literal (Z.of_nat n))) k_impl
      <{ pred (nlet [var] v k) }>.
  Proof. repeat straightline; eassumption. Qed.

  Notation b2w b :=
    (word.of_Z (Z.b2z b)).

  Lemma compile_bool_constant :
    forall (locals: Semantics.locals) (mem: Semantics.mem)
      tr functions T (pred: T -> predicate) b k k_impl,
    forall var,
      let v := b in
      (let v := v in
       <{ Trace := tr;
          Memory := mem;
          Locals := map.put locals var (b2w v);
          Functions := functions }>
       k_impl
       <{ pred (k v) }>) ->
      <{ Trace := tr;
         Memory := mem;
         Locals := locals;
         Functions := functions }>
      cmd.seq (cmd.set var (expr.literal (Z.b2z v))) k_impl
      <{ pred (nlet [var] v k) }>.
  Proof. repeat straightline; eassumption. Qed.

  (* FIXME generalize *)
  Lemma compile_xorb :
    forall (locals: Semantics.locals) (mem: Semantics.mem)
      tr functions T (pred: T -> predicate)
      x x_var y y_var k k_impl,
    forall var,
      map.get locals x_var = Some (b2w x) ->
      map.get locals y_var = Some (b2w y) ->
      let v := xorb x y in
      (let v := v in
       <{ Trace := tr;
          Memory := mem;
          Locals := map.put locals var (b2w v);
          Functions := functions }>
       k_impl
       <{ pred (k v) }>) ->
      <{ Trace := tr;
         Memory := mem;
         Locals := locals;
         Functions := functions }>
      cmd.seq (cmd.set var (expr.op bopname.xor (expr.var x_var) (expr.var y_var)))
              k_impl
      <{ pred (k v) }>.
  Proof.
    intros.
    repeat straightline.
    eexists; split.
    { repeat straightline.
      eexists; split; [ eassumption | ].
      repeat straightline.
      eexists; split; [ eassumption | ].
      reflexivity. }
    red.
    rewrite <-(word.of_Z_unsigned (word.xor _ _)).
    rewrite word.unsigned_xor_nowrap.
    rewrite !word.unsigned_of_Z_b2z, Z.lxor_xorb.
    assumption.
  Qed.

  Lemma compile_add :
    forall (locals: Semantics.locals) (mem: Semantics.mem)
      tr functions T (pred: T -> predicate)
      x x_var y y_var k k_impl,
    forall var,
      map.get locals x_var = Some x ->
      map.get locals y_var = Some y ->
      let v := word.add x y in
      (let v := v in
       <{ Trace := tr;
          Memory := mem;
          Locals := map.put locals var v;
          Functions := functions }>
       k_impl
       <{ pred (k v) }>) ->
      <{ Trace := tr;
         Memory := mem;
         Locals := locals;
         Functions := functions }>
      cmd.seq (cmd.set var (expr.op bopname.add (expr.var x_var) (expr.var y_var)))
              k_impl
      <{ pred (nlet [var] v k) }>.
  Proof.
    repeat straightline.
    eexists; split; eauto.
    repeat straightline.
    eexists; split; eauto.
    repeat straightline.
    eexists; split; eauto.
  Qed.

  Lemma compile_eqb :
    forall (locals: Semantics.locals) (mem: Semantics.mem)
      tr functions T (pred: T -> predicate)
      x x_var y y_var k k_impl,
    forall var,
      map.get locals x_var = Some x ->
      map.get locals y_var = Some y ->
      let v := word.eqb x y in
      (let v := v in
       <{ Trace := tr;
          Memory := mem;
          Locals := map.put locals var (b2w v);
          Functions := functions }>
       k_impl
       <{ pred (nlet [var] v k) }>) ->
      <{ Trace := tr;
         Memory := mem;
         Locals := locals;
         Functions := functions }>
      cmd.seq (cmd.set var (expr.op bopname.eq (expr.var x_var) (expr.var y_var)))
              k_impl
      <{ pred (nlet [var] v k) }>.
  Proof.
    intros. repeat straightline'.
    subst_lets_in_goal.
    rewrite word.unsigned_eqb in *. cbv [Z.b2z] in *.
    destruct_one_match; eauto.
  Qed.

  (* TODO: make more types *)
  Lemma compile_copy_local :
    forall (locals: Semantics.locals) (mem: Semantics.mem)
      tr functions T (pred: T -> predicate) v0 k k_impl
      src_var dst_var,
      map.get locals src_var = Some v0 ->
      let v := v0 in
      (let v := v in
       <{ Trace := tr;
          Memory := mem;
          Locals := map.put locals dst_var v;
          Functions := functions }>
       k_impl
       <{ pred (k v) }>) ->
      <{ Trace := tr;
         Memory := mem;
         Locals := locals;
         Functions := functions }>
      cmd.seq (cmd.set dst_var (expr.var src_var)) k_impl
      <{ pred (nlet [dst_var] v k) }>.
  Proof.
    repeat straightline'; eauto.
  Qed.

  (* FIXME check out what happens when running straightline on a triple with a cmd.seq; could we get rid of the continuation arguments?  Would it require more rewrites? *)

  (* N.B. this should *not* be added to any compilation tactics, since it will
     always apply; it needs to be applied manually *)
  Lemma compile_unset :
    forall (locals: Semantics.locals) (mem: Semantics.mem)
      tr functions (pred: predicate)
      var cmd,
      <{ Trace := tr;
         Memory := mem;
         Locals := map.remove locals var;
         Functions := functions }>
      cmd
      <{ pred }> ->
      <{ Trace := tr;
         Memory := mem;
         Locals := locals;
         Functions := functions }>
      cmd.seq (cmd.unset var) cmd
      <{ pred }>.
  Proof.
    repeat straightline'; eauto.
  Qed.

  Definition map_remove_many {K V} {M: map.map K V} m (ks: list K) :=
    List.fold_left map.remove ks m.

  Lemma compile_unsets :
    forall vars (locals: Semantics.locals) (mem: Semantics.mem)
      cmd tr functions (pred: predicate),
      (<{ Trace := tr;
          Memory := mem;
          Locals := map_remove_many locals vars;
          Functions := functions }>
       cmd
       <{ pred }>) ->
      (<{ Trace := tr;
          Memory := mem;
          Locals := locals;
          Functions := functions }>
       fold_right (fun v c => cmd.seq (cmd.unset v) c) cmd vars
       <{ pred }>).
  Proof.
    induction vars; cbn [fold_right]; intros.
    - assumption.
    - apply compile_unset.
      apply IHvars.
      assumption.
  Qed.

  (* N.B. should only be added to compilation tactics that solve their subgoals,
     since this applies to any shape of goal *)
  Lemma compile_copy_pointer :
    forall (locals: Semantics.locals) (mem: Semantics.mem)
      tr functions {T} (pred: T -> predicate)
      {data} (Data : Semantics.word -> data -> Semantics.mem -> Prop)
      x_var x_ptr (x : data) k k_impl var R,

      (* This assumption is used to drive the compiler, but it's not used by the proof *)
      (Data x_ptr x * R)%sep mem ->
      map.get locals x_var = Some x_ptr ->

      let v := x in
      (let v := v in
       <{ Trace := tr;
          Memory := mem;
          Locals := map.put locals var x_ptr;
          Functions := functions }>
       k_impl
       <{ pred (k v) }>) ->
      <{ Trace := tr;
         Memory := mem;
         Locals := locals;
         Functions := functions }>
      cmd.seq (cmd.set var (expr.var x_var)) k_impl
      <{ pred (nlet [var] v k) }>.
  Proof.
    unfold postcondition_cmd.
    intros.
    repeat straightline'.
    eassumption.
  Qed.

  Lemma compile_if_word : (* FIXME generalize to arbitrary ifs *)
    forall (locals: Semantics.locals) (mem: Semantics.mem)
      tr functions T (pred: T -> predicate)
      t_var f_var (t f : word) (c : bool) c_var
      k k_impl var,

      map.get locals c_var = Some (b2w c) ->
      map.get locals t_var = Some t ->
      map.get locals f_var = Some f ->

      let v := if c then t else f in

      (let v := v in
       <{ Trace := tr;
          Memory := mem;
          Locals := map.put locals var v;
          Functions := functions }>
       k_impl
       <{ pred (k v) }>) ->
      <{ Trace := tr;
         Memory := mem;
         Locals := locals;
         Functions := functions }>
      cmd.seq
        (cmd.cond (expr.var c_var)
                  (cmd.set var (expr.var t_var))
                  (cmd.set var (expr.var f_var)))
        k_impl
      <{ pred (let/n x as var := v in
               k x) }>.
  Proof.
    intros.
    repeat straightline'.
    split_if ltac:(repeat straightline').
    { subst_lets_in_goal. rewrite word.unsigned_of_Z_b2z.
      cbv [Z.b2z]; destruct_one_match; try congruence; [ ].
      intros. repeat straightline'. eauto. }
    { subst_lets_in_goal. rewrite word.unsigned_of_Z_b2z.
      cbv [Z.b2z]; destruct_one_match; try congruence; [ ].
      intros. repeat straightline'. eauto. }
  Qed.

  Lemma compile_if_pointer :
    forall (locals: Semantics.locals) (mem: Semantics.mem)
      tr functions T (pred: T -> predicate)
      {data} (Data : Semantics.word -> data -> Semantics.mem -> Prop) Rt Rf
      t_var f_var t_ptr f_ptr (t f : data) (c : bool) c_var
      k k_impl var,

      (Data t_ptr t * Rt)%sep mem ->
      (Data f_ptr f * Rf)%sep mem ->

      map.get locals c_var = Some (b2w c) ->
      map.get locals t_var = Some t_ptr ->
      map.get locals f_var = Some f_ptr ->

      let v := if c then t else f in
      (let v := v in
       <{ Trace := tr;
          Memory := mem;
          Locals := map.put locals var (if c then t_ptr else f_ptr);
          Functions := functions }>
       k_impl
       <{ pred (k v) }>) ->
      <{ Trace := tr;
         Memory := mem;
         Locals := locals;
         Functions := functions }>
      cmd.seq
        (cmd.cond (expr.var c_var)
                  (cmd.set var (expr.var t_var))
                  (cmd.set var (expr.var f_var)))
        k_impl
      <{ pred (let/n x as var := v in k x) }>.
  Proof.
    intros.
    unfold postcondition_cmd.

    intros.
    repeat straightline'.
    split_if ltac:(repeat straightline').
    { subst_lets_in_goal. rewrite word.unsigned_of_Z_b2z.
      cbv [Z.b2z]; destruct_one_match; try congruence; [ ].
      intros. repeat straightline'. eauto. }
    { subst_lets_in_goal. rewrite word.unsigned_of_Z_b2z.
      cbv [Z.b2z]; destruct_one_match; try congruence; [ ].
      intros. repeat straightline'. eauto. }
  Qed.

  Lemma postcondition_func_norets_postcondition_cmd
        {T} spec (x: T) cmd R tr mem locals functions :
    (let pred a := postcondition_cmd (fun _ : Semantics.locals => True) (spec a) [] R tr in
     <{ Trace := tr;
        Memory := mem;
        Locals := locals;
        Functions := functions }>
     cmd
     <{ pred x }>) ->
    <{ Trace := tr;
       Memory := mem;
       Locals := locals;
       Functions := functions }>
    cmd
    <{ fun (tr' : Semantics.trace) (m' : Semantics.mem) (_ : Semantics.locals) =>
         postcondition_func_norets (spec x) R tr tr' m' [] }>.
  Proof.
    cbv [postcondition_func_norets
           postcondition_func postcondition_cmd]; intros.
    eapply Proper_cmd;
      [ solve [apply Proper_call] | repeat intro
        | eassumption ].
    sepsimpl; cleanup; eauto; [ ].
    match goal with H : map.getmany_of_list _ [] = Some _ |- _ =>
                    inversion H; clear H; subst
    end.
    eauto.
  Qed.

  Lemma getmany_list_map l :
    forall a vs (P :_ -> Prop),
      map.getmany_of_list l a = Some vs ->
      P vs ->
      WeakestPrecondition.list_map (WeakestPrecondition.get l) a P.
  Proof.
    induction a; cbn [WeakestPrecondition.list_map
                        WeakestPrecondition.list_map_body]; intros;
      match goal with
      | H : map.getmany_of_list _ [] = _ |- _ => cbn in H; congruence
      | H : map.getmany_of_list _ (_ :: _) = _ |- _ =>
        pose proof (map.getmany_of_list_exists_elem
                      _ _ _ _ ltac:(eauto using in_eq) H);
          cbn in H
      end.
      cleanup; eexists; ssplit; [ eassumption | ].
      repeat destruct_one_match_hyp; try congruence; [ ].
      repeat match goal with
             | H : Some _ = Some _ |- _ =>
               inversion H; clear H; subst
             end.
      eapply IHa; eauto.
  Qed.

  Lemma postcondition_func_postcondition_cmd
        {T} spec (x: T) cmd R tr mem locals retvars functions :
    (let pred a := postcondition_cmd (fun _ : Semantics.locals => True) (spec a) retvars R tr in
     <{ Trace := tr;
        Memory := mem;
        Locals := locals;
        Functions := functions }>
     cmd
     <{ pred x }>) ->
    <{ Trace := tr;
       Memory := mem;
       Locals := locals;
       Functions := functions }>
    cmd
    <{ fun tr' m' l =>
         WeakestPrecondition.list_map
           (WeakestPrecondition.get l) retvars
           (fun rets => postcondition_func (spec x) R tr tr' m' rets) }>.
  Proof.
    cbv [postcondition_func postcondition_cmd]; intros.
    cleanup.
    use_hyp_with_matching_cmd; cleanup; subst.
    eapply getmany_list_map; sepsimpl; eauto.
  Qed.
End with_semantics.

Ltac term_head x :=
  match x with
  | ?f _ => term_head f
  | _ => x
  end.

Ltac setup :=
  cbv [program_logic_goal_for];
  (* modified version of a clause in straightline *)
  (intros; WeakestPrecondition.unfold1_call_goal;
   (cbv beta match delta [WeakestPrecondition.call_body]);
   lazymatch goal with
   | |- if ?test then ?T else _ =>
     replace test with true by reflexivity; change_no_check T
   end; cbv beta match delta [WeakestPrecondition.func]);
  repeat straightline; subst_lets_in_goal; cbn [length];
  first [ apply postcondition_func_norets_postcondition_cmd
        | apply postcondition_func_postcondition_cmd ];
  intros;
  lazymatch goal with
  | |- context [ WeakestPrecondition.cmd _ _ _ _ _ (?pred ?spec) ] =>
    let hd := term_head spec in unfold hd
  | |- context [ postcondition_cmd _ (fun r => ?pred ?spec r) ] => (* FIXME *)
    let hd := term_head spec in unfold hd
  | _ => fail "Postcondition not in expected shape (?pred gallina_spec)"
  end.

Ltac lookup_variable m val :=
  lazymatch m with
  | map.put _ ?k val => constr:(k)
  | map.put ?m' _ _ => lookup_variable m' val
  end.

Ltac solve_map_get_goal :=
  match goal with
  | [  |- map.get ?m _ = Some ?val ] =>
    let var := lookup_variable m val in
    instantiate (1 := var);
    rewrite ?map.get_put_diff by congruence;
    apply map.get_put_same
  | [  |- map.get ?m _ = None ] =>
    rewrite ?map.get_put_diff by congruence;
    apply map.get_empty
  | [ H : map.get ?m1 _ = Some ?val |- map.get ?m2 _ = Some ?val ] =>
    rewrite ?map.get_put_diff; [ apply H | congruence .. ]
  | [ H : map.get _ ?k = None  |- map.get _ ?k = None ] =>
    rewrite ?map.get_put_diff; [ apply H | congruence .. ]
  end.

Create HintDb compiler.

Ltac compile_get_binding :=
  lazymatch goal with
  | |- context [ WeakestPrecondition.cmd _ _ _ _ _ (_ (nlet _ ?v _)) ] => v
  end.

(* Using [simple apply] ensures that Coq doesn't unfold [nlet]s *)
Ltac compile_basics :=
  gen_sym_inc;                  (* FIXME remove? *)
  let name := gen_sym_fetch "v" in
  let hd := compile_get_binding in
  first [simple eapply compile_word_of_Z_constant |
         simple eapply compile_Z_constant |
         simple eapply compile_nat_constant |
         simple eapply compile_bool_constant |
         simple eapply compile_xorb |
         simple eapply compile_add |
         simple eapply compile_eqb |
         simple eapply compile_if_word |
         simple eapply compile_if_pointer ].

Ltac compile_custom := fail.

Ltac compile_step :=
  lazymatch goal with
  | [  |- let _ := _ in _ ] => intros
  | [  |- WeakestPrecondition.cmd _ _ _ _ _ _ ] =>
    try clear_old_seps;
    first [compile_custom | compile_basics ]
  | [  |- sep _ _ _ ] =>
    autounfold with compiler in *;
    cbn [fst snd] in *;
    ecancel_assumption
  | [  |- map.get _ _ = _ ] =>
    first [ solve_map_get_goal
          | progress subst_lets_in_goal; solve_map_get_goal ]
  | [  |- map.getmany_of_list _ [] = Some _ ] => reflexivity
  | _ => eauto with compiler
  end.

(* only apply compile_step when repeat_compile_step solves all the side
     conditions but one *)
Ltac safe_compile_step :=
  compile_step; [ solve [repeat compile_step] .. | ].

Ltac compile_done := simple eapply compile_skip; repeat compile_step.

Ltac compile :=
  setup; repeat compile_step; compile_done.
