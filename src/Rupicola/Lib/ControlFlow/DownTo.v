Require Import Rupicola.Lib.Core.
Require Import Rupicola.Lib.Notations.
Require Import Rupicola.Lib.Tactics.
Require Import Rupicola.Lib.Invariants.
Require Import Rupicola.Lib.Gensym.

Local Open Scope nat_scope.

Section Gallina.
  Context {A: Type}.
  Implicit Type a : A.
  Implicit Type step : A -> nat -> A.

  Definition downto' a0 start count step : A :=
    fold_left step (rev (skipn start (seq 0 count))) a0.

  Definition downto a0 count step : A :=
    downto' a0 0 count step.

  Open Scope nat_scope.

  Lemma downto'_step start count step a0 :
    0 < start <= count ->
    step (downto' a0 start count step) (start - 1) =
    downto' a0 (start - 1) count step.
  Proof. cbv [downto']; apply fold_left_skipn_seq. Qed.

  Lemma Nat_iter_as_downto' n (f: A -> A) : forall a i,
      Nat.iter n f a = downto' a i (i + n) (fun a _ => f a).
  Proof.
    unfold downto'.
    setoid_rewrite List.skipn_seq.
    setoid_rewrite (Nat.add_comm _ n); setoid_rewrite Nat.add_sub.
    simpl; induction n; simpl; intros.
    - reflexivity.
    - rewrite fold_left_app.
      auto using f_equal.
  Qed.

  Lemma Nat_iter_as_downto'_sub n (f: A -> A) a i:
    i <= n ->
    Nat.iter (n - i) f a = downto' a i n (fun a _ => f a).
  Proof.
    intros; replace n with (i + (n - i)) at 2 by lia.
    apply Nat_iter_as_downto'.
  Qed.

  Lemma Nat_iter_as_downto n (f: A -> A) a :
    Nat.iter n f a = downto a n (fun a _ => f a).
  Proof. apply (Nat_iter_as_downto' n f a 0). Qed.
End Gallina.

Definition cmd_downto i_var step_impl :=
  (* while (i > 0) { i--; step i } *)
  (cmd.while
     (expr.op bopname.ltu (expr.literal 0) (expr.var i_var))
     (cmd.seq (cmd.set i_var (expr.op bopname.sub (expr.var i_var) (expr.literal 1)))
              step_impl)).

Definition cmd_downto_fresh i_var i_expr step_impl k_impl :=
  cmd.seq (cmd.set i_var i_expr)
          (cmd.seq (cmd_downto i_var step_impl)
                   k_impl).

Section Compilation.
  Context {width: Z} {BW: Bitwidth width}.
  Local Notation word := (bits width).
  Context {mem: map.map word Byte.byte}.
  Context {locals: map.map String.string word}.
  Context {ext_spec: bedrock2.Semantics.ExtSpec}.
  Context {mem_ok : map.ok mem}.
  Context {locals_ok : map.ok locals}.
  Context {ext_spec_ok : Semantics.ext_spec.ok ext_spec}.
  Implicit Types (x : word).

  (* helper lemma for subtracting one from the loop counter *)
  Lemma word_to_nat_sub_1 x n :
    (0 < Zmod.unsigned x)%Z ->
    Zmod.unsigned x = Z.of_nat n ->
    Zmod.unsigned (Zmod.sub x (bits.of_Z width 1)) = Z.of_nat (n - 1).
  Proof.
    intros. pose proof (bits.unsigned_range x width_nonneg).
    rewrite Nat2Z.inj_sub by lia.
    rewrite Zmod.unsigned_sub, Zmod.of_Z_1, (bits.unsigned_1 width_ge_1).
    rewrite Z.mod_small by lia.
    f_equal. congruence.
  Qed.

  (* helper lemma for continuation case *)
  Lemma word_to_nat_0 x n :
    (Zmod.unsigned x <= 0)%Z ->
    Zmod.unsigned x = Z.of_nat n ->
    x = Zmod.zero.
  Proof.
    intros. pose proof (bits.unsigned_range x width_nonneg).
    apply Zmod.unsigned_inj; rewrite Zmod.unsigned_0; lia.
  Qed.

  Lemma word_of_Z_sub_1 n:
    n > 0 ->
    bits.of_Z width (Z.of_nat (n - 1)) =
    Zmod.sub
             (bits.of_Z width (Z.of_nat n)) (bits.of_Z width 1).
  Proof.
    intros; rewrite <- Zmod.of_Z_sub.
    f_equal; lia.
  Qed.

  Lemma compile_downto_continued : forall {tr mem locals functions} {A} (a0: A) count step,
      let v := downto a0 count step in
      forall {P} {pred: P v -> predicate} {k: nlet_eq_k P v} {k_impl step_impl}
        (loop_pred : nat -> A -> predicate)
        i_var vars,

        (Z.of_nat count < 2 ^ width)%Z ->
        loop_pred count a0 tr mem locals ->

        (forall i st tr mem locals,
            loop_pred i st tr mem locals ->
            map.get locals i_var = Some (bits.of_Z width (Z.of_nat i))) ->

        ((* loop body *)
         forall tr l m i,
           let st := downto' a0 (S i) count step in
           let wi := bits.of_Z width (Z.of_nat i) in
           loop_pred (S i) st tr m l ->
           i < count ->
           <{ Trace := tr;
              Memory := m;
              Locals := map.put l i_var wi;
              Functions := functions }>
           step_impl
           <{ loop_pred i (step st i) }>) ->

        (let v := v in
         (* continuation *)
         forall tr l m,
           loop_pred 0 v tr m l ->
           <{ Trace := tr;
              Memory := m;
              Locals := l;
              Functions := functions }>
           k_impl
           <{ pred (k v eq_refl) }>) ->

        <{ Trace := tr;
           Memory := mem;
           Locals := locals;
           Functions := functions }>
        cmd.seq (cmd_downto i_var step_impl) k_impl
        <{ pred (nlet_eq vars v k) }>.
  Proof.
    repeat straightline.

    (* handle while *)
    WeakestPrecondition.unfold1_cmd_goal; (cbv beta match delta [WeakestPrecondition.cmd_body]).
    eapply Loops.wp_while.

    exists nat, lt.
    exists (fun i t m l =>
         let st := downto' a0 i count step in
         loop_pred i st t m l /\ i <= count).
    ssplit; eauto using lt_wf; [ | ].

    { cbv zeta. subst.
      exists count; split.
      - unfold downto'; rewrite skipn_all2 by (rewrite seq_length; lia); eauto.
      - eauto using Zle_0_nat. }

    { repeat straightline'.
      repeat (eexists; split; repeat straightline; eauto).
      rewrite !bits.unsigned_of_Z_small by (pose proof modulus_pos; lia).
      destruct_one_match;
        rewrite ?Zmod.unsigned_0, ?(bits.unsigned_1 width_ge_1);
        ssplit; try lia; [ | ].
      { repeat straightline'.
        repeat (eexists; split; repeat straightline; eauto).
        subst_lets_in_goal.
        lazymatch goal with
        | [ Hcmd : context [WeakestPrecondition.cmd _ ?impl ],
            Hinv : context [loop_pred ?i ?st]
          |- WeakestPrecondition.cmd
              _ ?impl ?tr ?mem
              (map.put ?locals ?i_var (Zmod.sub ?wi (bits.of_Z _ 1)))
              ?post ] =>
          specialize (Hcmd tr locals mem (i - 1));
            replace (S (i-1)) with i in Hcmd by lia;
            unshelve epose proof (Hcmd _ _); clear Hcmd
        end; [ eauto; lia .. | ].

        rewrite <- word_of_Z_sub_1 by lia.
        use_hyp_with_matching_cmd; [ ].
        cbv [postcondition_cmd] in *; sepsimpl; cleanup; subst.
        repeat match goal with
               | |- exists _, _ => eexists; ssplit
               | _ => erewrite <- downto'_step; [ cbn [fst snd]; ecancel_assumption | ]
               | _ => lia || solve [eauto using word_to_nat_sub_1]
               end. }
      { repeat straightline'.
        match goal with
        | [ H: (Z.of_nat ?n <= 0)%Z |- _ ] => replace n with 0 in * by lia
        end.
        use_hyp_with_matching_cmd; subst_lets_in_goal; eauto. } }
  Qed.

  Lemma compile_downto : forall {tr mem locals functions} {A} (a0: A) count step,
      let v := downto a0 count step in
      forall {P} {pred: P v -> predicate} {k: nlet_eq_k P v} {k_impl step_impl}
        (loop_pred : nat -> A -> predicate)
        i_var i_expr vars,

        let zcount := Z.of_nat count in
        let wcount := bits.of_Z width zcount in

        (zcount < 2 ^ width)%Z ->
        WeakestPrecondition.dexpr mem locals i_expr wcount ->

        let locals0 := map.put locals i_var wcount in
        loop_pred count a0 tr mem locals0 ->

        (forall i st tr mem locals,
            loop_pred i st tr mem locals ->
            map.get locals i_var = Some (bits.of_Z width (Z.of_nat i))) ->

        (let lp := loop_pred in
         (* loop body *)
         forall tr l m i,
           let st := downto' a0 (S i) count step in
           let wi := bits.of_Z width (Z.of_nat i) in
           loop_pred (S i) st tr m l ->
           i < count ->
           <{ Trace := tr;
              Memory := m;
              Locals := map.put l i_var wi;
              Functions := functions }>
           step_impl
           <{ lp i (step st i) }>) ->

        (let v := v in
         (* continuation *)
         forall tr l m,
           loop_pred 0 v tr m l ->
           <{ Trace := tr;
              Memory := m;
              Locals := l;
              Functions := functions }>
           k_impl
           <{ pred (k v eq_refl) }>) ->

        <{ Trace := tr;
           Memory := mem;
           Locals := locals;
           Functions := functions }>
        cmd_downto_fresh i_var i_expr step_impl k_impl
        <{ pred (nlet_eq vars v k) }>.
  Proof.
      intros.
      unfold cmd_downto_fresh.
      repeat straightline; eexists; split; eauto.
      eapply compile_downto_continued; eauto.
  Qed.

  Lemma compile_Nat_iter : forall [tr mem locals functions] n {A} f (a: A),
      let v := Nat.iter n f a in
      forall {P} {pred: P v -> predicate} {k: nlet_eq_k P v} {k_impl f_impl}
        (loop_pred : nat -> A -> predicate)
        i_var i_expr vars,

        let zn := Z.of_nat n in
        let wn := bits.of_Z width zn in

        (zn < 2 ^ width)%Z ->
        WeakestPrecondition.dexpr mem locals i_expr wn ->

        let locals0 := map.put locals i_var wn in
        loop_pred n a tr mem locals0 ->

        (forall i st tr mem locals,
            loop_pred i st tr mem locals ->
            map.get locals i_var = Some (bits.of_Z width (Z.of_nat i))) ->

        (let lp := loop_pred in
         (* loop body *)
         forall tr l m i,
           let st := Nat.iter (n - S i) f a in
           let wi := bits.of_Z width (Z.of_nat i) in
           loop_pred (S i) st tr m l ->
           i < n ->
           <{ Trace := tr;
              Memory := m;
              Locals := map.put l i_var wi;
              Functions := functions }>
           f_impl
           <{ lp i (f st) }>) ->

        (let v := v in
         (* continuation *)
         forall tr l m,
           loop_pred 0 v tr m l ->
           <{ Trace := tr;
              Memory := m;
              Locals := l;
              Functions := functions }>
           k_impl
           <{ pred (k v eq_refl) }>) ->

        <{ Trace := tr;
           Memory := mem;
           Locals := locals;
           Functions := functions }>
        cmd_downto_fresh i_var i_expr f_impl k_impl
        <{ pred (nlet_eq vars v k) }>.
  Proof.
    cbv zeta; intros until a.
    rewrite Nat_iter_as_downto; intros * ???? Hf Hk.
    eapply compile_downto; eauto; [].
    cbv zeta; intros.
    rewrite <- Nat_iter_as_downto'_sub by lia;
      eapply Hf; [ | lia]; rewrite Nat_iter_as_downto'_sub by lia.
    eassumption.
  Qed.
End Compilation.

Ltac make_downto_predicate i_var i_arg vars args tr pred locals :=
  lazymatch substitute_target i_var i_arg pred locals with
  | (?pred, ?locals) =>
    make_predicate vars args tr pred locals
  end.

Ltac infer_downto_predicate' i_var argstype vars tr pred locals :=
  let val_pred :=
      constr:(fun (idx: nat) (args: argstype) =>
                ltac:(let f := make_downto_predicate
                                i_var idx vars args tr pred locals in
                      exact f)) in
  eval cbv beta in val_pred.

Ltac infer_downto_predicate i_var :=
  _infer_predicate_from_context
    ltac:(infer_downto_predicate' i_var).

Ltac _compile_downto locals lemma :=
  let i_v := gensym locals "i" in
  let lp := infer_downto_predicate i_v in
  eapply lemma with (i_var := i_v) (loop_pred := lp).

Ltac compile_downto :=
  lazymatch goal with
  | [ |- WeakestPrecondition.cmd _ _ _ _ ?locals (_ (nlet_eq _ ?v _)) ] =>
    lazymatch v with
    | downto _ _ _ => _compile_downto locals compile_downto
    | Nat.iter _ _ _ => _compile_downto locals compile_Nat_iter
    end
  end.

Module DownToCompiler.
  #[export] Hint Extern 1 (WP_nlet_eq (downto _ _ _)) =>
    compile_downto; shelve : compiler.
  #[export] Hint Extern 1 (WP_nlet_eq (Nat.iter _ _ _)) =>
    compile_downto; shelve : compiler.
End DownToCompiler.

Section GhostCompilation.
  Context {width: Z} {BW: Bitwidth width}.
  Local Notation word := (bits width).
  Context {mem: map.map word Byte.byte}.
  Context {locals: map.map String.string word}.
  Context {ext_spec: bedrock2.Semantics.ExtSpec}.
  Context {mem_ok : map.ok mem}.
  Context {locals_ok : map.ok locals}.
  Context {ext_spec_ok : Semantics.ext_spec.ok ext_spec}.
  Implicit Types (x : word).

  (* helper definition *)
  Definition downto'_dependent
             {A B} initA initB start count
             (stepA : A -> nat -> A) (stepB : A -> B -> nat -> B) :=
    fold_left_dependent stepA stepB
                        (rev (skipn start (seq 0 count))) initA initB.

  Lemma downto'_dependent_fst {A B} initA initB stepA stepB i count :
      fst (@downto'_dependent A B initA initB i count stepA stepB) =
      downto' initA i count stepA.
  Proof. apply fold_left_dependent_fst. Qed.

  Open Scope nat_scope.

  Lemma downto'_dependent_step
        {A B} i count stepA stepB (initA : A) (initB : B) :
    0 < i <= count ->
    (fun ab c =>
       (stepA (fst ab) c, stepB (fst ab) (snd ab) c))
      (downto'_dependent initA initB i count stepA stepB) (i-1)
    = downto'_dependent initA initB (i-1) count stepA stepB.
  Proof. apply fold_left_skipn_seq. Qed.

  (* In this lemma, state refers to the accumulator type for the Gallina downto
     loop, and ghost_state is any extra information that locals/memory invariants
     need access to. *)
  (* FIXME Do we actually need ghost state? *)
  (* TODO: consider taking in range of count instead of providing word? *)
  Lemma compile_downto_with_ghost_state :
    forall {tr mem locals functions} {state} (init : state) count step,
    let v := downto init count step in
    forall {P} {pred: P v -> predicate} {k: nlet_eq_k P v} {k_impl step_impl}
      wcount {ghost_state} (ginit : ghost_state)
      (ghost_step : state -> ghost_state -> nat -> ghost_state)
      (Inv : nat -> ghost_state -> state -> predicate) (* loop invariant *)
      i_var vars,

      Inv count ginit init tr mem (map.remove locals i_var) ->

      map.get locals i_var = Some wcount ->
      Zmod.unsigned wcount = Z.of_nat count ->

      (let v := v in
       (* loop iteration case *)
       forall tr l m i wi,
         let stgst := downto'_dependent init ginit (S i) count step ghost_step in
         let st := fst stgst in let gst := snd stgst in
         let inv' v tr' mem' locals :=
             map.get locals i_var = Some wi /\
             Inv i (ghost_step st gst i) v tr' mem' (map.remove locals i_var) in
         let gst' := ghost_step st gst i in
         Inv (S i) gst st tr m (map.remove l i_var) ->
         Zmod.unsigned wi = Z.of_nat i ->
         i < count ->
         <{ Trace := tr;
            Memory := m;
            Locals := map.put l i_var wi;
            Functions := functions }>
         step_impl
         <{ inv' (step st i)}>) ->
      (let v := v in
       (* continuation *)
       forall tr l m gst,
         Inv 0 gst v tr m (map.remove l i_var) ->
         map.get l i_var = Some Zmod.zero ->
         <{ Trace := tr;
            Memory := m;
            Locals := l;
            Functions := functions }>
         k_impl
         <{ pred (k v eq_refl) }>) ->

      <{ Trace := tr;
         Memory := mem;
         Locals := locals;
         Functions := functions }>
      cmd.seq (cmd_downto i_var step_impl) k_impl
      <{ pred (nlet_eq vars v k) }>.
  Proof.
    repeat straightline'.

    (* handle while *)
    WeakestPrecondition.unfold1_cmd_goal;
      (cbv beta match delta [WeakestPrecondition.cmd_body]).
    eapply Loops.wp_while.
    exists nat, lt.
    exists (fun i t m l =>
              let stgst :=
                  downto'_dependent init ginit i count
                                    step ghost_step in
              let st := fst stgst in
              let gst := snd stgst in
              Inv i gst st t m (map.remove l i_var)
              /\ i <= count
              /\ (exists wi,
                     Zmod.unsigned wi = Z.of_nat i
                     /\ map.get l i_var = Some wi)).
    ssplit; eauto using lt_wf; [ | ].

    { cbv zeta. subst.
      exists count; split.
      - unfold downto'_dependent;
          rewrite skipn_all2 by (rewrite seq_length; lia); eauto.
      - eauto using Zle_0_nat. }

    { intros. cleanup; subst.
      repeat straightline'.
      lazymatch goal with x := context [Z.ltb] |- _ => subst x end.
      rewrite bits.unsigned_of_Z_small by (pose proof modulus_pos; lia).
      destruct_one_match;
        rewrite ?Zmod.unsigned_0, ?(bits.unsigned_1 width_ge_1);
        ssplit; try lia; [ | ].
      { repeat straightline'.
        subst_lets_in_goal.
        lazymatch goal with
        | Hcmd:context [ WeakestPrecondition.cmd _ ?impl ],
               Hinv : context [Inv _ (snd ?stgst) (fst ?stgst)],
                      Hi : Zmod.unsigned ?wi = Z.of_nat ?i
          |- WeakestPrecondition.cmd
               _ ?impl ?tr ?mem
               (map.put ?locals ?i_var (Zmod.sub ?wi (bits.of_Z _ 1)))
               ?post =>
          specialize (Hcmd tr locals mem (i-1) (Zmod.sub wi (bits.of_Z width 1)));
            replace (S (i-1)) with i in Hcmd by lia;
            unshelve epose proof (Hcmd _ _ _); clear Hcmd
        end;
          [ eauto using word_to_nat_sub_1; lia .. | ].
        use_hyp_with_matching_cmd; [ ].
        cbv [postcondition_cmd] in *; sepsimpl; cleanup; subst.
        repeat match goal with
               | |- exists _, _ => eexists; ssplit
               | _ => erewrite <-downto'_dependent_step; [ cbn [fst snd]; ecancel_assumption | ]
               | _ => lia || solve [eauto using word_to_nat_sub_1]
               end. }
      { repeat straightline'.
        rewrite @downto'_dependent_fst in *.
        match goal with
        | H : (Zmod.unsigned ?x <= 0)%Z |- _ =>
          eapply word_to_nat_0 in H; [ | solve [eauto] .. ]; subst
        end.
        match goal with
          H : Zmod.unsigned Zmod.zero = Z.of_nat ?n |- _ =>
          assert (n = 0) by (rewrite Zmod.unsigned_0 in H; lia)
        end; subst.
        use_hyp_with_matching_cmd; subst_lets_in_goal; eauto. } }
  Qed.
End GhostCompilation.
