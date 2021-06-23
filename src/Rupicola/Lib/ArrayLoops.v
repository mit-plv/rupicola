Require Import Rupicola.Lib.Core.
Require Import Rupicola.Lib.Notations.
From Rupicola.Lib Require Import Core Notations Loops Arrays.

Section FoldsAsLoops.
  Context {semantics : Semantics.parameters}
          {semantics_ok : Semantics.parameters_ok semantics}.

  Lemma map_as_list_mutating_ranged_for {A} `{HasDefault A} Vfrom Vto Vxs xs:
    forall (f: A -> A),
      0 <= Z.of_nat (Datatypes.length xs) < 2 ^ Semantics.width ->
      List.map f xs =
      let/n from as Vfrom := word.of_Z 0 in
      let/n to as Vto := word.of_Z (Z.of_nat (List.length xs)) in
      ranged_for_u from to
                   (fun xs tok idx _ =>
                      let/n x := ListArray.get xs idx in
                      let/n x := f x in
                      let/n xs as Vxs := ListArray.put xs idx x in
                      (tok, xs))
                   xs.
  Proof.
    intros.
    apply map_as_mutating_ranged_for_u; unfold nlet; eauto.
    { unfold ListArray.get, ListArray.put, cast, Convertible_word_nat;
        simpl; intros.
      erewrite nth_error_nth; eauto. }
  Qed.

  Context (sz: AccessSize).
  Notation ai := (_access_info sz).
  Notation V := ai.(ai_type).

  Context (K := word).
  Context (K_to_nat := fun w => Z.to_nat (word.unsigned (width := Semantics.width) w)).

  Context
    (A: Type)
    (to_list: A -> list V)
    (get: A -> K -> V)
    (put: A -> K -> V -> A)
    (repr: address -> A -> Semantics.mem -> Prop).

  Definition array_repr a_ptr a :=
    (array ai.(ai_repr) (word.of_Z ai.(ai_width)) a_ptr a).

  (* Context (a : A) (a_ptr : word) (a_var : string) *)
  (*         (val: V) (val_var: string) *)
  (*         (idx : K) (idx_var : string). *)

  Context
    (Hget: forall idx a default,
       (K_to_nat idx < List.length (to_list a))%nat ->
       get a idx = nth (K_to_nat idx) (to_list a) default)
    (Hput: forall idx a val,
       (K_to_nat idx < List.length (to_list a))%nat ->
       to_list (put a idx val) =
       replace_nth (K_to_nat idx) (to_list a) val).

  Notation "!!" := (_ < _ < _) (only printing).

  Lemma map_as_any_mutating_ranged_for Vfrom Vto Vxs (xs: A):
    forall (f: V -> V),
      0 <= Z.of_nat (Datatypes.length (to_list xs)) < 2 ^ Semantics.width ->
      List.map f (to_list xs) =
      to_list
        (let/n from as Vfrom := word.of_Z 0 in
         let/n to as Vto := word.of_Z (Z.of_nat (List.length (to_list xs))) in
         ranged_for_u from to
                      (fun xs tok idx _ =>
                         let/n x := get xs idx in
                         let/n x := f x in
                         let/n xs as Vxs := put xs idx x in
                         (tok, xs))
                      xs).
  Proof.
    intros.
    unfold nlet.
    rewrite (map_as_list_mutating_ranged_for (H := get xs (word.of_Z 0)))
      with (Vfrom := Vfrom) (Vto := Vto) (Vxs := Vxs); unfold nlet; eauto.
    unfold ranged_for_u, ranged_for_w, w_body_tok.
    rewrite !word.unsigned_of_Z, !word.wrap_small by lia.
    unfold ranged_for, ranged_for' in *.
    (* remember (to_list xs). *)
    generalize (Z.le_refl (Z.of_nat (List.length (to_list xs)))).
    induction (to_list xs) at 1 3 4 6 7; cbn -[ai]; intros.
    - rewrite !ranged_for_break_exit; lia || eauto.
    - replace (Z.of_nat (S (Datatypes.length l)))
              with (Z.of_nat (Datatypes.length l) + 1) by lia.
      erewrite !ranged_for_break_unfold_r_nstop;
        (reflexivity || lia || eauto using ranged_for_break_nonstop).
      cbn [snd]; rewrite IHl by lia.
      set (ranged_for_break _ _ _ _ _).
      unfold ListArray.get, ListArray.put, cast, Convertible_word_nat.
      erewrite Hget.
      rewrite Hput.
      apply ranged_for_break_nonstop; reflexivity.
      rewrite IHl.
      cbv zeta.
      rewrite <- IHl.
      ranged_for



    { unfold ListArray.get, ListArray.put, cast, Convertible_word_nat;
        simpl; intros.

      assert (Z.to_nat (word.unsigned idx) < Datatypes.length xs0)%nat.


      rewrite Hput.
      subst K A K_to_nat; rewrite Hget in H0; inversion H0; try reflexivity.

      congruence.
      rewrite <- H0.
      symmetry.
      apply Hget.
      rewrite <- Hget.
      apply H0.
      rewrite Hget.
      replace x with (get xs0 idx) in *.

      pose proof Hget idx xs0.
      unfold K_to_nat in *.
      assert (Z.to_nat (word.unsigned idx) < Datatypes.length xs0)%nat by admit.
      specialize (H1 H).

      Set Printing Implicit.
      unfold V, ai in H1.
      rewrite H1 in H0.

      erewrite nth_error_nth; eauto. }
  Qed.
End FoldsAsLoops.

Section with_parameters.
  Context {semantics : Semantics.parameters}
          {semantics_ok : Semantics.parameters_ok semantics}.

  (* TODO: need to have a lemma for compiling maps directly, which requires generalizing the loop lemma to accept expressions instead of variables. *)

    Lemma _compile_ranged_for A {tr mem locals functions}
          (from to: Z) body (a0: A) :
      let v := ranged_for from to body a0 in
      forall {P} {pred: P v -> predicate}
        (loop_pred: forall (idx: Z) (a: A), predicate)
        {k: nlet_eq_k P v} {k_impl} {body_impl}
        (from_var to_var: string) vars,

        let lp from tok_acc tr mem locals :=
            let from := ExitToken.branch (fst tok_acc) to (from + 1) in
            loop_pred from (snd tok_acc) tr mem locals in

        (forall from a0 tr mem locals,
            loop_pred from a0 tr mem locals ->
            map.getmany_of_list locals [from_var; to_var] =
            Some [word.of_Z from; word.of_Z to]) ->

        loop_pred from a0 tr mem locals ->

        (if signed then in_signed_bounds from /\ in_signed_bounds to
         else in_unsigned_bounds from /\ in_unsigned_bounds to) ->

        ((* loop body *)
          let lp := lp in
          forall tr mem locals from'
            (Hl: from - 1 < from')
            (Hr: from' < to)
            (Hr': from' <= to),
            let a := ranged_for' from from' (wbody body pr Hr') a0 in
            let prev_tok := fst a in
            let acc := snd a in  (* FIXME use primitive projections? *)
            ExitToken.get prev_tok = false ->
            loop_pred from' acc tr mem locals ->
            (<{ Trace := tr;
                Memory := mem;
                Locals := locals;
                Functions := functions }>
             body_impl
             <{ lp from' (body acc ExitToken.new from' (conj Hl Hr)) }>)) ->
        (let v := v in
         forall from' tr mem locals,
           loop_pred from' v tr mem locals ->
           (<{ Trace := tr;
               Memory := mem;
               Locals := locals;
               Functions := functions }>
            k_impl
            <{ pred (k v eq_refl) }>)) ->
        <{ Trace := tr;
           Memory := mem;
           Locals := locals;
           Functions := functions }>
        cmd.seq
          (cmd.while
             (expr.op (if signed then bopname.lts else bopname.ltu)
                      (expr.var from_var)
                      (expr.var to_var))
             body_impl)
          k_impl
        <{ pred (nlet_eq vars v k) }>.
    Proof.
    Qed.

    (* TODO Use a section? *)

    Lemma compile_ranged_for_with_auto_increment A {tr mem locals functions}
          (from to: Z) body (a0: A) :
      let v := ranged_for from to body a0 in
      forall {P} {pred: P v -> predicate}
        (loop_pred: forall (idx: Z) (a: A), predicate)
        {k: nlet_eq_k P v} {k_impl} {body_impl}
        (from_var to_var: string) vars,

        let lp from tok_acc tr mem locals :=
            let from := ExitToken.branch (fst tok_acc) (to - 1) from in
            loop_pred from (snd tok_acc) tr mem locals in

        (forall from a0 tr mem locals,
            loop_pred from a0 tr mem locals ->
            map.getmany_of_list locals [from_var; to_var] =
            Some [word.of_Z from; word.of_Z to]) ->

        (forall from from' acc tr mem locals,
            loop_pred from acc tr mem locals ->
            loop_pred from' acc tr mem (map.put locals from_var (word.of_Z from'))) ->

        loop_pred from a0 tr mem locals ->

        (if signed then in_signed_bounds from /\ in_signed_bounds to
         else in_unsigned_bounds from /\ in_unsigned_bounds to) ->

        ((* loop body *)
          let lp := lp in
          forall tr mem locals from'
            (Hl: from - 1 < from')
            (Hr: from' < to)
            (Hr': from' <= to),
            let a := ranged_for' from from' (wbody body pr Hr') a0 in
            let prev_tok := fst a in
            let acc := snd a in  (* FIXME use primitive projections? *)
            ExitToken.get prev_tok = false ->
            loop_pred from' acc tr mem locals ->
            (<{ Trace := tr;
                Memory := mem;
                Locals := locals;
                Functions := functions }>
             body_impl
             <{ lp from' (body acc ExitToken.new from' (conj Hl Hr)) }>)) ->
        (let v := v in
         forall from' tr mem locals,
           loop_pred from' v tr mem locals ->
           (<{ Trace := tr;
               Memory := mem;
               Locals := locals;
               Functions := functions }>
            k_impl
            <{ pred (k v eq_refl) }>)) ->
        <{ Trace := tr;
           Memory := mem;
           Locals := locals;
           Functions := functions }>
        cmd.seq
          (cmd.while
             (expr.op (if signed then bopname.lts else bopname.ltu)
                      (expr.var from_var)
                      (expr.var to_var))
             (cmd.seq body_impl
                      (cmd.set from_var
                               (expr.op bopname.add
                                        (expr.var from_var)
                                        (expr.literal 1)))))
          k_impl
        <{ pred (nlet_eq vars v k) }>.
    Proof.
      intros; eapply _compile_ranged_for; try eassumption.
      (* Goal: (body; from := from + 1) does the right thing *)
      intros. simpl.
      eapply WeakestPrecondition_weaken; cycle 1.
      red; eauto.
      (* Goal: (from := from + 1) does the right thing *)

      subst lp acc a; cbv beta; intros * Hlp.

      eexists; split.
      eexists; split.
      eauto using getmany0.

      simpl. red. red. rewrite <- word.ring_morph_add.
      rewrite (ExitToken.map_branch (fun z => word.of_Z (z + 1))).
      ring_simplify (to - 1 + 1).
      rewrite <- ExitToken.map_branch.
      reflexivity.

      red. red. eauto.
    Qed.

    Context {to_Z: word -> Z}
            (of_Z_to_Z: forall w, word.of_Z (to_Z w) = w)
            (to_Z_of_Z: forall l h w,
                to_Z l <= w <= to_Z h ->
                to_Z (word.of_Z w) = w).

    Lemma compile_ranged_for_w A {tr mem locals functions}
          (from to: word)
          (H: if signed then in_signed_bounds (to_Z from) /\ in_signed_bounds (to_Z to)
              else in_unsigned_bounds (to_Z from) /\ in_unsigned_bounds (to_Z to))
          body (a0: A) :
      let v := ranged_for_w from to to_Z_of_Z body a0 in
      forall {P} {pred: P v -> predicate}
        (loop_pred: word -> A -> predicate)
        {k: nlet_eq_k P v} {k_impl} {body_impl}
        (from_var to_var: string) vars,

        let lp from tok_acc tr mem locals :=
            let from := ExitToken.branch (fst tok_acc) (word.sub to (word.of_Z 1)) from in
            loop_pred from (snd tok_acc) tr mem locals in

        (forall from a0 tr mem locals,
            loop_pred from a0 tr mem locals ->
            map.getmany_of_list locals [from_var; to_var] =
            Some [from; to]) ->

        (forall from from' acc tr mem locals,
            loop_pred from acc tr mem locals ->
            loop_pred from' acc tr mem (map.put locals from_var from')) ->

        loop_pred from a0 tr mem locals ->

        ((* loop body *)
          let lp := lp in
          forall tr mem locals from'
            (Hl: to_Z from - 1 < to_Z from')
            (Hr: to_Z from' < to_Z to)
            (Hr': to_Z from' <= to_Z to),
            let tok := ExitToken.new in
            let a := ranged_for' (to_Z from) (to_Z from')
                                (w_body_tok _ _ to_Z_of_Z
                                            (wbody body pr Hr')) a0 in
            ExitToken.get (fst a) = false ->

            loop_pred from' (snd a) tr mem locals ->
            (<{ Trace := tr;
                Memory := mem;
                Locals := locals;
                Functions := functions }>
             body_impl
             <{ lp from' (body (snd a) tok from' (conj Hl Hr)) }>)) ->
        (let v := v in
         forall from' tr mem locals,
           loop_pred from' v tr mem locals ->
           (<{ Trace := tr;
               Memory := mem;
               Locals := locals;
               Functions := functions }>
            k_impl
            <{ pred (k v eq_refl) }>)) ->
        <{ Trace := tr;
           Memory := mem;
           Locals := locals;
           Functions := functions }>
        cmd.seq
          (cmd.while
             (expr.op (if signed then bopname.lts else bopname.ltu)
                      (expr.var from_var)
                      (expr.var to_var))
             (cmd.seq
                body_impl
                (cmd.set from_var
                         (expr.op bopname.add
                                  (expr.var from_var)
                                  (expr.literal 1)))))
          k_impl
        <{ pred (nlet_eq vars v k) }>.
    Proof.
      intros * Hlocals Hfromindep Hinit Hbody Hk.
      apply compile_ranged_for_with_auto_increment
        with (loop_pred := fun z => loop_pred (word.of_Z z)).

      - rewrite of_Z_to_Z; eauto.
      - eauto.
      - rewrite of_Z_to_Z; eassumption.
      - eassumption.
      - intros.
        assert (exists h, a = ranged_for' (to_Z from) (to_Z (word.of_Z from')) (w_body_tok from (word.of_Z from') to_Z_of_Z (wbody body pr h)) a0) as [h eqn].
        { unshelve eexists; subst a.
          { rewrite (to_Z_of_Z from to); lia. }
          unshelve apply ranged_for'_Proper; reflexivity || eauto.
          { rewrite (to_Z_of_Z from to); try reflexivity; lia. }
          { unfold w_body_tok; intros; f_equal.
            apply range_unique. } }

        clearbody a; subst a; unfold w_body_tok at 1; cbv beta.
        eapply WeakestPrecondition_weaken; cycle 1.
        + unshelve (apply Hbody; eassumption);
            rewrite (to_Z_of_Z from to); lia.
        + unfold lp, lp0.
          set (ranged_for' _ _ _ _) as fr.

          set (body _ _ _ _) as b0; set (body _ _ _ _) as b1; assert (b0 = b1).
          { subst b0 b1. f_equal. apply range_unique. }
          clearbody b0; subst.

          intros * Hlp.
          * destruct (fst b1); simpl in *;
              repeat rewrite ?word.ring_morph_add, ?word.ring_morph_sub, ?of_Z_to_Z;
              eauto.
      - intros; eapply Hk.
        eassumption.
    Qed.
  End Generic.

  Context {A: Type}
          {tr : Semantics.trace}
          {mem : Semantics.mem}
          {locals : Semantics.locals}
          {functions : list (string * (list string * list string * cmd))}
          (from to : word).

  Definition compile_ranged_for_u :=
    @compile_ranged_for_w false _ word.of_Z_unsigned word_unsigned_of_Z_bracketed
                          A tr mem locals functions from to
                          (conj (word.unsigned_range _) (word.unsigned_range _)).

  Definition compile_ranged_for_s :=
    @compile_ranged_for_w true _ word.of_Z_signed word_signed_of_Z_bracketed
                          A tr mem locals functions from to
                          (conj (word.signed_range _) (word.signed_range _)).
End with_parameters.

Require bedrock2.BasicC64Semantics.

Module test.
  Import BasicC64Semantics.

  Time Compute (ranged_for 0 15
                        (fun acc t idx _ =>
                           if Z.ltb 11 idx then
                             let t' := ExitToken.break t in
                             (t', acc)
                           else
                             let acc := idx :: acc in
                             (t, acc)) []).

  Time Compute (ranged_for_u (word.of_Z 0) (word.of_Z 15)
                          (fun acc t idx _ =>
                             if word.ltu (word.of_Z 11) idx then
                               let t' := ExitToken.break t in
                               (t', acc)
                             else
                               let acc := idx :: acc in
                               (t, acc)) []).
End test.
