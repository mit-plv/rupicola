Require Import Rupicola.Lib.Core.
Require Import Rupicola.Lib.Notations.

Module Type ExitToken_sig.
  Axiom t : Set.
  Axiom new : t.
  Axiom get : t -> bool.
  Axiom break : t -> t.
  Axiom continue : t -> t.
End ExitToken_sig.

Module ExitToken <: ExitToken_sig.
  (* TODO figure out a representation that lets us store ExitToken.t in the same
     variable as the loop counter *)
  Definition t := bool.
  Definition new : t := false.
  Definition get (tok: t) : bool := tok.
  Definition break (tok: t) : t := true.
  Definition continue (tok: t) : t := false.
  Definition branch {T} (tok: t) (break continue: T) :=
    if tok then break else continue.

  Lemma map_branch {T1 T2} (f: T1 -> T2) tok break continue:
    f (branch tok break continue) =
    branch tok (f break) (f continue).
  Proof. destruct tok; reflexivity. Qed.
End ExitToken.

Open Scope Z_scope.
Open Scope list.

Section ZRange.
  Fixpoint z_range' z0 len :=
    match len with
    | O => []
    | S len => z0 :: z_range' (z0 + 1) len
    end.

  Lemma z_range'_snoc' z0 len :
    forall zs, z_range' z0 (S len) ++ zs =
          z_range' z0 len ++ [z0 + Z.of_nat len] ++ zs.
  Proof.
    induction len in z0 |- *.
    - rewrite Z.add_0_r; reflexivity.
    - remember (S len) as n; intros.
      simpl; rewrite IHlen; rewrite Heqn; cbn -[Z.of_nat].
      replace (z0 + Z.of_nat (S len)) with (z0 + 1 + Z.of_nat len) by lia.
      reflexivity.
  Qed.

  Lemma z_range'_snoc z0 len :
    z_range' z0 (S len) =
    z_range' z0 len ++ [z0 + Z.of_nat len].
  Proof.
    intros; pose proof z_range'_snoc' z0 len [] as H.
    rewrite !app_nil_r in H.
    assumption.
  Qed.

  Lemma z_range'_sound len :
    forall z0 z,
      List.In z (z_range' z0 len) ->
      z0 <= z < z0 + Z.of_nat len.
  Proof.
    induction len; cbn -[Z.of_nat].
    - inversion 1; subst; lia.
    - destruct 1 as [-> | H].
      + lia.
      + specialize (IHlen _ _ H). lia.
  Qed.

  Lemma z_range'_complete len :
    forall z0 z,
      z0 <= z < z0 + Z.of_nat len ->
      List.In z (z_range' z0 len).
  Proof.
    induction len; cbn -[Z.of_nat].
    - lia.
    - intros.
      destruct (Z.eq_dec z0 z);
        [left; eauto | right].
      apply IHlen.
      lia.
  Qed.

  Definition z_range from to :=
    z_range' from (Z.to_nat (to - from)).

  Lemma z_range_sound from to z:
    List.In z (z_range from to) ->
    from - 1 < z < to.
  Proof.
    unfold z_range; intros H%z_range'_sound; lia.
  Qed.

  Lemma z_range_complete from to z:
    from - 1 < z < to ->
    List.In z (z_range from to).
  Proof.
    unfold z_range; intros; apply z_range'_complete; lia.
  Qed.

  Lemma range_unique from to z :
    forall (h h': from - 1 < z < to), h = h'.
  Proof.
    destruct h, h'; f_equal;
      unfold Z.lt in *; eapply @Eqdep_dec.UIP_dec; decide equality.
  Qed.

  Lemma z_range_nil from to:
    from >= to ->
    z_range from to = [].
  Proof.
    intros; unfold z_range.
    replace (Z.to_nat (to - from)) with 0%nat by lia; reflexivity.
  Qed.

  Lemma z_range_cons from to:
    from < to ->
    z_range from to = from :: z_range (from + 1) to.
  Proof.
    unfold z_range; intros.
    replace (Z.to_nat (to - from)) with (S (Z.to_nat (to - (from + 1)))) by lia.
    reflexivity.
  Qed.

  Lemma z_range_snoc from to:
    from < to ->
    z_range from to = z_range from (to - 1) ++ [to - 1].
  Proof.
    unfold z_range; intros.
    replace (Z.to_nat (to - from)) with (S (Z.to_nat (to - (from + 1)))) by lia.
    rewrite z_range'_snoc.
    replace (to - (from + 1)) with (to - 1 - from) by lia.
    replace (from + Z.of_nat (Z.to_nat (to - 1 - from))) with (to - 1) by lia.
    reflexivity.
  Qed.
End ZRange.

Section Loops.
  Context {A: Type}.
  Context (from to: Z).
  Context (body: forall (idx: Z) (acc: A), from - 1 < idx < to -> A).

  Lemma iter'0 {idx tl P}:
    (forall z : Z, In z (idx :: tl) -> P z) ->
    (forall z : Z, In z tl -> P z).
  Proof. simpl; eauto. Qed.

  Section WithBreak.
    Context (stop: A -> bool).

    Fixpoint ranged_for_break' indexes :=
      match indexes return (forall z, List.In z indexes -> from - 1 < z < to) -> A -> A with
      | [] => fun _ acc => acc
      | idx :: tl =>
        fun pr acc =>
          if stop acc then acc
          else let acc := body idx acc (pr _ (or_introl eq_refl)) in
               ranged_for_break' tl (iter'0 pr) acc
      end.

    Definition ranged_for_break :=
      ranged_for_break' (z_range from to) (z_range_sound from to).

    Lemma ranged_for_break'_stop_idempotent zs H a0:
      stop a0 = true ->
      ranged_for_break' zs H a0 = a0.
    Proof.
      destruct zs; simpl; intros h; try rewrite h; reflexivity.
    Qed.

    Lemma ranged_for_break_exit a0:
      from >= to -> ranged_for_break a0 = a0.
    Proof.
      unfold ranged_for_break; intros.
      generalize (z_range_sound from to).
      rewrite (z_range_nil from to H).
      reflexivity.
    Qed.
  End WithBreak.

  Section NoBreak.
    Definition ranged_for_all :=
      ranged_for_break (fun _ => false).

    Lemma ranged_for_all_exit a0:
      from >= to -> ranged_for_all a0 = a0.
    Proof.
      intros; apply ranged_for_break_exit; assumption.
    Qed.
  End NoBreak.
End Loops.

Notation body_pointwise b b' :=
  (forall idx acc pr pr', b idx acc pr = b' idx acc pr').

Section Properties.
  Context {A: Type}.
  Implicit Type stop : A -> bool.

  Lemma ranged_for_break'_Proper :
    forall from from' to to' body body' stop stop' zs zs' a0 a0' H H',
      zs = zs' -> a0 = a0' ->
      (forall z a h h', body z a h = body' z a h') ->
      (forall a, stop a = stop' a) ->
      ranged_for_break' from to body stop zs H a0 =
      ranged_for_break' from' to' body' stop' zs' H' a0'.
  Proof.
    induction zs; intros * Hz Ha Hb Hs; subst; simpl in *.
    - reflexivity.
    - rewrite Hs; destruct stop'; try reflexivity.
      apply IHzs; f_equal; eauto.
  Qed.

  Lemma ranged_for_break'_app from to body stop:
    forall zs zs' a0 Hp H H',
      ranged_for_break' from to body stop (zs ++ zs') Hp a0 =
      ranged_for_break' from to body stop zs' H (ranged_for_break' from to body stop zs H' a0).
  Proof.
    induction zs; cbn; intros.
    - apply ranged_for_break'_Proper;
        intros; f_equal; apply range_unique || reflexivity.
    - erewrite IHzs.
      destruct stop eqn:?.
      + rewrite ranged_for_break'_stop_idempotent by assumption.
        reflexivity.
      + repeat f_equal.
        apply range_unique.
  Qed.

  Lemma ranged_for_break_Proper :
    forall from from' to to' body body' stop stop' a0 a0',
      a0 = a0' ->
      from = from' -> to = to' ->
      (forall z a h h', body z a h = body' z a h') ->
      (forall a, stop a = stop' a) ->
      ranged_for_break from to body stop a0 =
      ranged_for_break from' to' body' stop' a0'.
  Proof.
    intros; subst; unfold ranged_for_break;
      apply ranged_for_break'_Proper; eauto.
  Qed.

  Lemma ranged_for_all_Proper :
    forall from from' to to' body body' (a0 a0': A),
      a0 = a0' ->
      from = from' -> to = to' ->
      (forall z a h h', body z a h = body' z a h') ->
      ranged_for_all from to body a0 =
      ranged_for_all from' to' body' a0'.
  Proof.
    intros; apply ranged_for_break_Proper; eauto.
  Qed.

  Section Induction.
    Context (P: A -> Prop) (a0: A).

    Context (from to: Z).
    Context (body: forall (idx: Z) (acc: A), from - 1 < idx < to -> A).

    Context (H0: P a0).
    Context (Hbody: forall idx a1 Hle, P a1 -> P (body idx a1 Hle)).

    Section WithBreak.
      Context (stop: A -> bool).

      Lemma ranged_for_break'_ind' :
        forall zs H,
          P (ranged_for_break' from to body stop zs H a0).
      Proof.
        intros.
        revert zs H a0 H0.
        induction zs; cbn; eauto; [].
        intros; destruct (stop _); eauto.
      Qed.

      Lemma ranged_for_break_ind :
        P (ranged_for_break from to body stop a0).
      Proof. eapply ranged_for_break'_ind'. Qed.
    End WithBreak.

    Section NoBreak.
      Lemma ranged_for_all_ind :
        P (ranged_for_all from to body a0).
      Proof. eapply ranged_for_break_ind; eauto. Qed.
    End NoBreak.
  End Induction.

  Lemma ranged_for_break_unfold_l1 {from to}:
    from < to -> from - 1 < from < to.
  Proof. lia. Qed.

  Lemma ranged_for_break_unfold_l2 {from to z}:
    from + 1 - 1 < z < to -> from - 1 < z < to.
  Proof. lia. Qed.

  Lemma ranged_for_break_unfold_l from to body stop (a0: A):
    ranged_for_break from to body stop a0 =
    match Z_lt_dec from to with
    | left Hlt =>
      if stop a0 then a0
      else let a0 := body from a0 (ranged_for_break_unfold_l1 Hlt) in
           ranged_for_break
             (from + 1) to
             (fun idx acc pr => body idx acc (ranged_for_break_unfold_l2 pr))
             stop a0
    | right _ => a0
    end.
  Proof.
    destruct Z_lt_dec.
    - unfold ranged_for_break.
      generalize (z_range_sound from to) as Hrn.
      generalize (z_range_sound (from + 1) to) as Hrn1.
      rewrite (z_range_cons from to) by assumption.
      intros; simpl; destruct stop.
      + reflexivity.
      + apply ranged_for_break'_Proper;
          intros; f_equal; reflexivity || apply range_unique.
    - apply ranged_for_break_exit; lia.
  Qed.

  Lemma ranged_for_break_extend1 {from to}:
    forall idx, (from - 1 < idx < to)%Z -> (from - 1 < idx < to + 1)%Z.
  Proof. lia. Qed.

  Lemma ranged_for_break_unfold_r1 {from}:
    forall idx, (from - 1 < idx)%Z -> (from - 1 < idx < idx + 1)%Z.
  Proof. lia. Qed.

  Lemma ranged_for_break_unfold_r from to body stop (a0: A) H:
    ranged_for_break from (to + 1) body stop a0 =
    let butlast :=
        ranged_for_break
          from to
          (fun (idx : Z) (acc : A) (pr : (from - 1 < idx < to)%Z) =>
             body idx acc (ranged_for_break_extend1 idx pr))
          stop a0 in
    if stop butlast then butlast
    else body to butlast H.
  Proof.
    unfold ranged_for_break.
    generalize (z_range_sound from to) as Hin.
    generalize (z_range_sound from (to + 1)) as Hin1.

    rewrite z_range_snoc by lia. intros.
    erewrite ranged_for_break'_app; simpl.
    set (ranged_for_break' _ _ _ _ _ _ _) as fr.
    set (ranged_for_break' _ _ _ _ _ _ _) as fr1.
    assert (fr = fr1) as Hr.
    { subst fr fr1.
      apply ranged_for_break'_Proper;
        intros; f_equal; (lia || reflexivity || apply range_unique). }
    { rewrite Hr; destruct stop; try reflexivity.
      instantiate (1 := ?[h]).
      generalize (?h (to + 1 - 1) (or_introl eq_refl));
        replace (to + 1 - 1) with to by lia; intros.
      f_equal; apply range_unique. }
    Unshelve.
    { replace (to + 1 - 1) with to by lia.
      intros z ?%Hin; lia. }
    { simpl; destruct 1; lia. }
  Qed.

  Lemma ranged_for_break_unfold_r_nstop from to body body1 stop (a0: A) H:
    body_pointwise body body1 ->
    stop (ranged_for_break from to body stop a0) = false ->
    ranged_for_break from (to + 1) body1 stop a0 =
    body1 to (ranged_for_break from to body stop a0) H.
  Proof.
    intros Hb Hs.
    unshelve erewrite ranged_for_break_unfold_r; try lia.
    erewrite (ranged_for_break_Proper _ from _ to _ body _ stop _ a0); intros; eauto.
    cbv zeta; unshelve erewrite Hs by lia; f_equal; apply range_unique.
  Qed.

  Lemma ranged_for_break_monotonic from to body to1 body1 stop (a0: A):
    to1 >= to ->
    body_pointwise body body1 ->
    stop (ranged_for_break from to body stop a0) = true ->
    ranged_for_break from to1 body1 stop a0 =
    ranged_for_break from to body stop a0.
  Proof.
    intros Hgt Hb Hs.
    generalize (z_range_sound from to) as Hin.
    generalize (z_range_sound from to1) as Hin1.

    destruct (Z_le_gt_dec to1 from) as [?|Hgt'].
    { intros; rewrite !ranged_for_break_exit by lia; reflexivity. }

    revert body1 Hb;
      replace to1 with (to + Z.of_nat (Z.to_nat (to1 - to))) in * by lia;
      generalize (Z.to_nat (to1 - to)) as n;
      intros.

    induction n; cbn -[Z.of_nat].
    - (* split; [rewrite <- Hs; f_equal|]; *)
      apply ranged_for_break_Proper;
        rewrite ?Z.add_0_r; reflexivity || eauto.
    - revert body1 Hin1 Hb; rewrite Nat2Z.inj_succ;
        unfold Z.succ; rewrite Z.add_assoc; intros.

      destruct (Z_lt_le_dec (from - 1) (to + Z.of_nat n)).

      + unshelve erewrite ranged_for_break_unfold_r; try lia.
        erewrite IHn; cbv zeta; eauto; try rewrite Hs.
        * reflexivity.
        * auto using z_range_sound.
      + rewrite !ranged_for_break_exit;
          reflexivity || lia.
  Qed.

  Definition ranged_for_widen_bounds {from idx from' to} :
    from - 1 < idx < from' ->
    from' <= to ->
    from - 1 < idx < to.
  Proof. lia. Qed.
End Properties.

Section WithTok.
  Context {A: Type}.

  Section Loops.
    Context from to
            (body: forall (tok: ExitToken.t) (idx: Z) (acc: A),
                from - 1 < idx < to -> (ExitToken.t * A))
            (a0: A).

    Definition ranged_for' :=
      ranged_for_break
        from to
        (fun idx acc pr =>
           body ExitToken.new idx (snd acc) pr)
        (fun tok_acc => ExitToken.get (fst tok_acc))
        (ExitToken.new, a0).

    Definition ranged_for :=
      snd ranged_for'.

    Lemma ranged_for_exit :
      from >= to ->
      ranged_for = a0.
    Proof.
      unfold ranged_for, ranged_for'; intros.
      rewrite ranged_for_break_exit; eauto.
    Qed.
  End Loops.

  Lemma ranged_for'_Proper :
    forall from from' to to' body body' a0 a0',
      a0 = a0' ->
      from = from' -> to = to' ->
      (forall tok z a h h', body tok z a h = body' tok z a h') ->
      ranged_for' from to body a0 =
      ranged_for' from' to' body' a0'.
  Proof.
    unfold ranged_for'; intros.
    apply ranged_for_break_Proper; eauto || congruence.
  Qed.

  Lemma ranged_for'_unfold_r from to body a0 H:
    let wbody tok idx acc pr :=
        body tok idx acc (ranged_for_break_extend1 idx pr) in
    ranged_for' from (to + 1) body a0 =
    let butlast := ranged_for' from to wbody a0 in
    if fst butlast then butlast
    else body ExitToken.new to (snd butlast) H.
  Proof.
    unfold ranged_for'.
    erewrite ranged_for_break_unfold_r.
    reflexivity.
  Qed.

  Lemma ranged_for'_unfold_r_nstop from to body body' a0
        (H: from  - 1 < to < to + 1):
    (forall t, body_pointwise (body t) (body' t)) ->
    fst (ranged_for' from to body a0) = false ->
    ranged_for' from (to + 1) body' a0 =
    body' ExitToken.new to (snd (ranged_for' from to body a0)) H.
  Proof.
    unfold ranged_for'; intros Hb Hc.
    erewrite ranged_for_break_unfold_r_nstop; eauto; cbv beta; eauto.
  Qed.

  Lemma ranged_for'_monotonic from to body a0 to' body':
    to' >= to ->
    (forall t, body_pointwise (body t) (body' t)) ->
    fst (ranged_for' from to body a0) = true ->
    ranged_for' from to' body' a0 =
    ranged_for' from to body a0.
  Proof.
    unfold ranged_for'; intros.
    erewrite ranged_for_break_monotonic; eauto; cbv beta; eauto.
  Qed.
End WithTok.

Section with_parameters.
  Context {semantics : Semantics.parameters}
          {semantics_ok : Semantics.parameters_ok semantics}.

  Context {A: Type}
          (from to: word).

  Section Loops.
    Context {to_Z: word -> Z}
            (to_Z_of_Z: forall l h w,
                to_Z l <= w <= to_Z h ->
                to_Z (word.of_Z w) = w).

    Lemma ranged_for_w1 {idx}:
      to_Z from - 1 < idx < to_Z to ->
      to_Z from - 1 < to_Z (word.of_Z idx) < to_Z to.
    Proof. intros; erewrite (to_Z_of_Z from to); lia. Qed.

    Section WithTok.
      Context (body: forall (tok: ExitToken.t) (idx: word) (acc: A),
                  to_Z from - 1 < to_Z idx < to_Z to ->
                  (ExitToken.t * A)).

      Definition w_body_tok tok idx acc pr :=
        body tok (word.of_Z idx) acc (ranged_for_w1 pr).

      Definition ranged_for_w (a0: A) : A :=
        ranged_for (to_Z from) (to_Z to) w_body_tok a0.

      Lemma ranged_for_w_exit a0:
        to_Z from >= to_Z to -> ranged_for_w a0 = a0.
      Proof.
        intros; unfold ranged_for_w, ranged_for, ranged_for'.
        rewrite ranged_for_break_exit; eauto.
      Qed.

      Section Induction.
        Context (P: A -> Prop) (a0: A).
        Context (H0: P a0).
        Context (Hbody: forall tok idx a1 Hle, P a1 -> P (snd (body tok idx a1 Hle))).

        Lemma ranged_for_w_ind : P (ranged_for_w a0).
        Proof.
          unfold ranged_for_w, ranged_for, ranged_for'.
          apply ranged_for_break_ind; simpl; eauto.
        Qed.
      End Induction.
    End WithTok.

    Section NoBreak.
      Context (body: forall (idx: word) (acc: A),
                  to_Z from - 1 < to_Z idx < to_Z to ->
                  A).

      Definition w_body idx acc pr :=
        body (word.of_Z idx) acc (ranged_for_w1 pr).

      Definition ranged_for_all_w (a0: A) : A :=
        ranged_for_all (to_Z from) (to_Z to) w_body a0.

      Lemma ranged_for_all_w_exit a0:
        to_Z from >= to_Z to -> ranged_for_all_w a0 = a0.
      Proof.
        intros; apply ranged_for_all_exit; eauto.
      Qed.

      Section Induction.
        Context (P: A -> Prop) (a0: A).
        Context (H0: P a0).
        Context (Hbody: forall idx a1 Hle, P a1 -> P (body idx a1 Hle)).

        Lemma ranged_for_all_w_ind : P (ranged_for_all_w a0).
        Proof.
          unfold ranged_for_all_w.
          apply ranged_for_all_ind; simpl; eauto.
        Qed.
      End Induction.
    End NoBreak.
  End Loops.

  Section Unsigned.
    Lemma word_unsigned_of_Z_bracketed l h w:
      word.unsigned l <= w <= word.unsigned h ->
      word.unsigned (word.of_Z w) = w.
    Proof.
      pose proof word.unsigned_range l.
      pose proof word.unsigned_range h.
      intros; rewrite word.unsigned_of_Z, word.wrap_small; lia.
    Qed.

    Definition ranged_for_u :=
      ranged_for_w word_unsigned_of_Z_bracketed.

    Definition ranged_for_u_ind :=
      ranged_for_w_ind word_unsigned_of_Z_bracketed.

    Definition ranged_for_all_u :=
      ranged_for_all_w word_unsigned_of_Z_bracketed.

    Definition ranged_for_all_u_ind :=
      ranged_for_all_w_ind word_unsigned_of_Z_bracketed.
  End Unsigned.

  Section Signed.
    Lemma word_signed_of_Z_bracketed l h w:
      word.signed l <= w <= word.signed h ->
      word.signed (word.of_Z w) = w.
    Proof.
      pose proof word.signed_range l.
      pose proof word.signed_range h.
      intros; rewrite word.signed_of_Z, word.swrap_inrange; lia.
    Qed.

    Definition ranged_for_s :=
      ranged_for_w word_signed_of_Z_bracketed.

    Definition ranged_for_s_ind :=
      ranged_for_w_ind word_signed_of_Z_bracketed.

    Definition ranged_for_all_s :=
      ranged_for_all_w word_signed_of_Z_bracketed.

    Definition ranged_for_all_s_ind :=
      ranged_for_all_w_ind word_signed_of_Z_bracketed.
  End Signed.

  Definition wZ_must_pos (a: Z) :
    match Z_gt_dec a 0, Z_le_dec a (2 ^ 32 - 1) with
    | left _, left _ => word.unsigned (word.of_Z a) > 0
    | _, _ => True
    end.
  Proof.
    destruct Z_le_dec, Z_gt_dec; [ | exact I .. ].
    assert (2 ^ 32 - 1 <= 2 ^ Semantics.width - 1) by
        (destruct Semantics.width_cases as [-> | ->]; lia).
    rewrite word.unsigned_of_Z, word.wrap_small; lia.
  Qed.
End with_parameters.

Section with_parameters.
  Context {semantics : Semantics.parameters}
          {semantics_ok : Semantics.parameters_ok semantics}.

  Section Generic.
    Notation wbody body pr Hr :=
      (fun tok idx acc pr =>
         body tok idx acc (ranged_for_widen_bounds pr Hr)).

    Context (signed: bool).

    Lemma lts_of_Z x y:
      - 2 ^ (Semantics.width - 1) <= x < 2 ^ (Semantics.width - 1) ->
      - 2 ^ (Semantics.width - 1) <= y < 2 ^ (Semantics.width - 1) ->
      word.lts (word.of_Z x) (word.of_Z y) = (x <? y).
    Proof.
      intros; rewrite word.signed_lts, !word.signed_of_Z, !word.swrap_inrange; eauto.
    Qed.

    Lemma ltu_of_Z x y:
      0 <= x < 2 ^ Semantics.width ->
      0 <= y < 2 ^ Semantics.width ->
      word.ltu (word.of_Z x) (word.of_Z y) = (x <? y).
    Proof.
      intros; rewrite word.unsigned_ltu, !word.unsigned_of_Z, !word.wrap_small; eauto.
    Qed.

    Lemma getmany0 l t vt vx vy x y:
      map.getmany_of_list l (vx :: vy :: vt) = Some (x :: y :: t) ->
      map.get l vx = Some x.
    Proof.
      intros; eapply (map.getmany_of_list_get _ 0); eauto || reflexivity.
    Qed.

    Lemma getmany1 l t vt vx vy x y:
      map.getmany_of_list l (vx :: vy :: vt) = Some (x :: y :: t) ->
      map.get l vy = Some y.
    Proof.
      intros; eapply (map.getmany_of_list_get _ 1); eauto || reflexivity.
    Qed.

    Notation in_signed_bounds x :=
      (- 2 ^ (Semantics.width - 1) <= x < 2 ^ (Semantics.width - 1)).

    Notation in_unsigned_bounds x :=
      (0 <= x < 2 ^ Semantics.width).

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
             <{ lp from' (body ExitToken.new from' acc (conj Hl Hr)) }>)) ->
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
      intros * Hlocals Hinit Hbounds Hbody Hk.
      repeat straightline.

      destruct (Z_gt_le_dec from to).
      { (* Loop won't run at all *)
        eexists nat, lt, (fun n tr mem locals => loop_pred from a0 tr mem locals);
          repeat apply conj; eauto using lt_wf, 0%nat.

        intros.
        exists (word.of_Z 0); repeat apply conj.
        - eexists; split; eauto using getmany0.
          eexists; split; eauto using getmany1.
          pose proof Zlt_cases from to.
          destruct signed; simpl; rewrite ?lts_of_Z, ?ltu_of_Z by tauto;
            destruct (from <? to); reflexivity || lia.
        - rewrite word.unsigned_of_Z_0; intros; exfalso; lia.
        - intros. apply (Hk from).
          subst v. rewrite ranged_for_exit; eauto || lia. }

      pose (inv := (fun n tr mem locals =>
                     exists from' (Hr: from' <= to),
                       from <= from' /\
                       n = Z.to_nat (to - from') /\
                       let a := ranged_for' from from' (wbody body pr Hr) a0 in
                       (from' < to -> ExitToken.get (fst a) = false) /\
                       loop_pred from' (snd a) tr mem locals)).

      red. red.

      eexists nat, lt, inv; split.
      { apply lt_wf. }
      { split.
        { (* Initial invariant *)
          eexists; red.
          exists from.
          exists (ltac:(eauto): from <= to).
          split; try reflexivity.
          split; try reflexivity.
          unfold ranged_for, ranged_for';
            rewrite ranged_for_break_exit by lia.
          eauto. }
        intros niters * Hinv.
        destruct Hinv as (from' & Hl & Hr & -> & Hcontinue & Hpred).
        eexists ?[b]; split; [|split].
        { (* loop test can be eval'd *)
          eexists; split. eauto using getmany0.
          eexists; split. eauto using getmany1.
          destruct signed; simpl;
            rewrite ?lts_of_Z, ?ltu_of_Z by lia;
            reflexivity. }
        all:
          pose proof Zlt_cases from' to;
          intros Hnz; destruct (from' <? to);
            try (rewrite ?word.unsigned_of_Z_0, ?word.unsigned_of_Z_1 in Hnz;
                 congruence).

        { eapply WeakestPrecondition_weaken; cycle 1.
          { (* User-supplied loop body *)
            unshelve apply Hbody; cycle -2.
            { unshelve apply Hcontinue; eassumption. }
            { apply Hpred. }
            all: eauto with arith || lia. }
          { (* Invariant proof *)
            subst lp; cbv beta.
            set (body _ _ _ _) as acc_tok in *.
            set (ExitToken.branch (fst acc_tok) to (from' + 1)) as from'' in *.

            intros * Hlp.
            exists (Z.to_nat (to - from'')); split.

            assert (exists h,
                       acc_tok =
                       (ranged_for' from (from' + 1) (wbody body pr h) a0))
              as [? Hrefold].
            { exists (ltac:(lia): from' + 1 <= to).
              subst acc_tok.
              erewrite ranged_for'_unfold_r_nstop with (H0 := ?[H]).
              [H]: lia.
              f_equal; f_equal; apply range_unique.
              cbv beta; intros; f_equal; apply range_unique.
              erewrite ranged_for'_Proper; [apply Hcontinue|..];
                intros; cbv beta; f_equal; (congruence || lia || apply range_unique). }

            { (* Invariant proof *)
              exists from''.

              unshelve eexists;
                [subst from''; destruct (fst acc_tok); simpl; lia|].
              split;
                [subst from''; destruct (fst acc_tok); simpl; lia|].

              split; [reflexivity|].

              split.
              { (* If index is < to, loop didn't exit *)
                subst from'';
                  destruct (fst acc_tok) eqn:Htok; simpl in *;
                    [intros; exfalso; lia|].
                intros; rewrite <- Htok, Hrefold by assumption.
                unfold ExitToken.get; f_equal.
                apply ranged_for'_Proper;
                  intros; cbv beta; f_equal; (congruence || lia || apply range_unique). }

              { (* Final invariant holds *)
                subst from'';
                  destruct (fst acc_tok) eqn:Htok; simpl in *;
                    rewrite Hrefold in Hlp.
                { (* Loop exited early *)
                  erewrite ranged_for'_monotonic.
                  - eassumption.
                  - lia.
                  - cbv beta; intros; f_equal; apply range_unique.
                  - rewrite <- Hrefold; assumption. }
                { (* Loop did not exit early *)
                  erewrite ranged_for'_Proper;
                  [ eapply Hlp| .. ];
                  intros; cbv beta; f_equal; (congruence || lia || apply range_unique). } } }

            { (* Variant decreased *)
              subst from''. destruct (fst acc_tok); simpl; lia. } } }

        { (* Loop end analysis *)
          cbv zeta in Hpred.
          assert (from' = to) as Hend by lia; destruct Hend.
          eapply Hk.
          subst v.
          unfold ranged_for.
          erewrite ranged_for'_Proper;
            [ eapply Hpred| .. ];
            intros; cbv beta; f_equal; (congruence || lia || apply range_unique). } }
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
             <{ lp from' (body ExitToken.new from' acc (conj Hl Hr)) }>)) ->
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
             <{ lp from' (body tok from' (snd a) (conj Hl Hr)) }>)) ->
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
                        (fun t idx acc _ =>
                           if Z.ltb 11 idx then
                             let t' := ExitToken.break t in
                             (t', acc)
                           else
                             let acc := idx :: acc in
                             (t, acc)) []).

  Time Compute (ranged_for_u (word.of_Z 0) (word.of_Z 15)
                          (fun t idx acc _ =>
                             if word.ltu (word.of_Z 11) idx then
                               let t' := ExitToken.break t in
                               (t', acc)
                             else
                               let acc := idx :: acc in
                               (t, acc)) []).
End test.
