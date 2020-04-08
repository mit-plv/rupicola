Require Import Coq.ZArith.ZArith.
Require Import bedrock2.Map.Separation.
Require Import bedrock2.Map.SeparationLogic.
Require Import coqutil.Word.Interface coqutil.Word.Properties.
Require Import coqutil.Map.Interface coqutil.Map.Properties.
Require Import Rupicola.Examples.KVStore.KVStore.
Require Import Rupicola.Examples.KVStore.Properties.

Ltac unborrow_step Value :=
  match goal with
  | H : sep ?L ?R ?mem |- context [?mem] =>
    match type of H with
      context [?P (map.put ?m ?k (Borrowed ?px, ?x))] =>
      let F1 :=
          match (eval pattern
                      (P (map.put m k (Borrowed px, x))) in
                    (sep L R)) with ?f _ => f end in
      let F2 :=
          match (eval pattern (Value px x) in F1) with
            ?f _ => f end in
      let H' := fresh in
      assert (F2 (P (map.put m k (Reserved px, x))) (emp True) mem)
        as H' by (seprewrite reserved_borrowed_iff1;
                  ecancel_assumption);
      clear H; cbv beta in H'
    end
  | H : context [map.put (map.put _ _ (Borrowed ?px, ?x))
                         _ (Reserved ?py, ?y)] |- _ =>
    rewrite (map.put_put_diff_comm _ _ (Borrowed px, x)
                                   (Reserved py, y))
      in H by congruence
  end.
Ltac unborrow Value := progress (repeat unborrow_step Value).

Ltac unreserve_step :=
  match goal with
  | H : sep ?L ?R ?mem |- context [?mem] =>
    match type of H with
      context [?P (map.put ?m ?k (Reserved ?px, ?x))] =>
      let F1 :=
          match (eval pattern
                      (P (map.put m k (Reserved px, x))) in
                    (sep L R)) with ?f _ => f end in
      let H' := fresh in
      (* hacky because seprewrite doesn't do impl1 *)
      assert (F1 (P (map.put m k (Owned, x))) mem) as H'
          by (eapply Proper_sep_impl1;
              [ repeat
                  rewrite (sep_assoc (_ (map.put _ _ (Owned, _))));
                eapply Proper_sep_impl1;
                [ eapply reserved_owned_impl1 | reflexivity ]
              | reflexivity | ]; ecancel_assumption);
      clear H; cbv beta in H'
    end
  | H : context [map.put (map.put _ _ (Reserved ?px, ?x))
                         _ (Owned, ?y)] |- _ =>
    rewrite (map.put_put_diff_comm _ _ (Reserved px, x)
                                   (Owned, y))
      in H by congruence
  end.
Ltac unreserve := progress (repeat unreserve_step).

Ltac destruct_lists_of_known_length :=
  repeat match goal with
         | H : S _ = S _ |- _ => apply Nat.succ_inj in H
         | H : length ?x = S _ |- _ =>
           destruct x; cbn [length] in H; [ congruence | ]
         | H : length ?x = 0 |- _ =>
           destruct x; cbn [length] in H; [ clear H | congruence]
         end;
  cbn [hd tl] in *.

Ltac boolean_cleanup :=
  repeat match goal with
         | H : _ |- _ =>
           rewrite word.unsigned_of_Z_0 in H
         | H : _ |- _ =>
           rewrite word.unsigned_of_Z_1 in H
         | x := word.of_Z 0%Z |- _ => subst x
         | x := word.of_Z 1%Z |- _ => subst x
         | _ => congruence
         end.