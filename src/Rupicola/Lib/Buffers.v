From Coq Require Vector List Derive.
Require Import Rupicola.Lib.Core.
Require Import Rupicola.Lib.Notations.
Require Import Rupicola.Lib.Arrays.
Require Import Rupicola.Lib.Loops.
Require Import Rupicola.Lib.ExprReflection.
Require Import Rupicola.Lib.Compiler.

Section with_parameters.
  Context {width: Z} {BW: Bitwidth width}.
  Context {word: word.word width} {word_ok : word.ok word}.
  Context {Mem: map.map word Byte.byte} {Mem_ok : map.ok Mem}.
  Context {Locals: map.map String.string word} {Locals_ok : map.ok Locals}.
  Context {Env: map.map String.string (list String.string * list String.string * Syntax.cmd)} {Env_ok : map.ok Env}.
  Context {Ext_spec: bedrock2.Semantics.ExtSpec} {Ext_spec_ok : Semantics.ext_spec.ok Ext_spec}.

  Open Scope Z_scope.
  Open Scope list_scope.

  Definition buffer_t := list word.

  Notation wlen data :=
    (word.of_Z (Z.of_nat (length data))).

  (* Definition _buffer_value (ptr: word) (data: buffer_t) (capacity: nat) mem := *)
  (*   exists padding: list word, *)
  (*     length padding = (capacity - length data)%nat /\ *)
  (*     (listarray_value AccessWord ptr data ⋆ *)
  (*      listarray_value AccessWord (endof ptr data) padding) mem. *)

  (* Keeping `capacity` constant makes loop inference easier than storing the
     amount of free space left. *)
  Definition buffer_value (ptr: word) (data: buffer_t) (capacity: nat) mem :=
    exists padding: list word,
      sizedlistarray_value AccessWord capacity ptr (data ++ padding) mem.

  Lemma buffer_as_sizedlistarray ptr data capacity:
    forall R mem,
      (buffer_value ptr data capacity ⋆ R) mem ->
      exists padding,
        (sizedlistarray_value AccessWord capacity ptr (data ++ padding) ⋆ R) mem.
  Proof. intros * Hmem%sep_ex1_l. eassumption. Qed.

  Lemma sizedlistarray_as_buffer ptr data padding capacity:
    forall R mem,
      (sizedlistarray_value AccessWord capacity ptr (data ++ padding) ⋆ R) mem ->
      (buffer_value ptr data capacity ⋆ R) mem.
  Proof. intros. apply sep_ex1_l. eexists; eassumption. Qed.

  (*     #### Description of the problem *)

  (* This is a problem I commonly run into when developing code that depends on type classes *)

  Definition push (buf: buffer_t) (w: word) :=
    buf ++ [w].

  Definition app (buf: buffer_t) (arr: list word) :=
    buf ++ arr.

  Lemma push_length b w:
    length (push b w) = (length b + 1)%nat.
  Proof. unfold push; rewrite app_length; reflexivity. Qed.

  Lemma push_length_Z b w:
    Z.of_nat (length (push b w)) = (Z.of_nat (length b) + 1).
  Proof. rewrite push_length, Nat2Z.inj_add; reflexivity. Qed.

  Lemma push_wlen b w:
    wlen (push b w) =
    word.of_Z (width := width) (Z.of_nat (length b) + 1).
  Proof. rewrite push_length_Z; reflexivity. Qed.

  Set Printing Compact Contexts.

  Lemma compile_buffer_push : forall {tr mem locals functions} buf capacity w,
    let v := push buf w in
    forall {P} {pred: P v -> predicate} {k: nlet_eq_k P v} {k_impl : cmd}
      R (var : string) buf_ptr (buf_expr w_expr idx_expr: expr),

      (length buf < capacity)%nat ->

      sep (buffer_value buf_ptr buf capacity) R mem ->

      WeakestPrecondition.dexpr mem locals buf_expr buf_ptr ->
      WeakestPrecondition.dexpr mem locals idx_expr (wlen buf) ->
      WeakestPrecondition.dexpr mem locals w_expr w ->

      (let v := v in
       forall mem',
         sep (buffer_value buf_ptr (push buf w) capacity) R mem' ->
         <{ Trace := tr;
            Memory := mem';
            Locals := locals;
            Functions := functions }>
         k_impl
         <{ pred (k v eq_refl) }>) ->

      <{ Trace := tr;
         Memory := mem;
         Locals := locals;
         Functions := functions }>
      cmd.seq
        (cmd.store access_size.word
                   (offset buf_expr idx_expr
                           (expr.literal (Z.of_nat (Memory.bytes_per (width := width) access_size.word))))
           w_expr)
        k_impl
      <{ pred (nlet_eq [var] v k) }>.
  Proof.
    intros * Hlt [pad Hmem]%buffer_as_sizedlistarray Hbuf Hidx Hw Hk.
    pose proof sizedlistarray_value_app1_length Hmem.
    eapply WeakestPrecondition_weaken;
      [ .. | eapply @compile_word_sizedlistarray_put
               with (var := var) (k := fun _ _ => k _ eq_refl) ].
    all: unfold cast, Convertible_self, id.
    all: eassumption || lia || eauto.
    { intros; apply Hk.
      rewrite ListArray.put_app_len, List_assoc_app_cons in H0;
        eauto using sizedlistarray_as_buffer.
      all: cbn_array; reflexivity || lia || idtac. }
  Qed.




  Lemma app_as_foldl_push b1 b2 :
    app b1 b2 = List.fold_left push b2 b1.
  Proof.
    unfold app; revert b1; induction b2; simpl; intros.
    - rewrite app_nil_r; reflexivity.
    - rewrite List_assoc_app_cons, IHb2; reflexivity.
  Qed.

  Instance HasDefault_word : HasDefault word := word.of_Z 0.

  Lemma ListArray_nth_error_get_Z {A} `{HasDefault A} :
    forall (l: list A) (idx: Z),
      -1 < idx < Z.of_nat (length l) ->
      nth_error l (Z.to_nat idx) =
      Some (ListArray.get l (Z.to_nat idx)).
  Proof.
    intros.
    apply nth_error_nth'.
    unfold cast, Convertible_self, id; lia.
  Qed.




  (* Definition rupicola_app_step buf0 (arr: list word) := *)
  (*   (fun (p: \<< buffer_t, Z \>>) (tok: ExitToken.t) idx2 *)
  (*      (pr: -1 < idx2 < Z.of_nat (length arr)) => *)
  (*      let '\< buf, buf_len \> := p in *)
  (*      let/n idx1 := Z.of_nat (length buf0) + idx2 in (* needed? *) *)
  (*      let/n w := ListArray.get arr (Z.to_nat idx2) in *)
  (*      let/n buf' as "buf" := push buf w in *)
  (*      let/n buf_len := buf_len + 1 in *)
  (*      (tok, \<buf, buf_len\>)). *)

  Definition rupicola_app_step (buf0: buffer_t) (arr: list word) :=
    (fun (buf: buffer_t) (tok: ExitToken.t) idx2
       (pr: -1 < idx2 < Z.of_nat (length arr)) =>
       let/n idx1 := Z.of_nat (length buf0) + idx2 in
       let/n w := ListArray.get arr (Z.to_nat idx2) in
       let/n buf := push buf w in
       (tok, buf)).

  Lemma rupicola_app_eqn :
    forall buf0 arr from',
      0 <= from' < Z.of_nat (length arr) ->
      ranged_for' 0 from'
                  (fun (buf: buffer_t) (tok: ExitToken.t) idx2
                     (pr: -1 < idx2 < _) =>
                     let/n idx1 := Z.of_nat (length buf0) + idx2 in
                     let/n w := ListArray.get arr (Z.to_nat idx2) in
                     let/n buf := push buf w in
                     (tok, buf))  buf0 =
      (ExitToken.new, buf0 ++ List.firstn (Z.to_nat from') arr).
  Abort.
  (* FIXME the problem here is that we want to update buf_len every time, so maybe we need an assignment to it on the outside; but on the other hand we want to maintain it as (length buf), so not as its own independent thing, so we don't want to export its mutation outside the loop.

   If we do the first way we need a theorem that rewrites the result of the iteration as a length; this should be easier once there's a lemma for fold whose intermediate state is a fold.

   If we do the second way then we need to change the loop inference so that it generalizes `buf` also in the locals.

   With the first solution

   Maybe the right way to do this is to not increment buf_len every time at all; instead compute the original buf_len + idx2 *)

  Definition rupicola_app (buf: buffer_t) (arr: list word) :=
    let/n buf :=
       ranged_for 0 (Z.of_nat (length arr))
                  (rupicola_app_step buf arr) buf in
    buf.

  Lemma app_as_rupicola_app (b1 b2: buffer_t) :
    app b1 b2 = rupicola_app b1 b2.
  Proof.
    rewrite app_as_foldl_push.
    erewrite copying_foldl_as_ranged_for
      with (f' := fun b2 idx2 _ => ListArray.get b2 (Z.to_nat idx2)).
    - rewrite ranged_for_all_as_ranged_for. reflexivity.
    - eauto using ListArray_nth_error_get_Z.
  Qed.

  Instance spec_of_buf_append : spec_of "buf_append" :=
    fnspec! "buf_append" (buf_ptr buf_len arr_ptr arr_len: word) /
          (buf: buffer_t) (arr: list word) capacity
          (R: Mem -> Prop),
    { requires tr mem :=
        buf_len = wlen buf /\ arr_len = wlen arr /\
        Z.of_nat (length arr) < 2 ^ width /\
        (length buf + length arr <= capacity)%nat /\
        (buffer_value buf_ptr buf capacity ⋆
         listarray_value AccessWord arr_ptr arr ⋆ R) mem;
      ensures tr' mem' :=
        tr' = tr /\
        (buffer_value buf_ptr (app buf arr) capacity ⋆
         listarray_value AccessWord arr_ptr arr ⋆ R) mem' }.

  Lemma word_pow2_width_pos :
    0 < 2 ^ width.
  Proof. apply Z.pow_pos_nonneg, word.width_nonneg; lia. Qed.

  Hint Extern 1 => rewrite app_as_rupicola_app; shelve : compiler_setup.
  Hint Extern 1 (_ <= _) => lia : compiler_side_conditions.
  Hint Resolve word_pow2_width_pos : compiler_side_conditions.

  Hint Unfold cast Convertible_self id : compiler_cleanup.
  Hint Rewrite Z2Nat.id using lia : compiler_cleanup.

  Hint Resolve Z.pow_pos_nonneg word.width_nonneg : compiler_side_conditions.
  Hint Extern 1 => progress cbn [fst snd]; shelve : compiler_side_conditions.
  Hint Rewrite push_wlen : compiler_cleanup.
  Hint Unfold rupicola_app_step : compiler_cleanup.

  Hint Extern 1 => simple eapply compile_buffer_push; shelve : compiler.

  Import UnsizedListArrayCompiler.

  Require Import AdmitAxiom.

  Derive buf_append_body SuchThat
         (defn! "buf_append"("buf_ptr", "buf_len", "arr_ptr", "arr_len")
              { buf_append_body },
          implements rupicola_app)
         As buf_append_correct.
  Proof.
    compile_setup.
    repeat compile_step.

    (* FIXME: invariant *should* generalize the objects (since otherwise wlen below isn't generalized) *)
    apply compile_nlet_as_nlet_eq.

    (* eapply compile_ranged_for_fresh with *)
    (*     (signed := false) *)
    (*     (from_var := "idx2") (to_var := "len2") *)
    (*     (from_expr := expr.literal 0) *)
    (*     (loop_pred := fun from buf tr' mem' locals' => *)
    (*                    tr' = tr /\ *)
    (*                    locals' = #{ *)
    (*            "buf_ptr" => buf_ptr; "buf_len" => wlen buf; "arr_ptr" => *)
    (*            arr_ptr; "arr_len" => wlen arr; *)
    (*                                 "idx2" => word.of_Z from; *)
    (*                                          "len2" => wlen arr *)
    (*                                }# /\ *)
    (*                    (buffer_value buf_ptr buf capacity ⋆ *)
    (*                     listarray_value AccessWord arr_ptr arr ⋆ R) mem'). *)

    eapply compile_ranged_for_fresh with
        (signed := false)
        (from_var := "idx2") (to_var := "len2")
        (from_expr := expr.literal 0)
        (loop_pred := fun from buf' tr' mem' locals' =>
                       tr' = tr /\
                       locals' = #{
               "buf_ptr" => buf_ptr; "buf_len" => wlen buf; "arr_ptr" =>
               arr_ptr; "arr_len" => wlen arr;
                                    "idx2" => word.of_Z from;
                                             "len2" => wlen arr
                                   }# /\
                       (buffer_value buf_ptr buf' capacity ⋆
                        listarray_value AccessWord arr_ptr arr ⋆ R) mem').


    all: repeat compile_step.

    2: {                        (* FIXME proof general screws up error positions here *)
      replace (wlen acc) with (word.add (word := word) (wlen buf) (word.of_Z from')).
      repeat compile_step.
      admit.
    }

    subst acc a.
    set (ranged_for' _ _ _ _).
    pose (rupicola_app_step buf (List.firstn (Z.to_nat from') arr)) as f.
    rewrite firstn_length_le, Z2Nat.id in (type of f) by lia.
    replace (snd p) with (app buf (List.firstn (Z.to_nat from') arr)).
    rewrite app_length, firstn_length_le by lia.
    lia.

    admit.
  Qed.


  (* FIXME two kinds of fold: list A -> B -> list A that mutates in place, and
     all others (the difference is where they read values from) *)



  Section App.
    Context (var idx_var len_var: string).
    Context (buf_expr idx_expr len_expr arr_expr: expr).

    (* FIXME: compile this as a proper bedrock2 function — not as a macro! *)

    Derive buffer_append SuchThat
    (forall {tr mem locals functions} buf arr capacity,
        let v := app buf arr in
        let locals1 := map.put locals idx_var (word.of_Z 0) in
        let locals2 := map.put locals1 len_var (wlen arr) in
    forall {P} {pred: P v -> predicate} {k: nlet_eq_k P v} {k_impl : cmd}
      R buf_ptr arr_ptr,

      (length buf + length arr <= capacity)%nat ->

      sep (buffer_value buf_ptr buf capacity) R mem ->

      WeakestPrecondition.dexpr mem locals buf_expr buf_ptr ->
      WeakestPrecondition.dexpr mem locals1 arr_expr arr_ptr ->
      WeakestPrecondition.dexpr mem locals1 len_expr (wlen arr) ->
      WeakestPrecondition.dexpr mem locals1 idx_expr (wlen buf) ->

      (let v := v in
       forall mem',
         sep (buffer_value buf_ptr (app buf arr) capacity) R mem' ->
         <{ Trace := tr;
            Memory := mem';
            Locals := locals;
            Functions := functions }>
         k_impl
         <{ pred (k v eq_refl) }>) ->

      <{ Trace := tr;
         Memory := mem;
         Locals := locals;
         Functions := functions }>
      buffer_append
      <{ pred (nlet_eq [var] v k) }>)
  As compile_buffer_append.
  Proof.
    intros until P; unfold buffer_append, v;
      rewrite (app_as_ranged_for var buf arr); intros.
    eapply compile_ranged_for_fresh with
        (from_var := idx_var) (to_var := len_var)
        (from_expr := expr.literal 0) (to_expr := len_expr)
        (loop_pred := fun from buf tr' mem' locals' =>
                       tr' = tr /\
                       locals' = locals2 /\
                       (buffer_value buf_ptr buf capacity ⋆ R) mem').
    - reflexivity.
    - eassumption.
    - intros * Hp; decompose [and] Hp; subst; clear Hp.
      subst locals1.

    compile_ranged_for.
    rewrite app_is_push_loop in Heql.
    rewrite map_as_fold_left
    subst.

    intros * Hlt [pad Hmem]%buffer_as_sizedlistarray Hbuf Hidx Hw Hk.
    pose proof sizedlistarray_value_app1_length Hmem.
    eapply WeakestPrecondition_weaken;
      [ .. | eapply @compile_word_sizedlistarray_put
               with (var := var) (k := fun _ _ => k _ eq_refl) ].
    all: unfold cast, Convertible_self, id.
    all: eassumption || lia || eauto.
    { intros; apply Hk.
      rewrite ListArray.put_app_len, List_assoc_app_cons in H0;
        eauto using sizedlistarray_as_buffer.
      all: cbn_array; reflexivity || lia || idtac. }
  Qed.
End Section.

#[export] Hint Extern 1 => simple eapply compile_buffer_push; shelve : compiler.
