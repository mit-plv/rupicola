From Coq Require Vector List.
Require Import Rupicola.Lib.Core.
Require Import Rupicola.Lib.Notations.
(* Require Import Arith PeanoNat. *)

Class HasDefault (T: Type) := default: T.
Instance HasDefault_byte : HasDefault byte := Byte.x00.

Class Convertible (T1 T2: Type) := cast: T1 -> T2.
Instance Convertible_self {A}: Convertible A A := id.

Module VectorArray.
  Section VectorArray.
    Context {K V: Type}.
    Context {Conv: Convertible K nat}.

    Definition t n := Vector.t V n.
    Definition get {n} (a: t n) (k: K) (pr: cast k < n) : V :=
      Vector.nth_order a pr.
    Definition put {n} (a: t n) (k: K) (pr: cast k < n) (v: V) : t n :=
      Vector.replace_order a pr v.
    (* FIXME needs an accessor that generates a test and returns a default *)
  End VectorArray.

  Arguments t : clear implicits.
End VectorArray.

Module ListArray.
  Section ListArray.
    Context {K V: Type}.
    Context {HD: HasDefault V}.
    Context {Conv: Convertible K nat}.

    Definition t := list V.
    Definition get (a: t) (k: K) : V :=
      List.nth (cast k) a default.
    Definition put (a: t) (k: K) (v: V) : t :=
      replace_nth (cast k) a v.
    (* FIXME needs an accessor that generates a test and returns a default *)

    Lemma put_length (a: t) (k: K) (v: V) :
      List.length (put a k v) = List.length a.
    Proof. intros; apply replace_nth_length. Qed.
  End ListArray.

  Arguments t : clear implicits.
End ListArray.

Open Scope Z_scope.

(* Q: Why is the following using typeclasses instead of modules?
   A: Because the type of vectors is parametric in the length `n`, and modules are not first-class values. *)

Module Elem.
  Section with_parameters.
    Context {semantics : Semantics.parameters}
            {semantics_ok : Semantics.parameters_ok semantics}.

    Class elem_info :=
      { type : Type;
        size : access_size.access_size;
        repr : word -> type -> Semantics.mem -> Prop;
        to_word : type -> word;
        default : HasDefault type;

        (* FIXME use truncated_word and load_of_sep/store_of_sep? *)

        load_of_sep : forall addr value R (m: Semantics.mem),
            sep (repr addr value) R m ->
            Memory.load size m addr =
            Some (to_word value);
        store_of_sep : forall addr (oldvalue value: type) R m (post: _ -> Prop),
            sep (repr addr oldvalue) R m ->
            (forall m, sep (repr addr value) R m -> post m) ->
            exists m1, Memory.store size m addr (to_word value) = Some m1 /\
                  post m1 }.

    Definition width {AI: elem_info} :=
      Z.of_nat (@Memory.bytes_per Semantics.width size).
  End with_parameters.

  Ltac _cbv H :=
    cbv beta iota delta [type size repr to_word default width] in (type of H).
End Elem.

Section with_parameters.
  Context {semantics : Semantics.parameters}
          {semantics_ok : Semantics.parameters_ok semantics}.

  (* No 16 or 32 to avoid depending on two more word instances. *)
  Inductive AccessSize := AccessByte | AccessWord.

  (* FIXME this is a slightly different formulation from the one in Bedrock2,
       designed to line up with store_word_of_sep.  Move to Bedrock2? *)
  Lemma store_one_of_sep:
    forall (addr: word) (oldvalue value: byte) R m (post : _ -> Prop),
      sep (ptsto addr oldvalue) R m ->
      (forall m : Semantics.mem, sep (ptsto addr value) R m -> post m) ->
      exists m1, Memory.store access_size.one m addr (word_of_byte value) = Some m1 /\ post m1.
  Proof.
    intros addr oldvalue value R m post **.
    destruct (store_one_of_sep addr oldvalue (word_of_byte value) R m post);
      try rewrite to_byte_of_byte_nowrap; eauto.
  Qed.

  Definition _elem_info asize :=
    match asize with
    | AccessByte =>   {| Elem.size := access_size.one;
                        Elem.type := byte;
                        Elem.repr := scalar8;
                        Elem.default := Byte.x00;
                        Elem.to_word v := word_of_byte v;
                        Elem.load_of_sep := load_one_of_sep;
                        Elem.store_of_sep := store_one_of_sep |}
    | AccessWord =>   {| Elem.size := access_size.word;
                        Elem.type := word;
                        Elem.repr := scalar;
                        Elem.default := word.of_Z 0;
                        Elem.to_word v := v;
                        Elem.load_of_sep := load_word_of_sep;
                        Elem.store_of_sep := store_word_of_sep |}
    end.
End with_parameters.

Module GenericArray.
  Section with_parameters.
    Context {semantics : Semantics.parameters}
            {semantics_ok : Semantics.parameters_ok semantics}.

    Context {sz: AccessSize}.
    Let EI := _elem_info sz.
    Local Existing Instance EI.

    Notation V := Elem.type.

    Class array_info :=
      { A: Type;
        K: Type;
        to_list: A -> list V;
        K_to_nat: Convertible K nat;

        array_repr a_ptr a :=
          (array Elem.repr (word.of_Z Elem.width) a_ptr (to_list a));

        get: A -> K -> V;
        put: A -> K -> V -> A;
        repr: address -> A -> Semantics.mem -> Prop;

        Hget: forall a idx,
            get a idx = nth (K_to_nat idx) (to_list a) (get a idx);
        Hrw: forall a_ptr a,
            Lift1Prop.iff1 (repr a_ptr a) (array_repr a_ptr a);

        Hput: forall a idx val,
            (K_to_nat idx < List.length (to_list a))%nat ->
            to_list (put a idx val) =
            replace_nth (K_to_nat idx) (to_list a) val;
        Hgetput: forall a idx val,
            (K_to_nat idx < List.length (to_list a))%nat ->
            get (put a idx val) idx = val }.

    (* Definition awidth {T} `{ak: access_kind T} : Z := *)
    (*   Z.of_nat (@Memory.bytes_per Semantics.width a_size). *)

    Context {AI: array_info}.

    Notation K_to_word x := (word.of_Z (Z.of_nat (K_to_nat x))).

    Context (a : A) (a_ptr : word) (a_var : string)
            (val: V) (val_var: string)
            (idx : K) (idx_var : string).

    Definition offset base idx width :=
      (expr.op bopname.add base (expr.op bopname.mul width idx)).

    Lemma compile_array_get {tr mem locals functions}:
      let v := get a idx in
      forall {P} {pred: P v -> predicate} {k: nlet_eq_k P v} {k_impl : cmd}
        R (var : string),

        (K_to_nat idx < Datatypes.length (to_list a))%nat ->

        sep (repr a_ptr a) R mem ->
        map.get locals a_var = Some a_ptr ->
        map.get locals idx_var = Some (K_to_word idx) ->

        (let v := v in
         <{ Trace := tr;
            Memory := mem;
            Locals := map.put locals var (Elem.to_word v);
            Functions := functions }>
         k_impl
         <{ pred (k v eq_refl) }>) ->
        <{ Trace := tr;
           Memory := mem;
           Locals := locals;
           Functions := functions }>
        cmd.seq
          (cmd.set
             var
             (expr.load (Elem.size)
                        (offset (expr.var a_var)
                                (expr.var idx_var)
                                (expr.literal Elem.width))))
          k_impl
        <{ pred (nlet_eq [var] v k) }>.
    Proof.
      cbn; intros Hlt *.
      pose proof word.unsigned_range (K_to_word idx) as (Hge & _).

      exists (Elem.to_word (get a idx)); split; cbn; [ | assumption ].
      exists a_ptr; split; [ eassumption | ]; cbn.
      exists (K_to_word idx); split; [ eassumption | ]; cbn.
      eexists; split; [ | reflexivity ].

      seprewrite_in Hrw H0.        (* FIXME seprewrite shouldn't rename *)
      (* FIXME: BEDROCK2: Adding an extra "_" at the end shelves an inequality *)
      lazymatch goal with
      | [ H: (array_repr _ _ ⋆ _) ?mem |- _ ] =>
        unfold array_repr in *;
          seprewrite_in open_constr:(array_index_nat_inbounds
                                       _ _ (default := get a idx) _ _ (K_to_nat idx)) H
      end.
      { eassumption. }

      match goal with
      | [ H: context[word.of_Z (_ * _)] |- _ ] =>
        rewrite word.ring_morph_mul, !word.of_Z_unsigned in H by assumption
      end.

      rewrite Hget.
      eapply Elem.load_of_sep.
      rewrite <- nth_default_eq, List.hd_skipn_nth_default.
      cbn in *; ecancel_assumption.
    Qed.

    Lemma _compile_array_put_length :
      (K_to_nat idx < Datatypes.length (to_list a))%nat ->
      (K_to_nat idx < List.length (to_list (put a idx val)))%nat.
    Proof.
      intros; rewrite Hput by assumption.
      rewrite replace_nth_length; assumption.
    Qed.

    Lemma _compile_array_put_firstn :
      (K_to_nat idx < Datatypes.length (to_list a))%nat ->
      List.firstn (K_to_nat idx) (to_list (put a idx val)) =
      List.firstn (K_to_nat idx) (to_list a).
    Proof.
      intros; rewrite Hput, replace_nth_eqn by lia.
      rewrite List.firstn_app, List.firstn_firstn, Min.min_idempotent.
      rewrite List.firstn_length_le by lia.
      rewrite Nat.sub_diag; cbn [List.firstn]; rewrite app_nil_r.
      reflexivity.
    Qed.

    Lemma _compile_array_put_skipn :
      (K_to_nat idx < Datatypes.length (to_list a))%nat ->
      List.skipn (S (K_to_nat idx)) (to_list (put a idx val)) =
      List.skipn (S (K_to_nat idx)) (to_list a).
    Proof.
      intros; rewrite Hput, replace_nth_eqn by lia.
      change (val :: ?tl) with (List.app [val] tl).
      rewrite List.app_assoc, List.skipn_app, List.skipn_all, List.app_nil_l, List.skipn_skipn;
        rewrite !List.app_length, List.firstn_length_le, (Nat.add_comm _ 1) by lia.
      - rewrite Nat.sub_diag, Nat.add_0_l.
        reflexivity.
      - reflexivity.
    Qed.

    Lemma compile_array_put {tr mem locals functions} :
      let v := put a idx val in
      forall {P} {pred: P v -> predicate} {k: nlet_eq_k P v} {k_impl: cmd}
        R (var: string),

      (K_to_nat idx < Datatypes.length (to_list a))%nat ->

      sep (repr a_ptr a) R mem ->
      map.get locals a_var = Some a_ptr ->
      map.get locals idx_var = Some (K_to_word idx) ->
      map.get locals val_var = Some (Elem.to_word val) ->

      (let v := v in
       forall mem',
         sep (repr a_ptr v) R mem' ->
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
        (cmd.store
           (Elem.size)
           (offset (expr.var a_var)
                   (expr.var idx_var)
                   (expr.literal Elem.width))
           (expr.var val_var))
        k_impl
      <{ pred (nlet_eq [var] v k) }>.
    Proof.
      cbn; intros Hlt *.
      pose proof _compile_array_put_length as Hputlen.
      pose proof _compile_array_put_firstn as Hputfst.
      pose proof _compile_array_put_skipn as Hputskp.
      pose proof word.unsigned_range (K_to_word idx) as (Hge & _).
      eexists; split; cbn.

      { eexists; split; [ eassumption | ]; cbn.
        eexists; split; [ eassumption | reflexivity ]. }

      { eexists; split; cbn.
        { eexists; split; [ eassumption | reflexivity ]. }
        { seprewrite_in Hrw H0.

          lazymatch goal with
          | [ H: (array_repr _ _ ⋆ _) ?mem |- _ ] =>
            unfold array_repr in *;
              seprewrite_in open_constr:(array_index_nat_inbounds
                                           Elem.repr _ (default := get a idx) _ _
                                           (K_to_nat idx)) H
          end.
          { assumption. }

          match goal with
          | [ H: context[word.of_Z (_ * _)] |- _ ] =>
            rewrite word.ring_morph_mul, !word.of_Z_unsigned in H by assumption
          end.

          eapply Elem.store_of_sep.
          { ecancel_assumption. }

          intros m Hm; apply H4; seprewrite Hrw.
          unfold array_repr;
            once (seprewrite open_constr:(array_index_nat_inbounds
                                            _ _ (default := get (put a idx val) idx)
                                            _ _ (K_to_nat idx)));
            [ apply Hputlen; assumption | ].
          rewrite <- List.hd_skipn_nth_default, nth_default_eq.
          rewrite <- Hget, Hgetput, !Hputfst, !Hputskp by assumption.
          repeat rewrite word.ring_morph_mul, !word.of_Z_unsigned by lia.

          ecancel_assumption. } }
    Qed.
  End with_parameters.

  Ltac _cbv H :=
    cbv beta iota delta [A K to_list K_to_nat array_repr get put repr].
End GenericArray.

Module GenericVectorArray.
  Import GenericArray.

  Section with_parameters.
    Context {semantics : Semantics.parameters}
            {semantics_ok : Semantics.parameters_ok semantics}.

    Context {sz: AccessSize}.
    Let EI := _elem_info sz.
    Local Existing Instance EI.

    Context {n: nat}.

    Context {K0: Type}
            {ConvNat: Convertible K0 nat}.

    Notation to_list := Vector.to_list.
    Notation K_to_nat idx := (cast (proj1_sig (P:=fun idx0 : K0 => (cast idx0 < _)%nat) idx)).
    Notation K_to_word x := (word.of_Z (Z.of_nat (K_to_nat x))).

    Notation get a idx := (VectorArray.get a (proj1_sig idx) (proj2_sig idx)).
    Notation put a idx v := (VectorArray.put a (proj1_sig idx) (proj2_sig idx) v).

    Definition repr n (addr: address) (a: VectorArray.t Elem.type n) : Semantics.mem -> Prop :=
      array Elem.repr (word.of_Z Elem.width) addr (to_list a).

    Lemma Vector_to_list_nth {T}:
      forall (f: Fin.t n) idx (v : Vector.t T n) (t0 : T),
        idx = proj1_sig (Fin.to_nat f) ->
        Vector.nth v f = List.nth idx (Vector.to_list v) t0.
    Proof.
      induction f; cbn; intros; rewrite (Vector.eta v).
      - subst; reflexivity.
      - subst; destruct (Fin.to_nat f); cbn.
        erewrite IHf; reflexivity.
    Qed.

    Program Definition info : array_info :=
      {| A := VectorArray.t Elem.type n;
         K := {idx0 : K0 | (cast idx0 < n)%nat};

         GenericArray.to_list := to_list;
         GenericArray.K_to_nat idx := K_to_nat idx;

         GenericArray.get a idx := get a idx;
         GenericArray.put a idx v := put a idx v;

         GenericArray.repr addr a := repr n addr a
      |}.

    Next Obligation.
    Proof.
      simpl; unfold VectorArray.get.
      apply Vector_to_list_nth; rewrite Fin.to_nat_of_nat; reflexivity.
    Qed.

    Next Obligation.
    Proof. reflexivity. Qed.

    Next Obligation.
    Proof.
      simpl.
      unfold VectorArray.put, Vector.replace_order;
        erewrite Vector_to_list_replace by reflexivity.
      rewrite Fin.to_nat_of_nat; reflexivity.
    Qed.

    Next Obligation.
    Proof.
      unfold get, put, Vector.nth_order, Vector.replace_order.
      intros; apply Vector_nth_replace.
    Qed.

    Local Existing Instance info.

    Lemma compile_get {tr mem locals functions}
          (a: VectorArray.t Elem.type n) (idx: K0) pr:
      let v := VectorArray.get a idx pr in
      forall {P} {pred: P v -> predicate} {k: nlet_eq_k P v} {k_impl}
        R (a_ptr: address) a_var idx_var var,

        sep (repr n a_ptr a) R mem ->
        map.get locals a_var = Some a_ptr ->
        map.get locals idx_var = Some (word.of_Z (Z.of_nat (cast idx))) ->

        (let v := v in
         <{ Trace := tr;
            Memory := mem;
            Locals := map.put locals var (Elem.to_word v);
            Functions := functions }>
         k_impl
         <{ pred (k v eq_refl) }>) ->
        <{ Trace := tr;
           Memory := mem;
           Locals := locals;
           Functions := functions }>
        cmd.seq
          (cmd.set
             var
             (expr.load
                (Elem.size)
                (offset (expr.var a_var)
                        (expr.var idx_var)
                        (expr.literal Elem.width))))
          k_impl
        <{ pred (nlet_eq [var] v k) }>.
    Proof.
      intros.
      change v with (get a (exist (fun idx => cast idx < n)%nat idx pr)).
      eapply (compile_array_get (AI := info))
        with (a := a) (idx := exist (fun idx0 : K0 => (cast idx0 < n)%nat) idx pr); eauto.
      simpl; rewrite Vector_to_list_length; assumption.
    Qed.

    Lemma compile_put {tr mem locals functions}
          (a: VectorArray.t Elem.type n) (idx: K0) pr val:
      let v := VectorArray.put a idx pr val in
      forall {P} {pred: P v -> predicate} {k: nlet_eq_k P v} {k_impl}
        R a_ptr a_var idx_var val_var var,

        sep (repr n a_ptr a) R mem ->
        map.get locals a_var = Some a_ptr ->
        map.get locals idx_var = Some (word.of_Z (Z.of_nat (cast idx))) ->
        map.get locals val_var = Some (Elem.to_word val) ->

        (let v := v in
         forall mem',
           sep (repr n a_ptr v) R mem' ->
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
          (cmd.store
             (Elem.size)
             (offset (expr.var a_var)
                     (expr.var idx_var)
                     (expr.literal Elem.width))
             (expr.var val_var))
          k_impl
        <{ pred (nlet_eq [var] v k) }>.
    Proof.
      intros.
      change v with (put a (exist (fun idx => cast idx < n)%nat idx pr) val).
      simple eapply (compile_array_put (AI := info))
        with (a := a) (val := val) (idx := exist (fun idx0 : K0 => (cast idx0 < n)%nat) idx pr); eauto.
      simpl; rewrite Vector_to_list_length; assumption.
    Qed.
  End with_parameters.
End GenericVectorArray.

Module GenericListArray.
  Import GenericArray.

  Section with_parameters.
    Context {semantics : Semantics.parameters}
            {semantics_ok : Semantics.parameters_ok semantics}.

    Context {sz: AccessSize}.
    Let EI := _elem_info sz.
    Local Existing Instance EI.
    Notation V := Elem.type.

    Context {K: Type}
            {ConvNat: Convertible K nat}
            {HD: HasDefault V}.

    Notation to_list x := x (only parsing).
    Notation K_to_nat idx := (@cast _ _ ConvNat idx).
    Notation K_to_word x := (word.of_Z (Z.of_nat (K_to_nat x))).

    Notation get a idx := (ListArray.get a idx).
    Notation put a idx v := (ListArray.put a idx v).

    Definition repr (addr: address) (a: ListArray.t Elem.type) : Semantics.mem -> Prop :=
      array Elem.repr (word.of_Z Elem.width) addr a.

    Program Definition info : array_info :=
      {| A := ListArray.t Elem.type;
         GenericArray.K := K;

         GenericArray.to_list l := to_list l;
         GenericArray.K_to_nat idx := K_to_nat idx;

         GenericArray.get a idx := get a idx;
         GenericArray.put a idx v := put a idx v;

         GenericArray.repr addr a := repr addr a
      |}.

    Next Obligation.
    Proof.
      unfold ListArray.get.
      generalize (K_to_nat idx) as i; induction a; simpl; intros;
        destruct i; congruence.
    Qed.

    Next Obligation.
    Proof.
      reflexivity.
    Qed.

    Next Obligation.
    Proof.
      unfold get, put.
      intros; apply nth_replace_nth; (assumption || reflexivity).
    Qed.

    Local Existing Instance info.

    Lemma compile_get {tr mem locals functions}
          (a: ListArray.t Elem.type) (idx: K):
      let v := ListArray.get a idx in
      forall {P} {pred: P v -> predicate} {k: nlet_eq_k P v} {k_impl}
        R (a_ptr: address) a_var idx_var var,

        sep (repr a_ptr a) R mem ->
        map.get locals a_var = Some a_ptr ->
        map.get locals idx_var = Some (word.of_Z (Z.of_nat (cast idx))) ->

        (cast idx < Datatypes.length a)%nat ->

        (let v := v in
         <{ Trace := tr;
            Memory := mem;
            Locals := map.put locals var (Elem.to_word v);
            Functions := functions }>
         k_impl
         <{ pred (k v eq_refl) }>) ->
        <{ Trace := tr;
           Memory := mem;
           Locals := locals;
           Functions := functions }>
        cmd.seq
          (cmd.set
             var
             (expr.load
                (Elem.size)
                (offset (expr.var a_var)
                        (expr.var idx_var)
                        (expr.literal Elem.width))))
          k_impl
        <{ pred (nlet_eq [var] v k) }>.
    Proof.
      intros.
      eapply (compile_array_get (AI := info))
        with (a := a) (idx := idx); eauto.
    Qed.

    Lemma compile_put {tr mem locals functions}
          (a: ListArray.t Elem.type) (idx: K) val:
      let v := ListArray.put a idx val in
      forall {P} {pred: P v -> predicate} {k: nlet_eq_k P v} {k_impl}
        R (a_ptr: address) a_var idx_var val_var var,

        sep (repr a_ptr a) R mem ->
        map.get locals a_var = Some a_ptr ->
        map.get locals idx_var = Some (word.of_Z (Z.of_nat (cast idx))) ->
        map.get locals val_var = Some (Elem.to_word val) ->

        (K_to_nat idx < List.length a)%nat ->

        (let v := v in
         forall mem',
           sep (repr a_ptr v) R mem' ->
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
          (cmd.store
             (Elem.size)
             (offset (expr.var a_var)
                     (expr.var idx_var)
                     (expr.literal Elem.width))
             (expr.var val_var))
          k_impl
        <{ pred (nlet_eq [var] v k) }>.
    Proof.
      intros.
      simple eapply (compile_array_put (AI := info))
        with (a := a) (val := val) (idx := idx); eauto.
    Qed.
  End with_parameters.
End GenericListArray.

Module GenericSizedListArray.
  Import GenericArray.

  Section with_parameters.
    Context {semantics : Semantics.parameters}
            {semantics_ok : Semantics.parameters_ok semantics}.

    Context {sz: AccessSize}.
    Let EI := _elem_info sz.
    Local Existing Instance EI.
    Notation V := Elem.type.

    Context {K: Type}
            {ConvNat: Convertible K nat}
            {HD: HasDefault V}.

    Notation to_list x := x (only parsing).
    Notation K_to_nat idx := (@cast _ _ ConvNat idx).
    Notation K_to_word x := (word.of_Z (Z.of_nat (K_to_nat x))).

    Notation get a idx := (ListArray.get a idx).
    Notation put a idx v := (ListArray.put a idx v).

    Definition repr (addr: address) (len: nat) (a: ListArray.t Elem.type) : Semantics.mem -> Prop :=
      sep (emp (List.length a = len))
          (GenericListArray.repr addr a).

    Lemma repr_of_array addr len a mem :
      List.length a = len ->
      GenericListArray.repr addr a mem ->
      repr addr len a mem.
    Proof. intros; apply sep_emp_l; eauto. Qed.

    Lemma array_of_repr addr len a mem :
      repr addr len a mem ->
      GenericListArray.repr addr a mem.
    Proof. intros H; apply sep_emp_l in H; intuition. Qed.

    Lemma length_of_repr addr len a mem :
      repr addr len a mem ->
      List.length a = len.
    Proof. intros H; apply sep_emp_l in H; intuition. Qed.

    Program Definition info : array_info :=
      {| A := ListArray.t Elem.type;
         GenericArray.K := K;

         GenericArray.to_list l := to_list l;
         GenericArray.K_to_nat idx := K_to_nat idx;

         GenericArray.get a idx := get a idx;
         GenericArray.put a idx v := put a idx v;

         GenericArray.repr addr a := repr addr (List.length a) a
      |}.

    Next Obligation.
    Proof.
      apply GenericListArray.info_obligation_1.
    Qed.

    Next Obligation.
    Proof.
      unfold repr; intro; rewrite sep_emp_l; tauto.
    Qed.

    Next Obligation.
    Proof.
      apply GenericListArray.info_obligation_4; auto.
    Qed.

    Lemma SizedListArray_length :
      forall addr len (a: ListArray.t Elem.type) mem R,
        (repr addr len a * R)%sep mem -> List.length a = len.
    Proof.
      intros * H; unfold repr in H.
      eapply proj1. apply sep_emp_l with (m := mem).
      ecancel_assumption.
    Qed.

    Lemma compile_get {len} {tr mem locals functions}
          (a: ListArray.t Elem.type) (idx: K):
      let v := ListArray.get a idx in
      forall {P} {pred: P v -> predicate} {k: nlet_eq_k P v} {k_impl}
        R (a_ptr: address) a_var idx_var var,

        sep (repr a_ptr len a) R mem ->
        map.get locals a_var = Some a_ptr ->
        map.get locals idx_var = Some (word.of_Z (Z.of_nat (cast idx))) ->

        (cast idx < len)%nat ->

        (let v := v in
         <{ Trace := tr;
            Memory := mem;
            Locals := map.put locals var (Elem.to_word v);
            Functions := functions }>
         k_impl
         <{ pred (k v eq_refl) }>) ->
        <{ Trace := tr;
           Memory := mem;
           Locals := locals;
           Functions := functions }>
        cmd.seq
          (cmd.set
             var
             (expr.load
                (Elem.size)
                (offset (expr.var a_var)
                        (expr.var idx_var)
                        (expr.literal Elem.width))))
          k_impl
        <{ pred (nlet_eq [var] v k) }>.
    Proof.
      intros.
      simple eapply (compile_array_get (AI := info))
        with (a := a) (idx := idx); simpl;
        try erewrite SizedListArray_length; eauto.
    Qed.

    Lemma compile_put {len} {tr mem locals functions}
          (a: ListArray.t Elem.type) (idx: K) val:
      let v := ListArray.put a idx val in
      forall {P} {pred: P v -> predicate} {k: nlet_eq_k P v} {k_impl}
        R (a_ptr: address) a_var idx_var val_var var,

        sep (repr a_ptr len a) R mem ->
        map.get locals a_var = Some a_ptr ->
        map.get locals idx_var = Some (word.of_Z (Z.of_nat (cast idx))) ->
        map.get locals val_var = Some (Elem.to_word val) ->

        (cast idx < len)%nat ->

        (let v := v in
         forall mem',
           sep (repr a_ptr len v) R mem' ->
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
          (cmd.store
             (Elem.size)
             (offset (expr.var a_var)
                     (expr.var idx_var)
                     (expr.literal Elem.width))
             (expr.var val_var))
          k_impl
        <{ pred (nlet_eq [var] v k) }>.
    Proof.
      intros.
      simple eapply (compile_array_put (AI := info))
        with (a := a) (val := val) (idx := idx);
        simpl; erewrite ?ListArray.put_length;
          erewrite ?SizedListArray_length; eauto.
    Qed.
  End with_parameters.
End GenericSizedListArray.

Ltac prepare_array_lemma lemma sz := (* This makes [simple apply] work *)
  pose (fun {semantics : Semantics.parameters}
          {semantics_ok : Semantics.parameters_ok semantics} =>
          lemma semantics semantics_ok sz) as lem;
  cbv beta iota delta [_elem_info] in *;
  GenericArray._cbv lem; Elem._cbv lem;
  let t := type of lem in
  exact (lem: t).

Notation prepare_array_lemma lemma sz :=
  ltac:(prepare_array_lemma lemma sz) (only parsing).

Module ByteVectorArray.
  Notation repr := (GenericVectorArray.repr (sz := AccessByte)).
  Definition compile_get :=
    prepare_array_lemma (@GenericVectorArray.compile_get) AccessByte.
  Definition compile_put :=
    prepare_array_lemma (@GenericVectorArray.compile_put) AccessByte.
End ByteVectorArray.
Arguments ByteVectorArray.compile_get {_ _}.
Arguments ByteVectorArray.compile_put {_ _}.

Module WordVectorArray.
  Notation repr := (GenericVectorArray.repr (sz := AccessWord)).
  Definition compile_get :=
    prepare_array_lemma (@GenericVectorArray.compile_get) AccessWord.
  Definition compile_put :=
    prepare_array_lemma (@GenericVectorArray.compile_put) AccessWord.
End WordVectorArray.
Arguments WordVectorArray.compile_get {_ _}.
Arguments WordVectorArray.compile_put {_ _}.

Module ByteListArray.
  Notation repr := (GenericListArray.repr (sz := AccessByte)).
  Definition compile_get :=
    prepare_array_lemma (@GenericListArray.compile_get) AccessByte.
  Definition compile_put :=
    prepare_array_lemma (@GenericListArray.compile_put) AccessByte.
End ByteListArray.
Arguments ByteListArray.compile_get {_ _}.
Arguments ByteListArray.compile_put {_ _}.

Module WordListArray.
  Notation repr := (GenericListArray.repr (sz := AccessWord)).
  Definition compile_get :=
    prepare_array_lemma (@GenericListArray.compile_get) AccessWord.
  Definition compile_put :=
    prepare_array_lemma (@GenericListArray.compile_put) AccessWord.
End WordListArray.
Arguments WordListArray.compile_get {_ _}.
Arguments WordListArray.compile_put {_ _}.

Module ByteSizedListArray.
  Notation repr := (GenericSizedListArray.repr (sz := AccessByte)).
  Definition compile_get :=
    prepare_array_lemma (@GenericSizedListArray.compile_get) AccessByte.
  Definition compile_put :=
    prepare_array_lemma (@GenericSizedListArray.compile_put) AccessByte.
End ByteSizedListArray.
Arguments ByteSizedListArray.compile_get {_ _}.
Arguments ByteSizedListArray.compile_put {_ _}.

Module WordSizedListArray.
  Notation repr := (GenericSizedListArray.repr (sz := AccessWord)).
  Definition compile_get :=
    prepare_array_lemma (@GenericSizedListArray.compile_get) AccessWord.
  Definition compile_put :=
    prepare_array_lemma (@GenericSizedListArray.compile_put) AccessWord.
End WordSizedListArray.
Arguments WordSizedListArray.compile_get {_ _}.
Arguments WordSizedListArray.compile_put {_ _}.

Arguments _elem_info /.
Arguments Elem.width /.

Instance Convertible_Z_nat : Convertible Z nat :=
  fun w => Z.to_nat w.

Instance Convertible_word_nat {s: Semantics.parameters} : Convertible word nat :=
  fun w => Z.to_nat (word.unsigned w).

Hint Unfold cast : compiler_cleanup.
Hint Unfold Convertible_word_nat : compiler_cleanup.

Module VectorArrayCompiler.
  #[export] Hint Extern 1 => simple eapply (@ByteVectorArray.compile_get); shelve : compiler.
  #[export] Hint Extern 1 => simple eapply (@WordVectorArray.compile_get); shelve : compiler.
  #[export] Hint Extern 1 => simple eapply (@ByteVectorArray.compile_put); shelve : compiler.
  #[export] Hint Extern 1 => simple eapply (@WordVectorArray.compile_put); shelve : compiler.
End VectorArrayCompiler.

Module ListArrayCompiler.
  #[export] Hint Extern 1 => simple eapply (@ByteListArray.compile_get); shelve : compiler.
  #[export] Hint Extern 1 => simple eapply (@WordListArray.compile_get); shelve : compiler.
  #[export] Hint Extern 1 => simple eapply (@ByteListArray.compile_put); shelve : compiler.
  #[export] Hint Extern 1 => simple eapply (@WordListArray.compile_put); shelve : compiler.
End ListArrayCompiler.

Module SizedListArrayCompiler.
  #[export] Hint Extern 1 => simple eapply (@ByteSizedListArray.compile_get); shelve : compiler.
  #[export] Hint Extern 1 => simple eapply (@WordSizedListArray.compile_get); shelve : compiler.
  #[export] Hint Extern 1 => simple eapply (@ByteSizedListArray.compile_put); shelve : compiler.
  #[export] Hint Extern 1 => simple eapply (@WordSizedListArray.compile_put); shelve : compiler.
End SizedListArrayCompiler.

Export VectorArrayCompiler.
(* ListArrayCompiler and SizedListArrayCompiler conflict, so don't export them. *)
