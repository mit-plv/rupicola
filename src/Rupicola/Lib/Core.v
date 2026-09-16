From Coq Require Export
     Morphisms DecimalString
     String List ZArith Lia.
From Coq Require Vector.
From bedrock2 Require Export
     Array ArrayCasts Map.Separation ProgramLogic
     Map.SeparationLogic Scalars Syntax WeakestPreconditionProperties
     ZnWords.
From coqutil Require Export
     Macros.WithBaseName dlet Byte Datatypes.List
     Z.PushPullMod Tactics.Tactics Tactics.letexists
     Word.Properties Word.Bitwidth
     Map.Interface Map.Properties Map.SortedList.
From coqutil Require Import
     Decidable.
From coqutil Require
     Map.SortedListString.

Export Syntax.Coercions.

Open Scope string_scope.
Export ListNotations.

Declare Scope sep_scope.
Delimit Scope sep_scope with sep.
Infix "*" := (sep) : sep_scope.

Global Set Default Goal Selector "1".

Module P2.
  (* Note: Unlike ``coqutil.Datatypes.PrimitivePair.pair``, these are
     non-dependent and the notation for them associates to the left. *)
  Section Primitive.
    Set Primitive Projections.
    Record prod {A B} := pair { car: A; cdr: B }.
  End Primitive.
  Arguments prod: clear implicits.
  Arguments pair {A B} car cdr.
End P2.

Declare Scope p2_scope.
Delimit Scope p2_scope with p2.
Notation "\<<  x ,  .. ,  y ,  z  \>>" :=
  (P2.prod x%type .. (P2.prod y%type z%type) ..) : p2_scope.
Notation "\<  x ,  .. ,  y ,  z  \>" :=
  (P2.pair x .. (P2.pair y z) ..) : p2_scope.
Open Scope p2_scope.

(* ⚠ These pairs associate to the *left*: \< 1, 2, 3 \> is \< 1, \< 2, 3 \> \> *)
Definition __p2_assoc_test:
  (\< 1, 2, 3 \>       <: \<< nat, nat, nat \>>) =
  (\< 1, \< 2, 3 \> \> <: \<< nat, \<< nat, nat \>> \>>)
  := eq_refl.

Create HintDb lia.
#[export] Hint Extern 1 => lia : lia.

Create HintDb nia.
#[export] Hint Extern 1 => nia : nia.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Module map.
  Section __.
    Context {key value value'}
            {map : map.map key value}
            {map' : map.map key value'}
            {map_ok : map.ok map}
            {map'_ok : map.ok map'}
            {key_eqb : key -> key -> bool}
            {key_eq_dec : EqDecider key_eqb}.

    Implicit Types (m : map).

    Lemma get_mapped m k (f: value -> value'):
      map.get (map.fold (fun (m' : map') k v => map.put m' k (f v)) map.empty m) k =
      match map.get m k with
      | Some v => Some (f v)
      | None => None
      end.
    Proof.
      apply map.fold_spec.
      - rewrite !map.get_empty; reflexivity.
      - intros; rewrite !map.get_put_dec; destruct key_eqb; eauto.
    Qed.
  End __.

  Definition map_of_list' {K V} {map: map.map K V} (rev_bindings: list (K * V)) (acc: map) :=
    List.fold_right (fun '(k, v) m => map.put m k v) acc rev_bindings.

  Lemma of_list_is_fold_right' {K V} {map: map.map K V}:
    forall bs acc,
      (fix of_list (l : list (K * V)) : map :=
         match l with
         | [] => acc
         | (k, v) :: l => map.put (of_list l) k v
         end) bs =
      map_of_list' bs acc.
  Proof.
    induction bs as [ | [k v] ]; cbn; intros.
    - reflexivity.
    - rewrite IHbs; reflexivity.
  Qed.

  Lemma of_list_is_fold_right {K V} {map: map.map K V}:
    forall bs, map.of_list bs = map_of_list' bs map.empty :> map.
  Proof. intros; apply of_list_is_fold_right'. Qed.

  Definition map_domains_diff {K V} {map: map.map K V} (m0 m1: map) :=
    map.keys (map.fold (fun (m0: map) k _ => map.remove m0 k) m0 m1).

  Section MapCompat.
    Context {K V0 V1}
            {map0: map.map K V0}
            {map1: map.map K V1}
            {map_ok0: map.ok map0}
            {map_ok1: map.ok map1}
            {K_eqb : K -> K -> bool}
            {K_eq_dec : EqDecider K_eqb}
            (fV: V0 -> V1).

    Definition mapped_compat (m0 : map0) (m1 : map1) :=
      forall k v, map.get m0 k = Some v ->
             map.get m1 k = Some (fV v).

    Lemma mapped_compat_of_list bs1 bs2:
      bs2 = List.map (fun pr => (fst pr, fV (snd pr))) bs1 ->
      mapped_compat (map.of_list (map := map0) bs1)
                    (map.of_list (map := map1) bs2).
    Proof.
      induction bs1 as [| (k1 & v1) bs1] in bs2 |- *;
        (destruct bs2 as [| (k2 & v2) bs2];
         cbn - [map.get map.put];
         intros H k v; inversion H; subst; clear H;
         try congruence).
      - rewrite map.get_empty; inversion 1.
      - rewrite !map.get_put_dec.
        destruct (K_eq_dec k1 k).
        + inversion 1; subst; reflexivity.
        + intros. apply (IHbs1 _ eq_refl). eassumption.
    Qed.
  End MapCompat.

  Definition map_eq {K V} {map0 map1: map.map K V}
             {map_ok0: map.ok map0} {map_ok1: map.ok map1}
             m0 m1 :=
    (forall k, map.get (map := map0) m0 k = map.get (map := map1) m1 k).

#[global]
  Instance eq_refl {K V} {map: map.map K V} {map_ok: map.ok map} :
    RelationClasses.Reflexive (@map_eq K V map map map_ok map_ok).
  Proof. unfold map_eq; constructor; congruence. Qed.

  Lemma eq_trans {K V}
        {map0 map1 map2: map.map K V}
        {map_ok0: map.ok map0} {map_ok1: map.ok map1} {map_ok2: map.ok map2} :
    forall m0 m1 m2,
      map_eq (map0 := map0) (map1 := map1) m0 m1 ->
      map_eq (map0 := map1) (map1 := map2) m1 m2 ->
      map_eq m0 m2.
  Proof. unfold map_eq; congruence. Qed.

  Lemma eq_sym {K V}
        {map0 map1: map.map K V}
        {map_ok0: map.ok map0} {map_ok1: map.ok map1} :
    forall m0 m1,
      map_eq (map0 := map0) (map1 := map1) m0 m1 ->
      map_eq (map0 := map1) (map1 := map0) m1 m0.
  Proof. unfold map_eq; congruence. Qed.

  Lemma put_proper {K V}
        {map0 map1: map.map K V}
        {map_ok0: map.ok map0} {map_ok1: map.ok map1}
        {key_eqb: K -> K -> bool}
        {key_eq_dec : EqDecider key_eqb} :
    forall k v (m0: map.rep (map := map0)) (m1: map.rep (map := map1)),
      map_eq m0 m1 ->
      map_eq (map.put m0 k v) (map.put m1 k v).
  Proof.
    intros * Heq k.
    destr (key_eqb k0 k); rewrite ?map.get_put_same, ?map.get_put_diff; auto.
  Qed.

  Lemma remove_proper {K V}
        {map0 map1: map.map K V}
        {map_ok0: map.ok map0} {map_ok1: map.ok map1}
        {key_eqb: K -> K -> bool}
        {key_eq_dec : EqDecider key_eqb} :
    forall k (m0: map.rep (map := map0)) (m1: map.rep (map := map1)),
      map_eq m0 m1 ->
      map_eq (map.remove m0 k) (map.remove m1 k).
  Proof.
    intros * Heq k.
    destr (key_eqb k0 k); rewrite ?map.get_remove_same, ?map.get_remove_diff; auto.
  Qed.

  Definition remove_many {K V} {M: map.map K V} (m : M) (ks: list K) :=
    List.fold_left map.remove ks m.

  Lemma remove_many_proper {K V}
        {map0 map1: map.map K V}
        {map_ok0: map.ok map0} {map_ok1: map.ok map1}
        {key_eqb: K -> K -> bool}
        {key_eq_dec : EqDecider key_eqb} :
    forall ks (m0: map.rep (map := map0)) (m1: map.rep (map := map1)),
      map_eq m0 m1 ->
      map_eq (remove_many m0 ks) (remove_many m1 ks).
  Proof.
    unfold remove_many; induction ks; simpl; intros.
    - assumption.
    - apply IHks, remove_proper; assumption.
  Qed.

  Lemma ext_eq {K V} {map: map.map K V} {map_ok: map.ok map} :
    forall m0 m1, map_eq m0 m1 -> m0 = m1.
  Proof. apply map.map_ext. Qed.

  Lemma ext_rev {K V} {map: map.map K V} {map_ok: map.ok map} :
    forall m0 m1, m0 = m1 -> map_eq m0 m1.
  Proof. intros; subst; reflexivity. Qed.

  Lemma of_list_proper' {K V}
        {map0 map1: map.map K V}
        {map_ok0: map.ok map0} {map_ok1: map.ok map1}
        {key_eqb: K -> K -> bool}
        {key_eq_dec : EqDecider key_eqb} :
    forall bs m0 m1,
      map_eq (map0 := map0) (map1 := map1) m0 m1 ->
      map_eq (map_of_list' bs m0)
             (map_of_list' bs m1).
  Proof.
    induction bs as [ | (k & v) bs ]; simpl; intros.
    - assumption.
    - apply put_proper, IHbs; assumption.
  Qed.

  Lemma eq_empty {K V}:
    forall {map0 map1: map.map K V}
      {map_ok0: map.ok map0} {map_ok1: map.ok map1},
      map_eq (map.empty (map := map0)) (map.empty (map := map1)).
  Proof.
    red; intros; rewrite !map.get_empty; reflexivity.
  Qed.

  Lemma of_list_proper {K V}
        {map0 map1: map.map K V}
        {map_ok0: map.ok map0} {map_ok1: map.ok map1}
        {key_eqb: K -> K -> bool}
        {key_eq_dec : EqDecider key_eqb} :
    forall bs,
      map_eq (map.of_list (map := map0) bs)
             (map.of_list (map := map1) bs).
  Proof.
    intros; rewrite !of_list_is_fold_right;
      apply of_list_proper', eq_empty.
  Qed.

  Lemma eq_of_list {K V}
        {map0 map1: map.map K V}
        {map_ok0: map.ok map0} {map_ok1: map.ok map1}
        {key_eqb: K -> K -> bool}
        {key_eq_dec : EqDecider key_eqb} :
    forall b1 b2,
      map_eq (map.of_list (map := map0) b1) (map.of_list (map := map0) b2) ->
      map_eq (map.of_list (map := map1) b1) (map.of_list (map := map1) b2).
  Proof.
    intros.
    eapply (eq_trans (map1 := map0));
      [ eapply (eq_trans (map1 := map0)) | ].
    all: eauto using @of_list_proper.
  Qed.

  Lemma remove_many_diff_of_str_list {V} {map: map.map string V} {map_ok: map.ok map}:
    let SM := SortedListString.map V in
    let SM_ok := SortedListString.ok V in
    forall (b0 b1: list (string * V)) ks,
      let sb0 := map.of_list (map := SM) b0 in
      let sb1 := map.of_list (map := SM) b1 in
      ks = map_domains_diff sb0 sb1 -> (* Used for unification *)
      remove_many sb0 ks = sb1 ->
      remove_many (map.of_list (map := map) b0) ks = map.of_list b1.
  Proof.
    intros ?? * Hks Hm%ext_rev; apply ext_eq.
    eapply (eq_trans (map1 := SM)); [ eapply remove_many_proper, of_list_proper | ].
    eapply (eq_trans (map1 := SM)); [ | eapply of_list_proper ].
    exact Hm.
  Qed.

  Lemma get_of_str_list {V} {map: map.map string V} {map_ok: map.ok map}:
    let SM := SortedListString.map V in
    let SM_ok := SortedListString.ok V in
    forall (b: list (string * V)) k v,
      let sb := map.of_list (map := SM) b in
      map.get sb k = v ->
      map.get (map.of_list (map := map) b) k = v.
  Proof.
    intros; rewrite of_list_proper; eassumption.
  Qed.

  Lemma eq_of_str_list {V} {map: map.map string V} {map_ok: map.ok map}:
    let SM := SortedListString.map V in
    let SM_ok := SortedListString.ok V in
    forall (b1 b2: list (string * V)),
      map.of_list (map := SM) b1 = map.of_list (map := SM) b2 ->
      map.of_list (map := map) b1 = map.of_list (map := map) b2.
  Proof.
    intros SM SM_ok b1 b2 H%ext_rev; apply ext_eq.
    apply eq_of_list; assumption.
  Qed.

  Fixpoint list_assoc_str {V} (k: string) (l: list (string * V)) :=
    match l with
    | [] => None
    | (k', v) :: l => if String.eqb k' k then Some v else list_assoc_str k l
    end.

  Lemma get_of_str_list_assoc {V} {map: map.map string V} {map_ok: map.ok map}:
    forall k bs,
      map.get (map.of_list (map := map) bs) k =
      list_assoc_str k bs.
  Proof.
    induction bs as [|(k', v) bs IHbs]; simpl; intros.
    - rewrite map.get_empty; reflexivity.
    - rewrite map.get_put_dec, IHbs; reflexivity.
  Qed.

  Lemma get_of_str_list_assoc_impl {V} {map: map.map string V} {map_ok: map.ok map}:
    forall k bs v,
      list_assoc_str k bs = v ->
      map.get (map.of_list (map := map) bs) k = v.
  Proof. intros; rewrite get_of_str_list_assoc; eassumption. Qed.
End map.

#[global]
Hint Rewrite @map.get_put_diff @map.get_put_same @map.put_put_same
     @map.remove_put_diff @map.remove_put_same
     @map.remove_empty @map.get_empty
     using (typeclasses eauto || congruence) : mapsimpl.

Section Vectors.
  Lemma Vector_to_list_length {T n}:
    forall (v: Vector.t T n),
      List.length (Vector.to_list v) = n.
  Proof.
    induction v; cbn.
    - reflexivity.
    - f_equal; assumption.
  Qed.

  Lemma Vector_nth_hd_skipn {T n}:
    forall (f: Fin.t n) idx (v : Vector.t T n) (t0 : T),
      idx = proj1_sig (Fin.to_nat f) ->
      Vector.nth v f = List.hd t0 (List.skipn idx (Vector.to_list v)).
  Proof.
    induction f; cbn; intros; rewrite (Vector.eta v).
    - subst; reflexivity.
    - subst; destruct (Fin.to_nat f); cbn.
      erewrite IHf; reflexivity.
  Qed.

  Lemma Vector_to_list_app {A n1 n2} :
    forall v1 v2,
      Vector.to_list (@Vector.append A n1 n2 v1 v2) =
      List.app (Vector.to_list v1) (Vector.to_list v2).
  Proof.
    induction v1; cbn; intros.
    - reflexivity.
    - f_equal. apply IHv1.
  Qed.

  Lemma Vector_to_list_replace {A n}:
    forall (a: Vector.t A n) (idx: nat) (f: Fin.t n) v,
      idx = proj1_sig (Fin.to_nat f) ->
      Vector.to_list (Vector.replace a f v) =
      replace_nth idx (Vector.to_list a) v.
  Proof.
    intros; subst; induction f; cbn; intros; rewrite (Vector.eta a).
    - reflexivity.
    - destruct (Fin.to_nat f); cbn in *.
      f_equal; apply IHf.
  Qed.

  Lemma Vector_nth_replace {T n}:
    forall (idx: Fin.t n) (v: Vector.t T n) (val: T),
      Vector.nth (Vector.replace v idx val) idx = val.
  Proof.
    induction idx; intros; rewrite (Vector.eta v); cbn; try rewrite IHidx; reflexivity.
  Qed.
End Vectors.

Global Open Scope Z_scope.

Section Arith.
  Lemma Z_land_leq_right a b
    : 0 <= a -> 0 <= b ->
      0 <= Z.land a b <= b.
  Proof.
    destruct a as [|pa|], b as [|pb|];
      rewrite ?Z.land_0_l, ?Z.land_0_r;
      try lia; intros _ _.
    revert pb; induction pa; destruct pb; simpl in *; try lia.
    all: specialize (IHpa pb); destruct Pos.land in *; simpl; lia.
  Qed.

  Lemma Nat_mod_eq' a n:
    n <> 0%nat ->
    a = (n * (a / n) + (a mod n))%nat.
  Proof.
    intros; pose proof Nat.mul_div_le a n.
    rewrite Nat.mod_eq; lia.
  Qed.

  Lemma Nat_mod_eq'' a n:
    n <> 0%nat ->
    (n * (a / n) = a - (a mod n))%nat.
  Proof.
    intros; pose proof Nat.mul_div_le a n.
    rewrite Nat.mod_eq; lia.
  Qed.

  Lemma Z_mod_eq' a b:
    b <> 0 ->
    a = b * (a / b) + a mod b.
  Proof. pose proof Z.mod_eq a b; lia. Qed.

  Lemma Z_mod_eq'' a b:
    b <> 0 ->
    b * (a / b) = a - a mod b.
  Proof. pose proof Z.mod_eq a b; lia. Qed.
End Arith.

(** ** Nat.iter **)

Lemma Nat_iter_inv {A} (P: A -> Prop) (fA: A -> A):
  (forall a, P a -> P (fA a)) ->
  forall n a,
    P a ->
    P (Nat.iter n fA a).
Proof. intros Hind; induction n; simpl; auto. Qed.

Lemma Nat_iter_const_length {A : Type} f : forall (n : nat) (l0 : list A),
    (forall l, length (f l) = length l) ->
    length (Nat.iter n f l0) = length l0.
Proof. intros; apply Nat_iter_inv; congruence. Qed.

Lemma Nat_iter_rew {A B} (fA: A -> A) (fB: B -> B) (g: A -> B):
  (forall a, g (fA a) = fB (g a)) ->
  forall n a b,
    b = g a ->
    g (Nat.iter n fA a) = Nat.iter n fB b.
Proof.
  intros Heq; induction n; simpl; intros; subst.
  - reflexivity.
  - erewrite Heq, IHn; reflexivity.
Qed.

Lemma Nat_iter_rew_inv {A B} (P: A -> Prop) (fA: A -> A) (fB: B -> B) (g: A -> B):
  (forall a, P a -> P (fA a)) ->
  (forall a, P a -> g (fA a) = fB (g a)) ->
  forall n a b,
    P a ->
    b = g a ->
    P (Nat.iter n fA a) /\
    g (Nat.iter n fA a) = Nat.iter n fB b.
Proof.
  intros Hind Heq; induction n; simpl; intros * Ha ->.
  - eauto.
  - specialize (IHn _ _ Ha eq_refl) as [HPa Hg].
    split; eauto. erewrite Heq, Hg; eauto.
Qed.

Import List.

Lemma width_ge_1 {width} {BW: Bitwidth width} : 1 <= width.
Proof. pose proof width_pos; lia. Qed.

(* TODO: should be upstreamed to coqutil *)
Module word.
  Section __.
    Context {width} {BW: Bitwidth width}.
    Local Notation word := (bits width).

    Lemma smodulo_range z:
      - 2 ^ (width - 1) <= Z.smodulo z (2 ^ width) < 2 ^ (width - 1).
    Proof.
      rewrite word.smodulo_pow2; set (z + _) as z0.
      pose proof Z.mod_pos_bound z0 (2 ^ width) modulus_pos as h.
      rewrite (word.pow2_width_minus1 width_pos) in h at 3; lia.
    Qed.

    Lemma of_Z_smodulo z:
      bits.of_Z width z = bits.of_Z width (Z.smodulo z (2 ^ width)).
    Proof. apply Zmod.signed_inj; rewrite !bits.signed_of_Z, Z.smod_smod; reflexivity. Qed.

    Lemma unsigned_of_Z_le (z: Z):
      0 <= z ->
      Zmod.unsigned (bits.of_Z width z) <= z.
    Proof. rewrite bits.unsigned_of_Z; intros; apply Z.mod_le, modulus_pos; lia. Qed.

    Lemma and_leq_right (a b : word)
      : (Zmod.unsigned (Zmod.and a b)) <= (Zmod.unsigned b).
    Proof.
      rewrite bits.unsigned_and.
      apply Z_land_leq_right.
      all: apply (bits.unsigned_range _ width_nonneg).
    Qed.

    Implicit Types w : word.

    Lemma signed_gz_eq_unsigned w :
      0 <= Zmod.signed w ->
      Zmod.unsigned w = Zmod.signed w.
    Proof.
      rewrite (bits.signed_nonneg_iff _ width_nonneg); intros.
      symmetry; apply bits.signed_small; pose proof bits.unsigned_range w width_nonneg; lia.
    Qed.

    Lemma of_nat_to_nat_unsigned w:
      Z.of_nat (Z.to_nat (Zmod.unsigned w)) = (Zmod.unsigned w).
    Proof.
      pose proof bits.unsigned_range w width_nonneg.
      rewrite Z2Nat.id; intuition.
    Qed.

    Lemma of_Z_of_nat_to_nat_unsigned w:
      bits.of_Z width (Z.of_nat (Z.to_nat (Zmod.unsigned w))) = w.
    Proof.
      pose proof bits.unsigned_range w width_nonneg.
      rewrite Z2Nat.id, Zmod.of_Z_unsigned; intuition.
    Qed.

    (* FIXME make this a definition *)
    Notation word_of_byte b :=
      (bits.of_Z width (Byte.byte.unsigned b)).

    Notation byte_of_word w :=
      (byte.of_Z (Zmod.unsigned w)).

    Lemma byte_of_Z_unsigned b:
      byte.of_Z (byte.unsigned b) = b.
    Proof. destruct b; reflexivity. Qed.

    Lemma word_of_byte_range b:
      0 <= Zmod.unsigned (word_of_byte b) < 256.
    Proof.
      pose proof Byte.to_N_bounded b as H256%N2Z.inj_le.
      unfold Byte.byte.unsigned.
      rewrite bits.unsigned_of_Z_small; [ lia | ].
      destruct width_cases as [-> | ->]; lia.
    Qed.

    Definition b2w (b: bool) : word :=
      bits.of_Z width (Z.b2z b).

    Lemma b2w_if (b: bool) :
      b2w b = if b then Zmod.one else Zmod.zero.
    Proof. destruct b; reflexivity. Qed.

    Lemma unsigned_b2w b:
      Zmod.unsigned (b2w b) = Z.b2z b.
    Proof.
      unfold b2w; apply bits.unsigned_of_Z_small.
      destruct b, width_cases as [-> | ->]; cbn; lia.
    Qed.

    Lemma b2w_inj:
      forall b1 b2, b2w b1 = b2w b2 -> b1 = b2.
    Proof.
      intros [|] [|] H%(f_equal Zmod.unsigned);
        rewrite !unsigned_b2w in H; cbn in H; congruence.
    Qed.

    Section MinMax.
      Definition minu w1 w2 := if Semantics.ltu w2 w1 then w2 else w1.
      Definition mins w1 w2 := if Semantics.lts w2 w1 then w2 else w1.
      Definition maxu w1 w2 := if Semantics.ltu w1 w2 then w2 else w1.
      Definition maxs w1 w2 := if Semantics.lts w1 w2 then w2 else w1.

      Ltac t :=
        unfold minu, maxu, mins, maxs, Semantics.ltu, Semantics.lts, Z.min, Z.max;
        intros;
        rewrite ?bits.unsigned_of_Z_small, ?bits.signed_of_Z by assumption;
        rewrite ?(Z.smod_pow2_small _ _ width_pos)
          by (rewrite (word.pow2_width_minus1 width_pos); lia);
        (rewrite Z.compare_antisym + idtac);
        rewrite Z.ltb_compare; destruct (_ ?= _);
        cbv beta iota delta [CompOpp]; rewrite ?Zmod.of_Z_unsigned, ?Zmod.of_Z_signed;
        reflexivity.

      Lemma unsigned_minu w1 w2 :
        minu w1 w2 = bits.of_Z width (Z.min (Zmod.unsigned w1) (Zmod.unsigned w2)).
      Proof. t. Qed.

      Lemma unsigned_maxu w1 w2 :
        maxu w1 w2 = bits.of_Z width (Z.max (Zmod.unsigned w1) (Zmod.unsigned w2)).
      Proof. t. Qed.

      Lemma signed_mins w1 w2 :
        mins w1 w2 = bits.of_Z width (Z.min (Zmod.signed w1) (Zmod.signed w2)).
      Proof. t. Qed.

      Lemma signed_maxs w1 w2 :
        maxs w1 w2 = bits.of_Z width (Z.max (Zmod.signed w1) (Zmod.signed w2)).
      Proof. t. Qed.

      Lemma minu_unsigned w1 w2 :
        Zmod.unsigned (minu w1 w2) = Z.min (Zmod.unsigned w1) (Zmod.unsigned w2).
      Proof. t. Qed.

      Lemma maxu_unsigned w1 w2 :
        Zmod.unsigned (maxu w1 w2) = Z.max (Zmod.unsigned w1) (Zmod.unsigned w2).
      Proof. t. Qed.

      Lemma mins_signed w1 w2 :
        Zmod.signed (mins w1 w2) = Z.min (Zmod.signed w1) (Zmod.signed w2).
      Proof. t. Qed.

      Lemma maxs_signed w1 w2 :
        Zmod.signed (maxs w1 w2) = Z.max (Zmod.signed w1) (Zmod.signed w2).
      Proof. t. Qed.

      Lemma minu_of_Z z1 z2 :
        0 <= z1 < 2 ^ width -> 0 <= z2 < 2 ^ width ->
        minu (bits.of_Z width z1) (bits.of_Z width z2) = bits.of_Z width (Z.min z1 z2).
      Proof. t. Qed.

      Lemma maxu_of_Z z1 z2 :
        0 <= z1 < 2 ^ width -> 0 <= z2 < 2 ^ width ->
        maxu (bits.of_Z width z1) (bits.of_Z width z2) = bits.of_Z width (Z.max z1 z2).
      Proof. t. Qed.

      Lemma mins_of_Z z1 z2 :
        - 2 ^ (width - 1) <= z1 < 2 ^ (width - 1) ->
        - 2 ^ (width - 1) <= z2 < 2 ^ (width - 1) ->
        mins (bits.of_Z width z1) (bits.of_Z width z2) = bits.of_Z width (Z.min z1 z2).
      Proof. t. Qed.

      Lemma maxs_of_Z z1 z2 :
        - 2 ^ (width - 1) <= z1 < 2 ^ (width - 1) ->
        - 2 ^ (width - 1) <= z2 < 2 ^ (width - 1) ->
        maxs (bits.of_Z width z1) (bits.of_Z width z2) = bits.of_Z width (Z.max z1 z2).
      Proof. t. Qed.
    End MinMax.

    Ltac compile_binop_zzw_bitwise lemma :=
      intros; apply Zmod.unsigned_inj;
      rewrite lemma, !bits.unsigned_of_Z by lia;
      rewrite <- ?Z.land_ones by eauto using width_nonneg;
      bitblast.Z.bitblast.

    Lemma morph_and x y:
      bits.of_Z width (Z.land x y) = Zmod.and (bits.of_Z width x) (bits.of_Z width y).
    Proof. compile_binop_zzw_bitwise bits.unsigned_and. Qed.

    Lemma morph_or x y:
      bits.of_Z width (Z.lor x y) = Zmod.or (bits.of_Z width x) (bits.of_Z width y).
    Proof. compile_binop_zzw_bitwise bits.unsigned_or. Qed.

    Lemma morph_xor x y:
      bits.of_Z width (Z.lxor x y) = Zmod.xor (bits.of_Z width x) (bits.of_Z width y).
    Proof. compile_binop_zzw_bitwise bits.unsigned_xor. Qed.

    Lemma morph_shiftl z n:
      0 <= n < width ->
      bits.of_Z width (Z.shiftl z n) = Semantics.slu (bits.of_Z width z) (bits.of_Z width n).
    Proof.
      intros; apply Zmod.unsigned_inj.
      rewrite Semantics.unsigned_slu_shamtZ, !bits.unsigned_of_Z, !Z.shiftl_mul_pow2 by lia.
      Z.push_pull_mod; reflexivity.
    Qed.

    Lemma morph_shiftr z n:
      0 <= n < width ->
      0 <= z < 2 ^ width ->
      bits.of_Z width (Z.shiftr z n) = Semantics.sru (bits.of_Z width z) (bits.of_Z width n).
    Proof.
      intros; apply Zmod.unsigned_inj.
      rewrite Semantics.unsigned_sru_shamtZ, !Z.shiftr_div_pow2 by lia.
      rewrite !bits.unsigned_of_Z_small; try lia; try reflexivity.
      pose proof Z.pow_pos_nonneg 2 n.
      nia.
    Qed.

    Lemma morph_lts x y:
      - 2 ^ (width - 1) <= x < 2 ^ (width - 1) ->
      - 2 ^ (width - 1) <= y < 2 ^ (width - 1) ->
      (x <? y) = Z.ltb (Zmod.signed (bits.of_Z width x)) (Zmod.signed (bits.of_Z width y)).
    Proof.
      pose proof (word.pow2_width_minus1 width_pos).
      intros; rewrite !bits.signed_of_Z, !(Z.smod_pow2_small _ _ width_pos) by lia; reflexivity.
    Qed.

    Lemma morph_ltu x y:
      0 <= x < 2 ^ width ->
      0 <= y < 2 ^ width ->
      (x <? y) = Z.ltb (Zmod.unsigned (bits.of_Z width x)) (Zmod.unsigned (bits.of_Z width y)).
    Proof.
      intros; rewrite !bits.unsigned_of_Z_small by assumption; reflexivity.
    Qed.

    Lemma Z_land_wrap_l z1 z2:
      0 <= z2 < 2 ^ width ->
      Z.land (z1 mod 2 ^ width) z2 = Z.land z1 z2.
    Proof.
      pose proof width_pos.
      intros.
      rewrite <- Z.land_ones, <- Z.land_assoc by lia.
      rewrite (Z.land_comm _ z2), Z.land_ones by lia.
      rewrite Z.mod_small by lia.
      reflexivity.
    Qed.

    Lemma Z_land_wrap_r z1 z2:
      0 <= z1 < 2 ^ width ->
      Z.land z1 (z2 mod 2 ^ width) = Z.land z1 z2.
    Proof.
      intros; rewrite Z.land_comm at 1;
        rewrite Z_land_wrap_l by lia; apply Z.land_comm.
    Qed.

    Lemma of_Z_land_ones z :
      bits.of_Z width (Z.land z (Z.ones width)) = bits.of_Z width z.
    Proof.
      rewrite Z.land_ones by apply width_nonneg.
      apply bits.of_Z_mod.
    Qed.

    Lemma Z_land_ones_word_add (a b: word) :
      Z.land (Zmod.unsigned a + Zmod.unsigned b) (Z.ones width) =
        Zmod.unsigned (Zmod.add a b).
    Proof. rewrite Z.land_ones, Zmod.unsigned_add; reflexivity || apply width_nonneg. Qed.

    Lemma Z_land_ones_rotate (a: word) b (Hrange: 0 < b < width) :
      Z.land (Z.shiftl (Zmod.unsigned a) b + Z.shiftr (Zmod.unsigned a) (width - b)) (Z.ones width) =
        Zmod.unsigned (Zmod.add (Semantics.slu a (bits.of_Z width b)) (Semantics.sru a (Zmod.sub (bits.of_Z width width) (bits.of_Z width b)))).
    Proof.
      pose proof Zpow_facts.Zpower2_lt_lin width width_nonneg.
      rewrite <- Zmod.of_Z_sub, Z.land_ones, Zmod.unsigned_add by lia.
      rewrite Semantics.unsigned_slu_shamtZ, Semantics.unsigned_sru_shamtZ by lia.
      Z.push_pull_mod; reflexivity.
    Qed.

    Lemma of_Z_land_ones_rotate a b (Ha: 0 <= a < 2 ^ width) (Hb: 0 < b < width) :
      bits.of_Z width (Z.land (Z.shiftl a b + Z.shiftr a (width - b)) (Z.ones width)) =
        Zmod.add (Semantics.slu (bits.of_Z width a) (bits.of_Z width b))
                 (Semantics.sru (bits.of_Z width a) (Zmod.sub (bits.of_Z width width) (bits.of_Z width b))).
    Proof.
      pose proof Zpow_facts.Zpower2_lt_lin width width_nonneg.
      apply Zmod.unsigned_inj.
      rewrite <- Zmod.of_Z_sub, Zmod.unsigned_add, Semantics.unsigned_slu_shamtZ, Semantics.unsigned_sru_shamtZ by lia.
      rewrite !(bits.unsigned_of_Z_small _ Ha).
      rewrite Z.land_ones, bits.unsigned_of_Z by apply width_nonneg.
      Z.push_pull_mod; reflexivity.
    Qed.
  End __.
End word.

Notation word_of_byte b :=
  (bits.of_Z _ (Byte.byte.unsigned b)).
Notation byte_of_word w :=
  (byte.of_Z (Zmod.unsigned w)).

Module SeparationLogic. (* FIXME move to bedrock2? *)
  Import Lift1Prop.
  Section SeparationLogic. (* FIXME move to bedrock2? *)
    Context {key value : Type} {map : map.map key value}.

    Definition pure (P: Prop) := (fun m: map => P).

    (* FIXME replace by `and1` *)
    Definition unsep (p q: map -> Prop) : map -> Prop :=
      fun m => p m /\ q m.

    Fixpoint unseps (props: list (map -> Prop)) : map -> Prop :=
      match props with
      | [] => pure True
      | [prop] => prop
      | prop :: props => unsep prop (unseps props)
      end.

    Global Instance Proper_iff1_unsep :
      Proper (iff1 ==> iff1 ==> iff1) unsep.
    Proof. firstorder idtac. Qed.

    Global Instance Proper_impl1_unsep :
      Proper (impl1 ==> impl1 ==> impl1) unsep.
    Proof. firstorder idtac. Qed.

    Lemma unsep_assoc (p q r: map -> Prop) :
      iff1 (unsep (unsep p q) r) (unsep p (unsep q r)).
    Proof. firstorder idtac. Qed.

    Lemma unsep_pure_True_l P :
      iff1 (unsep (pure True) P) P.
    Proof. firstorder idtac. Qed.

    Lemma unsep_pure_True_r P :
      iff1 (unsep P (pure True)) P.
    Proof. firstorder idtac. Qed.

    Lemma unsep_pure_False_l P :
      iff1 (unsep (pure False) P) (pure False).
    Proof. firstorder idtac. Qed.

    Lemma unsep_pure_False_r P :
      iff1 (unsep P (pure False)) (pure False).
    Proof. firstorder idtac. Qed.

    Lemma sep_pure_False_l P :
      iff1 (sep (pure False) P) (pure False).
    Proof. firstorder idtac. Qed.

    Lemma sep_pure_False_r P :
      iff1 (sep P (pure False)) (pure False).
    Proof. firstorder idtac. Qed.

    Lemma impl1_pure_False_l P :
      impl1 (pure False) P.
    Proof. firstorder idtac. Qed.

    Lemma impl1_pure_True_r P :
      impl1 P (pure True).
    Proof. firstorder idtac. Qed.

    Lemma unsep_distr_sep_l: (* FIXME: this is sep_and_r_fwd *)
      forall p1 p2 p3 : map -> Prop,
        impl1 (sep p1 (unsep p2 p3)) (unsep (sep p1 p2) (sep p1 p3)).
    Proof. firstorder idtac. Qed.

    Lemma unsep_distr_sep_r: (* FIXME: this is sep_and_l_fwd *)
      forall p1 p2 p3 : map -> Prop,
        impl1 (sep (unsep p1 p2) p3) (unsep (sep p1 p3) (sep p2 p3)).
    Proof. firstorder idtac. Qed.

    Lemma unseps_distr_sep_l :
      forall p1 ps2,
        impl1 (sep p1 (unseps ps2))
              (unseps (List.map (sep p1) ps2)).
    Proof.
      induction ps2 as [| p2 [|] IHps2]; simpl in *; intros.
      - apply impl1_pure_True_r.
      - reflexivity.
      - rewrite <- IHps2, unsep_distr_sep_l; reflexivity.
    Qed.

    Lemma unseps_distr_sep_r :
      forall ps1 p2,
        impl1 (sep (unseps ps1) p2) (unseps (List.map (fun p1 => sep p1 p2) ps1)).
    Proof.
      induction ps1 as [| p1 [|] IHps1]; simpl in *; intros.
      - apply impl1_pure_True_r.
      - reflexivity.
      - rewrite <- IHps1, unsep_distr_sep_r; reflexivity.
    Qed.

    Lemma unseps_map_impl1_ext (f g: (map -> Prop) -> (map -> Prop))
          (H: forall p, impl1 (f p) (g p)) :
      forall ps, impl1 (unseps (List.map f ps)) (unseps (List.map g ps)).
    Proof.
      induction ps as [| p [|] IHps]; simpl in *; intros.
      - reflexivity.
      - eauto.
      - rewrite IHps, H; reflexivity.
    Qed.

    Lemma unseps_app :
      forall es1 es2,
        iff1 (unseps (es1 ++ es2))
             (unsep (unseps es1) (unseps es2)).
    Proof.
      induction es1 as [| e1 [|] IHes1]; simpl in *; intros.
      - rewrite unsep_pure_True_l; reflexivity.
      - destruct es2; simpl.
        + rewrite unsep_pure_True_r; reflexivity.
        + reflexivity.
      - rewrite IHes1, unsep_assoc.
        reflexivity.
    Qed.

    Lemma unseps_distr_sep:
      forall ps1 ps2,
        impl1 (sep (unseps ps1) (unseps ps2))
              (unseps (map2 sep (product ps1 ps2))).
    Proof.
      intros; rewrite map2_product; revert ps2.
      induction ps1 as [| p1 [|] IHps1]; simpl in *; intros.
      - apply impl1_pure_True_r.
      - rewrite app_nil_r.
        apply unseps_distr_sep_l.
      - rewrite unsep_distr_sep_r, unseps_app.
        rewrite <- IHps1.
        rewrite <- unseps_distr_sep_l.
        reflexivity.
    Qed.
  End SeparationLogic.
End SeparationLogic.

Export SeparationLogic.

Section Byte.
  Context {width: Z} {BW: Bitwidth width}.
  Local Notation word := (bits width).

  Lemma byte_morph_and b1 b2:
    word_of_byte (byte.and b1 b2) =
    Zmod.and (word_of_byte b1) (word_of_byte b2) :> word.
  Proof.
    apply Zmod.unsigned_inj.
    rewrite bits.unsigned_and, !bits.unsigned_of_Z, !wrap_byte_unsigned.
    rewrite byte_unsigned_land; reflexivity.
  Qed.

  Lemma byte_morph_xor b1 b2:
    word_of_byte (byte.xor b1 b2) =
    Zmod.xor (word_of_byte b1) (word_of_byte b2) :> word.
  Proof.
    apply Zmod.unsigned_inj.
    rewrite bits.unsigned_xor, !bits.unsigned_of_Z, !wrap_byte_unsigned.
    rewrite byte_unsigned_xor; reflexivity.
  Qed.
End Byte.

Require Import coqutil.Word.LittleEndianList.
Arguments le_combine: simpl nomatch.
Arguments le_split : simpl nomatch.
Arguments Z.mul: simpl nomatch.

Section combine_split.
End combine_split.

Section Array.
  Context {width : Z} {BW: Bitwidth width}.
  Local Notation word := (bits width).
  Context {value} {Mem : map.map word value} {Mem_ok : map.ok Mem}.
  Context {T} (element : word -> T -> Mem -> Prop) (size : word).

  Open Scope Z_scope.

  Definition no_aliasing {A} (repr: word -> A -> Mem -> Prop) :=
    (forall a b p delta m R,
        0 <= delta < Zmod.unsigned size ->
        ~ (repr p a * repr (Zmod.add p (bits.of_Z width delta)) b * R)%sep m).

  Lemma array_max_length': forall addr xs (R: Mem -> Prop) m,
      (array element size addr xs * R)%sep m ->
      no_aliasing element ->
      0 <= Zmod.unsigned size < 2 ^ width ->
      ~ Zmod.unsigned size * Z.of_nat (length xs) > 2 ^ width.
  Proof.
    unfold not; intros * H He **.
    pose (max_len := Z.to_nat (2 ^ width / Zmod.unsigned size)).
    assert (max_len <= Datatypes.length xs)%nat as B. {
      apply Nat2Z.inj_le; subst max_len; rewrite Z2Nat.id;
        [ apply Z.div_le_upper_bound | ]; ZnWords.
    }
    pose proof (List.firstn_skipn max_len xs) as E.
    pose proof @List.firstn_length_le _ xs max_len B as A.
    destruct (List.firstn max_len xs) as [|h1 t1] eqn:E1; [ ZnWordsL | ].
    destruct (List.skipn max_len xs) as [|h2 t2] eqn:E2; [ ZnWordsL | ].
    rewrite <- E in H.
    SeparationLogic.seprewrite_in @array_append H.
    SeparationLogic.seprewrite_in @array_cons H.
    SeparationLogic.seprewrite_in @array_cons H.
    (* FIXME: Find a way to shorten this proof *)
    rewrite A in H.
    set (Zmod.unsigned size * Z.of_nat max_len) as max_len_bytes in H.
    set (Zmod.add addr (bits.of_Z width max_len_bytes)) as base in H.
    replace (element addr) with
        (element (Zmod.add base (bits.of_Z width (Zmod.unsigned (Zmod.sub addr base))))) in H;
      cycle 1.
    - f_equal.
      apply Zmod.unsigned_inj.
      rewrite Zmod.unsigned_add, Zmod.of_Z_unsigned, Zmod.unsigned_sub.
      Z.push_pull_mod.
      erewrite <- (Z.mod_small (Zmod.unsigned addr)) at 2 by apply (bits.unsigned_range _ width_nonneg).
      f_equal; lia.
    - eapply He; [ | ecancel_assumption ].
      subst base max_len_bytes max_len; rewrite Z2Nat.id by ZnWords.
      rewrite Zmod.unsigned_sub, Zmod.unsigned_add, bits.unsigned_of_Z.
      Z.push_pull_mod.
      rewrite Z_mod_eq''.
      match goal with
      | [  |- _ <= ?t < _ ] => replace t with (2 ^ width mod Zmod.unsigned size mod 2 ^ width)
      end.
      + rewrite Z.mod_small; ZnWords.
      + etransitivity; [ | rewrite <- Z.mod_add with (b := 1) by ZnWords; reflexivity ].
        f_equal; rewrite Z.mul_1_l; lia.
      + lia.
  Qed.

  Lemma array_max_length: forall addr xs (R: Mem -> Prop) m,
      no_aliasing element ->
      0 < Zmod.unsigned size ->
      (array element size addr xs * R)%sep m ->
      Zmod.unsigned size * Z.of_nat (length xs) <= 2 ^ width.
  Proof.
    intros; pose proof (bits.unsigned_range size width_nonneg).
    eapply Znot_gt_le, array_max_length'; eauto.
  Qed.
End Array.

Section Aliasing.
  Context {width : Z} {BW: Bitwidth width}.
  Local Notation word := (bits width).
  Context {Mem : map.map word byte} {Mem_ok : map.ok Mem}.

  Open Scope Z_scope.

  Lemma bytes_per_word_range :
    0 < Memory.bytes_per_word width < 2 ^ width.
  Proof. (* FIXME: seriously?! *)
    unfold Memory.bytes_per_word; pose proof width_pos.
    split; [apply Z.div_str_pos; lia | ].
    apply Z.div_lt_upper_bound; try lia.
    apply Z.lt_add_lt_sub_r.
    replace (2 ^ width) with (2 ^ (Z.succ (width - 1))) by (f_equal; lia).
    rewrite Z.pow_succ_r by lia.
    replace (8 * (2 * 2 ^ (width - 1))) with (8 * 2 ^ (width - 1) + 8 * 2 ^ (width - 1)) by lia.
    assert (0 < 2 ^ (width - 1)) by (apply Z.pow_pos_nonneg; lia).
    transitivity (8 * 2 ^ (width - 1)); try lia.
    etransitivity; [ apply Zpow_facts.Zpower2_lt_lin; lia | ].
    replace (8 * 2 ^ (width - 1)) with (2 ^ (Z.succ (Z.succ (Z.succ (width - 1))))).
    apply Z.pow_lt_mono_r; lia.
    rewrite !Z.pow_succ_r by lia.
    lia.
  Qed.

  Lemma scalar8_no_aliasing :
    no_aliasing (Mem := Mem) Zmod.one ptsto.
  Proof.
    red; intros * h Hmem.
    rewrite bits.unsigned_1 in h by (pose proof width_pos; lia).
    replace delta with 0 in * by lia.
    rewrite Zmod.add_0_r in *.
    eapply ptsto_nonaliasing; eassumption.
  Qed.
End Aliasing.

Section Semantics.
  Context {width: Z} {BW: Bitwidth width}.
  Local Notation word := (bits width).
  Context {mem: map.map word byte}.
  Context {locals: map.map String.string word}.
  Context {ext_spec: bedrock2.Semantics.ExtSpec}.
  Context {mem_ok : map.ok mem}.
  Context {locals_ok : map.ok locals}.
  Context {ext_spec_ok : Semantics.ext_spec.ok ext_spec}.

  Definition trace_entry :=
    Eval cbv beta in ((fun {A} (_: list A) => A) _ ([]: Semantics.trace)).

  Definition predicate := Semantics.trace -> mem -> locals -> Prop.
  Definition wp_bind_retvars retvars (P: list word -> predicate) :=
    fun tr mem locals =>
      exists ws, map.getmany_of_list locals retvars = Some ws /\
            P ws tr mem locals.

  Definition pure_predicate := mem -> locals -> Prop.
  Definition wp_pure_bind_retvars retvars (P: list word -> pure_predicate) :=
    fun mem locals =>
      exists ws, map.getmany_of_list locals retvars = Some ws /\
            P ws mem locals.

  Lemma WeakestPrecondition_weaken :
    forall cmd {functions} (p1 p2: _ -> _ -> _ -> Prop),
      (forall tr mem locals, p1 tr mem locals -> p2 tr mem locals) ->
      forall tr mem locals,
        WeakestPrecondition.program
          functions cmd tr mem locals p1 ->
        WeakestPrecondition.program
          functions cmd tr mem locals p2.
  Proof. intros; eapply Proper_program; eassumption. Qed.

  Lemma WeakestPrecondition_dexpr_expr :
    forall mem locals (e: expr) w (k: word -> Prop),
      k w ->
      WeakestPrecondition.dexpr mem locals e w ->
      WeakestPrecondition.expr mem locals e k.
  Proof.
    intros; eapply Proper_expr; [ | eassumption ].
    intros ? ->; assumption.
  Qed.

  Lemma getmany_list_map (l : locals) :
    forall a vs (P :_ -> Prop),
      P vs ->
      map.getmany_of_list l a = Some vs ->
      WeakestPrecondition.list_map (WeakestPrecondition.get l) a P.
  Proof.
    unfold map.getmany_of_list;
      induction a; cbn in *; intros.
    all: repeat (destruct_one_match_hyp; [|discriminate]).
    all: match goal with H: Some _ = Some _ |- _ => inversion H; subst end.
    all: try red; eauto.
  Qed.

  (* FIXME generalize *)
  Definition postcondition_func
             (spec : list word -> mem -> Prop)
             R tr :=
    (fun (tr' : Semantics.trace) (mem' : mem) (rets : list word) =>
       tr = tr'
       /\ sep (spec rets) R mem').

  Definition postcondition_func_norets spec R tr :=
    postcondition_func (fun r => sep (emp (r = nil)) (spec r)) R tr.

  (* TODO: Remove locals_post *)
  Definition postcondition_cmd
             locals_post spec retvars R tr :=
    (fun (tr' : Semantics.trace) (mem' : mem)
       (locals : locals) =>
       tr = tr'
       /\ locals_post locals
       /\ exists rets,
           map.getmany_of_list locals retvars = Some rets
           /\ sep (spec rets) R mem').

  Lemma predicate_trivial : forall
        {tr: Semantics.trace}
        {mem: mem}
        {locals: locals} {T} t0,
    (fun (_: T) tr' mem' locals' =>
       tr' = tr /\ mem' = mem /\ locals' = locals)
      t0 tr mem locals.
  Proof. intuition auto with core. Qed.

  Lemma to_byte_of_byte_nowrap b:
    byte_of_word (word_of_byte b : word) = b.
  Proof.
    rewrite bits.unsigned_of_Z, Z.mod_small.
    - apply word.byte_of_Z_unsigned.
    - pose proof byte.unsigned_range b.
      destruct width_cases as [-> | ->]; lia.
  Qed.
End Semantics.

Section Misc.
  Lemma eq_impl : forall a b, a = b -> a -> b.
  Proof. intros * -> ?; eassumption. Qed.
End Misc.

Section Nat2Z.
  Lemma Nat2Z_inj_pow a b:
    Z.of_nat (a ^ b) = (Z.of_nat a ^ Z.of_nat b)%Z.
  Proof.
    induction b.
    - reflexivity.
    - cbn -[Z.of_nat Z.pow].
      rewrite Nat2Z.inj_succ, Z.pow_succ_r; lia.
  Qed.

  Lemma Z_div_eucl_unique a b q q' r r':
    0 <= r < b \/ b < r <= 0 ->
    0 <= r' < b \/ b < r' <= 0 ->
    a = b * q + r ->
    a = b * q' + r' ->
    (q = q' /\ r = r').
  Proof.
    intros Hr Hr' Hq Hq';
      erewrite (Z.div_unique a b q r Hr Hq);
      erewrite (Z.div_unique a b q' r' Hr' Hq');
      erewrite (Z.mod_unique a b q r Hr Hq);
      erewrite (Z.mod_unique a b q' r' Hr' Hq');
      split; reflexivity.
  Qed.

  Lemma Nat2Z_inj_odd : forall n,
    Z.odd (Z.of_nat n) = Nat.odd n.
  Proof.
    apply Nat.pair_induction.
    - intros ?? ->; reflexivity.
    - reflexivity.
    - reflexivity.
    - intros; rewrite !Nat2Z.inj_succ, Z.odd_succ_succ. eassumption.
  Qed.

  Lemma Natmod_odd: forall a : nat,
      (a mod 2 = if Nat.odd a then 1 else 0)%nat.
  Proof.
    apply Nat.pair_induction.
    - intros ?? ->; reflexivity.
    - reflexivity.
    - reflexivity.
    - intros.
      replace (S (S n)) with (n + 1 * 2)%nat at 1 by lia.
      rewrite Nat.mod_add by lia.
      eassumption.
  Qed.

  Lemma Natodd_mod : forall a : nat,
      (Nat.odd a = negb (a mod 2 =? 0))%nat.
  Proof.
    intros; rewrite Natmod_odd.
    destruct Nat.odd; reflexivity.
  Qed.
End Nat2Z.

#[deprecated(note = "Use Nat2Z.inj_div instead.")]
Notation Nat2Z_inj_div := Nat2Z.inj_div.
#[deprecated(note = "Use Nat2Z.inj_mod instead.")]
Notation Nat2Z_inj_mod := Nat2Z.inj_mod.

Section Rupicola.
  Definition __rupicola_program_marker {A} (a: A) := True.

  Definition nlet_eq {A} {P: forall a: A, Type}
             (vars: list string) (a0: A)
             (body : forall (a : A) (Heq: a = a0), P a) : P a0 :=
    let x := a0 in body x eq_refl.

  Definition nlet {A T}
             (vars: list string) (a0: A)
             (body : A -> T) : T :=
    let x := a0 in body x.

  Lemma nlet_as_nlet_eq {A T}
        (vars: list string) (val: A)
        (body : A -> T) :
    nlet vars val body =
    nlet_eq (P := fun _ => T) vars val (fun v _ => body v).
  Proof. reflexivity. Qed.

  Inductive RupicolaBindingInfo :=
  | RupicolaBinding (rb_type: Type) (rb_names: list string)
  | NotARupicolaBinding.

  Class IsRupicolaBinding {T} (t: T) := is_rupicola_binding: RupicolaBindingInfo.

  Class HasDefault (T: Type) := default: T.
  Global Instance HasDefault_nat : HasDefault nat := 0%nat.
  Global Instance HasDefault_Z : HasDefault Z := 0%Z.
  Global Instance HasDefault_byte : HasDefault byte := Byte.x00.
  Global Instance HasDefault_Fin {n} : HasDefault (Fin.t (S n)) :=
    Fin.F1.
  Global Instance HasDefault_word {width} : HasDefault (bits width) :=
    Zmod.zero.

  Class Convertible (T1 T2: Type) := cast: T1 -> T2.
  Global Instance Convertible_self {A}: Convertible A A := id.
  Global Instance Convertible_Z_nat : Convertible Z nat := Z.to_nat.
  Global Instance Convertible_byte_nat : Convertible byte nat :=
    fun b => Z.to_nat (byte.unsigned b).
  Global Instance Convertible_Fin_nat {n} : Convertible (Fin.t n) nat :=
    fun f => proj1_sig (Fin.to_nat f).
  Global Instance Convertible_word_nat {width : Z} : Convertible (bits width) nat :=
    fun w => Z.to_nat (Zmod.unsigned w).
End Rupicola.

(* TODO: should be upstreamed to coqutil *)
Module Z.
  Lemma lxor_xorb a b : Z.lxor (Z.b2z a) (Z.b2z b) = Z.b2z (xorb a b).
  Proof. destruct a, b; reflexivity. Qed.
End Z.
