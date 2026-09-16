From Rupicola Require Import Lib.Core Lib.Notations Lib.Tactics.

#[local] Notation of_Z z := (Zmod.of_Z _ z).
#[local] Notation of_N n := (Zmod.of_Z _ (Z.of_N n)).
#[local] Notation of_nat n := (Zmod.of_Z _ (Z.of_nat n)).
#[local] Notation of_byte n := (Zmod.of_Z _ (byte.unsigned n)).
#[local] Notation of_bool b := (word.b2w b).

Lemma Z_decide_word_bounds a b c:
  (Z.leb a b && Z.ltb b c)%bool = true ->
  a <= b < c.
Proof. lia. Qed.

Section ExprCompiler.
  Context {width: Z} {BW: Bitwidth width}.
  Local Notation word := (bits width).
  Context {mem: map.map word Byte.byte} {mem_ok : map.ok mem}.
  Context {locals: map.map String.string word} {locals_ok : map.ok locals}.

  Section WordLemmas.
    Lemma word_not_xor (w: word):
      Zmod.not w = Zmod.xor w (bits.of_Z width (-1)).
    Proof.
      rewrite <- (Zmod.of_Z_unsigned w).
      rewrite <- bits.of_Z_lnot, <- word.morph_xor.
      rewrite Z.lxor_m1_r; reflexivity.
    Qed.

    Lemma word_sru_div_2 z:
      0 <= z < 2 ^ width ->
      bits.of_Z width (z / 2) = Semantics.sru (bits.of_Z width z) (bits.of_Z width 1).
    Proof.
      pose proof width_at_least_32.
      intros; rewrite <- (Z.shiftr_div_pow2 _ 1), word.morph_shiftr; reflexivity || lia.
    Qed.

    Lemma word_and_odd z:
      word.b2w (Z.odd z) = Zmod.and (bits.of_Z width z) (bits.of_Z width 1).
    Proof.
      rewrite <- word.morph_and.
      rewrite (Z.land_ones _ 1), Zmod_odd by lia.
      destruct Z.odd; reflexivity.
    Qed.

    Lemma word_morph_eqb z1 z2:
      (0 <= z1 < 2 ^ width /\
       0 <= z2 < 2 ^ width) \/
      (- 2 ^ (width-1) <= z1 < 2 ^ (width-1) /\
       - 2 ^ (width-1) <= z2 < 2 ^ (width-1)) ->
      Zmod.eqb (bits.of_Z width z1) (bits.of_Z width z2) = (z1 =? z2).
    Proof.
      pose proof (word.pow2_width_minus1 width_pos).
      intros [(h1, h2) | (h1, h2)].
      - unfold Zmod.eqb; rewrite !bits.unsigned_of_Z_small by lia; reflexivity.
      - rewrite word.signed_eqb, !bits.signed_of_Z, !(Z.smod_pow2_small _ _ width_pos) by lia;
          reflexivity.
    Qed.

    Lemma word_unsigned_range_32 z :
      0 <= z < 2 ^ 32 ->
      0 <= z < 2 ^ width.
    Proof.
      pose proof width_at_least_32.
      pose proof Z.pow_le_mono_r 2 32 width.
      lia.
    Qed.

    Lemma word_signed_range_31 z :
      -2 ^ 31 <= z < 2 ^ 31 ->
      -2 ^ (width - 1) <= z < 2 ^ (width - 1).
    Proof.
      pose proof width_at_least_32.
      pose proof Z.pow_le_mono_r 2 31 (width - 1).
      lia.
    Qed.

  End WordLemmas.

  Context {m: mem} {l: locals}.

  Notation DEXPR :=
    (WeakestPrecondition.dexpr (mem := mem) (locals := locals) m).

  Notation DX := (DEXPR l).

  Notation mb z := (0 <= z < width).
  Notation ub z := (0 <= z < 2 ^ width).
  Notation Ub z := (0 < z < 2 ^ width).
  Notation sb z := (- 2 ^ (width - 1) <= z < 2 ^ (width - 1)).

  Ltac cleanup :=
    repeat straightline;
    repeat simple eapply WeakestPrecondition_dexpr_expr; eauto.

  Section Literals.
    Lemma expr_compile_Z_literal z : DX (expr.literal z) (of_Z z).
    Proof. cleanup. Qed.
    Lemma expr_compile_word_literal w : DX (expr.literal (Zmod.unsigned w)) w.
    Proof. cleanup; symmetry; apply Zmod.of_Z_unsigned. Qed.
    Lemma expr_compile_zero : DX (expr.literal 0) Zmod.zero.
    Proof. cleanup; apply Zmod.of_Z_0. Qed.
    Lemma expr_compile_one : DX (expr.literal 1) Zmod.one.
    Proof. cleanup; apply Zmod.of_Z_1. Qed.
  End Literals.

  Section Variables.
    Lemma expr_compile_var s w (h: map.get l s = Some w) : DX (expr.var s) w.
    Proof. cleanup. Qed.

    Lemma expr_compile_var_assoc {bs} s w (h: map.list_assoc_str s bs = Some w) :
      DEXPR (map.of_list bs) (expr.var s) w.
    Proof. cleanup. eauto using map.get_of_str_list_assoc_impl. Qed.
  End Variables.

  Section w_expr.
    Context (w1 w2: word) (e1 e2: expr).

    Hypothesis (H1: DX e1 w1).
    Hypothesis (H2: DX e2 w2).

    Local Lemma expr_compile_word_bop {bop}:
      DX (expr.op bop e1 e2) (Semantics.interp_binop bop w1 w2).
    Proof. cleanup. Qed.

    Notation DOP op w := (DX (expr.op op e1 e2) w).

    Definition expr_compile_word_add : DOP bopname.add (Zmod.add w1 w2) := expr_compile_word_bop.
    Definition expr_compile_word_sub : DOP bopname.sub (Zmod.sub w1 w2) := expr_compile_word_bop.
    Definition expr_compile_word_mul : DOP bopname.mul (Zmod.mul w1 w2) := expr_compile_word_bop.
    Definition expr_compile_word_mulhuu :
      DOP bopname.mulhuu (bits.of_Z width (Zmod.unsigned w1 * Zmod.unsigned w2 / 2 ^ width)) :=
      expr_compile_word_bop.
    Definition expr_compile_word_divu : DOP bopname.divu (Zmod.udiv w1 w2) := expr_compile_word_bop.
    Definition expr_compile_word_modu : DOP bopname.remu (Zmod.umod w1 w2) := expr_compile_word_bop.
    Definition expr_compile_word_and : DOP bopname.and (Zmod.and w1 w2) := expr_compile_word_bop.
    Definition expr_compile_word_or : DOP bopname.or (Zmod.or w1 w2) := expr_compile_word_bop.
    Definition expr_compile_word_xor : DOP bopname.xor (Zmod.xor w1 w2) := expr_compile_word_bop.

    Definition expr_compile_word_sru : DOP bopname.sru (Semantics.sru w1 w2) := expr_compile_word_bop.
    Definition expr_compile_word_slu : DOP bopname.slu (Semantics.slu w1 w2) := expr_compile_word_bop.
    Definition expr_compile_word_srs : DOP bopname.srs (Semantics.srs w1 w2) := expr_compile_word_bop.

    Definition expr_compile_word_lts : DOP bopname.lts (of_bool (Semantics.lts w1 w2)).
    Proof. rewrite word.b2w_if; eapply (@expr_compile_word_bop bopname.lts). Qed.
    Definition expr_compile_word_ltu : DOP bopname.ltu (of_bool (Semantics.ltu w1 w2)).
    Proof. rewrite word.b2w_if; eapply (@expr_compile_word_bop bopname.ltu). Qed.

    Definition expr_compile_word_eqb : DOP bopname.eq (of_bool (Zmod.eqb w1 w2)).
    Proof. rewrite word.b2w_if; eapply (@expr_compile_word_bop bopname.eq). Qed.

    Lemma expr_compile_word_not:
      DX (expr.op bopname.xor e1 (expr.literal (-1))) (Zmod.not w1).
    Proof. cleanup. apply word_not_xor. cleanup. Qed.
  End w_expr.

  (* TODO add other operators: les, leu, gts, gtu *)

  Section Z_expr.
    Context (z1 z2: Z) (e1 e2: expr).

    Notation to_w z := (bits.of_Z width z).

    Hypothesis (H1: DX e1 (to_w z1)).
    Hypothesis (H2: DX e2 (to_w z2)).

    Notation DOP op w := (DX (expr.op op e1 e2) w).

    Lemma expr_compile_Z_add : DOP bopname.add (to_w (Z.add z1 z2)).
    Proof. rewrite Zmod.of_Z_add; eauto using expr_compile_word_add. Qed.
    Lemma expr_compile_Z_sub : DOP bopname.sub (to_w (Z.sub z1 z2)).
    Proof. rewrite Zmod.of_Z_sub; eauto using expr_compile_word_sub. Qed.
    Lemma expr_compile_Z_mul : DOP bopname.mul (to_w (Z.mul z1 z2)).
    Proof. rewrite Zmod.of_Z_mul; eauto using expr_compile_word_mul. Qed.
    Lemma expr_compile_Z_div (h1: ub z1) (h2: Ub z2) : DOP bopname.divu (to_w (Z.div z1 z2)).
    Proof. rewrite (bits.of_Z_div _ _ h1 h2); eauto using expr_compile_word_divu. Qed.

    Lemma expr_compile_Z_land : DOP bopname.and (to_w (Z.land z1 z2)).
    Proof. rewrite word.morph_and; eauto using expr_compile_word_and. Qed.
    Lemma expr_compile_Z_lor : DOP bopname.or (to_w (Z.lor z1 z2)).
    Proof. rewrite word.morph_or; eauto using expr_compile_word_or. Qed.
    Lemma expr_compile_Z_lxor : DOP bopname.xor (to_w (Z.lxor z1 z2)).
    Proof. rewrite word.morph_xor; eauto using expr_compile_word_xor. Qed.
    Lemma expr_compile_Z_shiftl (h2: mb z2) :
      DOP bopname.slu (to_w (Z.shiftl z1 z2)).
    Proof. rewrite word.morph_shiftl by lia; eauto using expr_compile_word_slu. Qed.
    Lemma expr_compile_Z_shiftr (h1: ub z1) (h2: mb z2) :
      DOP bopname.sru (to_w (Z.shiftr z1 z2)).
    Proof. rewrite word.morph_shiftr by lia; eauto using expr_compile_word_sru. Qed.

    Lemma expr_compile_Z_eqb (h: (ub z1 /\ ub z2) \/ (sb z1 /\ sb z2)) :
      DOP bopname.eq (of_bool (Z.eqb z1 z2)).
    Proof. rewrite <- word_morph_eqb; eauto using expr_compile_word_eqb. Qed.

    Lemma expr_compile_Z_ltb_u (h1: ub z1) (h2: ub z2) :
      DOP bopname.ltu (of_bool (Z.ltb z1 z2)).
    Proof. rewrite (word.morph_ltu (width := width)); eauto using expr_compile_word_ltu. Qed.
    Lemma expr_compile_Z_ltb_s (h1: sb z1) (h2: sb z2) :
      DOP bopname.lts (of_bool (Z.ltb z1 z2)).
    Proof. rewrite (word.morph_lts (width := width)); eauto using expr_compile_word_lts. Qed.

    Lemma expr_compile_Z_gtb_u (h1: ub z1) (h2: ub z2) :
      DOP bopname.ltu (of_bool (Z.gtb z2 z1)).
    Proof. rewrite Z.gtb_ltb; auto using expr_compile_Z_ltb_u. Qed.
    Lemma expr_compile_Z_gtb_s (h1: sb z1) (h2: sb z2) :
      DOP bopname.lts (of_bool (Z.gtb z2 z1)).
    Proof. rewrite Z.gtb_ltb; auto using expr_compile_Z_ltb_s. Qed.

    Lemma expr_compile_Z_lnot :
      DX (expr.op bopname.xor e1 (expr.literal (-1))) (to_w (Z.lnot z1)).
    Proof. rewrite bits.of_Z_lnot; eauto using expr_compile_word_not. Qed.

    Lemma expr_compile_Z_div_2 (h1: ub z1) :
      DX (expr.op bopname.sru e1 (expr.literal 1)) (to_w (z1 / 2)).
    Proof. rewrite word_sru_div_2; eauto using expr_compile_word_sru, expr_compile_Z_literal. Qed.

    Lemma expr_compile_Z_odd :
      DX (expr.op bopname.and e1 (expr.literal 1)) (of_bool (Z.odd z1)).
    Proof. rewrite word_and_odd; eauto using expr_compile_word_and, expr_compile_Z_literal. Qed.

    Lemma expr_compile_Z_b2z b1:
      DX e1 (of_bool b1) -> DX e1 (to_w (Z.b2z b1)).
    Proof. intros; assumption. Qed.

    Lemma expr_compile_Z_wrap :
      DX e1 (to_w z1) -> DX e1 (to_w (z1 mod 2 ^ width)).
    Proof. rewrite bits.of_Z_mod; auto. Qed.
    Lemma expr_compile_Z_swrap :
      DX e1 (to_w z1) -> DX e1 (to_w (Z.smodulo z1 (2 ^ width))).
    Proof. rewrite <- word.of_Z_smodulo; auto. Qed.

    Lemma expr_compile_byte_wrap:
      DX e1 (to_w (Z.land z1 0xFF)) -> DX e1 (to_w (byte.wrap z1)).
    Proof. rewrite (Z.land_ones _ 8) by lia; auto. Qed.
  End Z_expr.

  Section N_expr.
    Context (n1 n2: N) (e1 e2: expr).

    Notation to_w z := (bits.of_Z width (Z.of_N z)).

    Hypothesis (H1: DX e1 (to_w n1)).
    Hypothesis (H2: DX e2 (to_w n2)).

    Notation DOP op w := (DX (expr.op op e1 e2) w).

    Lemma expr_compile_N_add : DOP bopname.add (to_w (N.add n1 n2)).
    Proof. rewrite N2Z.inj_add; eauto using expr_compile_Z_add. Qed.
    Lemma expr_compile_N_sub (h: N.le n2 n1) : DOP bopname.sub (to_w (N.sub n1 n2)).
    Proof. rewrite N2Z.inj_sub; eauto using expr_compile_Z_sub. Qed.
    Lemma expr_compile_N_mul : DOP bopname.mul (to_w (N.mul n1 n2)).
    Proof. rewrite N2Z.inj_mul; eauto using expr_compile_Z_mul. Qed.
  End N_expr.

  Section nat_expr.
    Context (n1 n2: nat) (e1 e2: expr).

    Notation to_w n := (bits.of_Z width (Z.of_nat n)).

    Hypothesis (H1: DX e1 (to_w n1)).
    Hypothesis (H2: DX e2 (to_w n2)).

    Notation DOP op w := (DX (expr.op op e1 e2) w).

    Lemma expr_compile_nat_add : DOP bopname.add (to_w (Nat.add n1 n2)).
    Proof. intros; rewrite Nat2Z.inj_add; eauto using expr_compile_Z_add. Qed.
    Lemma expr_compile_nat_sub :
      (n2 <= n1)%nat -> DOP bopname.sub (to_w (Nat.sub n1 n2)).
    Proof. intros; rewrite Nat2Z.inj_sub; eauto using expr_compile_Z_sub. Qed.
    Lemma expr_compile_nat_mul : DOP bopname.mul (to_w (Nat.mul n1 n2)).
    Proof. intros; rewrite Nat2Z.inj_mul; eauto using expr_compile_Z_mul. Qed.
  End nat_expr.

  Section byte_expr.
    Context (b1 b2: byte) (e1 e2: expr).
    Notation to_w b := (bits.of_Z width (byte.unsigned b)).

    Hypothesis (H1: DX e1 (to_w b1)).
    Hypothesis (H2: DX e2 (to_w b2)).

    Notation DOP op w := (DX (expr.op op e1 e2) w).

    Lemma expr_compile_byte_and : DOP bopname.and (to_w (byte.and b1 b2)).
    Proof. cleanup; apply byte_morph_and. Qed.
    Lemma expr_compile_byte_xor : DOP bopname.xor (to_w (byte.xor b1 b2)).
    Proof. cleanup; apply byte_morph_xor. Qed.
  End byte_expr.

  Section bool_expr.
    Context (b1 b2: bool) (e1 e2: expr).
    Notation to_w b := (of_bool b).

    Hypothesis (H1: DX e1 (to_w b1)).
    Hypothesis (H2: DX e2 (to_w b2)).

    Notation DOP op w := (DX (expr.op op e1 e2) w).

    Ltac cleanup_bool lemma :=
      cleanup; unfold word.b2w; try reflexivity;
      cbv beta iota delta [Semantics.interp_binop andb orb xorb negb Z.b2z];
      repeat match goal with |- context[if ?b then _ else _] => is_var b; destruct b end;
      cbv beta iota; rewrite <- ?lemma; reflexivity.

    Lemma expr_compile_bool_andb : DOP bopname.and (to_w (andb b1 b2)).
    Proof. cleanup_bool word.morph_and. Qed.
    Lemma expr_compile_bool_orb : DOP bopname.or (to_w (orb b1 b2)).
    Proof. cleanup_bool word.morph_or. Qed.
    Lemma expr_compile_bool_xorb : DOP bopname.xor (to_w (xorb b1 b2)).
    Proof. cleanup_bool word.morph_xor. Qed.

    Lemma expr_compile_bool_negb:
      DX (expr.op bopname.xor e1 (expr.literal 1)) (to_w (negb b1)).
    Proof. cleanup_bool word.morph_xor. Qed.
  End bool_expr.

  Section Assignments.
    Context {ext_spec: bedrock2.Semantics.ExtSpec}.
    Context {ext_spec_ok : Semantics.ext_spec.ok ext_spec}.

    Lemma compile_expr {A} (to_W: A -> word):
      forall [tr mem locals functions] (a: A) (e: expr),
      let v := a in
      forall {P} {pred: P v -> predicate}
        {k: nlet_eq_k P v} {k_impl}
        var,

        WeakestPrecondition.dexpr mem locals e (to_W v) ->

        (let v := v in
         <{ Trace := tr;
            Memory := mem;
            Locals := map.put locals var (to_W v);
            Functions := functions }>
         k_impl
         <{ pred (k v eq_refl) }>) ->

        <{ Trace := tr;
           Memory := mem;
           Locals := locals;
           Functions := functions }>
        cmd.seq (cmd.set var e) k_impl
        <{ pred (nlet_eq [var] v k) }>.
    Proof. repeat straightline; eauto. Qed.

    Definition compile_expr_w := compile_expr (fun w => w).
    Definition compile_expr_Z := compile_expr (fun z => of_Z z).
    Definition compile_expr_N := compile_expr (fun n => of_N n).
    Definition compile_expr_nat := compile_expr (fun n => of_nat n).
    Definition compile_expr_byte := compile_expr (fun b => of_byte b).
    Definition compile_expr_bool := compile_expr (fun b => of_bool b).
  End Assignments.
End ExprCompiler.

Notation DEXPR := WeakestPrecondition.dexpr.

Ltac find_key_by_value bs v0 :=
  lazymatch bs with
  | [] => constr:(@None string)
  | (?k, ?v) :: ?bs =>
      lazymatch v with
      | v0 => constr:(Some k)
      | _ => find_key_by_value bs v0
      end
  end.

Ltac reify_change_dexpr_locals :=
  lazymatch goal with
  | [  |- DEXPR _ ?locals _ _ ] =>
      lazymatch locals with
      | map.of_list _ => fail 0 "Already reified"
      | _ =>
          let bindings := map_to_list locals in
          set_change locals with (map.of_list bindings)
      end
  | [  |- ?g ] => fail 0 g "is not a dexpr goal"
  end.

Ltac expr_compile_var :=
  lazymatch goal with
  | [ |- DEXPR _ (map.of_list ?bs) _ ?w ] =>
      lazymatch find_key_by_value bs w with
      | Some ?k =>
          simple eapply (expr_compile_var_assoc k w); reflexivity
      | None => fail "Not a variable"
      end
  | [ |- DEXPR _ _ _ ?w ] =>
      fail 0 "cannot call expr_compile_var without reify_change_dexpr_locals"
  | [  |- ?g ] => fail 0 g "is not a dexpr goal"
  end.

Ltac compile_let_as_expr :=
  lazymatch goal with
  | [ |- WP_nlet_eq ?v ] =>
    lazymatch type of v with
    | Zmod _         => simple apply compile_expr_w
    | Z              => simple apply compile_expr_Z
    | N              => simple apply compile_expr_N
    | nat              => simple apply compile_expr_nat
    | Init.Byte.byte => simple apply compile_expr_byte
    | bool              => simple apply compile_expr_bool
    | ?t             => fail "[compile_let_as_expr]: Unrecognized type" t
    end; cbv beta in *
  | [  |- ?g ] => fail 0 g "is not a Rupicola goal"
  end.

Ltac compile_expr_step :=
  progress unshelve (typeclasses eauto 10 with expr_compiler); shelve_unifiable.

Ltac compile_expr :=
  (* LATER: Consider clearing local hypotheses here, since large contexts make
     `apply` slow (but careful not to remove [map.ok]). *)
  repeat compile_expr_step.

Ltac compile_assignment :=
  compile_let_as_expr; compile_expr.

Create HintDb expr_compiler.

(* For let-bound exprs: *)
#[export] Hint Extern 8 =>
  compile_assignment; shelve : compiler.
(* Higher priority than compilation lemmas for individual operations *)

(* For dexpr side conditions: *)
#[export] Hint Extern 8 (DEXPR _ _ _ _) =>
  compile_expr; shelve : compiler_side_conditions.

(* For variables *)
#[export] Hint Extern 7 =>
  expr_compile_var : expr_compiler.

(* Initial setup *)
#[export] Hint Extern 3 =>
  reify_change_dexpr_locals; shelve : expr_compiler.

(* Some hints to handle the side conditions that some of the Z lemmas return.
   In most cases its not crucial that these side conditions be solved by
   `compile_expr` in one shot, because there's only one reasonable thing to do
   (this is the case with shiftr, for example: if the arguments are not in
   bounds, what can we do?).  But in some cases it is important that the range
   side conditions be solved right away, because otherwise we want to backtrack;
   this is the case with `Z.ltb`, which is either a signed or an unsigned
   comparison depending on the range of the operands. *)
#[export] Hint Constructors and or eq : expr_compiler.
#[export] Hint Resolve byte.wrap_range Z.mod_pos_bound modulus_pos word.smodulo_range: expr_compiler.
#[export] Hint Resolve byte_range_32 byte_range_64 word_unsigned_range_32 word_signed_range_31: expr_compiler.
#[export] Hint Resolve bits.unsigned_range bits.signed_range' width_nonneg width_ge_1: expr_compiler.
#[export] Hint Extern 5 (_ <= _ < _) => apply Z_decide_word_bounds; reflexivity : expr_compiler.

(* Adding explicit patterns speeds up expr compilation by a factor ~10.
   We need Hint Extern because we want to shelve to make partial progress. *)
Notation DPAT p := (DEXPR _ _ _ p) (only parsing).

#[export] Hint Extern 5 (DPAT (Zmod.add _ _)) =>
  simple eapply expr_compile_word_add; shelve : expr_compiler.
#[export] Hint Extern 5 (DPAT (Zmod.sub _ _)) =>
  simple eapply expr_compile_word_sub; shelve : expr_compiler.
#[export] Hint Extern 5 (DPAT (Zmod.mul _ _)) =>
  simple eapply expr_compile_word_mul; shelve : expr_compiler.
#[export] Hint Extern 5 (DPAT (Zmod.of_Z _ (Zmod.unsigned _ * Zmod.unsigned _ / 2 ^ _))) =>
  simple eapply expr_compile_word_mulhuu; shelve : expr_compiler.
#[export] Hint Extern 5 (DPAT (Zmod.udiv _ _)) =>
  simple eapply expr_compile_word_divu; shelve : expr_compiler.
#[export] Hint Extern 5 (DPAT (Zmod.umod _ _)) =>
  simple eapply expr_compile_word_modu; shelve : expr_compiler.
#[export] Hint Extern 5 (DPAT (Zmod.and _ _)) =>
  simple eapply expr_compile_word_and; shelve : expr_compiler.
#[export] Hint Extern 5 (DPAT (Zmod.or _ _)) =>
  simple eapply expr_compile_word_or; shelve : expr_compiler.
#[export] Hint Extern 5 (DPAT (Zmod.xor _ _)) =>
  simple eapply expr_compile_word_xor; shelve : expr_compiler.
#[export] Hint Extern 5 (DPAT (Semantics.sru _ _)) =>
  simple eapply expr_compile_word_sru; shelve : expr_compiler.
#[export] Hint Extern 5 (DPAT (Semantics.slu _ _)) =>
  simple eapply expr_compile_word_slu; shelve : expr_compiler.
#[export] Hint Extern 5 (DPAT (Semantics.srs _ _)) =>
  simple eapply expr_compile_word_srs; shelve : expr_compiler.

#[export] Hint Extern 5 (DPAT (of_bool (Semantics.lts _ _))) =>
  simple eapply expr_compile_word_lts; shelve : expr_compiler.
#[export] Hint Extern 5 (DPAT (of_bool (Semantics.ltu _ _))) =>
  simple eapply expr_compile_word_ltu; shelve : expr_compiler.
#[export] Hint Extern 5 (DPAT (of_bool (Zmod.eqb _ _))) =>
  simple eapply expr_compile_word_eqb; shelve : expr_compiler.

#[export] Hint Extern 5 (DPAT (Zmod.not _)) =>
  simple eapply expr_compile_word_not; shelve : expr_compiler.
#[export] Hint Extern 5 (DPAT (of_Z (Z.lnot _))) =>
  simple eapply expr_compile_Z_lnot; shelve : expr_compiler.
#[export] Hint Extern 5 (DPAT (of_Z (_ / 2))) =>
  simple eapply expr_compile_Z_div_2; shelve : expr_compiler.
#[export] Hint Extern 5 (DPAT (of_bool (Z.odd _))) =>
  simple eapply expr_compile_Z_odd; shelve : expr_compiler.
#[export] Hint Extern 5 (DPAT (of_bool (negb _))) =>
  simple eapply expr_compile_bool_negb; shelve : expr_compiler.

#[export] Hint Extern 5 (DPAT (of_Z (Z.add _ _))) =>
  simple eapply expr_compile_Z_add; shelve : expr_compiler.
#[export] Hint Extern 5 (DPAT (of_Z (Z.sub _ _))) =>
  simple eapply expr_compile_Z_sub; shelve : expr_compiler.
#[export] Hint Extern 5 (DPAT (of_Z (Z.mul _ _))) =>
  simple eapply expr_compile_Z_mul; shelve : expr_compiler.
#[export] Hint Extern 6 (DPAT (of_Z (Z.div _ _))) =>
  simple eapply expr_compile_Z_div; shelve : expr_compiler.
#[export] Hint Extern 5 (DPAT (of_Z (Z.land _ _))) =>
  simple eapply expr_compile_Z_land; shelve : expr_compiler.
#[export] Hint Extern 5 (DPAT (of_Z (Z.lor _ _))) =>
  simple eapply expr_compile_Z_lor; shelve : expr_compiler.
#[export] Hint Extern 5 (DPAT (of_Z (Z.lxor _ _))) =>
  simple eapply expr_compile_Z_lxor; shelve : expr_compiler.
#[export] Hint Extern 5 (DPAT (of_Z (Z.shiftl _ _))) =>
  simple eapply expr_compile_Z_shiftl; shelve : expr_compiler.
#[export] Hint Extern 5 (DPAT (of_Z (Z.shiftr _ _))) =>
  simple eapply expr_compile_Z_shiftr; shelve : expr_compiler.
#[export] Hint Extern 5 (DPAT (of_bool (Z.eqb _ _))) =>
  simple eapply expr_compile_Z_eqb; shelve : expr_compiler.

(* Don't shelve side conditions for these two competing lemmas, since we'll use
   them (with backtracking) to pick the right one. *)
#[export] Hint Extern 5 (DPAT (of_bool (Z.ltb _ _))) =>
  simple eapply expr_compile_Z_ltb_u; [ shelve.. | | ] : expr_compiler.
#[export] Hint Extern 5 (DPAT (of_bool (Z.ltb _ _))) =>
  simple eapply expr_compile_Z_ltb_s; [ shelve.. | | ] : expr_compiler.
(* Don't shelve side conditions for these two either *)
#[export] Hint Extern 5 (DPAT (of_bool (Z.gtb _ _))) =>
  simple eapply expr_compile_Z_gtb_u; [ shelve.. | | ] : expr_compiler.
#[export] Hint Extern 5 (DPAT (of_bool (Z.gtb _ _))) =>
  simple eapply expr_compile_Z_gtb_s; [ shelve.. | | ] : expr_compiler.

#[export] Hint Extern 5 (DPAT (of_Z (Z.b2z _))) =>
  simple eapply expr_compile_Z_b2z : expr_compiler.

#[export] Hint Extern 5 (DPAT (of_Z (_ mod 2 ^ _))) =>
  simple eapply expr_compile_Z_wrap : expr_compiler.
#[export] Hint Extern 5 (DPAT (of_Z (Z.smodulo _ (2 ^ _)))) =>
  simple eapply expr_compile_Z_swrap : expr_compiler.
#[export] Hint Extern 5 (DPAT (of_Z (byte.wrap _))) =>
  simple eapply expr_compile_byte_wrap : expr_compiler.

#[export] Hint Extern 5 (DPAT (of_N (N.add _ _))) =>
  simple eapply expr_compile_N_add; shelve : expr_compiler.
#[export] Hint Extern 5 (DPAT (of_N (N.sub _ _))) =>
  simple eapply expr_compile_N_sub; shelve : expr_compiler.
#[export] Hint Extern 5 (DPAT (of_N (N.mul _ _))) =>
  simple eapply expr_compile_N_mul; shelve : expr_compiler.

#[export] Hint Extern 5 (DPAT (of_nat (Nat.add _ _))) =>
  simple eapply expr_compile_nat_add; shelve : expr_compiler.
#[export] Hint Extern 5 (DPAT (of_nat (Nat.sub _ _))) =>
  simple eapply expr_compile_nat_sub; shelve : expr_compiler.
#[export] Hint Extern 5 (DPAT (of_nat (Nat.mul _ _))) =>
  simple eapply expr_compile_nat_mul; shelve : expr_compiler.

#[export] Hint Extern 5 (DPAT (of_byte (byte.and _ _))) =>
  simple eapply expr_compile_byte_and; shelve : expr_compiler.
#[export] Hint Extern 5 (DPAT (of_byte (byte.xor _ _))) =>
  simple eapply expr_compile_byte_xor; shelve : expr_compiler.

#[export] Hint Extern 5 (DPAT (of_bool (andb _ _))) =>
  simple eapply expr_compile_bool_andb; shelve : expr_compiler.
#[export] Hint Extern 5 (DPAT (of_bool (orb _ _))) =>
  simple eapply expr_compile_bool_orb; shelve : expr_compiler.
#[export] Hint Extern 5 (DPAT (of_bool (xorb _ _))) =>
  simple eapply expr_compile_bool_xorb; shelve : expr_compiler.

#[export] Hint Extern 6 (DEXPR _ _ _ (of_Z _)) =>
  simple eapply expr_compile_Z_literal; shelve : expr_compiler.
#[export] Hint Extern 6 (DEXPR _ _ _ Zmod.zero) =>
  simple eapply expr_compile_zero; shelve : expr_compiler.
#[export] Hint Extern 6 (DEXPR _ _ _ Zmod.one) =>
  simple eapply expr_compile_one; shelve : expr_compiler.
#[export] Hint Extern 8 (DEXPR _ _ _ _) =>
  simple eapply expr_compile_word_literal; shelve : expr_compiler.

Section Tests.
  Context {width: Z} {BW: Bitwidth width}.
  Local Notation word := (bits width).
  Context {mem: map.map word Byte.byte} {locals: map.map String.string word}.
  Context {mem_ok : map.ok mem}.
  Context {locals_ok : map.ok locals}.

  Context (m: mem).

  Notation DEXPR l := (WeakestPrecondition.dexpr (mem := mem) (locals := locals) m l).

  Local Goal {e | forall w,
          DEXPR #{ "w" => w }# e (Zmod.and (bits.of_Z width 3) w) }.
  Proof. eexists; intros; compile_expr. Qed.

  Local Goal {e | forall z,
          DEXPR #{ "z" => of_Z z }# e (bits.of_Z width (Z.land 3 z)) }.
  Proof. eexists; intros; compile_expr. Qed.

  Local Goal {e | forall b,
          DEXPR #{ "b" => of_byte b }# e (word_of_byte (byte.and Byte.x03 b)) }.
  Proof. eexists; intros; compile_expr. Qed.

  Local Goal {e | forall z n, (* Casts come "for free" *)
          DEXPR #{ "z" => of_Z z; "n" => of_N n }# e (of_Z (Z.add z (Z.of_N n))) }.
  Proof. eexists; intros; compile_expr. Qed.

  Local Goal {e | forall b,
          DEXPR #{ "n" => word.b2w b }# e (word.b2w (andb (negb b) false)) }.
  Proof. eexists; intros; compile_expr. Qed.

  (* The compiler picks the right comparisons *)
  Local Goal {e | forall z, 0 <= z < 2 ^ width ->
          DEXPR #{ "n" => bits.of_Z width z }# e (word.b2w (orb (Z.ltb z 3) false)) }.
  Proof. eexists; intros; compile_expr. Qed.

  Local Goal {e | forall z, -2 ^ (width-1) <= z < 2 ^ (width-1) ->
          DEXPR #{ "n" => bits.of_Z width z }# e (word.b2w (orb (Z.eqb z 3) false)) }.
  Proof. eexists; intros; compile_expr. Qed.

  Local Goal {e | forall x b,
          0 <= x < 2 ^ width ->
          DEXPR #{ "x" => bits.of_Z width x; "b" => word_of_byte b }# e
                (Zmod.add (bits.of_Z width (Z.add (Z.lnot x) (Z.div x 2)))
                          (word_of_byte (byte.and b b))) }.
  Proof. eexists; intros; compile_expr. Qed.

  Local Goal {e | forall w,
          DEXPR #{ "w" => w }# e (Semantics.slu w 3) }.
  Proof. eexists; intros; compile_expr. Qed.
End Tests.
