Require Import Rupicola.Lib.Api.
Require Import Rupicola.Lib.Loops.
Require Import bedrock2.Semantics.
Require Import coqutil.Word.Bitwidth coqutil.Byte.
Require Import Rupicola.Lib.Arrays.
Require Import Rupicola.Examples.Cells.Cells.

Section __.
  Context {width: Z} {BW: Bitwidth width}.
  Local Notation word := (bits width).
  Context {mem: map.map word Byte.byte}.
  Context {locals: map.map String.string word}.
  Context {ext_spec: bedrock2.Semantics.ExtSpec}.
  Context {mapok : map.ok mem}.
  Context {localsok : map.ok locals}.
  Context {ext_spec_ok : Semantics.ext_spec.ok ext_spec}.
  Section Gallina.

    Definition all_1s : word := bits.of_Z width (-1).

    Definition is_mask mask : Prop :=
      mask = all_1s \/ mask = Zmod.zero.

    Definition mask_of_bool (b : bool) :=
      if b then all_1s else Zmod.zero.

    (*idea: if b then true_val else false_val *)
    Definition select_word (mask : word) true_val false_val :=
      let/n nmask := (Zmod.sub (bits.of_Z width (-1)) mask) in
      let/n r := Zmod.or (Zmod.and mask true_val) (Zmod.and nmask false_val) in
      r.

    (*Rupicola doesn't appear to behave well w/ a call to select_word*)
    Definition cmove_word (mask : word) (c1 c2 : cell) :=
      let/n nmask := (Zmod.sub (bits.of_Z width (-1)) mask) in
      let/n true_val := get c1 in
      let/n false_val := get c2 in
      let/n r := Zmod.or (Zmod.and mask true_val) (Zmod.and nmask false_val) in
      let/n c1 := put r in
      c1.

    Definition cswap_word (mask : word) (c1 c2 : cell) :=
      let/n nmask := (Zmod.sub (bits.of_Z width (-1)) mask) in
      let/n true_val := get c1 in
      let/n false_val := get c2 in
      let/n r := Zmod.or (Zmod.and mask true_val) (Zmod.and nmask false_val) in
      let/n c1 := put r in
      let/n r := Zmod.or (Zmod.and mask false_val) (Zmod.and nmask true_val) in
      let/n c2 := put r in
      (c1,c2).


    Instance HasDefault_word : HasDefault word :=
      Zmod.zero.

    Definition cmove_array mask len
               (a1: ListArray.t word)
               (a2: ListArray.t word) :=
      let/n from := Zmod.zero in
      let/n nmask := (Zmod.sub (bits.of_Z width (-1)) mask) in
      let/n a1 := ranged_for_u
                    from len
                    (fun a1 tok idx Hlt =>
                       let/n v1 := ListArray.get a1 idx in
                       let/n v2 := ListArray.get a2 idx in
                       let/n r := Zmod.or (Zmod.and mask v1)
                                          (Zmod.and nmask v2) in
                       let/n a1 :=
                          ListArray.put a1 idx r in
                       (tok, a1)) a1 in
      (a1,a2).

    Definition cswap_array mask len
               (a1: ListArray.t word)
               (a2: ListArray.t word) :=
      let/n from := Zmod.zero in
      let/n nmask := (Zmod.sub (bits.of_Z width (-1)) mask) in
      let/n (a1, a2) :=
         ranged_for_u
           from len
           (fun p tok idx Hlt =>
              let/n v1 := ListArray.get (P2.car p) idx in
              let/n v2 := ListArray.get (P2.cdr p) idx in
              let/n r1 := Zmod.or (Zmod.and mask v1)
                                 (Zmod.and nmask v2) in
              let/n r2 := Zmod.or (Zmod.and mask v2)
                                 (Zmod.and nmask v1) in
              let/n a1 := ListArray.put (P2.car p) idx r1 in
              let/n a2 := ListArray.put (P2.cdr p) idx r2 in
              (tok, \< a1, a2 \>)) \< a1, a2 \> in
      (a1, a2).
  End Gallina.


  Lemma z_lt_width : 0 <= width.
  Proof.
    destruct width_cases; lia.
  Qed.



  Lemma all_1s_and : forall x, Zmod.and all_1s x = x.
  Proof. intros; unfold all_1s; rewrite Zmod.of_Z_m1, word.and_comm; apply word.and_m1_r, width_pos. Qed.

  Lemma word_not_all1s : Zmod.not all_1s = Zmod.zero.
  Proof. unfold all_1s; rewrite Zmod.of_Z_m1; apply bits.not_m1. Qed.

  Lemma zero_and (x : word)
    : Zmod.and Zmod.zero x = Zmod.zero.
  Proof. apply Zmod.unsigned_inj; rewrite bits.unsigned_and, Zmod.unsigned_0; reflexivity. Qed.

  Lemma cmove_word_is_conditional mask c1 c2
    : is_mask mask ->
      cmove_word mask c1 c2 = if Zmod.eqb mask Zmod.zero then c2 else c1.
  Proof.
    case (Zmod.eqb_spec mask Zmod.zero).
    {
      unfold cmove_word; intros;
      destruct c1; destruct c2.
      cbv[nlet put get Cells.data].
      f_equal.
      subst.
      rewrite Zmod.sub_0_r, !zero_and, all_1s_and, word.or_0_l.
      reflexivity.
    }
    {
      unfold is_mask.
      intuition; subst.
      unfold cmove_word; intros;
        destruct c1; destruct c2.
       cbv[nlet put get Cells.data].
      f_equal.
      subst.
      unfold all_1s.
      rewrite Zmod.sub_same, !zero_and, all_1s_and, word.or_0_r.
      reflexivity.
    }
  Qed.

  Lemma cswap_word_is_conditional mask c1 c2
    : is_mask mask ->
      cswap_word mask c1 c2 =
      if Zmod.eqb mask Zmod.zero then (c2,c1) else (c1,c2).
  Proof.
    case (Zmod.eqb_spec mask Zmod.zero).
    {
      unfold cswap_word; intros;
      destruct c1; destruct c2.
      cbv[nlet put get Cells.data].
      repeat f_equal.

      all: subst; rewrite Zmod.sub_0_r, !zero_and, all_1s_and, word.or_0_l.
      all: reflexivity.
    }
    {
      unfold is_mask.
      intuition; subst.
      unfold cswap_word; intros;
        destruct c1; destruct c2.
      cbv[nlet put get Cells.data].
      repeat f_equal.

      all: subst; unfold all_1s.
      all: rewrite Zmod.sub_same, !zero_and, all_1s_and, word.or_0_r.
      all: reflexivity.
    }
  Qed.

  Instance spec_of_cmove_word : spec_of "cmove_word" :=
    fnspec! "cmove_word" mask ptr1 ptr2 / c1 c2 R,
    { requires tr mem :=
        is_mask mask /\
        (cell_value ptr1 c1 * cell_value ptr2 c2 * R)%sep mem;
      ensures tr' mem' :=
        tr' = tr /\
        (cell_value ptr1 (cmove_word mask c1 c2)
         * cell_value ptr2 c2 * R)%sep mem' }.

  Derive cmove_word_br2fn SuchThat
         (defn! "cmove_word" ("mask", "c1", "c2") { cmove_word_br2fn },
          implements cmove_word)
         As cmove_br2fn_ok.
  Proof.
    compile.
  Qed.

  Instance spec_of_cswap_word : spec_of "cswap_word" :=
    fnspec! "cswap_word" mask ptr1 ptr2 / c1 c2 R,
    { requires tr mem :=
        is_mask mask /\
        (cell_value ptr1 c1 * cell_value ptr2 c2 * R)%sep mem;
      ensures tr' mem' :=
        tr' = tr /\
        let (c1',c2') := (cswap_word mask c1 c2) in
        (cell_value ptr1 c1'
         * cell_value ptr2 c2' * R)%sep mem' }.

  Derive cswap_word_br2fn SuchThat
         (defn! "cswap_word" ("mask", "c1", "c2") { cswap_word_br2fn },
          implements cswap_word)
         As cswap_br2fn_ok.
  Proof.
    compile.
  Qed.



  Instance spec_of_cmove_array : spec_of "cmove_array" :=
    fnspec! "cmove_array" mask len ptr1 ptr2 / n c1 c2 R,
    (*TODO: if b then bw should be all 1s*)
    { requires tr mem :=
        Zmod.unsigned len = Z.of_nat n /\
        is_mask mask /\
        (sizedlistarray_value AccessWord n ptr1 c1
         * sizedlistarray_value AccessWord n ptr2 c2 * R)%sep mem;
      ensures tr' mem' :=
        tr' = tr /\
        let (c1,c2) := cmove_array mask len c1 c2 in
        (sizedlistarray_value AccessWord n ptr1 c1
         * sizedlistarray_value AccessWord n ptr2 c2 * R)%sep mem' }.

  Import SizedListArrayCompiler.
  Import LoopCompiler.
  Hint Extern 10 (_ < _) => lia: compiler_side_conditions.

  Derive cmove_array_br2fn SuchThat
         (defn! "cmove_array" ("mask", "len", "a1", "a2") { cmove_array_br2fn },
          implements cmove_array)
         As cmove_array_br2fn_ok.
  Proof.
    compile.
  Qed.

  Instance spec_of_cswap_array : spec_of "cswap_array" :=
    fnspec! "cswap_array" mask len ptr1 ptr2 / n c1 c2 R,
    (*TODO: if b then bw should be all 1s*)
    { requires tr mem :=
        Zmod.unsigned len = Z.of_nat n /\
        is_mask mask /\
        (sizedlistarray_value AccessWord n ptr1 c1
         * sizedlistarray_value AccessWord n ptr2 c2 * R)%sep mem;
      ensures tr' mem' :=
        tr' = tr /\
        let (c1,c2) := cswap_array mask len c1 c2 in
        (sizedlistarray_value AccessWord n ptr1 c1
         * sizedlistarray_value AccessWord n ptr2 c2 * R)%sep mem' }.

  Derive cswap_array_br2fn SuchThat
         (defn! "cswap_array" ("mask", "len", "a1", "a2") { cswap_array_br2fn },
          implements cswap_array)
         As cswap_array_br2fn_ok.
  Proof.
    compile.
  Qed.
End __.
