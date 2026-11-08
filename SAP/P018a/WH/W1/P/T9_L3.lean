import SAP.P018a.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

noncomputable section
namespace SAP.P018a.WH.W1.P.T9_L3

open Finset
open scoped BigOperators

lemma endpoints_lt {N : ℕ} (d : Dyad N) : firstUnit d < secondUnit d :=
  Finset.min'_lt_max'_of_card (members d) (by rw [members_card]; omega)

lemma members_endpoints {N : ℕ} (d : Dyad N) :
    members d = {firstUnit d, secondUnit d} := by
  symm
  apply Finset.eq_of_subset_of_card_le
  · intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl
    · exact Finset.min'_mem _ _
    · exact Finset.max'_mem _ _
  · rw [members_card]
    simp [ne_of_lt (endpoints_lt d)]

def mkDyad {N : ℕ} (i j : Fin N) (hij : i ≠ j) : Dyad N :=
  ⟨{i, j}, by simp [dyads, hij]⟩

lemma mkDyad_endpoints {N : ℕ} (i j : Fin N) (hij : i < j) :
    firstUnit (mkDyad i j hij.ne) = i ∧ secondUnit (mkDyad i j hij.ne) = j := by
  simp [firstUnit, secondUnit, members, mkDyad, Finset.min'_pair,
    Finset.max'_pair, min_eq_left hij.le, max_eq_right hij.le]

lemma upper_sum {N : ℕ} (F : Fin N → Fin N → ℝ) :
    (∑ d : Dyad N, F (firstUnit d) (secondUnit d)) =
      ∑ i : Fin N, ∑ j : Fin N, if i < j then F i j else 0 := by
  classical
  let P := (univ ×ˢ univ : Finset (Fin N × Fin N)).filter (fun p => p.1 < p.2)
  have h : (∑ d : Dyad N, F (firstUnit d) (secondUnit d)) =
      ∑ p ∈ P, F p.1 p.2 := by
    apply Finset.sum_bij (fun d _ => (firstUnit d, secondUnit d))
    · intro d hd
      simp [P, endpoints_lt]
    · intro d hd e he hde
      apply Subtype.ext
      change members d = members e
      rw [members_endpoints d, members_endpoints e]
      rw [Prod.mk.injEq] at hde
      rw [hde.1, hde.2]
    · intro p hp
      have hp' : p.1 < p.2 := (Finset.mem_filter.mp hp).2
      refine ⟨mkDyad p.1 p.2 hp'.ne, mem_univ _, ?_⟩
      obtain ⟨h₁, h₂⟩ := mkDyad_endpoints p.1 p.2 hp'
      exact Prod.ext h₁ h₂
    · intro d hd
      rfl
  rw [h]
  simp only [P, Finset.sum_filter, Finset.sum_product]

lemma weight_factor {N : ℕ} (d : Dyad N) :
    concentratedWeight d =
      AronowAudit.P018.Wave1.concentrated_weights_q (firstUnit d) *
        AronowAudit.P018.Wave1.concentrated_weights_q (secondUnit d) := by
  unfold SAP.P018a.concentratedWeight AronowAudit.P018.Wave1.concentrated_weights_q
  have he : ((firstUnit d).val + (secondUnit d).val + 2 : ℤ) =
      (((firstUnit d).val + 1 + ((secondUnit d).val + 1) : ℕ) : ℤ) := by
    push_cast
    ring
  rw [_root_.zpow_neg, he, zpow_natCast]
  simp only [pow_add, one_div, inv_pow, _root_.mul_inv_rev]
  ring

lemma weight_nonneg {N : ℕ} (d : Dyad N) : 0 ≤ concentratedWeight d := by
  rw [weight_factor]
  exact mul_nonneg
    (AronowAudit.P018.Wave1.concentrated_weights_q_pos (firstUnit d)).le
    (AronowAudit.P018.Wave1.concentrated_weights_q_pos (secondUnit d)).le

lemma weight_pos {N : ℕ} (d : Dyad N) : 0 < concentratedWeight d := by
  rw [weight_factor]
  exact mul_pos
    (AronowAudit.P018.Wave1.concentrated_weights_q_pos (firstUnit d))
    (AronowAudit.P018.Wave1.concentrated_weights_q_pos (secondUnit d))

lemma tail_weight_bounds {N : ℕ} (hN : 8 ≤ N) :
    0 ≤ W1TailWeight N ∧ W1TailWeight N ≤ (1 / 256 : ℝ) := by
  have hrepr : W1TailWeight N =
      ∑ i : Fin N, ∑ j : Fin N,
        if i < j then
          (if 8 ≤ j.val then
            AronowAudit.P018.Wave1.concentrated_weights_q i *
              AronowAudit.P018.Wave1.concentrated_weights_q j
          else 0)
        else 0 := by
    calc
      W1TailWeight N = ∑ d : Dyad N,
          (if 8 ≤ (secondUnit d).val then
            AronowAudit.P018.Wave1.concentrated_weights_q (firstUnit d) *
              AronowAudit.P018.Wave1.concentrated_weights_q (secondUnit d)
          else 0) := by
        unfold W1TailWeight
        apply Finset.sum_congr rfl
        intro d hd
        rw [weight_factor]
      _ = _ := upper_sum (fun i j => if 8 ≤ j.val then
          AronowAudit.P018.Wave1.concentrated_weights_q i *
            AronowAudit.P018.Wave1.concentrated_weights_q j else 0)
  have hq (i : Fin N) :
      0 < AronowAudit.P018.Wave1.concentrated_weights_q i :=
    AronowAudit.P018.Wave1.concentrated_weights_q_pos i
  have hterms (i j : Fin N) :
      (if i < j then
        (if 8 ≤ j.val then
          AronowAudit.P018.Wave1.concentrated_weights_q i *
            AronowAudit.P018.Wave1.concentrated_weights_q j else 0)
       else 0) ≤
        (if 8 ≤ j.val then
          AronowAudit.P018.Wave1.concentrated_weights_q i *
            AronowAudit.P018.Wave1.concentrated_weights_q j else 0) := by
    by_cases hij : i < j
    · simp [hij]
    · by_cases hj : 8 ≤ j.val
      · simp [hij, hj]
        exact mul_nonneg (hq i).le (hq j).le
      · simp [hij, hj]
  have hnonneg : 0 ≤ W1TailWeight N := by
    unfold W1TailWeight
    apply Finset.sum_nonneg
    intro d hd
    split_ifs
    · exact weight_nonneg d
    · exact le_rfl
  have hSnonneg : 0 ≤ AronowAudit.P018.Wave1.concentrated_weights_S N :=
    Finset.sum_nonneg (fun i hi => (hq i).le)
  have hTnonneg : 0 ≤ AronowAudit.P018.Wave1.concentrated_weights_tail N := by
    unfold AronowAudit.P018.Wave1.concentrated_weights_tail
    apply Finset.sum_nonneg
    intro i hi
    split_ifs
    · exact (hq i).le
    · exact le_rfl
  have hprod : W1TailWeight N ≤
      AronowAudit.P018.Wave1.concentrated_weights_S N *
        AronowAudit.P018.Wave1.concentrated_weights_tail N := by
    rw [hrepr]
    calc
      _ ≤ ∑ i : Fin N, ∑ j : Fin N,
          if 8 ≤ j.val then
            AronowAudit.P018.Wave1.concentrated_weights_q i *
              AronowAudit.P018.Wave1.concentrated_weights_q j else 0 := by
        apply Finset.sum_le_sum
        intro i hi
        apply Finset.sum_le_sum
        intro j hj
        exact hterms i j
      _ = ∑ i : Fin N,
          AronowAudit.P018.Wave1.concentrated_weights_q i *
            (∑ j : Fin N, if 8 ≤ j.val then
              AronowAudit.P018.Wave1.concentrated_weights_q j else 0) := by
        apply Finset.sum_congr rfl
        intro i hi
        calc
          _ = ∑ j : Fin N,
              AronowAudit.P018.Wave1.concentrated_weights_q i *
                (if 8 ≤ j.val then AronowAudit.P018.Wave1.concentrated_weights_q j else 0) := by
            apply Finset.sum_congr rfl
            intro j hj
            by_cases hjt : 8 ≤ j.val <;> simp [hjt]
          _ = _ := by rw [Finset.mul_sum]
      _ = AronowAudit.P018.Wave1.concentrated_weights_S N *
          (∑ j : Fin N, if 8 ≤ j.val then
            AronowAudit.P018.Wave1.concentrated_weights_q j else 0) := by
        unfold AronowAudit.P018.Wave1.concentrated_weights_S
        rw [← Finset.sum_mul]
      _ = AronowAudit.P018.Wave1.concentrated_weights_S N *
          AronowAudit.P018.Wave1.concentrated_weights_tail N := rfl
  have hSup : AronowAudit.P018.Wave1.concentrated_weights_S N ≤ 1 := by
    rw [AronowAudit.P018.Wave1.concentrated_weights_S_formula]
    have hx : 0 ≤ AronowAudit.P018.Wave1.concentrated_weights_x N := by
      unfold AronowAudit.P018.Wave1.concentrated_weights_x
      positivity
    linarith
  have hTup : AronowAudit.P018.Wave1.concentrated_weights_tail N ≤
      (1 / 256 : ℝ) :=
    AronowAudit.P018.Wave1.concentrated_weights_tail_le hN
  refine ⟨hnonneg, ?_⟩
  have hprod' :
      AronowAudit.P018.Wave1.concentrated_weights_S N *
        AronowAudit.P018.Wave1.concentrated_weights_tail N ≤
      AronowAudit.P018.Wave1.concentrated_weights_tail N := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hSup) hTnonneg]
  exact hprod.trans (hprod'.trans hTup)

lemma response_bounds {N : ℕ} (ω : Fin N → Bool) (d : Dyad N) :
    -2 ≤ response signKernel ω d ∧ response signKernel ω d ≤ 2 := by
  change -2 ≤ signValue (ω (firstUnit d)) + signValue (ω (secondUnit d)) ∧
    signValue (ω (firstUnit d)) + signValue (ω (secondUnit d)) ≤ 2
  cases ω (firstUnit d) <;> cases ω (secondUnit d) <;>
    norm_num [SAP.P018a.signValue]

lemma deviation_bound {N : ℕ} (ω : Fin N → Bool) (hω : ω ∈ W1WeightEvent N)
    (d : Dyad N) :
    0 ≤ 2 - response signKernel ω d ∧
      2 - response signKernel ω d ≤ if 8 ≤ (secondUnit d).val then 4 else 0 := by
  by_cases ht : 8 ≤ (secondUnit d).val
  · rw [if_pos ht]
    have hr := response_bounds ω d
    constructor <;> linarith
  · rw [if_neg ht]
    have hlt : (secondUnit d).val < 8 := by omega
    have hfirst : (firstUnit d).val < 8 := by
      have hh := endpoints_lt d
      omega
    have ha := hω (firstUnit d) hfirst
    have hb := hω (secondUnit d) hlt
    norm_num [response, signKernel, SAP.P018a.signValue, ha, hb]

lemma weight_tail_deviation {N : ℕ} (ω : Fin N → Bool)
    (hω : ω ∈ W1WeightEvent N) :
    (∑ d : Dyad N, concentratedWeight d *
      (2 - response signKernel ω d)) ≤ 4 * W1TailWeight N := by
  calc
    _ ≤ ∑ d : Dyad N, concentratedWeight d *
        (if 8 ≤ (secondUnit d).val then 4 else 0) := by
      apply Finset.sum_le_sum
      intro d hd
      exact mul_le_mul_of_nonneg_left (deviation_bound ω hω d).2
        (weight_nonneg d)
    _ = 4 * W1TailWeight N := by
      unfold W1TailWeight
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d hd
      by_cases ht : 8 ≤ (secondUnit d).val <;> simp [ht] <;> ring

lemma ols_scalar {N : ℕ} (ω : Fin N → Bool) :
    weightedOLS signKernel concentratedWeight ω 0 =
      (W1W N)⁻¹ *
        ∑ d : Dyad N, concentratedWeight d * response signKernel ω d := by
  have hg : weightedGram signKernel concentratedWeight ω =
      Matrix.of (fun _ _ : Fin 1 => W1W N) := by
    ext a b
    fin_cases a
    fin_cases b
    simp [weightedGram, W1W, Matrix.sum_apply, outer, design, signKernel,
      Matrix.of_apply]
  rw [weightedOLS, hg, Matrix.inv_def]
  simp [Matrix.det_unique, Matrix.adjugate_subsingleton, Ring.inverse_eq_inv,
    Matrix.mulVec, dotProduct, Fin.sum_univ_one, Finset.sum_apply, score,
    design, signKernel]

lemma Wpos {N : ℕ} (hN : 2 ≤ N) : 0 < W1W N := by
  have h := AronowAudit.P018.Wave1.concentrated_weights_W_lower hN
  change 0 < AronowAudit.P018.Wave1.concentrated_weights_W N
  linarith

lemma mean_identity {N : ℕ} (hN : 2 ≤ N) (ω : Fin N → Bool) :
    2 - weightedOLS signKernel concentratedWeight ω 0 =
      (W1W N)⁻¹ *
        ∑ d : Dyad N, concentratedWeight d * (2 - response signKernel ω d) := by
  have hwpos := Wpos hN
  have hsum :
      2 * W1W N - ∑ d : Dyad N, concentratedWeight d * response signKernel ω d =
        ∑ d : Dyad N, concentratedWeight d * (2 - response signKernel ω d) := by
    have hW : (∑ d : Dyad N, 2 * concentratedWeight d) = 2 * W1W N := by
      calc
        _ = 2 * (∑ d : Dyad N, concentratedWeight d) := by rw [Finset.mul_sum]
        _ = 2 * W1W N := by rfl
    calc
      _ = (∑ d : Dyad N, 2 * concentratedWeight d) -
          ∑ d : Dyad N, concentratedWeight d * response signKernel ω d := by rw [hW]
      _ = ∑ d : Dyad N,
          (2 * concentratedWeight d - concentratedWeight d * response signKernel ω d) := by
        rw [Finset.sum_sub_distrib]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro d hd
        ring
  rw [ols_scalar]
  calc
    _ = (W1W N)⁻¹ * (2 * W1W N) -
        (W1W N)⁻¹ * ∑ d : Dyad N,
          concentratedWeight d * response signKernel ω d := by
      rw [show (W1W N)⁻¹ * (2 * W1W N) = 2 from by field_simp [hwpos.ne']]
    _ = (W1W N)⁻¹ *
        (2 * W1W N - ∑ d : Dyad N,
          concentratedWeight d * response signKernel ω d) := by ring
    _ = _ := by rw [hsum]

lemma mean_bounds {N : ℕ} (hN : 8 ≤ N) (ω : Fin N → Bool)
    (hω : ω ∈ W1WeightEvent N) :
    0 ≤ 2 - weightedOLS signKernel concentratedWeight ω 0 ∧
      2 - weightedOLS signKernel concentratedWeight ω 0 ≤
        4 * W1TailWeight N / W1W N := by
  have hN2 : 2 ≤ N := by omega
  have hwpos := Wpos hN2
  have hid := mean_identity hN2 ω
  have hdev := weight_tail_deviation ω hω
  have hsum_nonneg : 0 ≤ ∑ d : Dyad N,
      concentratedWeight d * (2 - response signKernel ω d) :=
    Finset.sum_nonneg (fun d hd => mul_nonneg (weight_nonneg d)
      (deviation_bound ω hω d).1)
  constructor
  · rw [hid]
    exact mul_nonneg (inv_nonneg.mpr hwpos.le) hsum_nonneg
  · rw [hid]
    calc
      _ ≤ (W1W N)⁻¹ * (4 * W1TailWeight N) :=
        mul_le_mul_of_nonneg_left hdev (inv_nonneg.mpr hwpos.le)
      _ = 4 * W1TailWeight N / W1W N := by rw [div_eq_mul_inv]; ring

lemma score_sum_bound {N : ℕ} (hN : 8 ≤ N) (ω : Fin N → Bool)
    (hω : ω ∈ W1WeightEvent N) :
    (∑ d : Dyad N, |W1WeightScore ω d|) ≤ 8 * W1TailWeight N := by
  have hN2 : 2 ≤ N := by omega
  have hwpos := Wpos hN2
  have hm := mean_bounds hN ω hω
  have hdev := weight_tail_deviation ω hω
  have hmass :
      (∑ d : Dyad N, concentratedWeight d * |response signKernel ω d - 2|) ≤
        4 * W1TailWeight N := by
    calc
      _ = ∑ d : Dyad N, concentratedWeight d *
          (2 - response signKernel ω d) := by
        apply Finset.sum_congr rfl
        intro d hd
        have h := response_bounds ω d
        rw [abs_of_nonpos]
        · ring
        · linarith
      _ ≤ _ := hdev
  calc
    _ = ∑ d : Dyad N, concentratedWeight d *
        |response signKernel ω d - weightedOLS signKernel concentratedWeight ω 0| := by
      apply Finset.sum_congr rfl
      intro d hd
      simp [W1WeightScore, abs_mul, abs_of_pos (weight_pos d)]
    _ ≤ ∑ d : Dyad N, concentratedWeight d *
        (|response signKernel ω d - 2| +
          |weightedOLS signKernel concentratedWeight ω 0 - 2|) := by
      apply Finset.sum_le_sum
      intro d hd
      apply mul_le_mul_of_nonneg_left _ (weight_nonneg d)
      have h := abs_sub_le (response signKernel ω d) 2
        (weightedOLS signKernel concentratedWeight ω 0)
      simpa only [abs_sub_comm 2 (weightedOLS signKernel concentratedWeight ω 0)] using h
    _ = (∑ d : Dyad N, concentratedWeight d *
          |response signKernel ω d - 2|) +
        W1W N * |weightedOLS signKernel concentratedWeight ω 0 - 2| := by
      simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, W1W]
    _ ≤ 8 * W1TailWeight N := by
      have hWabs : W1W N * |weightedOLS signKernel concentratedWeight ω 0 - 2| ≤
          4 * W1TailWeight N := by
        have habs : |weightedOLS signKernel concentratedWeight ω 0 - 2| =
            2 - weightedOLS signKernel concentratedWeight ω 0 := by
          rw [abs_of_nonpos]
          · ring
          · linarith [hm.1]
        rw [habs]
        have hmul := mul_le_mul_of_nonneg_left hm.2 hwpos.le
        have hwdiv : (4 * W1TailWeight N / W1W N) * W1W N =
            4 * W1TailWeight N := by
          field_simp [hwpos.ne']
        calc
          _ ≤ (4 * W1TailWeight N / W1W N) * W1W N := by nlinarith
          _ = _ := hwdiv
      linarith [hmass]

lemma variance_scalar {N : ℕ} (ω : Fin N → Bool) :
    (weightedVariance signKernel concentratedWeight ω) 0 0 =
      (W1W N)⁻¹ *
        (∑ d : Dyad N, ∑ f : Dyad N,
          if overlap d f then W1WeightScore ω d * W1WeightScore ω f else 0) *
        (W1W N)⁻¹ := by
  have hg : weightedGram signKernel concentratedWeight ω =
      Matrix.of (fun _ _ : Fin 1 => W1W N) := by
    ext a b
    fin_cases a
    fin_cases b
    simp [weightedGram, W1W, Matrix.sum_apply, outer, design, signKernel,
      Matrix.of_apply]
  unfold weightedVariance
  rw [hg]
  simp [sandwich, Matrix.inv_def, Matrix.det_unique,
    Matrix.adjugate_subsingleton, Ring.inverse_eq_inv, Matrix.mul_apply,
    Fin.sum_univ_one, Matrix.sum_apply, meat, AronowAudit.P018.matrix_ite_apply, outer, score,
    dot, design, signKernel, W1WeightScore, overlap]
  left
  apply Finset.sum_congr rfl
  intro d hd
  apply Finset.sum_congr rfl
  intro f hf
  exact ite_congr rfl (fun _ => by simp [outer]) (fun _ => by simp [outer])

lemma meat_abs_bound {N : ℕ} (z : Dyad N → ℝ) :
    |∑ d : Dyad N, ∑ f : Dyad N,
      if overlap d f then z d * z f else 0| ≤ (∑ d : Dyad N, |z d|)^2 := by
  calc
    _ ≤ ∑ d : Dyad N,
        |∑ f : Dyad N, if overlap d f then z d * z f else 0| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ d : Dyad N, ∑ f : Dyad N,
        |if overlap d f then z d * z f else 0| :=
      Finset.sum_le_sum (fun d hd => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ d : Dyad N, ∑ f : Dyad N, |z d| * |z f| := by
      apply Finset.sum_le_sum
      intro d hd
      apply Finset.sum_le_sum
      intro f hf
      by_cases hdf : overlap d f
      · simp [hdf, abs_mul]
      · simp [hdf]
        exact mul_nonneg (abs_nonneg _) (abs_nonneg _)
    _ = _ := by simp only [← Finset.mul_sum, ← Finset.sum_mul, pow_two]

lemma variance_bound {N : ℕ} (hN : 8 ≤ N) (ω : Fin N → Bool)
    (hω : ω ∈ W1WeightEvent N) :
    |(weightedVariance signKernel concentratedWeight ω) 0 0| ≤
      64 * (W1TailWeight N / W1W N)^2 := by
  have hN2 : 2 ≤ N := by omega
  have hwpos := Wpos hN2
  have hscore := score_sum_bound hN ω hω
  have hR := (tail_weight_bounds hN).1
  have hsum_nonneg : 0 ≤ ∑ d : Dyad N, |W1WeightScore ω d| :=
    Finset.sum_nonneg (fun d hd => abs_nonneg _)
  have hm := meat_abs_bound (W1WeightScore ω)
  rw [variance_scalar, abs_mul, abs_mul, abs_inv, abs_of_pos hwpos]
  calc
    _ ≤ (W1W N)⁻¹ * (∑ d : Dyad N, |W1WeightScore ω d|)^2 * (W1W N)⁻¹ := by
      gcongr
    _ ≤ (W1W N)⁻¹ * (8 * W1TailWeight N)^2 * (W1W N)⁻¹ := by
      have h8R : 0 ≤ 8 * W1TailWeight N := by positivity
      gcongr
    _ = 64 * (W1TailWeight N / W1W N)^2 := by
      field_simp [hwpos.ne']
      <;> ring

end SAP.P018a.WH.W1.P.T9_L3

theorem SAP.P018a.WH.W1.T9_L3_proof : SAP.P018a.WH.W1.T9_L3 := by
  intro N hN
  refine ⟨?_, ?_⟩
  · exact (SAP.P018a.WH.W1.P.T9_L3.tail_weight_bounds hN).1
  · refine ⟨(SAP.P018a.WH.W1.P.T9_L3.tail_weight_bounds hN).2, ?_⟩
    intro ω hω
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact (SAP.P018a.WH.W1.P.T9_L3.mean_bounds hN ω hω).1
    · exact (SAP.P018a.WH.W1.P.T9_L3.mean_bounds hN ω hω).2
    · exact SAP.P018a.WH.W1.P.T9_L3.score_sum_bound hN ω hω
    · exact SAP.P018a.WH.W1.P.T9_L3.variance_bound hN ω hω
