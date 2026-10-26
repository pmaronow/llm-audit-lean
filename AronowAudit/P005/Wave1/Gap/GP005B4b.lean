import AronowAudit.P005.P005_Formalization

namespace AronowAudit.P005.Wave1

noncomputable section
open scoped BigOperators Matrix
open Finset Filter
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000

/-!
P005-T3. The leverage witness is normalized and regular on every
size-eight assignment. Its variance is computed from the inclusion indicators
of labels 0 and 1 under the fixed-size design.
-/

lemma GP005B4b_T3_univ16 : (univ : Finset (Fin 16)) =
    {0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15} := by decide

lemma GP005B4b_T3_scale_square : (Real.sqrt (8/71 : ℝ))^2 = 8/71 :=
  Real.sq_sqrt (by norm_num)

lemma GP005B4b_T3_raw_moments : popMean leverageA = 0 ∧
    popMean (fun i => leverageA i^2) = 71/8 := by
  norm_num [popMean, mean, GP005B4b_T3_univ16, leverageA]

lemma GP005B4b_T3_standardized : standardized leveragePopulation := by
  apply standardized_scalar
  · exact GP005B4b_T3_raw_moments.1
  · rw [GP005B4b_T3_scale_square, GP005B4b_T3_raw_moments.2]
    norm_num

lemma GP005B4b_T3_fiber_bound (i : Fin 16) :
    ((univ : Finset (Fin 16)).filter (fun j => leverageA j = leverageA i)).card ≤ 7 := by
  fin_cases i <;> norm_num [GP005B4b_T3_univ16, leverageA, Finset.filter_insert, Finset.filter_singleton]

/-- Positivity from the multiplicity bound; no enumeration of treatment subsets. -/
lemma GP005B4b_T3_arm_cov_pos (S : Finset (Fin 16)) (hs : S.card = 8) :
    0 < sampleCov S leverageA leverageA := by
  classical
  have hSn : S.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨i, hi⟩ := hSn
  have hex : ∃ j ∈ S, leverageA j ≠ mean S leverageA := by
    by_contra hnot
    push Not at hnot
    have hsub : S ⊆ univ.filter (fun j => leverageA j = leverageA i) := by
      intro j hj
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hnot j hj).trans (hnot i hi).symm⟩
    have hcard := (Finset.card_le_card hsub).trans (GP005B4b_T3_fiber_bound i)
    omega
  obtain ⟨j, hj, hjne⟩ := hex
  have hsum : 0 < ∑ i ∈ S, (leverageA i-mean S leverageA)^2 :=
    Finset.sum_pos' (fun i _ => sq_nonneg _) ⟨j, hj, sq_pos_of_ne_zero (sub_ne_zero.mpr hjne)⟩
  have hpos : 0 < mean S (fun i => (leverageA i-mean S leverageA)^2) := by
    unfold mean
    exact div_pos hsum (by rw [hs]; norm_num)
  have hid := (mean_square_centering S (Finset.card_pos.mp (by omega)) leverageA).1
  have hcov : sampleCov S leverageA leverageA =
      mean S (fun i => (leverageA i-mean S leverageA)^2) := by
    rw [hid]
    simp only [sampleCov, pow_two]
  rw [hcov]
  exact hpos

lemma GP005B4b_T3_control_card (S : Finset (Fin 16)) (hs : S.card = 8) :
    (control S).card = 8 := by
  rw [control, Finset.card_sdiff_of_subset (Finset.subset_univ S)]
  simp [hs]

lemma GP005B4b_T3_interacted_regular : interactedRegular leveragePopulation 8 := by
  intro S hS
  have hs : S.card = 8 := (Finset.mem_powersetCard.mp hS).2
  have hc := GP005B4b_T3_control_card S hs
  have hT := GP005B4b_T3_arm_cov_pos S hs
  have hC := GP005B4b_T3_arm_cov_pos (control S) hc
  constructor
  · change (armL (scalarPopulation leverageA leverageY (fun _ => 0)
        (Real.sqrt (8/71))) S).det ≠ 0
    rw [scalar_armL_det, GP005B4b_T3_scale_square]
    exact ne_of_gt (mul_pos (by norm_num) hT)
  · change (armL (scalarPopulation leverageA leverageY (fun _ => 0)
        (Real.sqrt (8/71))) (control S)).det ≠ 0
    rw [scalar_armL_det, GP005B4b_T3_scale_square]
    exact ne_of_gt (mul_pos (by norm_num) hC)

lemma GP005B4b_T3_square_partition (S : Finset (Fin 16)) (hs : S.card = 8) :
    mean S (fun i => leverageA i^2) + mean (control S) (fun i => leverageA i^2) =
      2 * popMean (fun i => leverageA i^2) := by
  have hc := GP005B4b_T3_control_card S hs
  have hsum : (∑ i ∈ control S, leverageA i^2) =
      (∑ i : Fin 16, leverageA i^2)-(∑ i ∈ S, leverageA i^2) := by
    simpa only [control] using
      (Finset.sum_sdiff_eq_sub (f := fun i => leverageA i^2) (Finset.subset_univ S))
  simp only [mean, popMean, hs, hc, Finset.card_univ, Fintype.card_fin]
  rw [hsum]
  norm_num <;> ring

lemma GP005B4b_T3_scalar_pooled_det (a yT yC : Fin 16 → ℝ) (s : ℝ)
    (S : Finset (Fin 16)) :
    (Lhat (scalarPopulation a yT yC s) 8 S).det =
      1 - s^2/2 * (mean S a)^2 - s^2/2 * (mean (control S) a)^2 := by
  rw [Matrix.det_unique]
  norm_num [Lhat, pT, pC, Matrix.vecMulVec, xMean, scalarPopulation, mean_mul]
  <;> ring

lemma GP005B4b_T3_noninteracted_regular : noninteractedRegular leveragePopulation 8 := by
  intro S hS
  have hs : S.card = 8 := (Finset.mem_powersetCard.mp hS).2
  have hc := GP005B4b_T3_control_card S hs
  have hT := GP005B4b_T3_arm_cov_pos S hs
  have hC := GP005B4b_T3_arm_cov_pos (control S) hc
  have hpartition := GP005B4b_T3_square_partition S hs
  rw [GP005B4b_T3_raw_moments.2] at hpartition
  have hdet : (Lhat leveragePopulation 8 S).det =
      (4/71 : ℝ) * (sampleCov S leverageA leverageA +
        sampleCov (control S) leverageA leverageA) := by
    unfold leveragePopulation
    rw [GP005B4b_T3_scalar_pooled_det, GP005B4b_T3_scale_square]
    have hmul : (fun i => leverageA i*leverageA i) = (fun i => leverageA i^2) := by
      funext i
      ring
    simp only [sampleCov, hmul]
    nlinarith [hpartition]
  rw [hdet]
  exact ne_of_gt (mul_pos (by norm_num) (add_pos hT hC))

lemma GP005B4b_T3_leverage_values : leverage leveragePopulation =
    fun i => if i.val < 2 then (512/71 : ℝ) else 8/71 := by
  rw [leveragePopulation, scalar_leverage, GP005B4b_T3_scale_square]
  funext i
  fin_cases i <;> norm_num [leverageA]

lemma GP005B4b_T3_hy_constant : ∀ i, leverage leveragePopulation i * leverageY i = (8/71 : ℝ) := by
  intro i
  rw [GP005B4b_T3_leverage_values]
  fin_cases i <;> norm_num [leverageY]

lemma GP005B4b_T3_kappa_value : kappa leveragePopulation = (32/71 : ℝ) := by
  have hrange : BddAbove (Set.range (fun i => leverage leveragePopulation i/(16 : ℝ))) :=
    (Set.finite_range _).bddAbove
  unfold kappa
  apply le_antisymm
  · apply csSup_le ⟨_, Set.mem_range_self (0 : Fin 16)⟩
    rintro z ⟨i, rfl⟩
    rw [GP005B4b_T3_leverage_values]
    dsimp only
    split_ifs <;> norm_num
  · have h := le_csSup hrange (Set.mem_range_self (0 : Fin 16))
    have h0 : leverage leveragePopulation (0 : Fin 16)/(16 : ℝ) = (32/71 : ℝ) := by
      norm_num [GP005B4b_T3_leverage_values]
    rw [h0] at h
    exact h

/-- The two-level mean is derived on every actual size-eight subset. -/
lemma GP005B4b_T3_two_level_mean (S : Finset (Fin 16)) (hs : S.card = 8) (a b : ℝ) :
    mean S (fun i => if i.val < 2 then a else b) =
      b + (a-b)/8 * (indicator S 0+indicator S 1) := by
  classical
  have hf : (fun i : Fin 16 => if i.val < 2 then a else b) =
      (fun i => (b + (if i=0 then a-b else 0)) + (if i=1 then a-b else 0)) := by
    funext i
    fin_cases i <;> norm_num <;> ring
  rw [hf]
  by_cases h0 : (0 : Fin 16) ∈ S <;> by_cases h1 : (1 : Fin 16) ∈ S <;>
    simp [mean, hs, Finset.sum_add_distrib, nsmul_eq_mul, indicator, h0, h1] <;> ring

lemma GP005B4b_T3_covariance_formula (S : Finset (Fin 16)) (hS : S ∈ design 16 8) :
    sampleCov S (leverage leveragePopulation) leverageY =
      -(27783/36352 : ℝ) * (indicator S 0+indicator S 1) +
        (3969/18176 : ℝ) * (indicator S 0*indicator S 1) := by
  classical
  have hs : S.card = 8 := (Finset.mem_powersetCard.mp hS).2
  have hSn : S.Nonempty := Finset.card_pos.mp (by omega)
  have hhy : (fun i => leverage leveragePopulation i*leverageY i) =
      (fun _ => (8/71 : ℝ)) := funext GP005B4b_T3_hy_constant
  unfold sampleCov
  rw [hhy, mean_const S hSn, GP005B4b_T3_leverage_values, GP005B4b_T3_two_level_mean S hs]
  change _ - _ * mean S (fun i => if i.val < 2 then (1/64 : ℝ) else 1) = _
  rw [GP005B4b_T3_two_level_mean S hs]
  by_cases h0 : (0 : Fin 16) ∈ S <;> by_cases h1 : (1 : Fin 16) ∈ S <;>
    norm_num [indicator, h0, h1]

lemma GP005B4b_T3_covariance_square_formula (S : Finset (Fin 16)) (hS : S ∈ design 16 8) :
    (sampleCov S (leverage leveragePopulation) leverageY)^2 =
      (771895089/1321467904 : ℝ) * (indicator S 0+indicator S 1) +
        (362318103/660733952 : ℝ) * (indicator S 0*indicator S 1) := by
  classical
  rw [GP005B4b_T3_covariance_formula S hS]
  by_cases h0 : (0 : Fin 16) ∈ S <;> by_cases h1 : (1 : Fin 16) ∈ S <;>
    norm_num [indicator, h0, h1]

lemma GP005B4b_T3_expectation_add (f g : Finset (Fin 16) → ℝ) :
    expectation 8 (fun S => f S+g S) = expectation 8 f+expectation 8 g := by
  simp only [expectation, Finset.sum_add_distrib, add_div]

lemma GP005B4b_T3_expectation_sub (f g : Finset (Fin 16) → ℝ) :
    expectation 8 (fun S => f S-g S) = expectation 8 f-expectation 8 g := by
  simp only [expectation, Finset.sum_sub_distrib, sub_div]

lemma GP005B4b_T3_design_card : (design 16 8).card = 12870 := by
  simp only [design, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
  decide

lemma GP005B4b_T3_expectation_const (c : ℝ) : expectation (n := 16) 8 (fun _ => c) = c := by
  simp [expectation, GP005B4b_T3_design_card, nsmul_eq_mul]
  <;> ring

lemma GP005B4b_T3_pair_inclusion :
    expectation (n := 16) 8 (fun S => indicator S 0*indicator S 1) = (7/30 : ℝ) := by
  classical
  have hp : ∀ S ∈ design 16 8,
      indicator S 0*indicator S 1 = if ({0,1} : Finset (Fin 16)) ⊆ S then 1 else 0 := by
    intro S hS
    by_cases h0 : (0 : Fin 16) ∈ S <;> by_cases h1 : (1 : Fin 16) ∈ S <;>
      simp [indicator, Finset.insert_subset_iff, h0, h1]
  rw [expectation_congr 8 _ _ hp]
  have h := inclusion_count (n := 16) (m := 8) ({0,1} : Finset (Fin 16)) (by decide)
  convert h using 1 <;> norm_num [Nat.choose]

lemma GP005B4b_T3_expectation_indicator_polynomial (a b : ℝ) :
    expectation (n := 16) 8 (fun S => a*(indicator S 0+indicator S 1) +
      b*(indicator S 0*indicator S 1)) = a+b*(7/30) := by
  rw [GP005B4b_T3_expectation_add, expectation_mul, expectation_mul,
    GP005B4b_T3_expectation_add, GP005B4b_T3_pair_inclusion,
    indicator_expectation (by decide) (by decide) (by decide),
    indicator_expectation (by decide) (by decide) (by decide)]
  norm_num

lemma GP005B4b_T3_expectation_covariance :
    expectation 8 (fun S => sampleCov S (leverage leveragePopulation) leverageY) =
      -(64827/90880 : ℝ) := by
  rw [expectation_congr 8 _ _ GP005B4b_T3_covariance_formula,
    GP005B4b_T3_expectation_indicator_polynomial]
  norm_num

lemma GP005B4b_T3_variance_identity (f : Finset (Fin 16) → ℝ) :
    variance 8 f = expectation 8 (fun S => (f S)^2)-(expectation 8 f)^2 := by
  have hf : (fun S => (f S-expectation 8 f)^2) =
      (fun S => (f S^2-(2*expectation 8 f)*f S)+(expectation 8 f)^2) := by
    funext S
    ring
  unfold variance
  rw [hf, GP005B4b_T3_expectation_add, GP005B4b_T3_expectation_sub, expectation_mul, GP005B4b_T3_expectation_const]
  ring

lemma GP005B4b_T3_variance_value :
    variance 8 (fun S => sampleCov S (leverage leveragePopulation) leverageY) =
      (1678565511/8259174400 : ℝ) := by
  rw [GP005B4b_T3_variance_identity, GP005B4b_T3_expectation_covariance,
    expectation_congr 8 _ _ GP005B4b_T3_covariance_square_formula,
    GP005B4b_T3_expectation_indicator_polynomial]
  norm_num

lemma GP005B4b_T3_bound_value : covarianceBound 8 (leverage leveragePopulation) leverageY =
    (117645319/619438080 : ℝ) := by
  norm_num [covarianceBound, GP005B4b_T3_leverage_values, popMean, mean, GP005B4b_T3_univ16, leverageY]

lemma GP005B4b_T3_second_bound_value :
    (2*((16 : ℝ)-8)/(8*(16-1))*popMean (fun i => (leverage leveragePopulation i)^2*leverageY i^2) +
      2*((16 : ℝ)-8)*16/((8 : ℝ)^3*(16-1))*popMean (fun i => leverageY i^2)*
        popMean (fun i => (leverage leveragePopulation i)^2)) = (334349/1744896 : ℝ) := by
  norm_num [GP005B4b_T3_leverage_values, popMean, mean, GP005B4b_T3_univ16, leverageY]

theorem leverage_variance_counterexample_proof :
    standardized leveragePopulation ∧ interactedRegular leveragePopulation 8 ∧
    noninteractedRegular leveragePopulation 8 ∧
    popMean (fun i => leverageY i^2) ≤ 1 ∧
    popMean (fun i => leveragePopulation.yC i^2) = 0 ∧
    (1/4 : ℝ) < pT 16 8 ∧ pT 16 8 < (3/4 : ℝ) ∧
    (design 16 8).card = 12870 ∧
    kappa leveragePopulation = (32/71 : ℝ) ∧
    (∀ i, leverage leveragePopulation i * leverageY i = (8/71 : ℝ)) ∧
    variance 8 (fun S => sampleCov S (leverage leveragePopulation) leverageY) =
      (1678565511/8259174400 : ℝ) ∧
    covarianceBound 8 (leverage leveragePopulation) leverageY = (117645319/619438080 : ℝ) ∧
    covarianceBound 8 (leverage leveragePopulation) leverageY <
      variance 8 (fun S => sampleCov S (leverage leveragePopulation) leverageY) ∧
    (2*((16 : ℝ)-8)/(8*(16-1))*popMean (fun i => (leverage leveragePopulation i)^2*leverageY i^2) +
      2*((16 : ℝ)-8)*16/((8 : ℝ)^3*(16-1))*popMean (fun i => leverageY i^2)*
        popMean (fun i => (leverage leveragePopulation i)^2)) = (334349/1744896 : ℝ) ∧
    (334349/1744896 : ℝ) < variance 8 (fun S => sampleCov S (leverage leveragePopulation) leverageY) := by
  refine ⟨GP005B4b_T3_standardized, GP005B4b_T3_interacted_regular, GP005B4b_T3_noninteracted_regular,
    ?_, ?_, ?_, ?_, GP005B4b_T3_design_card, GP005B4b_T3_kappa_value, GP005B4b_T3_hy_constant,
    GP005B4b_T3_variance_value, GP005B4b_T3_bound_value, ?_, GP005B4b_T3_second_bound_value, ?_⟩
  · norm_num [popMean, mean, GP005B4b_T3_univ16, leverageY]
  · norm_num [leveragePopulation, scalarPopulation, popMean, mean]
  · norm_num [pT]
  · norm_num [pT]
  · rw [GP005B4b_T3_bound_value, GP005B4b_T3_variance_value]
    norm_num
  · rw [GP005B4b_T3_variance_value]
    norm_num

end
end AronowAudit.P005.Wave1
