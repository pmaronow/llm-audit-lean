import SAP.P042.Bridge.Part1

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P042.Bridge

noncomputable section
open SAP.P042 Finset MeasureTheory ProbabilityTheory
open scoped BigOperators ProbabilityTheory Classical

/-- The rational pooled contrast and the integer numerator represent the same real number. -/
theorem binomialPooled_cast (x0 x1 x2 : Fin 101) :
    (SAP.P042.binomialPooled x0 x1 x2 : ℝ) =
      (((x1.val:ℤ)+(x2.val:ℤ)-2*(x0.val:ℤ):ℤ):ℝ)/200 := by
  simp only [SAP.P042.binomialPooled, SAP.P042.binomialD1, SAP.P042.binomialD2,
    Rat.cast_div, Rat.cast_add, Rat.cast_sub, Rat.cast_natCast,
    Rat.cast_ofNat, Int.cast_sub, Int.cast_add, Int.cast_mul, Int.cast_natCast,
    Int.cast_ofNat]
  ring

/-- Substitute that representation into the existing two interval equivalences. -/
theorem binomial_thresholds (x0 x1 x2 : Fin 101) :
    let q : ℤ := (x1.val:ℤ)+(x2.val:ℤ)-2*(x0.val:ℤ)
    (coversZero (SAP.P042.binomialPooled x0 x1 x2 : ℝ) (49/500) ↔ |q| ≤ 19) ∧
    (coversZero (SAP.P042.binomialPooled x0 x1 x2 : ℝ)
      ((49/25)*Real.sqrt (3/800)) ↔ |q| ≤ 24) := by
  have h := AronowAudit.P042.binomial_interval_thresholds x0 x1 x2
  exact ⟨by simpa only [binomialPooled_cast, coversZero_eq] using h.1,
    by simpa only [binomialPooled_cast, coversZero_eq] using h.2.1⟩

/-- The nominal interval event is the already certified threshold-19 event. -/
theorem binomial_nominal_coverage :
    SAP.P042.binomialTripleExpectation (fun x0 x1 x2 =>
      if coversZero (SAP.P042.binomialPooled x0 x1 x2 : ℝ)
        ((49/25)*Real.sqrt (1/400)) then 1 else 0) = SAP.P042.binomialCoverage 19 := by
  classical
  have he : (fun x0 x1 x2 : Fin 101 =>
      if coversZero (SAP.P042.binomialPooled x0 x1 x2 : ℝ)
        ((49/25)*Real.sqrt (1/400)) then (1:ℚ) else 0) =
      SAP.P042.binomialCountEvent 19 := by
    funext x0 x1 x2
    rw [AronowAudit.P042.binomial_diagonal_radius, (binomial_thresholds x0 x1 x2).1]
    unfold SAP.P042.binomialCountEvent
    norm_num only [Nat.cast_ofNat]
    split_ifs <;> rfl
  rw [he]
  rw [binomialTripleExpectation_eq, binomialCoverage_eq]
  exact AronowAudit.P042.Wave1.binomial_coverage_from_arms_proof 19

/-- The true-variance interval event is the already certified threshold-24 event. -/
theorem binomial_true_coverage :
    SAP.P042.binomialTripleExpectation (fun x0 x1 x2 =>
      if coversZero (SAP.P042.binomialPooled x0 x1 x2 : ℝ)
        ((49/25)*Real.sqrt (3/800)) then 1 else 0) = SAP.P042.binomialCoverage 24 := by
  classical
  have he : (fun x0 x1 x2 : Fin 101 =>
      if coversZero (SAP.P042.binomialPooled x0 x1 x2 : ℝ)
        ((49/25)*Real.sqrt (3/800)) then (1:ℚ) else 0) =
      SAP.P042.binomialCountEvent 24 := by
    funext x0 x1 x2
    rw [(binomial_thresholds x0 x1 x2).2]
    unfold SAP.P042.binomialCountEvent
    norm_num only [Nat.cast_ofNat]
    split_ifs <;> rfl
  rw [he]
  rw [binomialTripleExpectation_eq, binomialCoverage_eq]
  exact AronowAudit.P042.Wave1.binomial_coverage_from_arms_proof 24

theorem robo_fixed_exact : RoboFixedExact := AronowAudit.P042.robo_fixed_exact

/-- The extra displayed forms for Q and C follow by rational arithmetic on the exported values. -/
theorem robo_random_exact : RoboRandomExact := by
  rcases AronowAudit.P042.robo_random_exact with ⟨hQ, hQ1, hC, hTau, h0, h1, hM, hV⟩
  refine ⟨?_, hQ, hQ1, ?_, hC, hTau, h0, h1, hM, hV⟩
  · rw [roboQ_eq, hQ]
    norm_num [SAP.P042.roboEffects, SAP.P042.roboVariances, SAP.P042.roboSE]
  · rw [roboC_eq, hC]
    norm_num [SAP.P042.roboVariances, SAP.P042.roboSE]

theorem robo_random_rounding : RoboRandomRounding :=
  ⟨AronowAudit.P042.robo_random_rounding, AronowAudit.P042.robo_random_interval⟩

/-- Instantiate the existing uncorrelated precision-variance identity on the two fixed variances. -/
theorem robo_stochastic_variance : RoboStochasticVariance := by
  intro Ω _ μ _ D hD hv hc
  have hpos : ∀ j, 0 < variance (D j) μ := by
    intro j
    rw [hv j]
    fin_cases j <;> norm_num [SAP.P042.roboVariances, SAP.P042.roboSE]
  have hunc : ∀ j k, j ≠ k → covariance (D j) (D k) μ = 0 := by
    intro j k hjk
    fin_cases j <;> fin_cases k
    · exact (hjk rfl).elim
    · exact hc
    · rw [covariance_comm]
      exact hc
    · exact (hjk rfl).elim
  have hvf : (fun j => variance (D j) μ) = SAP.P042.roboVariances := funext hv
  simpa only [hvf, SAP.P042.roboFixedVariance, pooled_eq, normalizedWeight_eq,
    totalWeight_eq] using
    AronowAudit.P042.uncorrelated_precision_variance μ (by norm_num : 0 < 2) D hD hpos hunc

end
end SAP.P042.Bridge
