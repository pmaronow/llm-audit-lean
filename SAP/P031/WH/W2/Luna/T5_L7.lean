import SAP.P031.WH.W2.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators Topology
open Filter Finset
open SAP.P031 SAP.P031.Bridge SAP.P031.WH.W2

noncomputable section
namespace SAP.P031.WH.W2.Luna

theorem T5_L7_solution : T5_L7 := by
  intro P A c hNormal hc hRatio z hz
  let Q : ℕ → AronowAudit.P031.Population := fun n => Bridge.toPopulation (P n)
  let V : AronowAudit.P031.VarianceEstimator := fun R s => A (Bridge.fromPopulation R) s
  let X : AronowAudit.P031.VarianceEstimator := fun R s =>
    V R s / AronowAudit.P031.trueVariance R
  let W : AronowAudit.P031.VarianceEstimator := fun R s =>
    (AronowAudit.P031.pointEstimate R s - AronowAudit.P031.populationEffect R) /
      Real.sqrt (AronowAudit.P031.trueVariance R)
  let R : AronowAudit.P031.VarianceEstimator := fun R s => z * Real.sqrt (X R s)
  let t : ℝ := z * Real.sqrt c
  have hNormal' : AronowAudit.P031.StandardizedNormalLimit Q := by
    constructor
    · simpa only [Q, Bridge.trueVariance_eq] using hNormal.1
    · intro x
      have h := hNormal.2 x
      apply h.congr
      intro n
      change eventProbability (P n) _ =
        AronowAudit.P031.eventProbability (Bridge.toPopulation (P n)) _
      rw [← Bridge.eventProbability_eq]
      rfl
  have hRatio' : AronowAudit.P031.ConvergesInProbability Q X c := by
    intro ε hε
    have h := hRatio ε hε
    apply h.congr
    intro n
    change eventProbability (P n) _ =
      AronowAudit.P031.eventProbability (Bridge.toPopulation (P n)) _
    rw [← Bridge.eventProbability_eq]
    congr 2
  have hR : AronowAudit.P031.ConvergesInProbability Q R t := by
    simpa only [R, t, X] using
      AronowAudit.P031.Wave1.T6_continuous_probability Q X c hRatio'
        (fun x => z * Real.sqrt x) (Real.continuous_sqrt.continuousAt.const_mul z)
  have hNegR : AronowAudit.P031.ConvergesInProbability Q (fun U s => -R U s) (-t) := by
    simpa only [R, t] using
      AronowAudit.P031.Wave1.T6_continuous_probability Q R t hR
        (fun x => -x) continuous_neg.continuousAt
  have hUpper := AronowAudit.P031.Wave1.T6_random_cdf Q W R t hNormal'.2 hR
    (fun U s => W U s ≤ R U s) (fun _ _ h => h.le) (fun _ _ h => h)
  have hLower := AronowAudit.P031.Wave1.T6_random_cdf Q W (fun U s => -R U s) (-t)
    hNormal'.2 hNegR (fun U s => W U s < -R U s) (fun _ _ h => h) (fun _ _ h => h.le)
  have hlim := hUpper.sub hLower
  have hsym : AronowAudit.P031.normalCDF (-t) = 1 - AronowAudit.P031.normalCDF t := by
    change ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1) (-t) =
      1 - ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1) t
    exact AronowAudit.P053.NormalCompletion.normal_cdf_neg t
  rw [hsym] at hlim
  have hq : AronowAudit.P031.normalCDF t - (1 - AronowAudit.P031.normalCDF t) =
      2 * AronowAudit.P031.normalCDF t - 1 := by ring
  rw [hq] at hlim
  have hmass : ∀ᶠ n in atTop,
      AronowAudit.P031.eventProbability (Q n) (fun s => W (Q n) s ≤ R (Q n) s) -
        AronowAudit.P031.eventProbability (Q n) (fun s => W (Q n) s < -R (Q n) s) =
          AronowAudit.P031.coverage (Q n) V z := by
    filter_upwards [hNormal'.1] with n hn
    unfold AronowAudit.P031.coverage AronowAudit.P031.eventProbability
    rw [← AronowAudit.P031.expectation_sub]
    apply AronowAudit.P031.expectation_congr
    intro s _
    change ((if W (Q n) s ≤ R (Q n) s then (1 : ℝ) else 0) -
      (if W (Q n) s < -R (Q n) s then 1 else 0)) =
      if |AronowAudit.P031.pointEstimate (Q n) s -
          AronowAudit.P031.populationEffect (Q n)| ≤
        z * Real.sqrt (V (Q n) s) then 1 else 0
    have hr : 0 ≤ R (Q n) s := mul_nonneg hz.le (Real.sqrt_nonneg _)
    have hsqrt : 0 < Real.sqrt (AronowAudit.P031.trueVariance (Q n)) :=
      Real.sqrt_pos.mpr hn
    have hevent :
        (|AronowAudit.P031.pointEstimate (Q n) s -
          AronowAudit.P031.populationEffect (Q n)| ≤ z * Real.sqrt (V (Q n) s)) ↔
        |W (Q n) s| ≤ R (Q n) s := by
      dsimp only [W, R, X]
      rw [abs_div, abs_of_pos hsqrt, Real.sqrt_div' _ hn.le]
      rw [← mul_div_assoc, div_le_div_iff_of_pos_right hsqrt]
    have hi : (|W (Q n) s| ≤ R (Q n) s) ↔
        (W (Q n) s ≤ R (Q n) s ∧ ¬ W (Q n) s < -R (Q n) s) := by
      rw [abs_le]
      constructor
      · intro h
        exact ⟨h.2, not_lt.mpr h.1⟩
      · intro h
        exact ⟨le_of_not_gt h.2, h.1⟩
    simp only [hevent, hi]
    by_cases h2 : W (Q n) s < -R (Q n) s
    · have h1 : W (Q n) s ≤ R (Q n) s := by linarith
      simp [h1, h2]
    · by_cases h1 : W (Q n) s ≤ R (Q n) s <;> simp [h1, h2]
  have hCov : Tendsto (fun n => AronowAudit.P031.coverage (Q n) V z) atTop
      (𝓝 (2 * AronowAudit.P031.normalCDF t - 1)) := hlim.congr' hmass
  have hCovLocal : Tendsto (fun n => coverage (P n) A z) atTop
      (𝓝 (2 * normalCDF t - 1)) := by
    apply hCov.congr
    intro n
    rfl
  have hsqrt : 1 ≤ Real.sqrt c := by
    apply Real.le_sqrt_of_sq_le
    norm_num
    exact hc
  have ht : z ≤ t := by
    dsimp [t]
    nlinarith
  have hPhi := ProbabilityTheory.monotone_cdf (ProbabilityTheory.gaussianReal 0 1) ht
  have hNominal : 2 * normalCDF z - 1 ≤ 2 * normalCDF t - 1 := by
    change AronowAudit.P031.normalCDF z ≤ AronowAudit.P031.normalCDF t at hPhi
    change 2 * AronowAudit.P031.normalCDF z - 1 ≤
      2 * AronowAudit.P031.normalCDF t - 1
    linarith
  intro ε hε
  have hClose := Metric.tendsto_nhds.mp hCovLocal ε hε
  filter_upwards [hClose] with n hn
  rw [Real.dist_eq, abs_lt] at hn
  change 2 * normalCDF z - 1 - ε ≤ coverage (P n) A z
  linarith [hn.1, hNominal]

example : T5_L7 := T5_L7_solution

#print axioms T5_L7_solution

end SAP.P031.WH.W2.Luna
end
