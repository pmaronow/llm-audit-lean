import AronowAudit.P018.Wave1.Gap.TailBSignExtra
import AronowAudit.P018.Wave1.Gap.TailBSignInference

/-! P018-T7: the exact bounded-sign degenerate-inference counterexample. -/

namespace AronowAudit.P018.Wave1
open TailBSign

open Filter Finset Matrix MeasureTheory ProbabilityTheory in
open scoped BigOperators BoundedContinuousFunction ENNReal Matrix.Norms.Elementwise Topology in
/-- The bounded two-sign model has zero leading slope variance and a
non-Gaussian slope pivot, although absolute sandwich consistency holds
(T7(a),(b),(d), pp. 565--567,571). -/
theorem TailB_degenerate_inference_counterexample :
    (Standing signPairKernel ∧ Proposition1Extra signPairKernel ∧
    populationGram signPairKernel = !![1,1;1,2] ∧ populationBeta signPairKernel = 0 ∧
    projectionGamma signPairKernel = !![1,1;1,1] ∧ limitingTarget signPairKernel = !![4,0;0,0] ∧
    (∀ N : ℕ, 3 ≤ N → trueTarget signPairKernel N =
      !![4*(N : ℝ)/((N : ℝ)-1),-4/((N : ℝ)-1);-4/((N : ℝ)-1),4/((N : ℝ)-1)]) ∧
    Tendsto (fun N : ℕ => (unitSampleLaw signPairKernel N {ω |
      (sampleVariance members (design signPairKernel ω) (response signPairKernel ω)) 1 1 < 0}).toReal)
      atTop (𝓝 (1-Real.exp (-1/2))) ∧
    ¬weakLimit (unitSampleLaw signPairKernel) (fun N ω =>
      coefficientError signPairKernel ω 1 /
        Real.sqrt ((sampleVariance members (design signPairKernel ω) (response signPairKernel ω)) 1 1))
        (gaussianReal 0 1) ∧
    inProbability (unitSampleLaw signPairKernel) (fun N ω =>
      (N : ℝ) • sampleVariance members (design signPairKernel ω) (response signPairKernel ω) - (!![4,0;0,0] : Mat 2))) := by
  exact ⟨tb05_standing, tb05_proposition_extra, tb05_population_gram, tb05_population_beta,
    tb05_projection_gamma, tb05_limiting_target, fun N hN => tb05_true_target hN,
    tb05_negative_variance_probability, tb05_pivot_not_normal, tb05_absolute_consistency⟩

end AronowAudit.P018.Wave1
