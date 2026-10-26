import AronowAudit.P031.Wave1.LargeSampleRefutationBlueprint

/-! The quarter-relative-error probability tends to one, contradicting equivalence. -/

namespace AronowAudit.P031.Wave1.LargeSampleRefutation
noncomputable section
open scoped BigOperators Matrix Topology
open Filter MeasureTheory
attribute [local instance] Classical.propDecidable

theorem n17_proof : N17 := by
  intro hEC hError hTie hEquivalent
  have hEvent (n : ℕ) :
      eventProbability (hypercubePopulation n) (fun s =>
        (1 / 4 : ℝ) * |hc2Estimator (hypercubePopulation n) s| <
          |hrEstimator (hypercubePopulation n) s - hc2Estimator (hypercubePopulation n) s|) =
      1 - eventProbability (hypercubePopulation n)
        (fun s => ∃ i ∈ s, ∃ j ∈ s, i ≠ j ∧ hcQ n i = hcQ n j) := by
    calc
      _ = eventProbability (hypercubePopulation n)
          (fun s => ¬ ∃ i ∈ s, ∃ j ∈ s, i ≠ j ∧ hcQ n i = hcQ n j) := by
        unfold eventProbability
        apply expectation_congr
        intro s hs
        simp only [hError n s hs]
        congr
      _ = _ := (hEC (hypercubePopulation n)).2.2.2 _
  have hOne : Tendsto (fun n => eventProbability (hypercubePopulation n)
      (fun s => (1 / 4 : ℝ) * |hc2Estimator (hypercubePopulation n) s| <
        |hrEstimator (hypercubePopulation n) s - hc2Estimator (hypercubePopulation n) s|))
      atTop (nhds 1) := by
    have h := hTie.const_sub (1 : ℝ)
    simpa only [sub_zero] using h.congr (fun n => (hEvent n).symm)
  have hZero := hEquivalent (1 / 4) (by norm_num)
  have hImpossible : (0 : ℝ) = 1 := tendsto_nhds_unique hZero hOne
  norm_num at hImpossible

end
end AronowAudit.P031.Wave1.LargeSampleRefutation
