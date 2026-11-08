import SAP.P009a.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P009a.WH.W1.P.T1_L2

open Filter MeasureTheory Bridge
open scoped BigOperators Topology Classical

noncomputable section

theorem sparse_dispersion_sq (t : ℕ) :
    dispersionOfVariances (sparseSequence.experiment t) ^ 2 =
      (sampleSize sparseSequence t - 1) / sampleSize sparseSequence t ^ 2 := by
  exact AronowAudit.P009.Wave1.sparseCoverage_sdSigmaSq t

theorem sparse_msq (t : ℕ) :
    meanSquaredEffect (sparseSequence.experiment t) = 1 / sampleSize sparseSequence t := by
  exact AronowAudit.P009.Wave1.sparseCoverage_msq t

theorem sparse_dispersion_sq_tendsto :
    Tendsto (fun t => dispersionOfVariances (sparseSequence.experiment t) ^ 2)
      atTop (nhds 0) := by
  have hinv := SAP.P009a.WH.W1.sparse_inverse_limit
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hinv
  · intro t
    change 0 ≤ dispersionOfVariances (sparseSequence.experiment t) ^ 2
    rw [sparse_dispersion_sq]
    have hn : 0 < sampleSize sparseSequence t := by
      change (0 : ℝ) < (t + 1 : ℕ)
      positivity
    have hnum : 0 ≤ sampleSize sparseSequence t - 1 := by
      change (0 : ℝ) ≤ ((t + 1 : ℕ) : ℝ) - 1
      push_cast
      nlinarith
    exact div_nonneg hnum (sq_nonneg _)
  · intro t
    change dispersionOfVariances (sparseSequence.experiment t) ^ 2 ≤
      1 / sampleSize sparseSequence t
    rw [sparse_dispersion_sq]
    have hn : 0 < sampleSize sparseSequence t := by
      change (0 : ℝ) < (t + 1 : ℕ)
      positivity
    calc
      (sampleSize sparseSequence t - 1) / sampleSize sparseSequence t ^ 2 ≤
          sampleSize sparseSequence t / sampleSize sparseSequence t ^ 2 := by
        apply div_le_div_of_nonneg_right
        · linarith
        · positivity
      _ = 1 / sampleSize sparseSequence t := by
        field_simp [ne_of_gt hn]

theorem sparse_dispersion_tendsto :
    Tendsto (fun t => dispersionOfVariances (sparseSequence.experiment t))
      atTop (nhds 0) := by
  have hrepr : (fun t => dispersionOfVariances (sparseSequence.experiment t)) =
      (fun t => Real.sqrt (dispersionOfVariances (sparseSequence.experiment t) ^ 2)) := by
    funext t
    exact (Real.sqrt_sq (Real.sqrt_nonneg _)).symm
  rw [hrepr]
  have h := (Real.continuous_sqrt.continuousAt.tendsto).comp sparse_dispersion_sq_tendsto
  simpa [Function.comp_def] using h

theorem sparse_root_inverse_tendsto :
    Tendsto (fun t => 1 / Real.sqrt (sampleSize sparseSequence t)) atTop (nhds 0) := by
  have h := (Real.continuous_sqrt.continuousAt.tendsto).comp
    SAP.P009a.WH.W1.sparse_inverse_limit
  have heq : (fun t => Real.sqrt (1 / sampleSize sparseSequence t)) =
      (fun t => 1 / Real.sqrt (sampleSize sparseSequence t)) := by
    funext t
    rw [Real.sqrt_div' (1 : ℝ) (le_of_lt (by
      change (0 : ℝ) < (t + 1 : ℕ)
      positivity)), Real.sqrt_one]
  rw [← heq]
  simpa [Function.comp_def] using h

end
end SAP.P009a.WH.W1.P.T1_L2

namespace SAP.P009a.WH.W1

open Filter MeasureTheory Bridge
open SAP.P009a.WH.W1.P.T1_L2
open scoped BigOperators Topology Classical

noncomputable section

theorem T1_L2_proof : T1_L2 := by
  unfold T1_L2 SAP.P009a.W1SparseRates
  have hgraph (t : ℕ) :
      averageDependence (sparseSequence.experiment t) = 1 ∧
      maximumDependence (sparseSequence.experiment t) = 1 ∧
      rmsDependence (sparseSequence.experiment t) = 1 ∧
      spectralRadius (sparseSequence.experiment t) = 1 := by
    exact AronowAudit.P009.Wave1.sparseCoverage_graph t
  have hdispSq := sparse_dispersion_sq_tendsto
  have hdisp := sparse_dispersion_tendsto
  have hroot := sparse_root_inverse_tendsto
  have hmsq : Tendsto (fun t => meanSquaredEffect (sparseSequence.experiment t))
      atTop (nhds 0) := by
    have heq : (fun t => meanSquaredEffect (sparseSequence.experiment t)) =
        (fun t => 1 / sampleSize sparseSequence t) := by
      funext t
      exact sparse_msq t
    rw [heq]
    exact SAP.P009a.WH.W1.sparse_inverse_limit
  refine ⟨hdispSq, hdisp, ?_, ?_, ?_, ?_, ?_⟩
  · intro t
    rcases hgraph t with ⟨havg, hmax, hrms, hspec⟩
    constructor
    · rw [havg, hrms]
      norm_num
    constructor
    · rw [hmax, havg]
      simp
    · rw [hspec, havg]
      simp
  · change Tendsto
      (fun t => dispersionOfVariances (sparseSequence.experiment t) /
        (averageDependence (sparseSequence.experiment t) /
          rmsDependence (sparseSequence.experiment t))) atTop (nhds 0)
    have heq : (fun t => dispersionOfVariances (sparseSequence.experiment t) /
        (averageDependence (sparseSequence.experiment t) /
          rmsDependence (sparseSequence.experiment t))) =
        (fun t => dispersionOfVariances (sparseSequence.experiment t)) := by
      funext t
      rcases hgraph t with ⟨havg, _, hrms, _⟩
      simp [havg, hrms]
    rw [heq]
    exact hdisp
  · apply (tendsto_congr' ?_).2 hroot
    filter_upwards with t
    rcases hgraph t with ⟨havg, hmax, _, _⟩
    simp [havg, hmax]
  · apply (tendsto_congr' ?_).2 hroot
    filter_upwards with t
    rcases hgraph t with ⟨havg, _, _, hspec⟩
    simp [havg, hspec]
  · intro hpos
    rcases hpos with ⟨c, hc, hevent⟩
    have hsmall : ∀ᶠ t in atTop,
        meanSquaredEffect (sparseSequence.experiment t) < c :=
      hmsq (Iio_mem_nhds hc)
    obtain ⟨t, htSmall, htLarge⟩ := (hsmall.and hevent).exists
    exact (not_le_of_gt htSmall) htLarge

end
end SAP.P009a.WH.W1
