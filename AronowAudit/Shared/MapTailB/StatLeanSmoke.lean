import AronowAudit.External.StatLean.AsymptoticStatistics.LowerBounds.T6_FinDimLAN.NondominatedQMDLeCamThird

/-! Local score central limit theorem and contiguity for nondominated QMD paths. -/

open MeasureTheory Filter ProbabilityTheory
open scoped InnerProductSpace RealInnerProductSpace

open AsymptoticStatistics
open AsymptoticStatistics.Core.Hilbert
open AsymptoticStatistics.Core.NondominatedQMDPath
open AsymptoticStatistics.LowerBounds.T6_FinDimLAN.NondominatedQMDLeCamThird

theorem TailB_qmd_local_score_clt
    {E : Type*} [MeasurableSpace E] {P : Measure E} [IsProbabilityMeasure P]
    (γ : NondominatedQMDPath P) (a : ℝ) (ha : 0 ≤ a) (u : ↥(L2ZeroMean P)) :
    AsymptoticStatistics.WeakConverges
      (fun n => (Measure.pi (fun _ : Fin n =>
        γ.curve (a * (Real.sqrt n)⁻¹))).map (normalizedScoreSum u n))
      (gaussianReal (a * ⟪u, γ.score⟫_ℝ)
        (NNReal.mk (‖u‖^2) (sq_nonneg _))) := by
  exact qmd_local_score_clt γ a ha u

theorem TailB_qmd_local_contiguous
    {E : Type*} [MeasurableSpace E] {P : Measure E} [IsProbabilityMeasure P]
    (γ : NondominatedQMDPath P) (a : ℝ) (ha : 0 ≤ a) :
    AsymptoticStatistics.Contiguity.Contiguous atTop
      (fun n => Measure.pi (fun _ : Fin n => P))
      (fun n => Measure.pi (fun _ : Fin n => γ.curve (a * (Real.sqrt n)⁻¹))) := by
  exact qmd_local_contiguous γ a ha

