import AronowAudit.P018.Wave1.WeightedConsistencyBlueprint

set_option autoImplicit false

namespace AronowAudit.P018.Wave1.WeightedConsistency

open AronowAudit.P018 Finset Matrix MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology BoundedContinuousFunction Matrix.Norms.Elementwise ENNReal

universe u

noncomputable section

/-- A finite union of events with vanishing probabilities has vanishing probability. -/
theorem probability_finite_union_null {Ω : ℕ → Type u} [∀ N, MeasurableSpace (Ω N)]
    (μ : ∀ N, Measure (Ω N)) [∀ N, IsProbabilityMeasure (μ N)]
    {ι : Type*} [Fintype ι] (s : ∀ N, ι → Set (Ω N))
    (h : ∀ i, Tendsto (fun N => (μ N (s N i)).toReal) atTop (𝓝 0)) :
    Tendsto (fun N => (μ N (⋃ i, s N i)).toReal) atTop (𝓝 0) := by
  classical
  apply squeeze_zero (fun _ => ENNReal.toReal_nonneg) _
    (by simpa using tendsto_finsetSum univ (fun i _ => h i))
  intro N
  calc
    _ ≤ (∑ i, μ N (s N i)).toReal :=
      ENNReal.toReal_mono (ENNReal.sum_ne_top.mpr (fun _ _ => measure_ne_top _ _)) (measure_iUnion_fintype_le (μ N) (s N))
    _ = ∑ i, (μ N (s N i)).toReal := ENNReal.toReal_sum (fun _ _ => measure_ne_top _ _)

/-- Scalar Chebyshev convergence, without a measurability condition on a deviation set. -/
theorem centered_scalar_probability {Ω : ℕ → Type u} [∀ N, MeasurableSpace (Ω N)]
    (μ : ∀ N, Measure (Ω N)) [∀ N, IsProbabilityMeasure (μ N)]
    (F : ∀ N, Ω N → ℝ) (hF : ∀ N, MemLp (F N) 2 (μ N))
    (hvar : Tendsto (fun N => variance (F N) (μ N)) atTop (𝓝 0)) :
    inProbability μ (fun N ω => F N ω - ∫ ω, F N ω ∂μ N) := by
  intro ε hε
  apply squeeze_zero (fun _ => ENNReal.toReal_nonneg) _
    (by simpa using hvar.div_const (ε ^ 2))
  intro N
  calc
    _ ≤ (ENNReal.ofReal (variance (F N) (μ N) / ε ^ 2)).toReal :=
      ENNReal.toReal_mono ENNReal.ofReal_ne_top (meas_ge_le_variance_div_sq (hF N) hε)
    _ = _ := ENNReal.toReal_ofReal (div_nonneg (variance_nonneg _ _) (sq_nonneg _))

theorem g5_proof : G5.{u} := by
  classical
  intro Ω _ k μ _
  constructor
  · intro F hF hvar ε hε
    have hscalar (a b : Fin k) :=
      centered_scalar_probability μ (fun N ω => F N ω a b)
        (fun N => hF N a b) (hvar a b) ε hε
    have hUnion := probability_finite_union_null μ
      (fun N (ab : Fin k × Fin k) =>
        {ω | ε ≤ |F N ω ab.1 ab.2 - ∫ ω, F N ω ab.1 ab.2 ∂μ N|})
      (fun ab => hscalar ab.1 ab.2)
    apply squeeze_zero (fun _ => ENNReal.toReal_nonneg) _ hUnion
    intro N
    apply ENNReal.toReal_mono (measure_ne_top _ _)
    apply measure_mono
    intro ω hω
    by_contra hn
    have hcoord : ∀ a b, ‖(F N ω - meanMat (μ N) (F N)) a b‖ < ε := by
      intro a b
      apply lt_of_not_ge
      intro hab
      apply hn
      exact Set.mem_iUnion.mpr ⟨(a, b), hab⟩
    have hnrm : ‖F N ω - meanMat (μ N) (F N)‖ < ε :=
      (pi_norm_lt_iff hε).mpr (fun a => (pi_norm_lt_iff hε).mpr (hcoord a))
    exact (not_le.mpr hnrm) hω
  · intro F hF hvar ε hε
    have hscalar (a : Fin k) :=
      centered_scalar_probability μ (fun N ω => F N ω a)
        (fun N => hF N a) (hvar a) ε hε
    have hUnion := probability_finite_union_null μ
      (fun N a => {ω | ε ≤ |F N ω a - ∫ ω, F N ω a ∂μ N|}) hscalar
    apply squeeze_zero (fun _ => ENNReal.toReal_nonneg) _ hUnion
    intro N
    apply ENNReal.toReal_mono (measure_ne_top _ _)
    apply measure_mono
    intro ω hω
    by_contra hn
    have hcoord : ∀ a, ‖(F N ω - meanVec (μ N) (F N)) a‖ < ε := by
      intro a
      apply lt_of_not_ge
      intro ha
      exact hn (Set.mem_iUnion.mpr ⟨a, ha⟩)
    exact (not_le.mpr ((pi_norm_lt_iff hε).mpr hcoord)) hω

end
end AronowAudit.P018.Wave1.WeightedConsistency
