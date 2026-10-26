import AronowAudit.P011.P011_DenseInfrastructure
import AronowAudit.P011.P011_DenseCumulant
import AronowAudit.P011.P011_DenseContractionBound

/-! An actual bounded, centered dependency-graph quadratic variance bound.
The entrywise covariance and cumulant support estimates are derived from the
probability law and genuine dependency graph, not assumed variance inequalities. -/
namespace AronowAudit.P011.DenseCenteredVariance
open MeasureTheory ProbabilityTheory Filter
open Causalean.Mathlib.Probability.SteinMethod
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

/-- A deterministic symmetric quadratic form of genuinely graph-dependent,
centered bounded coordinates has variance of order n times squared operator norm. -/
theorem centered_variance_bound {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Z : Fin n → Ω → ℝ)
    (D : DepGraph Z μ) (hz : ∀ i, ∫ ω, Z i ω ∂μ = 0)
    (B : ℝ) (hB : 0 ≤ B) (hb : ∀ i, ∀ᵐ ω ∂μ, |Z i ω| ≤ B)
    (d : ℝ) (hd : 0 ≤ d)
    (hrow : ∀ i, (∑ j, if D.G i j then (1 : ℝ) else 0) ≤ d)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsSymm) :
    ProbabilityTheory.variance (fun ω => ∑ i, ∑ j, A i j * Z i ω * Z j ω) μ ≤
      (144 * d^3 + 2 * d^2) * B^4 * (operatorNorm A)^2 * (n : ℝ) := by
  rw [DenseCumulant.variance_expansion μ Z D.meas B hB hb A]
  have h := DenseContractionBound.dense_contraction_bound D.G
    (fun {_ _} h => D.symm _ _ h) d B (operatorNorm A) hd hB (norm_nonneg _) hrow
    A (DenseCumulant.pairMean μ Z) (DenseCumulant.cumulant4 μ Z)
    (fun i j => (hA.apply i j).symm)
    (DenseCompletion.entry_le_operatorNorm A)
    (by simpa only [Fintype.card_fin] using DenseCompletion.frobenius_sq_le_size_operatorNorm_sq A)
    (fun i j => DenseCumulant.pair_graph_bound μ Z D hz B hB hb i j)
    (DenseCumulant.cumulant_connected_bound μ Z D hz B hB hb)
  simpa only [Fintype.card_fin] using h

end
end AronowAudit.P011.DenseCenteredVariance
