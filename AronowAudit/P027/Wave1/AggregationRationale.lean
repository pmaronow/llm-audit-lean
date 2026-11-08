import AronowAudit.P027.Wave1.AggregationRationaleBlueprint
import AronowAudit.P027.Wave1.AggregationRationale.N1
import AronowAudit.P027.Wave1.AggregationRationale.N2

namespace AronowAudit.P027.Wave1

set_option autoImplicit false
noncomputable section
open AronowAudit.P027
attribute [local instance] Classical.propDecidable

/-- Refutes the labelled universal aggregation rationale: all exponents equal to
two give actual conservative-estimator biases eight before totalling and nine
after totalling. This makes no assertion about the printed hedged tendency. -/
theorem aggregation_rationale_counterexample :
    ¬ (∀ {Ω : Type} [Fintype Ω] {G : Type} [Fintype G] (D : Design G Ω), Positive D →
        ∀ (n : G → ℕ), (∀ g, 0 < n g) →
        ∀ (y : (Σ g, Fin (n g)) → ℝ)
          (a b : (Σ g, Fin (n g)) → (Σ g, Fin (n g)) → ℝ) (ac bc : G → G → ℝ),
        (∀ k l, k ≠ l ∧ joint (liftDesign D n) k l = 0 →
          (a k l).HolderConjugate (b k l)) →
        (∀ g h, g ≠ h ∧ joint D g h = 0 → (ac g h).HolderConjugate (bc g h)) →
        expect D (conservativeEstimator D (groupTotal n y) ac bc) -
            variance D (htTotal D (groupTotal n y)) ≤
          expect (liftDesign D n) (conservativeEstimator (liftDesign D n) y a b) -
            variance (liftDesign D n) (htTotal (liftDesign D n) y)) := by
  exact AronowAudit.P027.Wave1.AggregationRationale.assemble
    AronowAudit.P027.Wave1.AggregationRationale.n1_proof
    AronowAudit.P027.Wave1.AggregationRationale.n2_proof

example : AronowAudit.P027.Wave1.AggregationRationale.Target :=
  aggregation_rationale_counterexample

end
end AronowAudit.P027.Wave1
