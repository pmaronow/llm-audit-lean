import SAP.P027b.Defs.Part2

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P027b
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- Proposition 1, its same-sign consequence, and existence of both signs of bias. -/
def T20Statement : Prop :=
  (∀ (U Ω : Type) [Fintype U] [Fintype Ω] (D : Design U Ω), Positive D →
    ∀ y : U → ℝ,
      expect D (htVarianceEstimator D y) = variance D (htTotal D y) + biasA D y ∧
      (((∀ k, 0 ≤ y k) ∨ (∀ k, y k ≤ 0)) →
        0 ≤ biasA D y ∧ 0 ≤ expect D (htVarianceEstimator D y) - variance D (htTotal D y))) ∧
  (∃ (D : Design (Fin 3) (Fin 2)) (yPos yNeg : Fin 3 → ℝ), Positive D ∧
    0 < biasA D yPos ∧ biasA D yNeg < 0 ∧
    0 < expect D (htVarianceEstimator D yPos) - variance D (htTotal D yPos) ∧
    expect D (htVarianceEstimator D yNeg) - variance D (htTotal D yNeg) < 0)

/-- Proposition 2 with the correction's expectation and the two bias bounds. -/
def T21Statement : Prop :=
  ∀ (U Ω : Type) [Fintype U] [Fintype Ω] (D : Design U Ω), Positive D →
    ∀ (y : U → ℝ) (a b : U → U → ℝ),
      (∀ k l, k ≠ l ∧ joint D k l = 0 → (a k l).HolderConjugate (b k l)) →
      biasA D y ≤ youngA D y a b ∧ -biasA D y ≤ youngA D y a b ∧
      expect D (youngCorrection D y a b) = youngA D y a b ∧
      expect D (conservativeEstimator D y a b) =
        variance D (htTotal D y) + biasA D y + youngA D y a b ∧
      variance D (htTotal D y) ≤ expect D (conservativeEstimator D y a b)

/-- The printed sufficient conditions for equality in Proposition 2. -/
def T22Statement : Prop :=
  ∀ (U Ω : Type) [Fintype U] [Fintype Ω] (D : Design U Ω), Positive D →
    ∀ (y : U → ℝ) (a b : U → U → ℝ),
      (∀ k l, k ≠ l ∧ joint D k l = 0 → (a k l).HolderConjugate (b k l)) →
      (∀ k l, k ≠ l ∧ joint D k l = 0 → |y k| ^ (a k l) = |y l| ^ (b k l)) →
      (∀ k l, k ≠ l ∧ joint D k l = 0 → -y k * y l = |y k| * |y l|) →
      expect D (conservativeEstimator D y a b) = variance D (htTotal D y)

/-- The quadratic specialization and its conservativeness. -/
def T23Statement : Prop :=
  ∀ (U Ω : Type) [Fintype U] [Fintype Ω] (D : Design U Ω), Positive D →
    ∀ y : U → ℝ,
      c2Estimator D y = conservativeEstimator D y (fun _ _ => 2) (fun _ _ => 2) ∧
      variance D (htTotal D y) ≤ expect D (c2Estimator D y)

/-- Attainment and the samplewise comparison with every constant conjugate pair. -/
def T24Statement : Prop :=
  ∀ (U Ω : Type) [Fintype U] [Fintype Ω] (D : Design U Ω), Positive D →
    ∀ (y : U → ℝ) (ω : Ω),
      conservativeEstimator D y (fun _ _ => 2) (fun _ _ => 2) ω = c2Estimator D y ω ∧
      ∀ a b : ℝ, a.HolderConjugate b →
        c2Estimator D y ω ≤ conservativeEstimator D y (fun _ _ => a) (fun _ _ => b) ω

end
end SAP.P027b
