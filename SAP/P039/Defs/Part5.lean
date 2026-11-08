import SAP.P039.Defs.Part4

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P039
open scoped BigOperators Matrix NNReal
open MeasureTheory ProbabilityTheory

/-- Nested regressor geometry and the resulting conventional standard-error inequalities. -/
def NestedStandardErrorsStatement : Prop :=
  ∀ {n k₁ k₂ : ℕ}
    (Z₁ : Matrix (Fin n) (Fin k₁) ℝ) (Z₂ : Matrix (Fin n) (Fin k₂) ℝ)
    (q : Fin n → ℝ),
    (∀ a, ∃ b, Z₁ *ᵥ a = Z₂ *ᵥ b) →
    FullColumnRank (fullDesign Z₁ q) → FullColumnRank (fullDesign Z₂ q) →
    k₁+1 < n → k₂+1 < n →
let R₁ := olsSSE Z₁ q
    let R₂ := olsSSE Z₂ q
    (∃ a, IsLeastSquares Z₁ q a ∧ squaredLength (q-Z₁ *ᵥ a) = R₁) ∧
    (∃ a, IsLeastSquares Z₂ q a ∧ squaredLength (q-Z₂ *ᵥ a) = R₂) ∧
    0 < R₁ ∧ 0 < R₂ ∧ R₂ ≤ R₁ ∧
    ((fullDesign Z₁ q)ᵀ * fullDesign Z₁ q)⁻¹ (Fin.last k₁) (Fin.last k₁) = 1/R₁ ∧
    ((fullDesign Z₂ q)ᵀ * fullDesign Z₂ q)⁻¹ (Fin.last k₂) (Fin.last k₂) = 1/R₂ ∧
    (∀ y, 0 < olsSSE (fullDesign Z₁ q) y → 0 < olsSSE (fullDesign Z₂ q) y →
      let s₁ := Real.sqrt (olsSSE (fullDesign Z₁ q) y / ((n : ℝ)-k₁-1))
      let s₂ := Real.sqrt (olsSSE (fullDesign Z₂ q) y / ((n : ℝ)-k₂-1))
      let se₁ := Real.sqrt (olsSESquared (fullDesign Z₁ q) y (Fin.last k₁))
      let se₂ := Real.sqrt (olsSESquared (fullDesign Z₂ q) y (Fin.last k₂))
      se₁ = s₁ / Real.sqrt R₁ ∧ se₂ = s₂ / Real.sqrt R₂ ∧
      se₁/s₁ ≤ se₂/s₂ ∧ se₁ ≤ se₂*s₁/s₂)

/-- Closed rounding intervals for the four printed nested-fit cells cannot all hold. -/
def PrintedCellsImpossibleStatement : Prop :=
  ∀ (Z₁ : Matrix (Fin 17) (Fin 2) ℝ) (Z₂ : Matrix (Fin 17) (Fin 3) ℝ)
    (q y : Fin 17 → ℝ),
    (∀ a, ∃ b, Z₁ *ᵥ a = Z₂ *ᵥ b) →
    FullColumnRank (fullDesign Z₁ q) → FullColumnRank (fullDesign Z₂ q) →
    Real.sqrt (olsSESquared (fullDesign Z₁ q) y 2) ∈ Set.Icc (1.35 : ℝ) 1.45 →
    Real.sqrt (olsSESquared (fullDesign Z₂ q) y 3) ∈ Set.Icc (0.955 : ℝ) 0.965 →
    olsResidualStandardError (fullDesign Z₁ q) y ∈ Set.Icc (4.615 : ℝ) 4.625 →
    olsResidualStandardError (fullDesign Z₂ q) y ∈ Set.Icc (4.695 : ℝ) 4.705 → False

/-- The nested-fit SE inequality and the neighboring printed bins give the exact upper bound. -/
def PrintedCellsBoundStatement : Prop :=
  ∀ (Z₁ : Matrix (Fin 17) (Fin 2) ℝ) (Z₂ : Matrix (Fin 17) (Fin 3) ℝ)
    (q y : Fin 17 → ℝ),
    (∀ a, ∃ b, Z₁ *ᵥ a = Z₂ *ᵥ b) →
    FullColumnRank (fullDesign Z₁ q) → FullColumnRank (fullDesign Z₂ q) →
    0 < olsSSE (fullDesign Z₁ q) y → 0 < olsSSE (fullDesign Z₂ q) y →
    Real.sqrt (olsSESquared (fullDesign Z₂ q) y 3) ≤ (0.965 : ℝ) →
    olsResidualStandardError (fullDesign Z₁ q) y ≤ (4.625 : ℝ) →
    (4.695 : ℝ) ≤ olsResidualStandardError (fullDesign Z₂ q) y →
    Real.sqrt (olsSESquared (fullDesign Z₁ q) y 2) ≤ (7141/7512 : ℝ)

/-- Corrected income coefficients and standard-error display bins for the exact deposited inputs. -/
def CorrectedTableCellsStatement : Prop :=
  (∃! β, IsLeastSquares tableA1 tableTwoOutcome β) ∧
  (∃! β, IsLeastSquares tableA2 tableTwoOutcome β) ∧
  (∃! β, IsLeastSquares tableA3 tableTwoOutcome β) ∧
  ols tableA1 tableTwoOutcome 1 = 7146187962914975000000/1117667657915636289559 ∧
  (6.385 : ℝ) ≤ ols tableA1 tableTwoOutcome 1 ∧ ols tableA1 tableTwoOutcome 1 < 6.395 ∧
  olsSESquared tableA1 tableTwoOutcome 1 =
    7736251837253462080128985902187500000000000/8744266954854366478686864008983610246901367 ∧
  (0.935 : ℝ)^2 ≤ olsSESquared tableA1 tableTwoOutcome 1 ∧
  olsSESquared tableA1 tableTwoOutcome 1 < (0.945 : ℝ)^2 ∧
  (0.935 : ℝ) ≤ Real.sqrt (olsSESquared tableA1 tableTwoOutcome 1) ∧
  Real.sqrt (olsSESquared tableA1 tableTwoOutcome 1) < (0.945 : ℝ) ∧
  ols tableA2 tableTwoOutcome 1 =
    315309901567374756223272228924480076940000000/49481205176565031631955325062456554157036059 ∧
  (6.365 : ℝ) ≤ ols tableA2 tableTwoOutcome 1 ∧ ols tableA2 tableTwoOutcome 1 < 6.375 ∧
  (0.955 : ℝ) ≤ Real.sqrt (olsSESquared tableA2 tableTwoOutcome 1) ∧
  Real.sqrt (olsSESquared tableA2 tableTwoOutcome 1) < (0.965 : ℝ) ∧
  ols tableA3 tableTwoOutcome 1 =
    560959205595590684404193874010188762669512981839878401170000000/
      87848341864933029922153613743599975715147930782629447955391927 ∧
  (6.385 : ℝ) ≤ ols tableA3 tableTwoOutcome 1 ∧ ols tableA3 tableTwoOutcome 1 < 6.395 ∧
  (0.95 : ℝ) ≤ Real.sqrt (olsSESquared tableA3 tableTwoOutcome 1) ∧
  Real.sqrt (olsSESquared tableA3 tableTwoOutcome 1) < (1.05 : ℝ) ∧
  (1.005 : ℝ) ≤ Real.sqrt (olsSESquared tableA3 tableTwoOutcome 1) ∧
  Real.sqrt (olsSESquared tableA3 tableTwoOutcome 1) < (1.015 : ℝ)

/-- Nested-fit inequality, exact printed-cell incompatibility, and corrected table cells. -/
def T7Statement : Prop :=
  NestedStandardErrorsStatement ∧ PrintedCellsImpossibleStatement ∧
  ((0.965 : ℝ)*4.625/4.695 = 7141/7512 ∧
  (7141/7512 : ℝ) < 0.951 ∧
    (27/20 : ℝ) - 7141/7512 = 15001/37560 ∧ (0 : ℝ) < 15001/37560) ∧
  PrintedCellsBoundStatement ∧ CorrectedTableCellsStatement

end SAP.P039
