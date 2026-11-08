import SAP.P032.Defs.Part4

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P032

open scoped BigOperators
open Matrix MeasureTheory ProbabilityTheory Filter

noncomputable section

variable {R M P : Type*} [Fintype R] [Fintype M] [Fintype P]
  [DecidableEq R] [DecidableEq M] [DecidableEq P]

/-! Universal lower-bound readings refuted by the audit. -/

def UniversalPopulationBound : Prop :=
  ∀ (n p k : ℕ) (d : Fin n → DyadData (Fin k))
    (X : Matrix (Fin n) (Fin p) ℝ) (c : Fin p → ℝ)
    (A : Matrix (Fin n) (Fin n) ℝ),
    (X.transpose * X).det ≠ 0 → A.PosSemidef →
    (∃ r s, ¬((d r).members ∩ (d s).members).Nonempty ∧ A r s ≠ 0) →
    quadForm (dyadicRestriction d A) (X *ᵥ (olsBread X *ᵥ c)) ≤
      quadForm A (X *ᵥ (olsBread X *ᵥ c))

def UniversalStrictPopulationBound : Prop :=
  ∀ (n p k : ℕ) (d : Fin n → DyadData (Fin k))
    (X : Matrix (Fin n) (Fin p) ℝ) (c : Fin p → ℝ)
    (A : Matrix (Fin n) (Fin n) ℝ),
    (X.transpose * X).det ≠ 0 → A.PosSemidef →
    (∃ r s, ¬((d r).members ∩ (d s).members).Nonempty ∧ A r s ≠ 0) →
    quadForm (dyadicRestriction d A) (X *ᵥ (olsBread X *ᵥ c)) <
      quadForm A (X *ᵥ (olsBread X *ᵥ c))

def UniversalExpectationBound : Prop :=
  ∀ (Ω : Type) [meas : MeasurableSpace Ω] (μ : @Measure Ω meas)
    [_prob : @IsProbabilityMeasure Ω meas μ] (n p k : ℕ)
    (d : Fin n → DyadData (Fin k)) (X : Matrix (Fin n) (Fin p) ℝ)
    (β c : Fin p → ℝ) (u : Fin n → Ω → ℝ),
    (X.transpose * X).det ≠ 0 → (∀ r, MemLp (u r) 2 μ) →
    (∀ r, ∫ ω, u r ω ∂μ = 0) →
    (∃ r s, ¬((d r).members ∩ (d s).members).Nonempty ∧ errorMoments μ u r s ≠ 0) →
    (∫ ω, quadForm (plugInCovariance X (fitResidual X (X *ᵥ β + fun r => u r ω)) (dyadicMask d)) c ∂μ) ≤
      variance (fun ω => c ⬝ᵥ leastSquares X (X *ᵥ β + fun r => u r ω)) μ

def UniversalLimitBound : Prop :=
  ∀ (Ω : Type) [meas : MeasurableSpace Ω] (μ : @Measure Ω meas)
    [_prob : @IsProbabilityMeasure Ω meas μ] (p : ℕ)
    (R M : ℕ → Type) [rows : ∀ m, Fintype (R m)] [rowEq : ∀ m, DecidableEq (R m)]
    [members : ∀ m, Fintype (M m)] [memberEq : ∀ m, DecidableEq (M m)]
    (d : ∀ m, R m → DyadData (M m)) (X : ∀ m, Matrix (R m) (Fin p) ℝ) (β c : Fin p → ℝ)
    (u : ∀ m, R m → Ω → ℝ),
    Tendsto (fun m => Fintype.card (R m)) atTop atTop →
    (∀ m, ((X m).transpose * X m).det ≠ 0) →
    (∀ m r, MemLp (u m r) 2 μ) → (∀ m r, ∫ ω, u m r ω ∂μ = 0) →
    (∀ᶠ m in atTop, ∃ r s, ¬((d m r).members ∩ (d m s).members).Nonempty ∧
      errorMoments μ (u m) r s ≠ 0) →
    (∀ᶠ m in atTop, 0 < variance (fun ω => c ⬝ᵥ leastSquares (X m)
      (X m *ᵥ β + fun r => u m r ω)) μ) →
    ∀ L : ℝ, TendstoInMeasure μ
      (fun m ω => quadForm (plugInCovariance (X m)
        (fitResidual (X m) (X m *ᵥ β + fun r => u m r ω)) (dyadicMask (d m))) c /
          variance (fun ω => c ⬝ᵥ leastSquares (X m) (X m *ᵥ β + fun r => u m r ω)) μ)
      atTop (fun _ => L) → L ≤ 1

end
end SAP.P032
