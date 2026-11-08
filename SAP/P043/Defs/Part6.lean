import SAP.P043.Defs.Part5

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P043

open Finset MeasureTheory ProbabilityTheory
open scoped BigOperators

noncomputable section
universe u v

/-! Corrected observation-and-stratum indicators; q=0 is the legitimate single-stratum model. -/

def stratumDummy {n q : ℕ} (s : Fin n → Fin (q + 1)) (i : Fin n) (k : Fin q) : ℝ :=
  if s i = k.castSucc then 1 else 0

def stratumEffect {n q : ℕ} (s : Fin n → Fin (q + 1)) (γ : Fin q → ℝ)
    (i : Fin n) : ℝ := ∑ k, γ k * stratumDummy s i k

def stratumCoefficient {q : ℕ} (γ : Fin q → ℝ) (r : Fin (q + 1)) : ℝ :=
  Fin.lastCases 0 γ r

def correctedRegressionRHS {n q : ℕ} (s : Fin n → Fin (q + 1)) (γ : Fin q → ℝ)
    (X : Fin n → Fin 2) (u : Fin n → ℝ) (β₀ β₁ : ℝ) (i : Fin n) : ℝ :=
  β₀ + β₁ * (X i).val + stratumEffect s γ i + u i

/-- All corrected-notation identities, with q+1 strata and the last stratum as reference. -/
def T6Statement : Prop :=
  ∀ {n q : ℕ} (s : Fin n → Fin (q + 1)) (γ : Fin q → ℝ),
  (∀ i k, s i = k.castSucc → stratumEffect s γ i = γ k) ∧
  (∀ i, s i = Fin.last q → stratumEffect s γ i = 0) ∧
  (∀ i, (∑ k : Fin q, stratumDummy s i k) =
    1 - (if s i = Fin.last q then (1 : ℝ) else 0)) ∧
  (∀ (X : Fin n → Fin 2) (u Y : Fin n → ℝ) (β₀ β₁ : ℝ),
    (∀ i, Y i = correctedRegressionRHS s γ X u β₀ β₁ i) ↔
    (∀ i, Y i = (β₀ + stratumCoefficient γ (s i)) + β₁ * (X i).val + u i))

end
end SAP.P043
