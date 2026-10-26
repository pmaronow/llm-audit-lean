import Mathlib

namespace AronowAudit.P043

open Finset
noncomputable section

/-- Corrected equation (1), p. 471 (PDF p. 9): "The K-1 dummy variables for
all strata except the reference stratum are denoted D_ik, where D_ik=1 if
observation i belongs to stratum k and 0 otherwise" (P043-E008).
There are `q+1=K` strata, labelled by `Fin (q+1)`; its last element is the
reference stratum. Printed labels 1,...,K correspond to Lean labels 0,...,q. -/
def stratumDummy {n q : ℕ} (s : Fin n → Fin (q + 1)) (i : Fin n) (k : Fin q) : ℝ :=
  if s i = k.castSucc then 1 else 0

/-- The corrected sum in equation (1), `∑_{k=1}^{K-1} γ_k D_ik` (p. 471). -/
def stratumEffect {n q : ℕ} (s : Fin n → Fin (q + 1)) (γ : Fin q → ℝ)
    (i : Fin n) : ℝ := ∑ k, γ k * stratumDummy s i k

/-- Target T6's convention γ_K=0: extend the nonreference coefficients by
zero at the reference stratum. This convention unfolds the corrected model. -/
def stratumCoefficient {q : ℕ} (γ : Fin q → ℝ) (r : Fin (q + 1)) : ℝ :=
  Fin.lastCases 0 γ r

/-- Corrected equation (1)'s right-hand side, p. 471. X_i is binary with
scores 0 and 1; u_i is the disturbance, β₀ the common intercept, β₁ the
coefficient on assignment, and γ_k the nonreference stratum intercept offset. -/
def correctedRegressionRHS {n q : ℕ} (s : Fin n → Fin (q + 1)) (γ : Fin q → ℝ)
    (X : Fin n → Fin 2) (u : Fin n → ℝ) (β₀ β₁ : ℝ) (i : Fin n) : ℝ :=
  β₀ + β₁ * (X i).val + stratumEffect s γ i + u i

/-- T6(i): the corrected dummy sum selects the observation's stratum
coefficient, with zero offset in the reference stratum (equation (1), p. 471). -/
theorem stratum_effect_selects {n q : ℕ} (s : Fin n → Fin (q + 1))
    (γ : Fin q → ℝ) (i : Fin n) :
    stratumEffect s γ i = stratumCoefficient γ (s i) := by
  unfold stratumEffect stratumDummy stratumCoefficient
  generalize s i = r
  refine Fin.lastCases ?_ (fun k => ?_) r
  · have hneq : ∀ k : Fin q, Fin.last q ≠ k.castSucc := by
      intro k h
      have hv := congrArg Fin.val h
      simp only [Fin.val_last, Fin.val_castSucc] at hv
      omega
    simp [hneq]
  · simp [Fin.castSucc_inj]

/-- T6(ii): the omitted reference indicator is 1 minus the sum of the
included indicators, explaining "all strata but one" (p. 471). -/
theorem stratum_dummy_sum {n q : ℕ} (s : Fin n → Fin (q + 1)) (i : Fin n) :
    (∑ k : Fin q, stratumDummy s i k) =
      1 - (if s i = Fin.last q then (1 : ℝ) else 0) := by
  unfold stratumDummy
  generalize s i = r
  refine Fin.lastCases ?_ (fun k => ?_) r
  · have hneq : ∀ k : Fin q, Fin.last q ≠ k.castSucc := by
      intro k h
      have hv := congrArg Fin.val h
      simp only [Fin.val_last, Fin.val_castSucc] at hv
      omega
    simp [hneq]
  · simp [Fin.castSucc_inj]

/-- T6, complete corrected notation: nonreference and reference selection,
the intercept dependence of all K indicators, and equation (1) expressed as
a stratum-specific intercept plus the single treatment coefficient. This
asserts no causal interpretation, estimation property, or GLS result. -/
theorem corrected_strata {n q : ℕ} (s : Fin n → Fin (q + 1)) (γ : Fin q → ℝ) :
    (∀ i k, s i = k.castSucc → stratumEffect s γ i = γ k) ∧
    (∀ i, s i = Fin.last q → stratumEffect s γ i = 0) ∧
    (∀ i, (∑ k : Fin q, stratumDummy s i k) =
      1 - (if s i = Fin.last q then (1 : ℝ) else 0)) ∧
    (∀ (X : Fin n → Fin 2) (u Y : Fin n → ℝ) (β₀ β₁ : ℝ),
      (∀ i, Y i = correctedRegressionRHS s γ X u β₀ β₁ i) ↔
      (∀ i, Y i = (β₀ + stratumCoefficient γ (s i)) + β₁ * (X i).val + u i)) := by
  refine ⟨?_, ?_, stratum_dummy_sum s, ?_⟩
  · intro i k h
    rw [stratum_effect_selects, h]
    simp [stratumCoefficient]
  · intro i h
    rw [stratum_effect_selects, h]
    simp [stratumCoefficient]
  · intro X u Y β₀ β₁
    have h : ∀ i, correctedRegressionRHS s γ X u β₀ β₁ i =
        (β₀ + stratumCoefficient γ (s i)) + β₁ * (X i).val + u i := by
      intro i
      rw [correctedRegressionRHS, stratum_effect_selects]
      ring
    simp only [h]

end
end AronowAudit.P043

