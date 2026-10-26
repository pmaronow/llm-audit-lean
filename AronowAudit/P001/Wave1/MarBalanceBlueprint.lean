import AronowAudit.P001.Wave1.MarSelectionBlueprint

/-!
# MAR and the propensity score (P001-T112)

Theorem 6.1.12 (pp. 217–218, proof p. 218), with `Supp[R] = {0,1}`,
a.e. binary values and a.e. positivity. The conclusions are balance
`R ⊥ X | p(X)`, `Y ⊥ R | p(X)`, and `Pr[R = 1 | p(X)] > ε`, the last expressed as
`IsCEF μ (p ∘ X) R id` together with `ε < p(X)` a.e.
No integrability of `Y` is assumed; only indicators of `Y` occur.

Write `G = σ(X)`, `S = p(X)`, `H = σ(S) ≤ G`, and
`r_A(s) = 1_{0∈A}(1-s) + 1_{1∈A}s`.
The intermediate statements concern the binary-event CEF, balance and the score's
self-CEF, and reduction of MAR to the score.
-/

set_option autoImplicit false

universe u v

namespace AronowAudit.P001.Wave1.MarBalance

open AronowAudit.P001 MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

noncomputable section


def Target : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] {K : ℕ} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → Fin K → ℝ) (hX : Measurable X) (Y R : Ω → ℝ), Measurable Y → Measurable R →
    (∀ᵐ ω ∂μ, R ω = 0 ∨ R ω = 1) →
    0 < prob μ {ω | R ω = 0} → 0 < prob μ {ω | R ω = 1} →
    ∀ (p : (Fin K → ℝ) → ℝ) (hp : IsCEF μ X R p), CI μ X hX Y R →
    ∀ (ε : ℝ), 0 < ε → (∀ᵐ ω ∂μ, ε < p (X ω)) →
    CI μ (p ∘ X) (hp.1.comp hX) R X ∧ CI μ (p ∘ X) (hp.1.comp hX) Y R ∧
      IsCEF μ (p ∘ X) R id ∧ (∀ᵐ ω ∂μ, ε < p (X ω))

open Classical in
/-- Conditional expectations of binary-event indicators are affine functions of the propensity. -/
def N1 : Prop :=
  ∀ {Ω : Type u} {E : Type v} [MeasurableSpace Ω] [MeasurableSpace E] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (X : Ω → E) (R : Ω → ℝ) (p : E → ℝ), Measurable X →
    Measurable R → (∀ᵐ ω ∂μ, R ω = 0 ∨ R ω = 1) → IsCEF μ X R p →
    ∀ A : Set ℝ, MeasurableSet A →
      μ[(fun ω => if R ω ∈ A then (1 : ℝ) else 0) | MeasurableSpace.comap X inferInstance]
        =ᵐ[μ] fun ω => (if (0 : ℝ) ∈ A then 1 - p (X ω) else 0) +
          (if (1 : ℝ) ∈ A then p (X ω) else 0)

/-- Under `N1` and `MarSelection.N1`, the propensity score balances `R` and `X`,
and is its own CEF for `R`. -/
def N2 : Prop :=
  N1.{u, v} → MarSelection.N1.{u} →
  ∀ {Ω : Type u} {E : Type v} [MeasurableSpace Ω] [MeasurableSpace E] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (X : Ω → E) (hX : Measurable X) (R : Ω → ℝ) (p : E → ℝ)
    (hp : IsCEF μ X R p), Measurable R → (∀ᵐ ω ∂μ, R ω = 0 ∨ R ω = 1) →
    CI μ (p ∘ X) (hp.1.comp hX) R X ∧ IsCEF μ (p ∘ X) R id

/-- Under `N1` and `MarSelection.N1`, conditional independence of `Y` and `R`
given `X` implies conditional independence given the propensity score. -/
def N3 : Prop :=
  N1.{u, v} → MarSelection.N1.{u} →
  ∀ {Ω : Type u} {E : Type v} [MeasurableSpace Ω] [MeasurableSpace E] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (X : Ω → E) (hX : Measurable X) (Y R : Ω → ℝ) (p : E → ℝ)
    (hp : IsCEF μ X R p), Measurable Y → Measurable R → (∀ᵐ ω ∂μ, R ω = 0 ∨ R ω = 1) →
    CI μ X hX Y R → CI μ (p ∘ X) (hp.1.comp hX) Y R

/-- The balance, conditional independence, self-CEF, and positivity conclusions follow
from `N1`–`N3` and `MarSelection.N1`. -/
theorem assemble (h0 : MarSelection.N1.{u}) (h1 : N1.{u, 0}) (h2 : N2.{u, 0})
    (h3 : N3.{u, 0}) : Target.{u} := by
  intro Ω _ K μ _ X hX Y R hY hR hbin _ _ p hp hmar ε _ hpos
  obtain ⟨hbal, hself⟩ := h2 h1 h0 μ X hX R p hp hR hbin
  exact ⟨hbal, h3 h1 h0 μ X hX Y R p hp hY hR hbin hmar, hself, hpos⟩

end

end AronowAudit.P001.Wave1.MarBalance
