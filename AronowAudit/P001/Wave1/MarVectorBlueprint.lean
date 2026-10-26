import AronowAudit.P001.Wave1.MarDiscreteBlueprint

/-!
# CEF under MAR for vector covariates (P001-T111)

Theorem 6.1.10 (p. 217), with both response statuses in support, a.e. binary
values, and a response propensity bounded below almost surely by a fixed positive
constant. The respondent CEF evaluated at X is assumed integrable. The covariate
is a general `K`-dimensional real vector; no countability, density or smoothness
is required.

The respondent CEF is a population CEF: `IsCEF μ X Y m`, or
`E[Y|X] = E[Y*|R=1,X]`. Consequently `E[Y] = E[m(X)]`.
The proof uses the general CEF transfer and the CEF identity on the whole space.
-/

set_option autoImplicit false

universe u

namespace AronowAudit.P001.Wave1.MarVector

open AronowAudit.P001 MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

noncomputable section


def Target : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] {K : ℕ} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → Fin K → ℝ) (hX : Measurable X) (Y R : Ω → ℝ), Measurable Y → Measurable R →
    Integrable Y μ → (∀ᵐ ω ∂μ, R ω = 0 ∨ R ω = 1) →
    0 < prob μ {ω | R ω = 0} → 0 < prob μ {ω | R ω = 1} →
    ∀ (p m : (Fin K → ℝ) → ℝ), IsCEF μ X R p →
    (∃ ε : ℝ, 0 < ε ∧ ∀ᵐ ω ∂μ, ε < p (X ω)) →
    CI μ X hX Y R →
    IsCEF (μ.restrict {ω | R ω = 1}) X (fun ω => censored (Y ω) (R ω)) m →
    Integrable (m ∘ X) μ →
    IsCEF μ X Y m ∧ mean μ Y = mean μ (m ∘ X)

/-- CEF transfer with `U = Y`, `g = Prod.snd`, and `Z = censored Y R`
establishes the population CEF; the CEF identity on `univ` gives the mean equality. -/
theorem assemble (hS : MarSelection.AllShared.{u, 0, 0}) : Target.{u} := by
  intro Ω _ K μ _ X hX Y R hY hR hYi hbin _ _ p m hp hpos hmar hm hmi
  have hcef : IsCEF μ X Y m :=
    MarSelection.transfer_of hS μ X hX Y R (fun z => z.2) (fun ω => censored (Y ω) (R ω))
      p m hY hR measurable_snd hbin hmar hp hpos hYi
      (Filter.Eventually.of_forall fun ω h1 => by
        simp only [h1, MarDiscrete.censored_of_one]) hm hmi
  exact ⟨hcef, MarDiscrete.mean_eq_of_isCEF μ X Y m hcef⟩

end

end AronowAudit.P001.Wave1.MarVector
