import AronowAudit.P001.Wave1.MarSelectionBlueprint

/-!
# MAR identification with discrete covariates (P001-T111)

Theorems 6.1.9–6.1.10 (pp. 216–217), Definition 6.1.8 (p. 215), with
`Supp[R] = {0,1}`, a.e. binary values and a.e. positivity. The covariate profiles
are countable (`[Countable E]`, footnote 8).

The respondent CEF of `Y* = censored Y R` is a population CEF of `Y`, the
weighted family `m(x) P(X = x)` is summable, and `E[Y] = ∑' x, m(x) P(X = x)`.

The proof combines CEF transfer with the countable partition formula.
The positive probabilities of both response statuses restrict the domain to that of
the paper; they are not used by the proof.
-/

set_option autoImplicit false

universe u v

namespace AronowAudit.P001.Wave1.MarDiscrete

open AronowAudit.P001 MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

noncomputable section


def Target : Prop :=
  ∀ {Ω : Type u} {E : Type v} [MeasurableSpace Ω] [MeasurableSpace E]
    [Countable E] [MeasurableSingletonClass E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → E) (hX : Measurable X)
    (Y R : Ω → ℝ), Measurable Y → Measurable R →
    Integrable Y μ → (∀ᵐ ω ∂μ, R ω = 0 ∨ R ω = 1) →
    0 < prob μ {ω | R ω = 0} → 0 < prob μ {ω | R ω = 1} →
    ∀ (p : E → ℝ), IsCEF μ X R p →
    (∃ ε : ℝ, 0 < ε ∧ ∀ᵐ ω ∂μ, ε < p (X ω)) →
    CI μ X hX Y R → ∀ (m : E → ℝ),
    IsCEF (μ.restrict {ω | R ω = 1}) X (fun ω => censored (Y ω) (R ω)) m →
    Integrable (m ∘ X) μ →
    IsCEF μ X Y m ∧
      Summable (fun x : E => m x * prob μ {ω | X ω = x}) ∧
      mean μ Y = ∑' x : E, m x * prob μ {ω | X ω = x}

/-- For an integrable function of a countable discrete covariate, the weighted values
are summable and their sum equals the mean. -/
def N1 : Prop :=
  ∀ {Ω : Type u} {E : Type v} [MeasurableSpace Ω] [MeasurableSpace E]
    [Countable E] [MeasurableSingletonClass E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → E), Measurable X →
    ∀ (m : E → ℝ), Integrable (m ∘ X) μ →
      Summable (fun x : E => m x * prob μ {ω | X ω = x}) ∧
      mean μ (m ∘ X) = ∑' x : E, m x * prob μ {ω | X ω = x}

/-- On the respondent event the censored outcome is the outcome. -/
theorem censored_of_one (y : ℝ) : censored y 1 = y := by
  simp [censored]

/-- A CEF identity tested on the whole space gives equality of means. -/
theorem mean_eq_of_isCEF {Ω : Type u} {E : Type v} [MeasurableSpace Ω] [MeasurableSpace E]
    (μ : Measure Ω) (X : Ω → E) (Y : Ω → ℝ) (m : E → ℝ) (h : IsCEF μ X Y m) :
    mean μ Y = mean μ (m ∘ X) := by
  have := h.2.2.2 Set.univ MeasurableSet.univ
  simpa [mean, Set.preimage_univ, Measure.restrict_univ] using this

/-- CEF transfer and the countable partition identity yield the population CEF
and its summable representation of the mean. -/
theorem assemble (hS : MarSelection.AllShared.{u, v, 0}) (hN1 : N1.{u, v}) :
    Target.{u, v} := by
  intro Ω E _ _ _ _ μ _ X hX Y R hY hR hYi hbin _ _ p hp hpos hmar m hm hmi
  have hcef : IsCEF μ X Y m :=
    MarSelection.transfer_of hS μ X hX Y R (fun z => z.2) (fun ω => censored (Y ω) (R ω))
      p m hY hR measurable_snd hbin hmar hp hpos hYi
      (Filter.Eventually.of_forall fun ω h1 => by simp only [h1, censored_of_one]) hm hmi
  obtain ⟨hsum, hmean⟩ := hN1 μ X hX m hmi
  exact ⟨hcef, hsum, (mean_eq_of_isCEF μ X Y m hcef).trans hmean⟩

end

end AronowAudit.P001.Wave1.MarDiscrete
