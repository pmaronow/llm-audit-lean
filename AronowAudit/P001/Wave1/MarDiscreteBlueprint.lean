import AronowAudit.P001.Wave1.MarSelectionBlueprint

/-!
# Blueprint: MAR identification with discrete covariates, paper support (P001-T111)

Record 10 of group P001a: P001-T111 / held `AronowAudit.P001.mar_cef_and_discrete_mean`;
resolution `repair_and_prove`. Theorems 6.1.9-6.1.10 (pp. 216-217), Definition 6.1.8
(p. 215). The held draft (:4299) allows a constant response indicator; the repair (mapper's
`mar_discrete_paper_support_identification`) restores `Supp[R] = {0,1}` (`hR0`, `hR1`),
uses a.e. binary values and a.e. positivity, keeps countably many covariate profiles
(`[Countable E]`, footnote 8), and adds the summability of the weighted series.

Conclusion: the respondent CEF of `Y* = censored Y R` is a population CEF of `Y`, the
weighted family `m(x) P(X = x)` is summable, and `E[Y] = ∑' x, m(x) P(X = x)`.

Nodes: the shared `MarSelection.N1`-`MarSelection.N7` (bundled as `MarSelection.AllShared`;
only `MarSelection.N1`-`N5` are used) and the record node `MarDiscrete.N1` (countable
partition formula). `hR0`, `hR1` are paper-
domain restrictions, not used by the proof. Writers prove `theorem n1_proof : N1` in
`AronowAudit/P001/Wave1/MarDiscrete/N1.lean`.
-/

set_option autoImplicit false

universe u v

namespace AronowAudit.P001.Wave1.MarDiscrete

open AronowAudit.P001 MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

noncomputable section

/-- The frozen statement the record is resolved by (mapper's
`AronowAudit.P001.Wave1.mar_discrete_paper_support_identification`). -/
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

/-- **Node N1** (paper proof, record 10, third paragraph: "The measurable disjoint sets
C_x={X=x} cover Ω. For the integrable M=m(X), countable additivity of its integral gives
E[M]=∑_x∫_{C_x}M=∑_x m(x)P(C_x). The series is absolutely convergent:
∑_x|m(x)|P(C_x)=∫|M|<∞"). Countable partition formula for an integrable function of a
countable discrete covariate.
Suggested route: `integral_iUnion` / `hasSum_integral_iUnion` on the disjoint measurable
cells `X ⁻¹' {x}` (`measurableSet_singleton`, `Set.iUnion` of preimages is `univ`);
on each cell `∫ m(X) = m x * μ.real (X⁻¹{x})` (`setIntegral_congr_fun`,
`setIntegral_const`); summability from `HasSum.summable`. `prob μ A = (μ A).toReal`. -/
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

/-- The nodes suffice: the shared transfer `N5` (with `U = Y`, `g = Prod.snd`,
`Z = censored Y R`) gives the population CEF; its `univ` identity and `N1` give the series. -/
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
