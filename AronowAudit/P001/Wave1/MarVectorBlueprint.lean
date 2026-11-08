import AronowAudit.P001.Wave1.MarDiscreteBlueprint

/-!
# Blueprint: CEF under MAR for vector covariates, paper support (P001-T111)

Record 11 of group P001a: P001-T111 / held `AronowAudit.P001.mar_cef_general_covariates`;
resolution `repair_and_prove`. Theorem 6.1.10 (p. 217). The held wrapper (:7203) calls the
unfinished `mar_respondent_cef_is_population_cef` (:6015, sorry), and allows a constant
response indicator. The repair (mapper's `mar_vector_paper_support_cef`) restores both
response statuses in support (`hR0`, `hR1`), uses a.e. binary values and positivity, and
keeps a general `K`-dimensional real covariate (no countability, density or smoothness).

Conclusion: `IsCEF μ X Y m` (the respondent version is a population version,
`E[Y|X] = E[Y*|R=1,X]`) and `E[Y] = E[m(X)]`.

Nodes: the shared `MarSelection` nodes (bundled `AllShared`); no record-specific node (the
mapper's incremental `mar_vector_transfer` is the assembly below, fully proved). It must
reuse the general transfer `N5`, never the countable-sum record-10 node.
-/

set_option autoImplicit false

universe u

namespace AronowAudit.P001.Wave1.MarVector

open AronowAudit.P001 MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

noncomputable section

/-- The frozen statement the record is resolved by (mapper's
`AronowAudit.P001.Wave1.mar_vector_paper_support_cef`). -/
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

/-- The nodes suffice: the shared transfer `N5` with `U = Y`, `g = Prod.snd`,
`Z = censored Y R`, then the CEF identity on `univ`. -/
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
