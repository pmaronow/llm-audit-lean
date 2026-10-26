import AronowAudit.P001.Wave1.MarDiscreteBlueprint

/-!
# Double robustness for missing data (P001-T113)

Theorem 6.2.9 (p. 229, proof pp. 229–230), with `Supp[R] = {0,1}` and
a.e. binary values, positivity and bounds. The two printed alternatives are:
(i) correct respondent regression with `η < q(X) < 1 - η`; or
(ii) `q(X) = p(X)` a.e., where MAR already bounds `p(X)` below.
The finite-expectation convention for `m(X)` is explicit (footnote 2, p. 45).
No bounded outcome or L² assumption is imposed.

The proof applies the augmented-arm identity with `U = Y`, `V = Y`, and
`Z = censored Y R`. The two-sided bound on `q` supplies the lower bound `η ≤ q(X)`.
-/

set_option autoImplicit false

universe u

namespace AronowAudit.P001.Wave1.MissingDr

open AronowAudit.P001 MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

noncomputable section


def Target : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] {K : ℕ} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → Fin K → ℝ) (hX : Measurable X) (Y R : Ω → ℝ), Measurable Y → Measurable R →
    Integrable Y μ → (∀ᵐ ω ∂μ, R ω = 0 ∨ R ω = 1) →
    0 < prob μ {ω | R ω = 0} → 0 < prob μ {ω | R ω = 1} →
    ∀ (p : (Fin K → ℝ) → ℝ), IsCEF μ X R p →
    (∃ ε : ℝ, 0 < ε ∧ ∀ᵐ ω ∂μ, ε < p (X ω)) →
    CI μ X hX Y R →
    ∀ (m q : (Fin K → ℝ) → ℝ), Measurable m → Measurable q → Integrable (m ∘ X) μ →
    ((IsCEF (μ.restrict {ω | R ω = 1}) X (fun ω => censored (Y ω) (R ω)) m ∧
        ∃ η : ℝ, 0 < η ∧ ∀ᵐ ω ∂μ, η < q (X ω) ∧ q (X ω) < 1 - η) ∨
      q ∘ X =ᵐ[μ] p ∘ X) →
    mean μ Y =
      mean μ (fun ω => m (X ω) + R ω * (censored (Y ω) (R ω) - m (X ω)) / q (X ω))

/-- The nodes suffice: `N7` (augmented arm mean) at `U = Y`, `g = Prod.snd`,
`Z = censored Y R`. -/
theorem assemble (hS : MarSelection.AllShared.{u, 0, 0}) : Target.{u} := by
  intro Ω _ K μ _ X hX Y R hY hR hYi hbin _ _ p hp hpos hmar m q hm hq hmi hcorrect
  have hcase : (IsCEF (μ.restrict {ω | R ω = 1}) X (fun ω => censored (Y ω) (R ω)) m ∧
      ∃ c : ℝ, 0 < c ∧ ∀ᵐ ω ∂μ, c ≤ q (X ω)) ∨ q ∘ X =ᵐ[μ] p ∘ X := by
    rcases hcorrect with ⟨hcef, η, hη, hqη⟩ | h
    · exact Or.inl ⟨hcef, η, hη, hqη.mono fun ω h => h.1.le⟩
    · exact Or.inr h
  have hZ : Measurable (fun ω => censored (Y ω) (R ω)) := by
    unfold censored; fun_prop
  obtain ⟨-, h⟩ := MarSelection.armMean_of hS μ X hX Y R (fun z => z.2)
    (fun ω => censored (Y ω) (R ω)) p m q hY hR measurable_snd hZ hbin hmar hp hpos hYi
    (Filter.Eventually.of_forall fun ω h1 => by
      simp only [h1, MarDiscrete.censored_of_one]) hm hq hmi hcase
  exact h.symm

end

end AronowAudit.P001.Wave1.MissingDr
