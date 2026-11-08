import SAP.P001f.Defs.WholeW2
import SAP.P001f.Bridge

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P001f.WH.W2

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

noncomputable section
universe u

/-- Respondent integrability transfers to the population under uniform positive
response propensity. No MAR assumption is needed here. Prove that R*m(X) is
integrable by identifying it a.e. with the respondent-event indicator times
m(X). Use isCEF_condExp and the conditional-expectation pull-out theorem to
deduce integrability of p(X)*m(X), then dominate |m(X)| by
ε⁻¹*|p(X)*m(X)|. The pull-out theorem requires integrability of the product
and of R, and does not require integrability of m(X). -/
def T113_L1 : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] {K : ℕ} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → Fin K → ℝ) (_hX : Measurable X) (R : Ω → ℝ), Measurable R →
    (∀ᵐ ω ∂μ, R ω = 0 ∨ R ω = 1) →
    ∀ p : (Fin K → ℝ) → ℝ, ConditionalMean μ X R p →
    (∃ ε : ℝ, 0 < ε ∧ ∀ᵐ ω ∂μ, ε < p (X ω)) →
    ∀ m : (Fin K → ℝ) → ℝ, Measurable m →
    Integrable (m ∘ X) (μ.restrict {ω | R ω = 1}) → Integrable (m ∘ X) μ

/-- True-propensity weighting: the observed weighted outcome is integrable and
has the outcome mean, and W=R/p(X) is integrable with E[W|X]=1. First bound
R and 1/p(X) and use Integrable.bdd_mul/mul_bdd. The existing restricted
double-robustness theorem with the zero nuisance regression gives the weighted
outcome mean (or use MarSelection.n6_proof). For normalization pull 1/p(X)
out of E[R/p(X)|X] and substitute isCEF_condExp; positivity legitimizes the
cancellation. True propensity may equal one on a region. -/
def T113_L2 : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] {K : ℕ} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → Fin K → ℝ) (hX : Measurable X) (Y R : Ω → ℝ),
    Measurable Y → Measurable R → Integrable Y μ →
    (∀ᵐ ω ∂μ, R ω = 0 ∨ R ω = 1) →
    0 < (μ {ω | R ω = 0}).toReal → 0 < (μ {ω | R ω = 1}).toReal →
    ∀ p : (Fin K → ℝ) → ℝ, ConditionalMean μ X R p →
    (∃ ε : ℝ, 0 < ε ∧ ∀ᵐ ω ∂μ, ε < p (X ω)) →
    ConditionallyIndependent μ X hX Y R →
    Integrable (fun ω => R ω * censoredOutcome (Y ω) (R ω) / p (X ω)) μ ∧
    (∫ ω, R ω * censoredOutcome (Y ω) (R ω) / p (X ω) ∂μ) = (∫ ω, Y ω ∂μ) ∧
    Integrable (fun ω => R ω / p (X ω)) μ ∧
    μ[(fun ω => R ω / p (X ω)) | MeasurableSpace.comap X inferInstance] =ᵐ[μ]
      (fun _ => (1 : ℝ))

/-- Cancellation with a possibly nonintegrable measurable nuisance factor M.
For integrable B, W and complete score B+M*(1-W), where E[W|G]=1 and M is
G-measurable, the score and B have the same integral. Subtract B to obtain an
integrable product M*(1-W). condExp_sub and condExp_const give
E[1-W|G]=0. Pull M out with condExp_mul_of_stronglyMeasurable_left (no L1
assumption on M), integrate with integral_condExp, and add B back. -/
def T113_L3 : Prop :=
  ∀ {Ω : Type u} [mΩ : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (G : MeasurableSpace Ω), G ≤ mΩ → ∀ M W B : Ω → ℝ,
    StronglyMeasurable[G] M → Integrable W μ → Integrable B μ →
    μ[W | G] =ᵐ[μ] (fun _ => (1 : ℝ)) →
    Integrable (fun ω => B ω + M ω * (1 - W ω)) μ →
    (∫ ω, B ω + M ω * (1 - W ω) ∂μ) = ∫ ω, B ω ∂μ

/-- The two correctness branches: transfer integrability only in the regression
branch; in the propensity branch cancel the nuisance without assuming its
integrability. All divisions used in the latter branch have positive denominator. -/
theorem T113_assembly (h1 : T113_L1.{u}) (h2 : T113_L2.{u}) (h3 : T113_L3.{u}) :
    T113WholeStatement.{u} := by
  intro Ω _ K μ _ X hX Y R hY hR hYi hbin hR0 hR1 p hp hpos hCI m q hm hq hSi hcorrect
  rcases hcorrect with hreg | hprop
  · have hmi : Integrable (m ∘ X) μ :=
      h1 μ X hX R hR hbin p hp hpos m hm hreg.1.2.2.1
    exact SAP.P001f.Bridge.transportT113 μ X hX Y R hY hR hYi hbin hR0 hR1
      p hp hpos hCI m q hm hq hmi (Or.inl hreg)
  · obtain ⟨hBi, hBmean, hWi, hWcond⟩ :=
      h2 μ X hX Y R hY hR hYi hbin hR0 hR1 p hp hpos hCI
    let M : Ω → ℝ := m ∘ X
    let W : Ω → ℝ := fun ω => R ω / p (X ω)
    let B : Ω → ℝ := fun ω => R ω * censoredOutcome (Y ω) (R ω) / p (X ω)
    have heq : (fun ω => augmentedMissingScore (Y ω) (R ω) (m (X ω)) (q (X ω)))
        =ᵐ[μ] (fun ω => B ω + M ω * (1 - W ω)) := by
      filter_upwards [hprop] with ω hω
      change q (X ω) = p (X ω) at hω
      simp only [augmentedMissingScore, hω, M, W, B, Function.comp_apply]
      ring
    have hMm : StronglyMeasurable[MeasurableSpace.comap X inferInstance] M :=
      (hm.comp (comap_measurable X)).stronglyMeasurable
    have hc := h3 μ (MeasurableSpace.comap X inferInstance) hX.comap_le M W B
      hMm hWi hBi hWcond (hSi.congr heq)
    calc
      (∫ ω, Y ω ∂μ) = ∫ ω, B ω ∂μ := hBmean.symm
      _ = ∫ ω, B ω + M ω * (1 - W ω) ∂μ := hc.symm
      _ = ∫ ω, augmentedMissingScore (Y ω) (R ω) (m (X ω)) (q (X ω)) ∂μ :=
        integral_congr_ae heq.symm

/-- The population theorem is already available. All added individual-imputation
and six-unit arithmetic clauses have short direct proofs, so this target needs
no new leaf. -/
theorem T114_assembly : T114WholeStatement.{u} := by
  refine ⟨SAP.P001f.Bridge.transportT114.{u}.1, ?_, ?_,
    SAP.P001f.Bridge.transportT114.{u}.2, ?_⟩
  · intro y0 y1 d a b hy0 hy1 hd
    rcases hd with rfl | rfl
    · simpa [realizedOutcome, imputedPotentialOne, imputedPotentialZero,
        lowerATE, upperATE] using hy1
    · simpa [realizedOutcome, imputedPotentialOne, imputedPotentialZero,
        lowerATE, upperATE] using hy0
  · norm_num [imputedPotentialOne, imputedPotentialZero, exampleOutcome,
      exampleIndicator, Fin.sum_univ_succ]
  · norm_num

end
end SAP.P001f.WH.W2
