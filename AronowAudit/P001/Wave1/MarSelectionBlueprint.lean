import AronowAudit.P001.P001_Foundations

/-!
# Binary selection under conditional independence (P001-T111–T117)

The setting is a probability space, a covariate `X : Ω → E` with `G = σ(X)`,
a measurable potential object `U : Ω → F`, and an a.e. binary selection indicator `R`
with `CI μ X hX U R`. This is the conditional-independence component of MAR
for `U = Y`, and of strong ignorability for `U = (Y0, Y1)` with `R = D` or
`R = 1 - D`. The required positivity bounds are imposed separately in the
identification statements below. Write `ρ := μ[R | G]`.

* `N1`: `0 ≤ μ[R|m] ≤ 1` a.e. for every sub-σ-algebra `m`.
* `N2`: on covariate-outcome rectangles, `∫ R = ∫ ρ`.
* `N3`: `μ[R | σ(X,U)] = ρ` a.e., by a π–λ extension of the rectangle identity.
* `N4`: for integrable `V = g(X,U)`, `μ[R V | G] = ρ μ[V | G]` a.e.
* `N5`: a CEF of an observed `Z` equal to `V` on `{R = 1}`, under
  `μ.restrict {R = 1}`, is a population CEF of `V` when `ρ = p(X) > ε` a.e.
* `N6`: `∫ R V / q(X) = ∫ ρ μ[V|G] / q(X)` when `q(X) ≥ c > 0` a.e.
* `N7`: `∫ (m(X) + R (Z - m(X)) / q(X)) = ∫ V` under either correctness
  alternative: correct respondent regression with `q(X) ≥ c > 0`, or `q = p`.

All statements allow arbitrary measurable covariate spaces, without countability.
Dependencies are expressed as implications.
-/

set_option autoImplicit false

universe u v w

namespace AronowAudit.P001.Wave1.MarSelection

open AronowAudit.P001 MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

noncomputable section

/-- Every conditional expectation of a measurable, a.e. binary indicator lies in `[0,1]` a.e. -/
def N1 : Prop :=
  ∀ {Ω : Type u} [mΩ : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (m : MeasurableSpace Ω), m ≤ mΩ → ∀ (R : Ω → ℝ), Measurable R →
    (∀ᵐ ω ∂μ, R ω = 0 ∨ R ω = 1) →
    ∀ᵐ ω ∂μ, 0 ≤ (μ[R | m]) ω ∧ (μ[R | m]) ω ≤ 1

/-- Conditional independence gives equality of the integrals of `R` and `μ[R|σ(X)]`
over measurable covariate-outcome rectangles. -/
def N2 : Prop :=
  ∀ {Ω : Type u} {E : Type v} {F : Type w} [MeasurableSpace Ω] [MeasurableSpace E]
    [MeasurableSpace F] (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → E)
    (hX : Measurable X) (U : Ω → F) (R : Ω → ℝ), Measurable U → Measurable R →
    (∀ᵐ ω ∂μ, R ω = 0 ∨ R ω = 1) → CI μ X hX U R →
    ∀ (C : Set E) (A : Set F), MeasurableSet C → MeasurableSet A →
      ∫ ω in X ⁻¹' C ∩ U ⁻¹' A, R ω ∂μ =
        ∫ ω in X ⁻¹' C ∩ U ⁻¹' A, (μ[R | MeasurableSpace.comap X inferInstance]) ω ∂μ

/-- Under `N1` and `N2`, conditioning `R` on `(X,U)` agrees a.e. with conditioning on `X`. -/
def N3 : Prop :=
  N1.{u} → N2.{u, v, w} →
  ∀ {Ω : Type u} {E : Type v} {F : Type w} [MeasurableSpace Ω] [MeasurableSpace E]
    [MeasurableSpace F] (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → E)
    (hX : Measurable X) (U : Ω → F) (R : Ω → ℝ), Measurable U → Measurable R →
    (∀ᵐ ω ∂μ, R ω = 0 ∨ R ω = 1) → CI μ X hX U R →
    μ[R | MeasurableSpace.comap (fun ω => (X ω, U ω)) inferInstance] =ᵐ[μ]
      μ[R | MeasurableSpace.comap X inferInstance]

/-- Under `N1`–`N3`, selection factors out of the conditional expectation of every
integrable `V = g(X,U)`, and `R V` is integrable. -/
def N4 : Prop :=
  N1.{u} → N3.{u, v, w} → N2.{u, v, w} →
  ∀ {Ω : Type u} {E : Type v} {F : Type w} [MeasurableSpace Ω] [MeasurableSpace E]
    [MeasurableSpace F] (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → E)
    (hX : Measurable X) (U : Ω → F) (R : Ω → ℝ), Measurable U → Measurable R →
    (∀ᵐ ω ∂μ, R ω = 0 ∨ R ω = 1) → CI μ X hX U R →
    ∀ g : E × F → ℝ, Measurable g → Integrable (fun ω => g (X ω, U ω)) μ →
      Integrable (fun ω => R ω * g (X ω, U ω)) μ ∧
      μ[(fun ω => R ω * g (X ω, U ω)) | MeasurableSpace.comap X inferInstance] =ᵐ[μ]
        fun ω => (μ[R | MeasurableSpace.comap X inferInstance]) ω *
          (μ[(fun ω => g (X ω, U ω)) | MeasurableSpace.comap X inferInstance]) ω

/-- Under `N1`–`N4` and a propensity bounded away from zero, a respondent CEF for
an observed `Z` equal to `g(X,U)` on `{R = 1}` transfers to the population. -/
def N5 : Prop :=
  N1.{u} → N4.{u, v, w} → N3.{u, v, w} → N2.{u, v, w} →
  ∀ {Ω : Type u} {E : Type v} {F : Type w} [MeasurableSpace Ω] [MeasurableSpace E]
    [MeasurableSpace F] (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → E)
    (hX : Measurable X) (U : Ω → F) (R : Ω → ℝ) (g : E × F → ℝ) (Z : Ω → ℝ)
    (p m : E → ℝ), Measurable U → Measurable R → Measurable g →
    (∀ᵐ ω ∂μ, R ω = 0 ∨ R ω = 1) → CI μ X hX U R → IsCEF μ X R p →
    (∃ ε : ℝ, 0 < ε ∧ ∀ᵐ ω ∂μ, ε < p (X ω)) →
    Integrable (fun ω => g (X ω, U ω)) μ →
    (∀ᵐ ω ∂μ, R ω = 1 → Z ω = g (X ω, U ω)) →
    IsCEF (μ.restrict {ω | R ω = 1}) X Z m → Integrable (m ∘ X) μ →
    IsCEF μ X (fun ω => g (X ω, U ω)) m

/-- Under `N1`–`N4`, the weighted selection variable is integrable and its integral
factors through conditional expectations when `q(X)` is bounded below by `c > 0` a.e. -/
def N6 : Prop :=
  N1.{u} → N4.{u, v, w} → N3.{u, v, w} → N2.{u, v, w} →
  ∀ {Ω : Type u} {E : Type v} {F : Type w} [MeasurableSpace Ω] [MeasurableSpace E]
    [MeasurableSpace F] (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → E)
    (hX : Measurable X) (U : Ω → F) (R : Ω → ℝ) (g : E × F → ℝ) (q : E → ℝ),
    Measurable U → Measurable R → Measurable g → Measurable q →
    (∀ᵐ ω ∂μ, R ω = 0 ∨ R ω = 1) → CI μ X hX U R →
    Integrable (fun ω => g (X ω, U ω)) μ → (∃ c : ℝ, 0 < c ∧ ∀ᵐ ω ∂μ, c ≤ q (X ω)) →
    Integrable (fun ω => R ω * g (X ω, U ω) / q (X ω)) μ ∧
    ∫ ω, R ω * g (X ω, U ω) / q (X ω) ∂μ =
      ∫ ω, (μ[R | MeasurableSpace.comap X inferInstance]) ω *
        (μ[(fun ω => g (X ω, U ω)) | MeasurableSpace.comap X inferInstance]) ω / q (X ω) ∂μ

/-- Under `N1`–`N6`, the augmented variable is integrable and has mean `E[g(X,U)]`
when either the respondent regression is correct and `q(X)` is bounded away from zero,
or `q(X) = p(X)` a.e. -/
def N7 : Prop :=
  N1.{u} → N2.{u, v, w} → N3.{u, v, w} → N4.{u, v, w} → N5.{u, v, w} → N6.{u, v, w} →
  ∀ {Ω : Type u} {E : Type v} {F : Type w} [MeasurableSpace Ω] [MeasurableSpace E]
    [MeasurableSpace F] (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → E)
    (hX : Measurable X) (U : Ω → F) (R : Ω → ℝ) (g : E × F → ℝ) (Z : Ω → ℝ)
    (p m q : E → ℝ), Measurable U → Measurable R → Measurable g → Measurable Z →
    (∀ᵐ ω ∂μ, R ω = 0 ∨ R ω = 1) → CI μ X hX U R → IsCEF μ X R p →
    (∃ ε : ℝ, 0 < ε ∧ ∀ᵐ ω ∂μ, ε < p (X ω)) →
    Integrable (fun ω => g (X ω, U ω)) μ →
    (∀ᵐ ω ∂μ, R ω = 1 → Z ω = g (X ω, U ω)) →
    Measurable m → Measurable q → Integrable (m ∘ X) μ →
    ((IsCEF (μ.restrict {ω | R ω = 1}) X Z m ∧ ∃ c : ℝ, 0 < c ∧ ∀ᵐ ω ∂μ, c ≤ q (X ω)) ∨
      q ∘ X =ᵐ[μ] p ∘ X) →
    Integrable (fun ω => m (X ω) + R ω * (Z ω - m (X ω)) / q (X ω)) μ ∧
    ∫ ω, (m (X ω) + R ω * (Z ω - m (X ω)) / q (X ω)) ∂μ = ∫ ω, g (X ω, U ω) ∂μ

/-- The shared intermediate statements, bundled together. -/
def AllShared : Prop :=
  N1.{u} ∧ N2.{u, v, w} ∧ N3.{u, v, w} ∧ N4.{u, v, w} ∧ N5.{u, v, w} ∧ N6.{u, v, w} ∧
    N7.{u, v, w}


/-- The augmented-arm identity follows under `AllShared` and either correctness alternative. -/
theorem armMean_of (h : AllShared.{u, v, w}) :
    ∀ {Ω : Type u} {E : Type v} {F : Type w} [MeasurableSpace Ω] [MeasurableSpace E]
    [MeasurableSpace F] (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → E)
    (hX : Measurable X) (U : Ω → F) (R : Ω → ℝ) (g : E × F → ℝ) (Z : Ω → ℝ)
    (p m q : E → ℝ), Measurable U → Measurable R → Measurable g → Measurable Z →
    (∀ᵐ ω ∂μ, R ω = 0 ∨ R ω = 1) → CI μ X hX U R → IsCEF μ X R p →
    (∃ ε : ℝ, 0 < ε ∧ ∀ᵐ ω ∂μ, ε < p (X ω)) →
    Integrable (fun ω => g (X ω, U ω)) μ →
    (∀ᵐ ω ∂μ, R ω = 1 → Z ω = g (X ω, U ω)) →
    Measurable m → Measurable q → Integrable (m ∘ X) μ →
    ((IsCEF (μ.restrict {ω | R ω = 1}) X Z m ∧ ∃ c : ℝ, 0 < c ∧ ∀ᵐ ω ∂μ, c ≤ q (X ω)) ∨
      q ∘ X =ᵐ[μ] p ∘ X) →
    Integrable (fun ω => m (X ω) + R ω * (Z ω - m (X ω)) / q (X ω)) μ ∧
    ∫ ω, (m (X ω) + R ω * (Z ω - m (X ω)) / q (X ω)) ∂μ = ∫ ω, g (X ω, U ω) ∂μ :=
  h.2.2.2.2.2.2 h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2.1

/-- The respondent CEF transfers to the population under `AllShared` and positivity. -/
theorem transfer_of (h : AllShared.{u, v, w}) :
    ∀ {Ω : Type u} {E : Type v} {F : Type w} [MeasurableSpace Ω] [MeasurableSpace E]
    [MeasurableSpace F] (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → E)
    (hX : Measurable X) (U : Ω → F) (R : Ω → ℝ) (g : E × F → ℝ) (Z : Ω → ℝ)
    (p m : E → ℝ), Measurable U → Measurable R → Measurable g →
    (∀ᵐ ω ∂μ, R ω = 0 ∨ R ω = 1) → CI μ X hX U R → IsCEF μ X R p →
    (∃ ε : ℝ, 0 < ε ∧ ∀ᵐ ω ∂μ, ε < p (X ω)) →
    Integrable (fun ω => g (X ω, U ω)) μ →
    (∀ᵐ ω ∂μ, R ω = 1 → Z ω = g (X ω, U ω)) →
    IsCEF (μ.restrict {ω | R ω = 1}) X Z m → Integrable (m ∘ X) μ →
    IsCEF μ X (fun ω => g (X ω, U ω)) m :=
  h.2.2.2.2.1 h.1 h.2.2.2.1 h.2.2.1 h.2.1

end

end AronowAudit.P001.Wave1.MarSelection
