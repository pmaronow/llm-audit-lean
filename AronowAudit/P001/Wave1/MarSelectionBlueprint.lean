import AronowAudit.P001.P001_Foundations

/-!
# Shared blueprint nodes: binary selection under conditional independence (P001-T111-T117)

Blueprint (Wave 1, group P001a). Shared by records 10, 11 (MAR CEF transfer), 13
(balancing score, node `N1` only), 14 (missing-data double robustness) and 16 (causal IPW and
double robustness, once for each arm). Mapper report, "Shared lemmas" items 1-4, and the
paper proofs of records 10, 14, 16.

Setting: a probability space, a covariate `X : Ω → E` with `G = σ(X)`, a measurable
"potential" object `U : Ω → F`, and an a.e. binary selection indicator `R` with
`CI μ X hX U R` (MAR for `U = Y`; strong ignorability for `U = (Y0, Y1)`, `R = D` or
`R = 1 - D`). `ρ := μ[R | G]`.

* `N1`: `0 ≤ μ[R|m] ≤ 1` a.e. for every sub-σ-algebra `m`.
* `N2`: on covariate-outcome rectangles, `∫ R = ∫ ρ` (indicator CI with `B = {1}`, pull-out).
* `N3`: `μ[R | σ(X,U)] = ρ` a.e. (π-λ extension of `N2`).
* `N4`: for integrable `V = g(X,U)`, `μ[R V | G] = ρ μ[V | G]` a.e. (tower and pull-out).
* `N5`: respondent CEF transfer: a CEF of an observed `Z` (equal to `V` on `{R = 1}`) under
  `μ.restrict {R = 1}` is a population CEF of `V`, given `ρ = p(X) > ε` a.e.
* `N6`: weighted integral: `∫ R V / q(X) = ∫ ρ μ[V|G] / q(X)` when `q(X) ≥ c > 0` a.e.
* `N7`: the augmented arm mean `∫ (m(X) + R (Z - m(X)) / q(X)) = ∫ V` under either
  correctness alternative (correct respondent regression with `q(X) ≥ c > 0`, or `q = p`).

All nodes are stated for arbitrary measurable covariate spaces (no countability), as both
referees require. Dependencies are explicit implications, so every node can be proved
independently. Writers prove `theorem nk_proof : Nk` in
`AronowAudit/P001/Wave1/MarSelection/Nk.lean`. The sorry-bearing drafts
`mar_respondent_cef_is_population_cef` (:6015), `mar_cef_and_discrete_mean` (:4299),
`mar_cef_general_covariates` (:7203, depends on :6015), `mar_balancing_score`,
`missing_double_robustness`, `causal_ipw_and_double_robustness`,
`strong_ignorability_identification_and_balance` must not be used. Usable proved inputs:
`isCEF_condExp` (:3337), `positive_cef_inverse_weights` (:3715, bounded-numerator pattern only).
-/

set_option autoImplicit false

universe u v w

namespace AronowAudit.P001.Wave1.MarSelection

open AronowAudit.P001 MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

noncomputable section

/-- **Node N1** (paper proof, record 10, first paragraph: "The IsCEF identities and
conditional-expectation uniqueness give ρ=E[R|G] almost surely, hence 0≤ρ≤1"). For an a.e.
binary integrable indicator, every conditional expectation lies in `[0,1]` a.e.
Suggested route: `0 ≤ R ≤ 1` a.e.; `condExp_nonneg`, `condExp_mono` against the constant `1`
and `condExp_const` (`hm : m ≤ m₀`); integrability of `R` from the a.e. bound
(`Integrable.of_bound`, `hR.aestronglyMeasurable`). -/
def N1 : Prop :=
  ∀ {Ω : Type u} [mΩ : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (m : MeasurableSpace Ω), m ≤ mΩ → ∀ (R : Ω → ℝ), Measurable R →
    (∀ᵐ ω ∂μ, R ω = 0 ∨ R ω = 1) →
    ∀ᵐ ω ∂μ, 0 ≤ (μ[R | m]) ω ∧ (μ[R | m]) ω ≤ 1

/-- **Node N2** (paper proof, record 10, first paragraph: "The MAR definition CI supplies,
for every measurable outcome set A, E[R1_{Y∈A}|G]=ρE[1_{Y∈A}|G]. Multiply by the indicator
of any G-event B and integrate. Because ρ is G-measurable, this gives
E[R1_B1_{Y∈A}]=E[ρ1_B1_{Y∈A}]"). Rectangle identity: for measurable `C ⊆ E`, `A ⊆ F`,
`∫_{X⁻¹C ∩ U⁻¹A} R = ∫_{X⁻¹C ∩ U⁻¹A} μ[R|σ(X)]`.
Suggested route: specialize `CI` at `A` and `B = {1}`; `R = 1_{R=1}` a.e. (binary);
`setIntegral_condExp` on the `σ(X)`-set `X⁻¹C` (`⟨C, hC, rfl⟩`), then
`condExp_mul_of_stronglyMeasurable_right`/`_left` to pull `ρ` (bounded by `N1`-type bounds;
here only integrability of `ρ · 1_{U∈A}` is needed, from `|1_{U∈A}| ≤ 1`) and
`setIntegral_condExp` again; `integral_indicator`, `Set.indicator_inter`. -/
def N2 : Prop :=
  ∀ {Ω : Type u} {E : Type v} {F : Type w} [MeasurableSpace Ω] [MeasurableSpace E]
    [MeasurableSpace F] (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → E)
    (hX : Measurable X) (U : Ω → F) (R : Ω → ℝ), Measurable U → Measurable R →
    (∀ᵐ ω ∂μ, R ω = 0 ∨ R ω = 1) → CI μ X hX U R →
    ∀ (C : Set E) (A : Set F), MeasurableSet C → MeasurableSet A →
      ∫ ω in X ⁻¹' C ∩ U ⁻¹' A, R ω ∂μ =
        ∫ ω in X ⁻¹' C ∩ U ⁻¹' A, (μ[R | MeasurableSpace.comap X inferInstance]) ω ∂μ

/-- **Node N3** (paper proof, record 10, first paragraph: "The sets B∩{Y∈A} form a
pi-system generating σ(X,Y). Equality of the finite measures C↦E[R1_C] and C↦E[ρ1_C]
therefore extends to all events of that sigma-field. Thus E[R|σ(X,Y)]=ρ"). Under `N2` and
`N1`, `μ[R | σ(X,U)] = μ[R | σ(X)]` a.e.
Suggested route: `ae_eq_condExp_of_forall_setIntegral_eq` with `m := comap (X, U)`
(`ρ` is `σ(X,U)`-measurable since `comap X ≤ comap (X,U)`, via `Measurable.fst`/
`MeasurableSpace.comap_mono`-type facts); every `σ(X,U)`-set is `(X,U)⁻¹ T` with `T`
measurable in `E × F`; the finite measures `T ↦ ∫⁻_{(X,U)⁻¹T} ofReal R` and
`T ↦ ∫⁻_{(X,U)⁻¹T} ofReal ρ` (both integrands `≥ 0` a.e., by binarity and `N1`) agree on the
π-system `Set.image2 (· ×ˢ ·)` of rectangles (`N2`) and on `univ`, hence everywhere
(`MeasureTheory.ext_of_generate_finite`, `generateFrom_prod`, `isPiSystem_prod`);
convert back with `ofReal_integral_eq_lintegral_ofReal`. -/
def N3 : Prop :=
  N1.{u} → N2.{u, v, w} →
  ∀ {Ω : Type u} {E : Type v} {F : Type w} [MeasurableSpace Ω] [MeasurableSpace E]
    [MeasurableSpace F] (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → E)
    (hX : Measurable X) (U : Ω → F) (R : Ω → ℝ), Measurable U → Measurable R →
    (∀ᵐ ω ∂μ, R ω = 0 ∨ R ω = 1) → CI μ X hX U R →
    μ[R | MeasurableSpace.comap (fun ω => (X ω, U ω)) inferInstance] =ᵐ[μ]
      μ[R | MeasurableSpace.comap X inferInstance]

/-- **Node N4** (paper proof, record 10, first paragraph: "By simple-function approximation
and L¹ truncation, E[RY|G]=ρu. The same reasoning applies to any integrable σ(X,Y)-measurable
variable V, giving E[RV|G]=ρE[V|G]. Products are integrable because |R|≤1 and |ρ|≤1 almost
surely"; "Shared lemmas" item 2). Selection factorization for every integrable
`V = g(X,U)`, together with integrability of `R V`.
Suggested route (avoids simple-function approximation): tower
`condExp_condExp_of_le (comap X ≤ comap (X,U))`; pull `V` out of `μ[R V | σ(X,U)]`
(`condExp_mul_of_stronglyMeasurable_right`, `V` is `σ(X,U)`-measurable as
`g ∘ (X,U)`), replace `μ[R|σ(X,U)]` by `ρ` (`N3`, `condExp_congr_ae`), then pull `ρ` out of
`μ[ρ V | σ(X)]` (`condExp_mul_of_stronglyMeasurable_left`, `stronglyMeasurable_condExp`).
Integrability of `R V`, `ρ V` from `|R|, |ρ| ≤ 1` a.e. (`N1`; `Integrable.bdd_mul`). -/
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

/-- **Node N5** (paper proof, record 10, second paragraph: "The respondent CEF premise says,
for every covariate event B=X^{-1}(A), that E[1_B R(Y*-M)]=0 ... the preceding
factorization gives E[1_B ρ(u-M)]=0. The variable ρ(u-M) is G-measurable and integrable;
vanishing integrals over all G-events imply ρ(u-M)=0 almost surely ... Positivity ρ>ε>0
almost surely implies u=M"; "Shared lemmas" item 3; record 16, "arm_regression_cef_transfer").
Respondent CEF transfer for a general potential `V = g(X,U)` observed as `Z` on `{R = 1}`.
Suggested route: `setIntegral` over `X⁻¹C` under `μ.restrict {R=1}` equals `∫_{X⁻¹C} R Z`
(`Measure.restrict_restrict`, `setIntegral_indicator`, `R = 1_{R=1}` a.e.), and `R Z = R V`
a.e.; apply `N4` to `g' (x, f) = g (x, f) - m x`; `setIntegral_condExp`; conclude
`ρ (μ[V|G] - m∘X) = 0` a.e. by `ae_eq_zero_of_forall_setIntegral_eq_of_sigmaFinite'`/
`ae_eq_of_forall_setIntegral_eq_of_sigmaFinite'` (σ(X)-version, `Measure.trim`), divide by
`ρ = p(X) > ε` (`isCEF_condExp`), and assemble `IsCEF` via `setIntegral_condExp`. -/
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

/-- **Node N6** (paper proof, record 14, "mar_augmented_conditional_mean"; "Shared lemmas"
item 4: "For integrable V and measurable Q with Q≥c>0 a.e., V/Q is integrable and
E[V/Q|G]=E[V|G]/Q when Q is G-measurable, because |V/Q|≤|V|/c and conditional pullout
applies"). Weighted selection integral for a weight `q(X)` bounded below by `c > 0` a.e.
Suggested route: `R V / q(X) = (q(X))⁻¹ * (R V)`; integrability from
`|R V / q(X)| ≤ |V| / c` (`N1`-free: `|R| ≤ 1` a.e.); `integral_condExp` then
`condExp_mul_of_stronglyMeasurable_left` for the `σ(X)`-measurable bounded factor
`(q(X))⁻¹`, then `N4`. -/
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

/-- **Node N7** (paper proof, record 14, "In case (i), the respondent CEF transfer ... yields
u=M ... the residual term ... conditional mean is ρ(u-M)/Q=0 ... In case (ii), Q=ρ almost
surely ... M+ρ(u-M)/ρ=u"; record 16, "causal_dr_two_cases"). The augmented arm mean under
either correctness alternative, with integrability of the augmented variable.
Instantiations: record 14 (`U = Y`, `V = Y`, `Z = censored Y R`); record 16 treated arm
(`U = (Y0,Y1)`, `R = D`, `V = Y1`, `Z = Y`), control arm (`R = 1 - D`, propensity `1 - p`,
weight `1 - q`, `V = Y0`); and IPW (`m = 0`, `q = p`, second alternative).
Suggested route: `R (Z - m X) = R (V - m X)` a.e.; `N6` with `g' (x, f) = g (x, f) - m x` and
`c` (case (i)) or `ε` (case (ii), via `q(X) = p(X)` a.e.); case (i): `N5` and `isCEF_condExp`
give `μ[V - m X | G] = 0` a.e.; case (ii): `ρ = p(X) = q(X)` a.e. so `ρ μ[V-mX|G]/q(X) =
μ[V-mX|G]` a.e. and `integral_condExp`; finish with `IsCEF` at `univ` / `integral_add`,
`integral_sub`. -/
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

/-- Every shared node, bundled (convenience for the record assemblies). -/
def AllShared : Prop :=
  N1.{u} ∧ N2.{u, v, w} ∧ N3.{u, v, w} ∧ N4.{u, v, w} ∧ N5.{u, v, w} ∧ N6.{u, v, w} ∧
    N7.{u, v, w}

/-- The respondent CEF transfer, with every upstream node discharged. -/
theorem transfer (h : AllShared.{u, v, w}) : N5.{u, v, w} := h.2.2.2.2.1

/-- The augmented-arm identity, with every upstream node discharged by the bundle. -/
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

/-- The CEF transfer with every upstream node discharged by the bundle. -/
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
