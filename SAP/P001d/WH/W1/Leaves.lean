import SAP.P001d.WH.W1.Easy
import SAP.P001d.WH.W1.ConditionalGlue

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal Topology

noncomputable section
namespace SAP.P001d.WH.W1

/-- Residual orthogonality with only the moments actually used by covariance.
Proof route (about 150 lines): obtain E[epsilon | sigma(X)] = 0 from
residual_means. The measurable g(X) is strongly measurable for sigma(X).
Use condExp_mul_of_aestronglyMeasurable_left, with the stated integrability of
the residual product, and integral_condExp to show E[g(X) epsilon] = 0.
Expand covariance's centered product using the two integrable first moments
and the integrable raw product, then use E[epsilon] = 0. Do not use
covariance_eq_sub with its unnecessary separate L2 hypotheses. This replaces
the former non-Borel construction after the author's 2026-11-04 decision. -/
def T74_L1V2 : Prop :=
  ∀ {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → E), Measurable X →
    ∀ (Y : Ω → ℝ), Measurable Y → ∀ m : E → ℝ, IsCEF μ X Y m →
    ∀ g : E → ℝ, Measurable g → Integrable (g ∘ X) μ →
    Integrable (fun ω => g (X ω) * (Y ω - m (X ω))) μ →
    covariance (g ∘ X) (fun ω => Y ω - m (X ω)) μ = 0

/-- Construct a conditional-variance version and prove both variance identities,
without assuming that Y or its conditional mean is separately in L2.
Proof route (about 250 lines): let R = Y - m(X). By residual_means its
conditional and unconditional means vanish. Let V = E[R^2 | sigma(X)];
integrable_condExp supplies its first moment, and stronglyMeasurable_condExp
followed by StronglyMeasurable.exists_eq_measurable_comp factors V through X
as a measurable v. setIntegral_condExp gives IsCEF for R^2. The genuine CEF
identity isCEF_condExp and the zero residual conditional mean identify the two
centered squares almost surely, so condExp_congr_ae gives the conditional
variance equality. Finally variance_eq_integral and integral_condExp give the
total identity. Integrability of R^2 is the only new second-moment premise. -/
def T74_L2V2 : Prop :=
  ∀ {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → E), Measurable X →
    ∀ (Y : Ω → ℝ), Measurable Y → ∀ m : E → ℝ, IsCEF μ X Y m →
    Integrable (fun ω => (Y ω - m (X ω))^2) μ →
    WholeResidualVarianceFacts μ X Y m

/-- Reconstruct the classical normal joint law from its conditional kernel.
Proof route (about 200 lines): compare the two finite joint measures on Borel
rectangles using Measure.ext_prod. The given WholeConditionalLaw supplies the
left rectangle mass. For the translated product on the right, use map_apply
and lintegral_prod; the inner Gaussian probability is the normal law translated
by wholeLinearMean beta x, by gaussianReal_map_add_const. The inner integrand
is measurable (a Borel Gaussian kernel) as included in the conditional-law
certificate. This is a law reconstruction, with no additional distributional
assumption and no moment assumption on the random location. -/
def T74_L3V2 : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {K : ℕ} (X : Ω → Fin (K+1) → ℝ) (Y : Ω → ℝ),
    Measurable X → Measurable Y →
    ∀ (β : Fin (K+1) → ℝ) (s : ℝ), 0 < s →
    WholeConditionalLaw μ X Y (wholeNormalKernel β s) →
    μ.map (fun ω => (X ω, Y ω)) =
      ((μ.map X).prod (gaussianReal 0 ⟨s^2, sq_nonneg _⟩)).map
        (fun xy => (xy.1, wholeLinearMean β xy.1 + xy.2))

/-- Mean-zero glue, the moment and variance leaves, the reconstructed Gaussian
law, and the existing four-point failure of independence give the whole claim. -/
theorem T74_assembly (h1 : T74_L1V2) (h2 : T74_L2V2) (h3 : T74_L3V2) :
    T74WholeStatement := by
  refine ⟨?_, ?_, ordinary_nonindependence⟩
  · intro Ω E _ _ μ _ X hX Y hY m hm
    have hr := residual_means μ X hX Y m hm
    exact ⟨hr.1, hr.2.1, hr.2.2.1, hr.2.2.2,
      h1 μ X hX Y hY m hm, h2 μ X hX Y hY m hm⟩
  · intro Ω _ μ _ K X Y hX hY _hinter β s hs hmodel
    have hm : Measurable (wholeLinearMean β) := by unfold wholeLinearMean; fun_prop
    have hjoint := h3 μ X Y hX hY β s hs hmodel
    have h := AronowAudit.P001.classical_normal_residual_independent μ X Y hX hY
      (wholeLinearMean β) hm s hs hjoint
    let v : ℝ≥0 := ⟨s^2, sq_nonneg _⟩
    haveI : IsProbabilityMeasure (gaussianReal (0 : ℝ) v) := inferInstance
    refine ⟨?_, independent_conditional_law μ X _ hX (hY.sub (hm.comp hX))
      (gaussianReal (0 : ℝ) v) h.1 h.2, h.1, h.2⟩
    intro x
    change (gaussianReal (wholeLinearMean β x) v).map (fun y => y - wholeLinearMean β x) =
      gaussianReal 0 v
    simpa only [sub_self] using
      (gaussianReal_map_sub_const (μ := wholeLinearMean β x) (v := v) (wholeLinearMean β x))

/-- All additions for the covariance estimators are proved directly. -/
theorem T66_assembly : T66WholeStatement := whole66

/-- All additions for fixed-scale likelihood and full-rank OLS are proved. -/
theorem T76_assembly : T76WholeStatement := whole76

/-- Both the population example and the APD plug-in formula are proved. -/
theorem T69_assembly : T69WholeStatement := whole69

/-- Measurable signal functions give the whole additive-noise CEF assertion. -/
theorem T68_assembly : T68WholeStatement := whole68

end SAP.P001d.WH.W1
