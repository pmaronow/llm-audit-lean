import SAP.P001c.Defs.WholeW2
import SAP.P001c.Bridge
import AronowAudit.P001.Wave1.UnbiasedMeanVariance

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P001c.WH.W2

open MeasureTheory ProbabilityTheory Filter
open AronowAudit.P001 AronowAudit.P001.Wave1
open scoped BigOperators ENNReal NNReal Topology Classical ContDiff
universe u
noncomputable section

/-- T39, mixture marginal laws. Factor each bivariate density into a normal marginal
and a conditional normal density using `bivariate_normal_factor`; integrate the latter
with Tonelli. Symmetry gives the other marginal. Add the two half-weight laws using
withDensity_add_left and withDensity_smul. The same calculation certifies mass one and
integrability/nonnegativity of the displayed mixture density. About 150–250 lines. -/
def T39_L1 : Prop :=
  IsProbabilityMeasure normalMixtureLaw ∧ isJointDensity normalMixtureLaw normalMixtureDensity ∧
  normalMixtureLaw.map Prod.fst = gaussianReal 0 1 ∧
  normalMixtureLaw.map Prod.snd = gaussianReal 0 1

/-- T39, zero mixture covariance. Write the measure as half the sum of its two
components. Transfer L2 bounds from `bivariate_normal_second_moments`, then integrate
first and cross moments with integral_add_measure and integral_smul_measure. The
component means vanish and the covariances 3/5 and −3/5 cancel. About 100–180 lines. -/
def T39_L2 : Prop :=
  MemLp (Prod.fst : ℝ × ℝ → ℝ) 2 normalMixtureLaw ∧
  MemLp (Prod.snd : ℝ × ℝ → ℝ) 2 normalMixtureLaw ∧
  covariance Prod.fst Prod.snd normalMixtureLaw = 0

/-- T39, dependence of the smooth mixture. If its two standard-normal marginals
were independent, the joint density would equal the product density almost everywhere.
Continuity promotes that equality to everywhere. At the origin the two densities are
5/(8π) and 1/(2π), respectively. Use the joint-law characterization of independence,
withDensity uniqueness and full support of volume. About 150–250 lines. -/
def T39_L3 : Prop :=
  IsProbabilityMeasure normalMixtureLaw →
  normalMixtureLaw.map Prod.fst = gaussianReal 0 1 →
  normalMixtureLaw.map Prod.snd = gaussianReal 0 1 →
  ¬ IndepFun Prod.fst Prod.snd normalMixtureLaw

/-- T39, arbitrary-space bivariate transport, including both normal marginal laws.
First obtain the marginal laws by integrating the factored density, as in L1, for
general positive scales. Then use integral_map, variance_map, covariance_map,
MemLp.comp_of_map and map_map along z ↦ (X z,Y z). Independence at zero correlation
is transported with indepFun_iff_map_prod_eq_prod_map_map. About 200–300 lines. -/
def T39_L4 : Prop := wholeBivariateTransport.{u}

/-- T43, polynomial risk calculus. Expand risk with linearRisk_mean_covariance_form;
fun_prop proves joint C-infinity smoothness. Differentiate the quadratic polynomial
and its affine first partials to obtain genuine second-partial certificates in both
mixed orders. variance_eq_sub gives the determinant. No positivity is needed.
About 150–250 lines. -/
def T43_L1 : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X Y : Ω → ℝ), MemLp X 2 μ → MemLp Y 2 μ → wholeRiskCalculus μ X Y

/-- T43, existence and automatic L2 bounds for Borel CEF versions. Factor the
sigma(X)-measurable conditional expectation through X using exists_eq_measurable_comp;
setIntegral_condExp proves the event identities and MemLp.condExp gives the L2 bound.
For an arbitrary version use isCEF_condExp and memLp_congr_ae. This needs no moment
assumption on X. About 80–150 lines. -/
def T43_L2 : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X Y : Ω → ℝ), Measurable X → MemLp Y 2 μ →
    (∃ m : ℝ → ℝ, isConditionalMean μ X Y m ∧ MemLp (m ∘ X) 2 μ) ∧
    (∀ m : ℝ → ℝ, isConditionalMean μ X Y m → MemLp (m ∘ X) 2 μ)

/-- T43, the zero-regressor-variance footnote and residuals. Use
ae_eq_integral_of_variance_eq_zero to replace X almost surely by E[X]. Every function
of X is then its value at E[X], so mse_general_identity_and_unique_minimum proves
optimality and the affine minimizing line. Centering Y and integral_const_mul give
the residual means; covariance of an a.s. constant covariate is zero. The risk
integrands are integrable by these same a.s. identities, even for non-Borel g,h.
About 120–220 lines. -/
def T43_L3 : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X Y : Ω → ℝ), MemLp X 2 μ → MemLp Y 2 μ → variance X μ = 0 → wholeZeroBlp μ X Y

private theorem meanEstimate_eq {Ω : Type u} (X : ℕ → Ω → ℝ) :
    wholeMeanVarianceEstimate X = fun n z => pluginVariance X n z / ((n : ℝ)-1) := by
  funext n z
  cases n with
  | zero => simp [wholeMeanVarianceEstimate, unbiasedSampleVariance, pluginVariance, sampleAverage]
  | succ n =>
    have hn : ((n+1 : ℕ) : ℝ) ≠ 0 := by positivity
    dsimp [wholeMeanVarianceEstimate, unbiasedSampleVariance]
    field_simp

/-- All T55 additions are algebra and applications of existing proved declarations. -/
theorem T55_assembly : T55WholeStatement.{u} := by
  constructor
  · intro Ω _ μ _ θhat Vhat θ hθ hV hnonneg ν _ hν hlim
    exact variance_estimate_scale_general_contract μ θhat Vhat θ hθ hV hnonneg ν hν hlim
  intro Ω _ μ _ X hiid h2 hv
  rw [meanEstimate_eq]
  obtain ⟨hvm, hvnn, hfin, hE, hCLT, hVC, hSE, hcent, hSEcent⟩ :=
    sample_mean_unbiased_variance_contract μ X hiid h2 hv
  have hvmean (n : ℕ) (hn : 0 < n) :
      (n : ℝ)*variance (sampleAverage X n) μ = variance (X 0) μ := by
    have hh := (iid_sample_mean_finite_moments μ X hiid h2 n hn).2
    change variance (sampleAverage X n) μ = variance (X 0) μ / (n : ℝ) at hh
    rw [hh, mul_div_cancel₀ _ (by exact_mod_cast hn.ne')]
  refine ⟨hvm, hvnn, ?_, ?_, hvmean, hCLT, hVC, hSE, ?_, ?_, hcent, hSEcent⟩
  · intro n hn z
    have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
    have hid := UnbiasedMeanVariance.n1_proof X n z (by omega)
    change (n : ℝ) * pluginVariance X n z = _ at hid
    refine ⟨?_, rfl⟩
    dsimp [unbiasedSampleVariance]
    rw [div_mul_eq_mul_div, hid]
    rfl
  · intro n hn
    have hn0 : 0 < n := by omega
    have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn0.ne'
    have hS : unbiasedSampleVariance X n =
        fun z => (n : ℝ) * (pluginVariance X n z / ((n : ℝ)-1)) := by
      funext z
      dsimp [unbiasedSampleVariance]
      ring
    constructor
    · rw [hS]
      change (∫ z, (n : ℝ) * (pluginVariance X n z / ((n : ℝ)-1)) ∂μ) = _
      rw [integral_const_mul]
      change (n : ℝ) * mean μ (fun z => pluginVariance X n z / ((n : ℝ)-1)) = _
      have hEn : mean μ (fun z => pluginVariance X n z / ((n : ℝ)-1)) =
          variance (X 0) μ / (n : ℝ) := hE n hn
      rw [hEn, mul_div_cancel₀ _ hnR]
    · exact (hE n hn).trans (iid_sample_mean_finite_moments μ X hiid h2 n hn0).2.symm
  · intro n hn z
    rw [hvmean n hn]
  · intro ε hε
    have heq : (fun (n : ℕ) => probability μ {z | ε ≤ dist
        ((n : ℝ)*(pluginVariance X n z / ((n : ℝ)-1)) -
          (n : ℝ)*variance (sampleAverage X n) μ) 0}) =ᶠ[atTop]
        (fun (n : ℕ) => probability μ {z | ε ≤ dist
          ((n : ℝ)*(pluginVariance X n z / ((n : ℝ)-1)) - variance (X 0) μ) 0}) := by
      filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
      rw [hvmean n hn]
    exact (hcent ε hε).congr' heq.symm

/-- Assemble the normal sum and bivariate-density donors with the new mixture and transport. -/
theorem T39_assembly (h1 : T39_L1) (h2 : T39_L2) (h3 : T39_L3)
    (h4 : T39_L4.{u}) : T39WholeStatement.{u} := by
  refine ⟨?_, ?_, h4, h1.1, h1.2.1, h1.2.2.1, h1.2.2.2, h2.1, h2.2.1, ?_,
    h3 h1.1 h1.2.2.1 h1.2.2.2⟩
  · intro Ω _
    constructor
    · intro μ _ n X hX hi m a v hv hlaw hreal b
      exact nontrivial_independent_normal_sum μ X hX hi m a v hv hlaw hreal b
    · intro mx my sx sy ρ hx hy hρ
      obtain ⟨hp, hpdf, hmx, hmy, hsx, hsy, hc, hz⟩ :=
        bivariate_normal_zero_correlation_independent_proof mx my sx sy ρ hx hy hρ
      obtain ⟨hX2, hY2, -, -⟩ := bivariate_normal_second_moments mx my sx sy ρ hx hy hρ
      refine ⟨hp, hpdf, hX2, hY2, hmx, hmy, hsx, hsy, ?_, hz⟩
      unfold correlationCoefficient
      change Real.sqrt (variance Prod.fst _) = sx at hsx
      change Real.sqrt (variance Prod.snd _) = sy at hsy
      rw [Bridge.bivariatePDF_eq, hsx, hsy]
      exact hc
  · intro Ω _ μ _ X hX m s hs hlaw
    have hM : MemLp id 2 (μ.map X) := hlaw ▸ memLp_id_gaussianReal' 2 (by norm_num)
    refine ⟨hM.comp_of_map hX.aemeasurable, ?_, ?_⟩
    · change (∫ z, X z ∂μ) = m
      calc
        _ = ∫ x : ℝ, x ∂μ.map X :=
          (integral_map hX.aemeasurable measurable_id.aestronglyMeasurable).symm
        _ = m := by rw [hlaw]; exact integral_id_gaussianReal
    · have hvar : variance X μ = s^2 := by
        calc
          _ = variance id (μ.map X) := (variance_id_map hX.aemeasurable).symm
          _ = s^2 := by rw [hlaw]; exact variance_id_gaussianReal
      rw [hvar]
      exact Real.sqrt_sq hs.le
  · simp [correlationCoefficient, h2.2.2]

/-- Assemble the positive-variance regression donor after removing the supplied-CEF gates. -/
theorem T43_assembly (h1 : T43_L1.{u}) (h2 : T43_L2.{u}) (h3 : T43_L3.{u}) :
    T43WholeStatement.{u} := by
  intro Ω _ μ _ X Y hX hY hX2 hY2
  obtain ⟨hex, hall⟩ := h2 μ X Y hX hY2
  refine ⟨h1 μ X Y hX2 hY2, hex, hall, ?_, h3 μ X Y hX2 hY2⟩
  intro hv
  obtain ⟨m, hm, hm2⟩ := hex
  obtain ⟨-, hN, hmin⟩ := blp_corrected_derivatives_and_minimum μ X Y hX2 hY2 hv
  obtain ⟨-, -, -, hR, hXR, hcov, -⟩ :=
    blp_hessian_and_cef_corollaries μ X Y hX2 hY2 hv m hm hm2
  refine ⟨hN, hmin, mul_pos (by norm_num) hv, hR, hXR, hcov, ?_⟩
  intro m' hm'
  obtain ⟨-, -, hbest, -, -, -, hlinear⟩ :=
    blp_hessian_and_cef_corollaries μ X Y hX2 hY2 hv m' hm' (hall m' hm')
  exact ⟨hbest, hlinear⟩

/-- All T46 conclusions follow from existing moment, CEF and regression donors. -/
theorem T46_assembly : T46WholeStatement.{u} := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro Ω _ μ _ X W hX hW hi hx hw
    obtain ⟨hCEF, hmX, hmX2, hmX3, hvX, hmY, hcov, hs, ha⟩ :=
      quadratic_cef_factor_ten μ X W hX hW hi hx hw
    have hmin := (uniform_quadratic_cef_unique_blp μ X W hX hW hi hx hw).2.2.2
    obtain ⟨hX2, hXX2, hW2⟩ := QuadraticUniqueBlp.n1_proof μ X W hX hW hx hw
    exact ⟨hX2, (hXX2.const_mul 10).add hW2, hCEF, hmX, hmX2, hmX3, hvX,
      hmY, hcov, hs, ha, hmin⟩
  · intro Ω _ μ _ X Y _ _ hX2 hY2 hv
    exact (blp_corrected_derivatives_and_minimum μ X Y hX2 hY2 hv).2.2
  · intro Ω _ μ _ X Y hX hY hYi hi
    exact independent_constant_cef μ X Y hX hY hYi hi
  · intro Ω _ μ _ X W hX hW hi hx hw Y
    obtain ⟨hCEF, hmX, hmX2, hmX3, hvX, hmY, hcov, hs, ha⟩ :=
      quadratic_cef_factor_ten μ X W hX hW hi hx hw
    obtain ⟨hX2, hXX2, hW2⟩ := QuadraticUniqueBlp.n1_proof μ X W hX hW hx hw
    have hW0 : expectation μ W = 0 := by
      unfold expectation
      calc
        _ = ∫ x : ℝ, x ∂μ.map W :=
          (integral_map hW.aemeasurable measurable_id.aestronglyMeasurable).symm
        _ = 0 := by rw [hw]; exact integral_id_gaussianReal
    have hSq : isConditionalMean μ X (fun z => (X z)^2) (fun x => x^2) :=
      ⟨by fun_prop, hXX2.integrable one_le_two, hXX2.integrable one_le_two,
        fun _ _ => rfl⟩
    have hNoise : isConditionalMean μ X W (fun _ => 0) := by
      have hh : isConditionalMean μ X W (fun _ => expectation μ W) :=
        independent_constant_cef μ X W hX hW (hW2.integrable one_le_two) hi
      simpa only [hW0] using hh
    have hCY := (isCEF_condExp μ X hX Y (fun x => 10*x^2) hCEF).symm
    have hCS := isCEF_condExp μ X hX (fun z => (X z)^2) (fun x => x^2) hSq
    have hCW := isCEF_condExp μ X hX W (fun _ => 0) hNoise
    refine ⟨hSq, hNoise, ?_, hCY, ?_, ?_, ?_⟩
    · filter_upwards [hCY, hCS, hCW] with z hy' hs' hw'
      dsimp [Function.comp_def] at hy' hs' hw'
      calc
        _ = 10 * (X z)^2 := hy'
        _ = _ := by rw [← hs', ← hw']; ring
    · change expectation μ X = 1/2 at hmX
      change expectation μ (fun z => (X z)^2) = 1/3 at hmX2
      change expectation μ (fun z => (X z)^3) = 1/4 at hmX3
      rw [hcov, hmX3, hmX, hmX2]
      norm_num
    · change regressionSlope μ X Y = 10 at hs
      rw [hs]
      norm_num
    · change regressionIntercept μ X Y = -5/3 at ha
      rw [ha]
      norm_num



end
end SAP.P001c.WH.W2
