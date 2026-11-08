import SAP.P037a.Defs.WholeW1
import SAP.P037a.Bridge
import AronowAudit.P037.P037_FiniteDesign
import AronowAudit.P037.P037_ReportedNumbers
import AronowAudit.P037.P037_Bootstrap
import AronowAudit.P037.Wave1.Gap.GP037B4b
import AronowAudit.P053.P053_NormalQuantiles

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P037a.WH.W1

open MeasureTheory ProbabilityTheory Set Filter SAP.P037a.Bridge
open scoped BigOperators ENNReal NNReal Classical Topology

/-- Complete supports of the four-stratum count laws, and 454 positive
collapsed states. Prove the one-referent support by nonnegative convolution
and zero mass above four; for three referents distribute any k≤12 among
four counts ≤3, all of positive mass. Count by the six treated pairs:
5² + 4·5·13 + 13². Finite rational enumeration is also a valid route, but
use kernel-checked arithmetic and factor the school sums before counting. -/
def T1_L1 : Prop := compositionFullSupport

/-- Existence of an actual least-squares minimizer for each finite block
sample, with no rank assumption. View predictions as the image of the
linear map from block intercepts and three slopes to Euclidean observation
space. This finite-dimensional subspace is closed, hence admits an
orthogonal projection of the observed response. Pull that projection back
to parameters. Include B=0, where every loss is zero. -/
def T1_L2 : Prop := blockOLSExists

/-- Profiling actual minimizers gives the pooled within-block normal
equations. Vary one block intercept to obtain its residual sum zero; vary
each slope to obtain the column-residual cross-product zero. Substitute
the intercept equations, expand the finite sums, and recover the centered
cross-product used by `pooledCompositionGram`. No inverse or rank premise
is needed, and B=0 is included. This is a quadratic-polynomial argument. -/
def T1_L3 : Prop := ∀ B (w : Fin B → CompositionAssignment)
  (alpha : Fin B → ℝ) (theta : Fin 3 → ℝ), IsBlockOLS w alpha theta →
  (pooledCompositionGram w).mulVec theta = pooledCompositionRhs w

/-- CDF-to-finite-integral identity for z≥0. Use the Gaussian density,
the already proved normal CDF at zero, and the integral over (0,z];
the density there is exp(-t²/2)/sqrt(2π). Its continuity supplies all
integrability obligations. This step assumes no numerical tail bound. -/
def T3_L1 : Prop := ∀ z : ℝ, 0 ≤ z →
  wholeNormalCDF z = 1/2 + (1 / Real.sqrt (2*Real.pi)) *
    ∫ t : ℝ in (0:ℝ)..z, Real.exp (-t^2/2)

noncomputable def expTaylor (d : ℕ) (u : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (d+1), (-u)^k / k.factorial

/-- Signed Taylor enclosures, globally for u≥0: odd degree 25 is a
lower bound and even degree 24 an upper bound for exp(-u). Use Taylor's
Lagrange remainder at zero and iterated derivatives (-1)^k exp(-u);
the remainder has the needed sign. Handle u=0 separately. Smoothness is
`ContDiff ℝ ∞`, or the finite differentiability order actually needed. -/
def T3_L2 : Prop := ∀ u : ℝ, 0 ≤ u →
  expTaylor 25 u ≤ Real.exp (-u) ∧ Real.exp (-u) ≤ expTaylor 24 u

noncomputable def gaussianTaylorIntegral (d : ℕ) (z : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (d+1),
    (-1:ℝ)^k * z^(2*k+1) / ((2:ℝ)^k * k.factorial * (2*k+1))

def normalTaylorEnclosure : Prop := ∀ z : ℝ, 0 ≤ z →
  1 - 2 * gaussianTaylorIntegral 24 z / Real.sqrt (2*Real.pi) ≤ wholeNormalTail z ∧
  wholeNormalTail z ≤ 1 - 2 * gaussianTaylorIntegral 25 z / Real.sqrt (2*Real.pi)

/-- Integrate the signed Taylor inequalities on [0,z], substituting
u=t²/2. Finite sums and `integral_pow` give exactly
`gaussianTaylorIntegral`; positivity of sqrt(2π) and the CDF identity give
the two tail bounds. The analytic premises are the previous two leaves;
no tail or quantile estimate is a premise. Continuous functions on the
compact interval provide integrability for every comparison. -/
def T3_L3 : Prop := T3_L1 → T3_L2 → normalTaylorEnclosure

/-- Exact numerical certificates from the preceding enclosure. First
bound sqrt(2π) between 2.50662827463100050241 and
2.50662827463100050243 by squaring, using `Real.pi_gt_d20` and
`Real.pi_lt_d20`. Evaluate the degree-24/25 rational polynomials at
1.9, 2, 1.95996, 1.95997 and the six displayed ratios. Rational
cross-multiplication proves the strict margins and the five-decimal error
bounds. `scratch/gaussian_certificates.py` independently checks all the
exact fractions and signs; the Lean proof must certify them too. -/
def T3_L4 : Prop := normalTaylorEnclosure → wholeNormalNumbers

/-- Geometry of the inverse coordinates (p,t)↦(tp,t(1-∑p)). On the
open simplex times t>0 this is a bijection onto the positive orthant, with
the explicitly defined inverse. Differentiate its polynomial coordinates.
For the determinant, the top-left block is tI, and its Schur complement
is (1-∑p)+∑p=1; hence the absolute determinant is t^(n+1).
This is the inverse-map Jacobian, with n+2 school weights. -/
def T4_L1 : Prop := ∀ n : ℕ,
  BijOn (simplexConeMap n) (simplexCone n) (positiveOrthant n) ∧
  (∀ e ∈ positiveOrthant n,
    simplexConeInverse n e ∈ simplexCone n ∧
    simplexConeMap n (simplexConeInverse n e) = e) ∧
  (∀ x ∈ simplexCone n,
    simplexConeInverse n (simplexConeMap n x) = x ∧
    HasFDerivAt (simplexConeMap n)
      (Matrix.toLin' (simplexConeJacobian n x)).toContinuousLinearMap x ∧
    |(simplexConeJacobian n x).det| = x (Fin.last (n+1))^(n+1))

/-- Product exponential density with respect to ordinary coordinate
Lebesgue measure. Expand `expMeasure` and its positive-half-line density;
combine the coordinate densities with the finite-product withDensity
formula (or induction using `prod_withDensity` and the volume-preserving
Fin-splitting equivalence). Product exp(-e_i) is exp(-∑e_i).
This is a density identity, not an assumed gamma-Dirichlet theorem. -/
def T4_L2 : Prop := ∀ n : ℕ,
  exponentialProduct n = (volume.restrict (positiveOrthant n)).withDensity
    (fun e => ENNReal.ofReal (Real.exp (-(∑ i, e i))))

/-- Change variables using the proved inverse-coordinate geometry and
product density. Apply the injective Jacobian change-of-variables theorem
on the measurable open cone, multiply by exp(-∑e), and use ∑e=t there.
Pull back with the explicit inverse; conclude the joint density
t^(n+1)exp(-t). Establish measurability before using map or withDensity.
Both mathematical inputs are explicit leaf premises. -/
def T4_L3 : Prop := T4_L1 → T4_L2 → exponentialJointLaw

/-- Marginalize the joint cone density. Split the last coordinate by
the volume-preserving Fin-snoc equivalence, apply Tonelli, and use
`simplex_gamma_integral (n+1)` to integrate t. Append the final simplex
coordinate to get the normalized-exponential law. Transfer probability
normalization from the product exponential law and prove positivity and
unit sum on the open simplex. No unproved literature premise is allowed. -/
def T4_L4 : Prop := exponentialJointLaw → exponentialSimplexLaw

/-- Transport the product calculation to arbitrary independent measurable
draws on a probability space, without assuming independence between the
uniform and exponential families. Use `iIndepFun.map_fun_eq_pi_map` for
each joint law. Uniforms are in (0,1) and exponentials in (0,∞) almost
surely, so all denominators are positive; apply the already proved ratio
cancellation there. Evaluate the normalized events through their laws
using the existing 1/6 and simplex 1/4 donor. The exponential raw event
has the same probability by almost-everywhere equality of events. -/
def T4_L5 : Prop := exponentialSimplexLaw → bootstrapRandomComparison

/-- Full column rank and positive weights make the weighted Gram matrix
positive definite: its quadratic form is ∑ w_i (Xv)_i², positive for
v≠0 by injectivity. Thus its determinant is nonzero. Expand WLS into
G b=h, apply the matrix inverse for existence and injectivity for
uniqueness. Include empty K (the determinant is one); no nonempty row
type is needed when K is empty. -/
def T4_L6 : Prop := wlsRegularity

private theorem composition_finite : T1Statement := by
  refine ⟨AronowAudit.P037.composition_witness_counterexample,
    AronowAudit.P037.witness_expected_normal_equations, ?_,
    AronowAudit.P037.witness_mixture_causal_curve,
    AronowAudit.P037.composition_witness_mixture,
    ⟨witness_mixture_observed, witness_mixture_potential⟩⟩
  change AronowAudit.P037.witnessGram.det = 31/60000 ∧
    AronowAudit.P037.witnessGram.det ≠ 0
  rw [AronowAudit.P037.witness_expected_normal_equations.1]
  norm_num [Matrix.det_fin_three]

private theorem composition_conditional (h : T1Statement) : compositionConditionalMoments := by
  intro i
  have hm := h.1.2.2.1 i
  dsimp
  rw [hm.1]
  refine ⟨by norm_num, ?_, ?_, ?_⟩
  · linarith [hm.2.1]
  · linarith [hm.2.2]
  · unfold eligibleFraction
    split_ifs <;> norm_num

private theorem inverse_coefficient_limit (eps : ℝ) (heps : 0 < eps) :
    Tendsto (fun B => repeatedCompositionProbability B
      (fun w => eps < |pooledCompositionCoefficient w 2 - (-16/31)|)) atTop (𝓝 0) := by
  exact AronowAudit.P037.witness_ols_probability_limit eps heps

private theorem repeated_nonneg (B : ℕ)
    (A : (Fin B → CompositionAssignment) → Prop) :
    0 ≤ repeatedCompositionProbability B A := by
  unfold repeatedCompositionProbability
  apply Finset.sum_nonneg
  intro w _
  exact mul_nonneg (Finset.prod_nonneg (fun b _ =>
    AronowAudit.P037.witness_state_probability_law.1 (w b))) (by split_ifs <;> norm_num)

private theorem repeated_mono (B : ℕ) (A C : (Fin B → CompositionAssignment) → Prop)
    (h : ∀ w, A w → C w) :
    repeatedCompositionProbability B A ≤ repeatedCompositionProbability B C := by
  exact AronowAudit.P037.WitnessCompletion.probability_mono
    (AronowAudit.P037.productDesign (fun _ : Fin B =>
      AronowAudit.P037.WitnessCompletion.witnessDesign)) A C h

private theorem singular_limit : blockSingularProbabilityLimit := by
  apply squeeze_zero (fun B => repeated_nonneg B _)
    (fun B => repeated_mono B _ _ ?_) (inverse_coefficient_limit (8/31) (by norm_num))
  intro w hw
  have hzero : (pooledCompositionGram w)⁻¹ = 0 :=
    Matrix.nonsing_inv_apply_not_isUnit _ (by rw [hw]; norm_num)
  simp only [pooledCompositionCoefficient, hzero, Matrix.zero_mulVec, Pi.zero_apply]
  norm_num

private theorem ols_limit (profile : T1_L3) : blockOLSProbabilityLimit := by
  intro alpha theta hmin eps heps
  have hsum := singular_limit.add (inverse_coefficient_limit eps heps)
  simp only [add_zero] at hsum
  apply squeeze_zero (fun B => repeated_nonneg B _) (fun B => ?_) hsum
  unfold repeatedCompositionProbability
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro w _
  have hw : 0 ≤ ∏ b, assignmentMass (w b) :=
    Finset.prod_nonneg (fun b _ => AronowAudit.P037.witness_state_probability_law.1 (w b))
  by_cases hdet : (pooledCompositionGram w).det = 0
  · simp only [hdet, ite_true]
    split_ifs <;> nlinarith
  · have htheta : theta B w = pooledCompositionCoefficient w := by
      have hn := profile B w (alpha B w) (theta B w) (hmin B w)
      unfold pooledCompositionCoefficient
      rw [← hn, Matrix.mulVec_mulVec,
        Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hdet), Matrix.one_mulVec]
    simp only [hdet, ite_false, mul_zero, zero_add, htheta]
    exact le_rfl

theorem T1_assembly (h1 : T1_L1) (h2 : T1_L2) (h3 : T1_L3) : T1WholeStatement := by
  exact ⟨composition_finite, h1, composition_conditional composition_finite,
    h2, singular_limit, ols_limit h3⟩

private theorem wald_finite : T3Statement :=
  ⟨AronowAudit.P037.significance_claims_incompatible,
    AronowAudit.P037.rounded_wald_opposite_decisions,
    AronowAudit.P037.wald_rounding_envelope,
    AronowAudit.P037.wald_envelope_attainable⟩

private theorem wald_rounding : wholeWaldRounding := by
  intro e s he h
  change e < 0 ∧ 11/200 < |e| ∧ |e| < 13/200 ∧ 1/40 < s ∧ s < 7/200 at h
  rw [abs_of_neg he] at h
  have hrE : round (100*e) = (-6:ℤ) := round_eq_iff.mpr ⟨by norm_num; linarith, by norm_num; linarith⟩
  have hrS : round (100*s) = (3:ℤ) := round_eq_iff.mpr ⟨by norm_num; linarith, by norm_num; linarith⟩
  norm_num [roundHundredth, hrE, hrS]

private theorem normal_critical_cdf : wholeNormalCDF wholeNormalCritical = 39/40 := by
  have h := AronowAudit.P053.NormalCompletion.normalCritical_cdf (1/20) (by norm_num) (by norm_num)
  rw [AronowAudit.P053.NormalCompletion.standardNormalCDF_eq_cdf] at h
  convert h using 1 <;> norm_num [wholeNormalCritical, wholeNormalCDF,
    AronowAudit.P053.normalCritical, AronowAudit.P053.standardNormalCDF,
    ProbabilityTheory.cdf_eq_real, Measure.real_def]

private theorem normal_quantile (hn : wholeNormalNumbers) : wholeNormalQuantile := by
  have hm : StrictMono wholeNormalCDF := AronowAudit.P053.NormalCompletion.strictMono_normal_cdf
  have hq := normal_critical_cdf
  have lo : 19/10 < wholeNormalCritical := hm.lt_iff_lt.mp (by
    have h := hn.1
    dsimp [wholeNormalTail] at h
    linarith)
  have hi : wholeNormalCritical < 2 := hm.lt_iff_lt.mp (by
    have h := hn.2.1
    dsimp [wholeNormalTail] at h
    linarith)
  have lof : 195996/100000 < wholeNormalCritical := hm.lt_iff_lt.mp (by
    have h := hn.2.2.1
    dsimp [wholeNormalTail] at h
    linarith)
  have hif : wholeNormalCritical < 195997/100000 := hm.lt_iff_lt.mp (by
    have h := hn.2.2.2.1
    dsimp [wholeNormalTail] at h
    linarith)
  exact ⟨hq, fun z => ⟨fun hz => hm.injective (hz.trans hq.symm), fun hz => hz ▸ hq⟩,
    lo, hi, lof, hif, by linarith, by linarith⟩

private theorem normal_decisions (hn : wholeNormalNumbers) : wholeNormalDecisions := by
  have hc := wald_finite.2.1 (19/10) ⟨le_rfl, by norm_num⟩
  have hm : StrictAnti wholeNormalTail := by
    intro x y hxy
    have h := AronowAudit.P053.NormalCompletion.strictMono_normal_cdf hxy
    dsimp [wholeNormalTail, wholeNormalCDF]
    linarith
  have ha : wholeNormalTail (waldStatistic (-57/1000) (7/250)) < 1/20 := by
    rw [hc.2.2.1]
    exact lt_trans (hm (by norm_num : (2:ℝ) < 57/28)) hn.2.1
  have hb : 1/20 < wholeNormalTail (waldStatistic (-57/1000) (17/500)) := by
    rw [hc.2.2.2.1]
    exact lt_trans hn.1 (hm (by norm_num : (57/34:ℝ) < 19/10))
  have ra := wald_rounding (-57/1000) (7/250) (by norm_num) hc.1
  have rb := wald_rounding (-57/1000) (17/500) (by norm_num) hc.2.1
  exact ⟨ha, hb, -57/1000, 7/250, -57/1000, 17/500,
    by norm_num, by norm_num, hc.1, hc.2.1, ra.1, rb.1, ra.2, rb.2, ha, hb⟩

theorem T3_assembly (h1 : T3_L1) (h2 : T3_L2) (h3 : T3_L3) (h4 : T3_L4) :
    T3WholeStatement := by
  have hn := h4 (h3 h1 h2)
  exact ⟨wald_finite, wald_rounding, hn, normal_quantile hn, normal_decisions hn⟩

private theorem bootstrap_finite : T4Statement := by
  refine ⟨AronowAudit.P037.Wave1.uniform_weights_not_bayesian_bootstrap_proof,
    AronowAudit.P037.bootstrap_ratio_cancellation,
    AronowAudit.P037.uniform_witness_integral,
    AronowAudit.P037.exponential_witness_integrals,
    AronowAudit.P037.weighted_least_squares_scale, ?_, ?_⟩
  · intro n
    have h := AronowAudit.P037.Wave1.uniform_weights_not_bayesian_bootstrap_proof n
    constructor
    · intro ht
      have hp := h.1
      change uniformWeightLaw n (ratioEvent n) = ⊤ at ht
      change (uniformWeightLaw n (ratioEvent n)).toReal = 1/6 at hp
      rw [ht, ENNReal.toReal_top] at hp
      norm_num at hp
    · intro ht
      have hp := h.2.1
      change (simplexLaw (n+1) (ratioEvent n)).toReal = 1/4 at hp
      rw [ht, ENNReal.toReal_top] at hp
      norm_num at hp
  · intro K _ _ n w X y hw hX
    have hs : 0 < ∑ i, w i := Finset.sum_pos (fun i _ => hw i) Finset.univ_nonempty
    have h := (AronowAudit.P037.weighted_least_squares_scale w X y 0 hw hX
      (1 / ∑ i, w i) (one_div_pos.mpr hs)).1
    have hwEq : normalizedWeights w = (fun i => (1 / ∑ j, w j) * w i) := by
      funext i
      simp only [normalizedWeights, div_eq_mul_inv, one_mul]
      ring
    rw [hwEq]
    exact h

private theorem combined_integral : exponentialCombinedIntegral := by
  have heq : (fun v : ℝ => Real.exp (-v) * (1 - Real.exp (-v/3))) =
      (fun v => Real.exp (-v) - Real.exp (-(4/3)*v)) := by
    funext v
    rw [mul_sub, mul_one, ← Real.exp_add]
    congr 2
    ring
  rw [exponentialCombinedIntegral, heq]
  have h1 := integrableOn_exp_neg_Ioi (0:ℝ)
  have h2 := integrableOn_exp_mul_Ioi (by norm_num : (-(4/3):ℝ) < 0) (0:ℝ)
  refine ⟨h1.sub h2, ?_⟩
  rw [integral_sub h1 h2, AronowAudit.P037.exponential_witness_integrals.1,
    AronowAudit.P037.exponential_witness_integrals.2.1]
  norm_num

theorem T4_assembly (h1 : T4_L1) (h2 : T4_L2) (h3 : T4_L3)
    (h4 : T4_L4) (h5 : T4_L5) (h6 : T4_L6) : T4WholeStatement := by
  have hs := h4 (h3 h1 h2)
  exact ⟨bootstrap_finite, hs, h5 hs, combined_integral, h6⟩

private theorem two_forward_derivative :
    HasFDerivAt twoExponentialForward twoExponentialForwardDerivative ![1,1] := by
  have h0 := hasFDerivAt_apply (𝕜 := ℝ) (0 : Fin 2) (![1,1] : Fin 2 → ℝ)
  have h1 := hasFDerivAt_apply (𝕜 := ℝ) (1 : Fin 2) (![1,1] : Fin 2 → ℝ)
  have hs := h0.add h1
  have hnz : ((fun e : Fin 2 → ℝ => e 0 + e 1) (![1,1])) ≠ 0 := by norm_num
  have hi := (hasDerivAt_inv hnz).comp_hasFDerivAt (![1,1] : Fin 2 → ℝ) hs
  have hr := h0.mul hi
  apply hasFDerivAt_pi'.mpr
  intro i
  fin_cases i
  · convert hr using 1
    · ext e
      simp [twoExponentialForward, div_eq_mul_inv]
    · ext e
      norm_num [twoExponentialForwardDerivative, Matrix.toLin'_apply,
        Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      ring
  · convert hs using 1
    · ext e
      simp [twoExponentialForward]
    · ext e
      norm_num [twoExponentialForwardDerivative, Matrix.toLin'_apply,
        Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem T5_assembly : T5WholeStatement := by
  refine ⟨?_, ?_, ?_, two_forward_derivative, ?_, ?_⟩
  · intro i
    fin_cases i <;> norm_num
  · norm_num [Fin.sum_univ_two]
  · norm_num [twoExponentialForward]
  · norm_num [Matrix.det_fin_two]
  · norm_num [Matrix.det_fin_two, Fin.sum_univ_two]

end SAP.P037a.WH.W1
