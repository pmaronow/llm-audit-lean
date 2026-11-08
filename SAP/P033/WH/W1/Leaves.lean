import SAP.P033.WH.W1.Moments

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u v w

namespace SAP.P033.WH.W1

open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators Topology ContDiff

noncomputable section

/-- Physical support and finite-sum reduction. Normalize x_j by h=1/n, use
j.val<n iff the triangular weight is positive (the boundary j.val=n has weight
zero), then sum along wholeActiveIndex. Fin.card_filter_val_lt counts the
support. Finset.sum_bij or a sum over the first n indices proves both reduction
identities; the second works for arbitrary padded weights. About 100 lines. -/
def T4_L1 : Prop :=
  ∀ n : ℕ, 3 ≤ n → wholePhysicalGeometry n

/-- Nonsingularity at degrees one and two, including the five repeated records
and the outer zero rows. The first p+1 active nodes are distinct and have
strictly positive weights. A vector in the Gram kernel gives a degree-p
polynomial vanishing on them; use a Vandermonde minor to make that vector zero.
Equivalently use positive definiteness of the weighted Gram matrix and
Matrix.PosDef.isUnit. Apply the same argument to the physical nodes, or use
G_physical = 5 D_h G_normalized D_h. The supplied geometry is a proved design
fact in the assembly, not a rank assumption on data. About 150–250 lines. -/
def T4_L2 : Prop :=
  ∀ n : ℕ, 3 ≤ n → wholePhysicalGeometry n → wholePhysicalRank n

/-- Rescale WLS coefficients for arbitrary real record outcomes, not just the
cluster-constant sign realization. Delete zero rows with the geometry sum
identity, aggregate the five records to their means, and put
D_h=diag(h^r). The Gram and RHS are 5 D_h G D_h and 5 D_h RHS_normalized.
Use nonsingularity to solve the normal equations uniquely, giving
h^r beta_physical,r = beta_normalized,r. No equality of record outcomes is
assumed. About 150–250 lines. -/
def T4_L3 : Prop :=
  ∀ n : ℕ, 3 ≤ n → wholePhysicalGeometry n → wholePhysicalRank n →
    wholePhysicalRescaling n

/-- Normalized linear intercept row and the same-bandwidth bias correction.
For the linear row invert the two-by-two moment Gram matrix and use the
positive determinant in AronowAudit.P033.shrinking_wls_certificate. For the
correction, the first two quadratic normal equations imply that the linear fit
of the quadratic fitted values has intercept beta_0 + m beta_2, where
m=sum_j a_j u_j^2; the remaining residual is orthogonal to 1 and u. Thus
subtracting m times the quadratic curvature leaves its intercept. The rank
premise makes both inverse-defined fits actual unique WLS solutions.
About 150–250 lines, without computing a general three-by-three inverse. -/
def T4_L4 : Prop :=
  ∀ n : ℕ, 3 ≤ n → wholePhysicalRank n → wholeNormalizedRows n

/-- Physical linear-intercept weights and the bias moment's units. Reduce
physical moments to h^k times shrinkingMoment n k using the geometry. Their
linear Gram determinant is h^2 times the positive normalized determinant.
Cancellation in the displayed intercept formula gives the active coefficients
shrinkingIntercept n and zero outside the support. Sum again to obtain
m_physical=h^2 m_normalized. Only finite algebra and nonzero denominators are
needed; about 100–180 lines. -/
def T4_L5 : Prop :=
  ∀ n : ℕ, 3 ≤ n → wholePhysicalGeometry n →
    (∀ j, wholePhysicalIntercept n j = wholePaddedWeight n (shrinkingIntercept n) j) ∧
    wholePhysicalBiasMoment n = wholeBandwidth n ^ 2 *
      (∑ j, shrinkingIntercept n j * shrinkingDistance n j ^ 2)

/-- Sampling moments on the full physical sign cubes, with arbitrary active
weights. Expand each estimator as a weighted sum of independent symmetric
signs and use AronowAudit.P033.weighted_sign_moments. Outer coefficients are
zero, so their square sum reduces to the active one. In the noisy model each
cluster sign has coefficient a and its five independent record signs have
coefficients a/5; their square sum is a^2+5(a/5)^2=(6/5)a^2 on each side.
Do not enumerate either sign cube. About 100–180 lines. -/
def T4_L6 : Prop :=
  ∀ n : ℕ, 3 ≤ n → ∀ a : Fin n → ℝ,
    finiteMean (wholePaddedSignEstimator n a) = 0 ∧
    finiteVariance (wholePaddedSignEstimator n a) = 2 * ∑ j, a j ^ 2 ∧
    finiteMean (wholePaddedNoisyEstimator n a) = 0 ∧
    finiteVariance (wholePaddedNoisyEstimator n a) = (6/5) * (2 * ∑ j, a j ^ 2)

/-- All new one-side moment steps have short proofs in Moments; no open leaves. -/
theorem T1_assembly : T1WholeStatement := by
  refine ⟨existing_T1, critical_well_defined, score_probability, population_probability,
    potential_moments, fixed_kernel_eq, rd_estimator_memLp m1Linear,
    rd_estimator_memLp m1Corrected, ?_⟩
  intro side
  exact ⟨side_sum_memLp side m1Linear, side_sum_memLp side m1Bias,
    side_sum_memLp side m1Corrected, side_probability_certificate side⟩

/-- The omitted smoothness is polynomial calculus and needs no proof leaf. -/
theorem T2_assembly : T2WholeStatement.{u, v, w} := by
  have hZ : HasLaw (fun Y => (rdEstimator m1Linear Y-4)/m1SELinear)
      (gaussianReal 0 1) (rdConditionalLaw m2Treated m1Control) :=
    existing_T2.{u, v, w}.2.2.2.2.2.1
  have hZLp := hZ.memLp (memLp_id_gaussianReal (μ := 0) (v := 1) 2)
  refine ⟨existing_T2, critical_well_defined, ?_, ?_, ?_, ?_, ?_, ?_,
    AronowAudit.P033.Wave1.GP010P033B1b_t2_printed_threshold,
    hZLp.integrable_sq, ?_, ?_, by norm_num⟩
  · unfold m1Control
    fun_prop
  · unfold m1Treated
    fun_prop
  · unfold m2Perturbation
    fun_prop
  · unfold m2Treated m1Treated m2Perturbation
    fun_prop
  · change MemLp (AronowAudit.P033.rdEstimator AronowAudit.P033.m1Linear) 2
      (AronowAudit.P033.rdConditionalLaw AronowAudit.P033.m2Treated AronowAudit.P033.m1Control)
    rw [AronowAudit.P033.m2_conditional_law_eq]
    exact rd_estimator_memLp m1Linear
  · have hc := AronowAudit.P033.Wave1.GP010P033B1b_t2_central_lower 5 (by norm_num)
    rw [AronowAudit.P033.Wave1.GP010P033B1b_t1_normal_central_mass 5 (by norm_num)] at hc
    change 1-1/(5 : ℝ)^2 ≤ 2*normalCDF 5-1 at hc
    linarith
  · have hv := variance_fun_id_gaussianReal (μ := 0) (v := 1)
    rw [variance_eq_integral measurable_id'.aemeasurable] at hv
    simp only [integral_id_gaussianReal, sub_zero, NNReal.coe_one] at hv
    have he := hZ.integral_comp (f := fun x : ℝ => x^2) (by fun_prop)
    simpa only [Function.comp_def] using he.trans hv
  · rcases existing_T1.1 with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hp, _⟩
    exact hp

theorem T4_assembly (h1 : T4_L1) (h2 : T4_L2) (h3 : T4_L3)
    (h4 : T4_L4) (h5 : T4_L5) (h6 : T4_L6) : T4WholeStatement.{u, v} := by
  refine ⟨SAP.P033.Bridge.T4_correspondence.mpr
    (@AronowAudit.P033.clustered_variance_correction), ?_, contDiff_const, ?_⟩
  · change Tendsto (fun n : ℕ => 1/(n : ℝ)) atTop (𝓝 0)
    simpa only [one_div, Function.comp_def] using
      (tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop (R := ℝ)))
  intro n hn
  have hg := h1 n hn
  have hr := h2 n hn hg
  have hs := h3 n hn hg hr
  have hnr := h4 n hn hr
  rcases h5 n hn hg with ⟨ha, hm⟩
  have hpad := hg.2.2.2.2.2.2
  have hrow (y : Fin (n*(n+1)) → Fin 5 → ℝ) :
      wholePhysicalFit n 1 y 0 = ∑ j, wholePhysicalIntercept n j * wholeClusterMean n y j := by
    have hh := hs 1 (Or.inl rfl) y 0
    norm_num only [Fin.val_zero, pow_zero, one_mul] at hh
    rw [hh, hnr.1]
    simp_rw [ha]
    exact (hpad (shrinkingIntercept n) (wholeClusterMean n y)).symm
  have hbc (y : Fin (n*(n+1)) → Fin 5 → ℝ) :
      wholePhysicalCorrected n y = wholeNormalizedCorrected n (wholeActiveMean n y) ∧
      wholePhysicalCorrected n y = wholePhysicalFit n 2 y 0 := by
    have hl := hs 1 (Or.inl rfl) y 0
    have hq := hs 2 (Or.inr rfl) y 2
    have hz := hs 2 (Or.inr rfl) y 0
    norm_num only [Fin.val_zero, Fin.val_two, pow_zero, one_mul] at hl hq hz
    have he : wholePhysicalCorrected n y =
        wholeNormalizedCorrected n (wholeActiveMean n y) := by
      unfold wholePhysicalCorrected wholeNormalizedCorrected
      rw [hl, hm, ← hq]
      ring
    exact ⟨he, he.trans ((hnr.2 _).trans hz.symm)⟩
  have he (y : (Fin 2 × Fin (n*(n+1))) → Fin 5 → ℝ) :
      wholePhysicalEstimator n y = wholePaddedEstimator n (shrinkingIntercept n) y := by
    unfold wholePhysicalEstimator wholePaddedEstimator
    simp_rw [ha]
  have heS : wholePhysicalSignEstimator n = wholePaddedSignEstimator n (shrinkingIntercept n) := by
    funext data
    exact he _
  have heN : wholePhysicalNoisyEstimator n = wholePaddedNoisyEstimator n (shrinkingIntercept n) := by
    funext data
    exact he _
  have hprob := h6 n hn (shrinkingIntercept n)
  rw [← heS, ← heN] at hprob
  change finiteMean (wholePhysicalSignEstimator n) = 0 ∧
    finiteVariance (wholePhysicalSignEstimator n) = shrinkingVariance n ∧
    finiteMean (wholePhysicalNoisyEstimator n) = 0 ∧
    finiteVariance (wholePhysicalNoisyEstimator n) = (6/5)*shrinkingVariance n at hprob
  refine ⟨hg, hr, ⟨hs, hrow, ha, hm, hbc⟩, hprob.1, hprob.2.1,
    hprob.2.2.1, hprob.2.2.2, ?_⟩
  intro f ell y
  have hzero (g : Fin 2 × Fin (n*(n+1))) : (∑ i, nnResidual (y g) i) = 0 :=
    AronowAudit.P033.nn_residual_sum (by norm_num : 2 ≤ 5) (y g)
  simp [hzero]

/-- The existing denominator guards express exactly the claim's presuppositions. -/
theorem T5_assembly : T5WholeStatement := by
  exact SAP.P033.Bridge.T5_of_project AronowAudit.P033.count_standardization_counterexample

end
end SAP.P033.WH.W1
