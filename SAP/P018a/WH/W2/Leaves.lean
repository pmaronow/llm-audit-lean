import SAP.P018a.Defs.WholeW2
import SAP.P018a.Bridge
import AronowAudit.P018.Wave1.Gap.GLP0181B1
import AronowAudit.P018.Wave1.Gap.GLP0181B3
import AronowAudit.P018.Wave1.Gap.GP0181B3
import AronowAudit.P018.Wave1.Gap.GLP0181B5
import AronowAudit.P018.Wave1.Gap.GLP0182B1
import AronowAudit.P018.Wave1.Gap.GLP0182B2
import AronowAudit.P018.Wave1.Gap.GP0182B1
import AronowAudit.P018.Wave1.Gap.GP0181B1
import AronowAudit.P018.Wave1.Gap.GP0181B2
import AronowAudit.P018.Wave1.Gap.TailBSignDegeneracy
import AronowAudit.P018.Wave1.WeightedConsistency

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

noncomputable section
namespace SAP.P018a.WH.W2
open Finset Matrix MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology BoundedContinuousFunction Matrix.Norms.Elementwise ENNReal
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

/-- Transport the a.e. pair bounds to each observed record, then multiply
and sum to obtain L-infinity bounds for the weighted Gram and XY sums.
Copy the pair-preserving and record_memLp arguments of GP0181B2, dropping
its unused positive-block premise. Fin 0 contributes an empty sum. -/
def T12_L1 : Prop :=
  ∀ {U : Type u} [MeasurableSpace U] {k N : ℕ} (R : RepeatedKernel U k),
    WholeRecordRegular R N → ∀ w : (d : Dyad N) → Fin (R.T N d) → ℝ,
    (∀ a b, MemLp (fun ω => recordWeightedGram R w ω a b) ∞ (repeatedLaw R N)) ∧
    (∀ a, MemLp (fun ω => recordWeightedXY R w ω a) ∞ (repeatedLaw R N)) ∧
    (∀ β d a, MemLp (fun ω => recordWeightedBlockScore R w β ω d a) ∞ (repeatedLaw R N))

/-- Finite population normal equations and covariance transport, including
pointwise sample linearization. Use L1, expand S=b-G beta, and reproduce
the finite_contract proof in GP0181B2. Symmetry of E[G] and its inverse
removes the covariance transpose. Signed weights and empty blocks cause
no change. The scalar c is nonzero; no sample-rank premise is used for
population identities. The sample identity is an implication for EACH sample. -/
def T12_L2 : Prop := T12_L1.{u} →
  ∀ {U : Type u} [MeasurableSpace U] {k N : ℕ} (R : RepeatedKernel U k),
    WholeRecordRegular R N →
    ∀ (w : (d : Dyad N) → Fin (R.T N d) → ℝ) (c : ℝ), c ≠ 0 →
    (c⁻¹ • meanMat (repeatedLaw R N) (recordWeightedGram R w)).det ≠ 0 →
      wholeRecordContract R w c

/-- Disjoint blocks are functions of disjoint iid unit coordinates, hence
independent and have zero covariance. Use WeightedConsistency.g2_proof,
L1, and variance_sum_identity; split diagonal, neighbors and disjoint terms.
For the last implication use covariance_eq_sub and individual mean zero,
or variance_sparse_identity. Do not infer block centering from total centering. -/
def T12_L3 : Prop := T12_L1.{u} →
  ∀ {U : Type u} [MeasurableSpace U] {k N : ℕ} (R : RepeatedKernel U k),
    WholeRecordRegular R N → ∀ w β, wholeRecordSparse (N := N) R w β

/-- Mixed uniform/sign model moments. Split the product integrals into
uniform monomials and fair-sign integrals. This gives Q, beta, H and the
one-unit projection moment Gamma; verify boundedness and symmetry directly.
All expectations exist by boundedness. No independence beyond the product
unit law in wholeMixedKernel is imposed. -/
def T12_L4 : Prop := Standing wholeMixedKernel ∧
  populationGram wholeMixedKernel = !![1,0;0,2/3] ∧
  populationBeta wholeMixedKernel = 0 ∧
  scoreH wholeMixedKernel = !![2,0;0,4/3] ∧
  projectionGamma wholeMixedKernel = !![1,0;0,1/3]

/-- The repeated sign-model check for every positive fixed record count.
The count m multiplies Gram and XY by m, leaves beta unchanged and
multiplies the total score by m. Its variance scales by m^2, which cancels
L^2. Use appendixB_scoreSum and printed_S_variance, also at N=3.
For unit weights use corrected_target_reductions_proof. -/
def T12_L5 : Prop :=
  (∀ N m : ℕ, 3 ≤ N → 0 < m → repeatedTarget (wholeRepeatedSign m) N = !![4]) ∧
  (∀ N : ℕ, 3 ≤ N → weightedTarget signKernel (fun _ : Dyad N => 1) = !![4])

/-- Finite input certificate for the repeated-block refutation. Counts are
1,2,3, all records have intercept 1 and common response sequence 0,1,-2.
At N=4 enumerate the six dyads to obtain L=9 and Gram=9, hence H=1.
Use printed_upper_sum to avoid computation on the dyad subtype. -/
def T2_L1 : Prop := T2WitnessInput

/-- Compute the stacked population projection and individual block scores.
The total response is 1-1=0, so beta=0; only the two disjoint special blocks
have scores +1 and -1. Use L1's Gram and finite integral linearity under
the Dirac product law. This is a finite calculation. -/
def T2_L2 : Prop := T2WitnessInput → T2WitnessProjection

/-- From L2, the total score is identically zero. The sparse raw meat keeps
the two squared special scores and drops their disjoint cross terms, so
it is 2. Enumerate six dyads or use overlap_meat_identity. The incompatible
matrices certify the failed repeated-block prescription. -/
def T2_L3 : Prop := T2WitnessProjection → T2WitnessFailure

/-- The response is a polynomial of its own row, so conditional expectation
given that row equals the response. To exclude an a.e. affine representation,
use nonsingular population normal equations to identify its coefficients
with beta, then contradict H_00=E[epsilon^2]=28/45. Boundedness supplies all
integrability. Use condExp_of_stronglyMeasurable and the population certificates. -/
def T1_L1 : Prop := T1Conditional

/-- Export the zero conditional factors, including the literal singleton
repeated and unit-weight weighted displays. First show their population
coefficients and design sigma-algebras agree with the ordinary model, using
corrected_single_beta and corrected_one_beta. The retained a.e. zero
conditional residual covariances then kill every finite summand. -/
def T1_L2 : Prop := T1PrintedZeros

/-- Fourth mixed moment of iid fair signs. Partition index coincidences;
an odd multiplicity gives zero by coordinate independence, two even pairs
give one, and four equal indices give 3-2=1. This includes N=0 with no indices.
Use iIndepFun_pi and integral_fintype, not enumeration of 2^N samples. -/
def T3_L1 : Prop := WholeFourthSignMoment

/-- Expand four finite linear forms, integrate using L1, and subtract the
product of second moments from appendixB_linear_product. The three pairings
leave the two cross pairings and the -2 diagonal correction. -/
def T3_L2 : Prop := WholeFourthSignMoment → T3LinearCovariance

/-- Sum L1 over all four indices to obtain E[S^4]=3N^2-2N; combine with
printed_S_second for Var(S^2). Apply printed_scaled_sandwich and variance
under affine scalar transformations to obtain Var(N Vhat) and its rational
limit. All random variables live on finite fair-sign spaces. -/
def T3_L3 : Prop := WholeFourthSignMoment → T3SignMoments

/-- Specialize the four-linear-form identity to the fitted loadings
1{i in d}-2/N, giving 16(N+6)/N^3 for the disjoint endpoint unions. Check
the configuration by finite set arithmetic. Identify fairAverage with the
finite product-law integral, and signResidual8 with the actual OLS residual
using appendixB_residual_linear. This also transfers both N=8 certificates. -/
def T3_L4 : Prop := T3LinearCovariance → T3FittedCovariances

/-- The three mean limits from the exact sample/mean formulas: the quadratic
(-4N+6)(N-1) tends to minus infinity; dividing by the prescribed scale tends
to zero; and E[N Vhat] tends to 4. Use eventual N>=4 and rational limits
in 1/N, keeping every cast subtraction in R. -/
def T3_L5 : Prop := T3SampleFormulas → T3MeanLimits

/-- Export det Q=2 Var(exp(-T)). Expand the 2x2 determinant, use independence
of the two unit coordinates for the variance of their sum, and use
inverse_gram_population_det_pos for strict positivity. The exponential is
bounded on the support, so both moments are finite. -/
def T3_L6 : Prop := T3InverseDet

/-- The constant intercept design generates the trivial sigma-algebra, so
the printed conditional residual covariance is the unconditional covariance.
Its sparse sum is the total score variance, N(N-1)^2. Establish the
conditional expectations with integrability, then use the existing sign
score-sum calculation. This is not an exogeneity assumption on a general model. -/
def T3_L7 : Prop := ∀ N : ℕ, 4 ≤ N →
  printedSigma signKernel N = !![(N : ℝ)*((N : ℝ)-1)^2]

/-- Exact rank classification and failure probability. The two possible row
values have rank two unless all Z signs agree (for N>=3). Use tb05_sample_gram
or the existence of within-group and cross-group dyads. The two constant-Z
events are disjoint and each has probability 2^(-N); W is unrestricted. -/
def T7_L1 : Prop := T7Rank

/-- Export residual and score moments of the sign-pair model by finite
fair-sign integration. The arbitrary overlapping pair is transferred to
three iid units; vc3_overlap_moment gives the overlapping score moment.
Then use vc3_sparse_variance and vc3_closed_covariance for the finite
total-score covariance. No conditional-mean-zero premise is added. -/
def T7_L2 : Prop := T7Moments

/-- Compute the missing N=8 meat via overlap_meat_identity. Transfer the
explicit 28-row enumeration to Dyad 8 with printed_upper_sum (and the
incidence version for meat). The specified sign-pair atom has mass 4^(-8)
by pi_singleton; transport Gram, fit, meat and sandwich to that atom.
This identifies the negative estimate with a positive-probability outcome. -/
def T7_L3 : Prop := T7Atom

/-- Slope expansion in probability. On the bounded boxes for the normalized
sums Z,W,ZW use tb05_sample_ols and tb05_fitB, then clear the denominator
using tb05_gram_nonsingular_on_box. The leading term is 2 A_N B_N; the
remainder vanishes uniformly on each box. tb05_box_probability controls the
complement. Singular samples are included in that complement for large N. -/
def T7_L4 : Prop := T7SlopeApproximation

/-- Joint second-order weak limit. Apply the continuous polynomial map
wholeSecondOrderMap to tb05_joint_sign_clt. Combine the slope error from
L4 with tb05_second_order_in_probability in the finite-dimensional norm,
then use TailB_weakLimit_perturbation for the VECTOR. Separate marginal
limits do not establish this leaf. -/
def T7_L5 : Prop := T7SlopeApproximation → T7JointLimit

theorem T2_assembly (h1 : T2_L1) (h2 : T2_L2) (h3 : T2_L3) : T2WholeStatement :=
  ⟨h1, h2 h1, h3 (h2 h1)⟩

private theorem mixed_check (h4 : T12_L4) :
    ∀ N : ℕ, 3 ≤ N → weightedTarget wholeMixedKernel (fun _ : Dyad N => 1) =
      !![4,0;0,3*(N : ℝ)/((N : ℝ)-1)] := by
  obtain ⟨hK,hQ,_,hH,hΓ⟩ := h4
  have hi : (populationGram wholeMixedKernel)⁻¹ = !![1,0;0,3/2] := by
    rw [hQ]
    apply Matrix.inv_eq_left_inv
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [Matrix.mul_apply, Fin.sum_univ_two]
  intro N hN
  have hr : weightedTarget wholeMixedKernel (fun _ : Dyad N => 1) = trueTarget wholeMixedKernel N :=
    (AronowAudit.P018.Wave1.corrected_target_reductions_proof
      (Bridge.toKernel wholeMixedKernel) hK (by omega)).2
  have hv : varMat (unitSampleLaw wholeMixedKernel N) (scoreSum wholeMixedKernel) =
      (Dreal N) • scoreH wholeMixedKernel +
        ((N : ℝ)*((N : ℝ)-1)*((N : ℝ)-2)) • projectionGamma wholeMixedKernel :=
    (AronowAudit.P018.Wave1.vc3_sparse_variance (Bridge.toKernel wholeMixedKernel) hK).trans
      (AronowAudit.P018.Wave1.vc3_closed_covariance (Bridge.toKernel wholeMixedKernel) hK)
  have hn : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have hn0 : (N : ℝ) ≠ 0 := by linarith
  have hn1 : (N : ℝ)-1 ≠ 0 := by linarith
  rw [hr, trueTarget, hv, hi, hH, hΓ]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [sandwich, Matrix.mul_apply, Fin.sum_univ_two, Dreal] <;>
    field_simp [hn0, hn1] <;> ring

theorem T12_assembly (h1 : T12_L1.{u}) (h2 : T12_L2.{u}) (h3 : T12_L3.{u})
    (h4 : T12_L4) (h5 : T12_L5) : T12WholeStatement.{u} := by
  refine ⟨?_, ?_, h3 h1, ?_, ?_, h5.1, h5.2, h4.1, h4.2.1, h4.2.2.1, mixed_check h4⟩
  · intro U _ k N R hR _ hL hH
    apply h2 h1 R hR (fun _ _ => 1) (repeatedL R N) (ne_of_gt hL)
    have hg : recordWeightedGram (N := N) R (fun _ _ => 1) = repeatedGram R := by
      funext ω
      simp only [recordWeightedGram, repeatedGram, one_smul]
    simpa only [hg, repeatedH] using hH
  · intro U _ k N R hR hN w hH
    apply h2 h1 R hR w (Dreal N)
    · exact ne_of_gt (show 0 < Dreal N from AronowAudit.P018.Wave1.printed_Dpos hN)
    · exact hH
  · intro U _ k N K hK hN
    exact AronowAudit.P018.Wave1.corrected_target_reductions_proof (Bridge.toKernel K) hK hN
  · intro U _ k N R hN hL hG
    exact AronowAudit.P018.repeated_target_normalization (Bridge.toRepeated R) hN (ne_of_gt hL) hG

private theorem retained_T1 : T1Statement := by
  exact ⟨AronowAudit.P018.Wave1.nonlinear_counterexample_proof,
    AronowAudit.P018.nonlinear_bounds,
    AronowAudit.P018.nonlinear_population_projection.2.1,
    AronowAudit.P018.nonlinear_matrix_certificate.2.1,
    AronowAudit.P018.nonlinear_matrix_certificate.2.2.2.1⟩

private theorem nonlinear_score_facts : T1ScoreFacts := by
  obtain ⟨hK, _, _, _, hβ, _, hΓ, _⟩ :=
    AronowAudit.P018.Wave1.nonlinear_counterexample_proof
  refine ⟨?_, ?_⟩
  · intro z t
    change nonlinearKernel.Y z t - dot (nonlinearKernel.X z t) (populationBeta nonlinearKernel) = _
    rw [show populationBeta nonlinearKernel = ![2/3,0] from hβ]
    simp [nonlinearKernel, dot, Fin.sum_univ_two]
  · intro N _
    refine ⟨?_, ?_, ?_⟩
    · intro d
      have hm : meanVec (unitSampleLaw nonlinearKernel N) (fun ω =>
          score (design nonlinearKernel ω d) (epsilon nonlinearKernel ω d)) = 0 :=
        AronowAudit.P018.Wave1.vc3_dyad_mean _ hK d
      refine ⟨?_, ?_, hm⟩
      · simpa [meanVec, score, design, nonlinearKernel] using congrFun hm 0
      · simpa [meanVec, score, mul_comm] using congrFun hm 1
    · intro d f hd
      exact AronowAudit.P018.Wave1.vc3_disjoint_moment _ hK d f hd
    · intro d f hne hov
      exact (AronowAudit.P018.Wave1.vc3_overlap_moment _ hK d f hne hov).trans hΓ

private theorem nonlinear_variance_display : T1VarianceDisplay := by
  obtain ⟨_, _, _, _, _, _, _, _, hfinite, _⟩ :=
    AronowAudit.P018.Wave1.nonlinear_counterexample_proof
  have hv (N : ℕ) (hN : 3 ≤ N) :
      varMat (unitSampleLaw nonlinearKernel N) (scoreSum nonlinearKernel) =
        (Dreal N) • nonlinearH + ((N : ℝ)*((N : ℝ)-1)*((N : ℝ)-2)) • nonlinearGamma :=
    (hfinite N hN).2.2.1
  refine ⟨?_, ?_, ?_⟩
  · intro N hN
    rw [hv N hN]
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [Dreal, nonlinearH, nonlinearGamma] <;> ring
  · have hs (N : ℕ) (hN : 3 ≤ N) :
        ((N : ℝ)/(Dreal N)^2) • varMat (unitSampleLaw nonlinearKernel N) (scoreSum nonlinearKernel) =
          (2/((N : ℝ)-1)) • nonlinearH + (4*((N : ℝ)-2)/((N : ℝ)-1)) • nonlinearGamma := by
      have hn : (3 : ℝ) ≤ N := by exact_mod_cast hN
      have hn0 : (N : ℝ) ≠ 0 := by linarith
      have hn1 : (N : ℝ)-1 ≠ 0 := by linarith
      rw [hv N hN, smul_add, smul_smul, smul_smul]
      congr 1 <;> congr 1 <;> dsimp [Dreal] <;> field_simp <;> ring
    have hl := (AronowAudit.P018.Wave1.vc3_coefficient_limits.1.smul
      (tendsto_const_nhds (x := nonlinearH))).add
      (AronowAudit.P018.Wave1.vc3_coefficient_limits.2.smul
      (tendsto_const_nhds (x := nonlinearGamma)))
    simp only [zero_smul, zero_add] at hl
    apply hl.congr'
    filter_upwards [eventually_ge_atTop 3] with N hN
    exact (hs N hN).symm
  · have hi : nonlinearQ⁻¹ = !![7,-3;-3,3/2] := by
      apply Matrix.inv_eq_left_inv
      ext i j
      fin_cases i <;> fin_cases j <;>
        norm_num [nonlinearQ, Matrix.mul_apply, Fin.sum_univ_two]
    rw [hi]
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [nonlinearVstar, nonlinearGamma, sandwich, Matrix.mul_apply, Fin.sum_univ_two]

theorem T1_assembly (h1 : T1_L1) (h2 : T1_L2) : T1WholeStatement := by
  refine ⟨retained_T1, ?_, h1, nonlinear_score_facts, h2, nonlinear_variance_display⟩
  intro z
  norm_num [Matrix.det_fin_two]

private theorem retained_T3 : T3Statement := by
  obtain ⟨hK, ⟨N0, hRank⟩, hProb, hLower, hInfinite⟩ :=
    AronowAudit.P018.Wave1.inverse_gram_counterexample_proof
  refine ⟨AronowAudit.P018.Wave1.appendixB_counterexample_proof,
    AronowAudit.P018.missing_N_counterexample,
    AronowAudit.P018.Wave1.inverse_spike_counterexample_proof,
    AronowAudit.P018.fitted_products_counterexample, hK, hProb,
    max 3 N0, le_max_left _ _, ?_⟩
  intro N hN
  have h3 : 3 ≤ N := le_trans (le_max_left _ _) hN
  exact ⟨hRank N (le_trans (le_max_right _ _) hN), hLower N h3, hInfinite N h3⟩

private theorem sign_score_variance (N : ℕ) :
    varMat (unitSampleLaw signKernel N) (scoreSum signKernel) = !![(N : ℝ)*((N : ℝ)-1)^2] := by
  ext a b
  fin_cases a
  fin_cases b
  change ProbabilityTheory.covariance (fun ω => scoreSum signKernel ω 0)
    (fun ω => scoreSum signKernel ω 0) (unitSampleLaw signKernel N) = _
  simp_rw [show (fun ω : Fin N → Bool => scoreSum signKernel ω 0) =
    (fun ω => ((N : ℝ)-1)*wholeSignSum ω) from
      funext (fun ω => AronowAudit.P018.Wave1.appendixB_scoreSum ω)]
  rw [covariance_self (measurable_of_countable _).aemeasurable, variance_const_mul]
  change ((N : ℝ)-1)^2 * ProbabilityTheory.variance
    (fun ω => wholeSignSum ω) (unitSampleLaw signKernel N) = (N : ℝ)*((N : ℝ)-1)^2
  rw [show ProbabilityTheory.variance (fun ω => wholeSignSum ω) (unitSampleLaw signKernel N) =
    (N : ℝ) from AronowAudit.P018.Wave1.printed_S_variance N]
  ring

private theorem sign_fit (h7 : T3_L7) : T3Fit := by
  refine ⟨?_, ?_⟩
  · rw [show populationGram signKernel = (1 : Mat 1) from
      AronowAudit.P018.Wave1.appendixB_populationGram]
    ext i j
    fin_cases i
    fin_cases j
    rfl
  · intro N hN
    refine ⟨?_, sign_score_variance N, h7 N hN⟩
    intro ω
    refine ⟨?_, AronowAudit.P018.Wave1.printed_Dpos (by omega), ?_, ?_⟩
    · rw [show sampleGram (design signKernel ω) = Dreal N • (1 : Mat 1) from
        AronowAudit.P018.Wave1.printed_gram ω]
      ext i j
      fin_cases i
      fin_cases j
      simp
    · ext i
      fin_cases i
      change sampleOLS (design signKernel ω) (response signKernel ω) 0 = 2*wholeSignSum ω/(N : ℝ)
      rw [show sampleOLS (design signKernel ω) (response signKernel ω) 0 =
          2/(N : ℝ)*wholeSignSum ω from AronowAudit.P018.Wave1.printed_fit (by omega) ω]
      ring
    · intro d
      refine ⟨?_, ?_, ?_⟩
      · simp [epsilon, populationResidual, dot,
          show populationBeta signKernel = 0 from AronowAudit.P018.Wave1.appendixB_populationBeta,
          response]
      · have he : fittedResidual (design signKernel ω) (response signKernel ω) d =
            signValue (ω (firstUnit d)) + signValue (ω (secondUnit d)) -
              2/(N : ℝ)*wholeSignSum ω :=
          AronowAudit.P018.Wave1.appendixB_residual (by omega : 2 ≤ N) ω d
        rw [he]
        ring
      · exact AronowAudit.P018.Wave1.appendixB_residual_bound ω d

private theorem sign_overlap : T3Overlap := by
  intro N r
  have h : meat members (fun d : Dyad N => (![r d] : Vec 1)) =
      (∑ i : Fin N, outer (unitScore members (fun d => (![r d] : Vec 1)) i)
        (unitScore members (fun d => (![r d] : Vec 1)) i)) -
        dyadMeat (fun d => (![r d] : Vec 1)) :=
    AronowAudit.P018.overlap_meat_identity members members_card
      (fun d f h => Subtype.ext h) (fun d : Dyad N => (![r d] : Vec 1))
  have he := congrArg (fun M : Mat 1 => M 0 0) h
  have hx : (meat members (fun d : Dyad N => (![r d] : Vec 1))) 0 0 =
      ∑ d : Dyad N, ∑ f : Dyad N, if overlap d f then r d*r f else 0 := by
    simp only [meat, Matrix.sum_apply]
    apply Finset.sum_congr rfl
    intro d _
    apply Finset.sum_congr rfl
    intro f _
    change (if overlap d f then outer (![r d] : Vec 1) ![r f] else 0) 0 0 = _
    split_ifs <;> rfl
  rw [hx] at he
  simpa [outer, unitScore, dyadMeat, Finset.sum_apply, pow_two,
    Matrix.sum_apply, ite_apply] using he

private theorem sign_sample_formulas : T3SampleFormulas := by
  intro N hN
  have hn : (4 : ℝ) ≤ N := by exact_mod_cast hN
  have hn0 : (N : ℝ) ≠ 0 := by linarith
  have hn1 : (N : ℝ)-1 ≠ 0 := by linarith
  have hV (ω : Fin N → Bool) : (N : ℝ)*wholeSignVariance ω =
      (4*((N : ℝ)-2)*((N : ℝ)-3)/((N : ℝ)-1)^2)*(1-(wholeSignSum ω)^2/(N : ℝ)^2) := by
    have h : (N : ℝ)*wholeSignVariance ω =
        (4*((N : ℝ)-2)*((N : ℝ)-3)/((N : ℝ)-1)^2)*(1-(wholeSignSum ω/(N : ℝ))^2) :=
      AronowAudit.P018.Wave1.printed_scaled_sandwich hN ω
    simpa only [div_pow] using h
  have hM (ω : Fin N → Bool) : (Dreal N)^2*wholeSignVariance ω = wholeSignMeat ω :=
    AronowAudit.P018.Wave1.appendixB_meat_sandwich (by omega) ω
  have hm : (∫ ω, wholeSignMeat ω ∂ unitSampleLaw signKernel N) =
      ((N : ℝ)-1)*((N : ℝ)-2)*((N : ℝ)-3) := by
    exact congrArg (fun M : Mat 1 => M 0 0)
      (AronowAudit.P018.Wave1.appendixB_meat_mean hN)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro ω
    refine ⟨?_, ?_, hV ω⟩
    · have hv := hV ω
      rw [← hM ω]
      dsimp [Dreal]
      field_simp [hn0, hn1] at hv ⊢
      nlinarith [hv]
    · rw [← hM ω]
      field_simp [Dreal, hn0, hn1]
  · rw [hm]
    ring
  · rw [hm]
    dsimp [Dreal]
    field_simp [hn0, hn1]
    ring
  · rw [integral_const_mul]
    rw [show (∫ ω, wholeSignVariance ω ∂ unitSampleLaw signKernel N) =
        4*((N : ℝ)-2)*((N : ℝ)-3)/((N : ℝ)^2*((N : ℝ)-1)) from
        AronowAudit.P018.Wave1.appendixB_variance_mean hN]
    field_simp

private theorem inverse_all_sizes : T3InverseAllSizes := by
  obtain ⟨_, _, _, hlo, htop⟩ := AronowAudit.P018.Wave1.inverse_gram_counterexample_proof
  intro N hN
  refine ⟨?_, hlo N hN, htop N hN⟩
  filter_upwards [AronowAudit.P018.Wave1.inverse_gram_ae_distinct
    (⟨0, by omega⟩ : Fin N) ⟨1, by omega⟩ (by change (0 : ℕ) < 1; omega)] with ω hω
  have hpos := AronowAudit.P018.Wave1.inverse_gram_det_pos hN ω hω
  intro hz
  apply hpos.ne'
  have hz' : (AronowAudit.P018.sampleGram (AronowAudit.P018.design AronowAudit.P018.inverseKernel ω)).det = 0 := hz
  rw [AronowAudit.P018.Wave1.inverse_gram_Q, Matrix.det_smul, hz', mul_zero]

theorem T3_assembly (h1 : T3_L1) (h2 : T3_L2) (h3 : T3_L3) (h4 : T3_L4)
    (h5 : T3_L5) (h6 : T3_L6) (h7 : T3_L7) : T3WholeStatement :=
  ⟨retained_T3, sign_fit h7, sign_overlap, sign_sample_formulas, h5 sign_sample_formulas,
    h2 h1, h3 h1, h4 (h2 h1), h6, inverse_all_sizes⟩

private theorem retained_T7 : T7Statement := by
  obtain ⟨h1,h2,h3,h4,h5,h6,h7,h8,_,h10⟩ :=
    AronowAudit.P018.Wave1.TailB_degenerate_inference_counterexample
  exact ⟨⟨h1,h2,h3,h4,h5,h6,h7,h8,h10⟩,
    AronowAudit.P018.degenerate_numeric_certificate⟩

theorem T7_assembly (h1 : T7_L1) (h2 : T7_L2) (h3 : T7_L3) (h4 : T7_L4)
    (h5 : T7_L5) : T7WholeStatement := by
  refine ⟨retained_T7, h1, h2, ?_, ?_, ?_, ?_, h3, h5 h4, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show populationGram signPairKernel = !![1,1;1,2] from
      AronowAudit.P018.Wave1.TailBSign.tb05_population_gram]
    norm_num [Matrix.det_fin_two]
  · exact AronowAudit.P018.Wave1.TailBSign.tb05_population_inverse
  · exact fun _ ω d => AronowAudit.P018.Wave1.TailBSign.tb05_model_fitted_residual_bound ω d
  · exact AronowAudit.P018.Wave1.TailBSign.tb05_true_target_limit
  · exact AronowAudit.Shared.MapTailB.TailB_gaussian_disk.1
  · have he : Real.exp (-1/2) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
    linarith
  · intro N ω hneg ⟨r, hr⟩
    linarith [sq_nonneg r]
  · intro N ω hnonpos
    rw [Real.sqrt_eq_zero_of_nonpos hnonpos, div_zero]
  · exact AronowAudit.P018.Wave1.TailBSign.tb05_pivot_not_normal
  · exact AronowAudit.P018.Wave1.variance_consistency_corrected_proof _
      AronowAudit.P018.Wave1.TailBSign.tb05_standing

end SAP.P018a.WH.W2
