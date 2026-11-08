import SAP.P018a.WH.W1.Glue

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u
noncomputable section
namespace SAP.P018a.WH.W1
open Finset Matrix MeasureTheory ProbabilityTheory Filter
open AronowAudit.P018.Wave1.WeightedConsistency
open scoped BigOperators Topology BoundedContinuousFunction Matrix.Norms.Elementwise ENNReal
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

/-- Global strict concavity for the six logistic rows. Use
`AronowAudit.P026.LogitCompletion.bernoulliTerm_strictConcave` on each predictor.
Rows (1,0) and (1,2) separate distinct coefficients; one term is therefore strict.
Sum the six weak inequalities and that strict inequality with `Finset.sum_lt_sum`.
This is a finite affine-composition argument, requiring no new calculus. -/
def T13_L1 : Prop := StrictConcaveOn ℝ Set.univ
  (fun β : Vec 2 => ∑ d, logLikelihood (logitX d) (logitY d) β)

/-- The deterministic setup certificates in the concentrated-weight model. Prove weighted
population centering by finite integral linearity and fair-sign means. Positive normalized
weights make the fitted coefficient a convex average in [-2,2], so residuals are in [-4,4].
Use `appendixB_populationBeta`, `appendixB_standing`, `appendixB_sampleRank`, and
`printed_gram`. Fixed-label weight invariance is immediate from its exponent.
Two directed copies reduce to weights 2w; `concentrated_repetitions_scale_total`
then identifies their fit and sandwich with the original pair. -/
def T9_L1 : Prop := W1T9Setup

/-- Sum and first coefficient of the geometric linear fit. Evaluate
`concentrated_weights_pair_linear` on the constant-one vector to get sum c = 2.
Use the already proved formulas for S and W and W >= 1/8 to simplify the first coefficient;
0 < x <= 1/4 gives its lower bound. No probability arguments are needed. -/
def T9_L2 : Prop := W1T9Coefficients

/-- Dyad-tail control on the first-eight-positive event. The tail dyad mass is
W_N-W_8 <= 1/256 (use the geometric W formula), not the unit-tail sum.
The weighted response is at most 2, and differs from 2 only on tail dyads.
Bound the total absolute residual score by 8 R_N, then use
`concentrated_weights_meat_bound` and the scalar sandwich formula. The bound on
2-betaHat may be sharpened to 2 R_N/W_N. All divisions have W_N >= 1/8. -/
def T9_L3 : Prop := W1T9Tail

/-- Transfer ordered-kernel regularity and moments to all present records, including
zero-record blocks. Adapt `WeightedConsistency.m0_proof` and `m2_proof`, using the
common kernel's explicit regularity instead of extracting a record at N=2.
`g1_proof` and product-law reversal give the common record moments. Empty sums need no
chosen record. Expected proof: the two donor proofs with their count-positivity uses removed. -/
def T10_L1 : Prop :=
  ∀ {U : Type u} [MeasurableSpace U] {k : ℕ} (R : RepeatedKernel U k)
    (K : Kernel U k) (dir : ∀ N : ℕ, (d : Dyad N) → Fin (R.T N d) → Bool)
    (v : ∀ N : ℕ, (d : Dyad N) → Fin (R.T N d) → ℝ) (C : ℝ) (H : Mat k),
    W1DirectedSetting R K dir v C H →
    RecordRegular (Bridge.toRepeated R) ∧ RecordMoments (Bridge.toRepeated R) K.X K.Y

/-- Population algebra for possibly empty directed blocks. The expected normalized Gram
is c_N Q. Its intercept entry and positive limit imply c_N->c>0 and det Q != 0.
Thus weighted beta equals Q^{-1}r eventually (early entirely empty samples are allowed).
Every block score at this common beta is centered, including empty blocks. Adapt
`m3_proof` and `m4_proof`; state eventual beta equality, not equality at every N>=2. -/
def T10_L2 : Prop :=
  ∀ {U : Type u} [MeasurableSpace U] {k : ℕ} (R : RepeatedKernel U k)
    (K : Kernel U k) (dir : ∀ N : ℕ, (d : Dyad N) → Fin (R.T N d) → Bool)
    (v : ∀ N : ℕ, (d : Dyad N) → Fin (R.T N d) → ℝ) (C : ℝ) (H : Mat k),
    W1DirectedSetting R K dir v C H → RecordRegular (Bridge.toRepeated R) →
    RecordMoments (Bridge.toRepeated R) K.X K.Y →
    (populationGram K).det ≠ 0 ∧
    (∀ N (d : Dyad N), meanVec (repeatedLaw R N)
      (fun ω => recordWeightedBlockScore R (v N) (populationBeta K) ω d) = 0) ∧
    (∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N → recordWeightedBeta R (v N) = populationBeta K)

/-- Gram and centered-score laws of large numbers for the empty-block extension.
Adapt `m5_proof` and `m6_proof`. Direction injectivity gives T<=2 even for empty blocks;
bounded block variables have variance O(N^3), and division by D^2 gives O(1/N).
Use `g3_proof`, `g4_proof`, `g5_proof`; all sum bounds are valid when T=0. -/
def T10_L3 : Prop :=
  ∀ {U : Type u} [MeasurableSpace U] {k : ℕ} (R : RepeatedKernel U k)
    (K : Kernel U k) (dir : ∀ N : ℕ, (d : Dyad N) → Fin (R.T N d) → Bool)
    (v : ∀ N : ℕ, (d : Dyad N) → Fin (R.T N d) → ℝ) (C : ℝ) (H : Mat k),
    W1DirectedSetting R K dir v C H → RecordRegular (Bridge.toRepeated R) →
    (∀ N (d : Dyad N), meanVec (repeatedLaw R N)
      (fun ω => recordWeightedBlockScore R (v N) (populationBeta K) ω d) = 0) →
    GramLLN (Bridge.toRepeated R) v ∧ ScoreLLN (Bridge.toRepeated R) v (populationBeta K)

/-- Coefficient consistency and residual substitution, permitting empty blocks. Given
the two LLNs, inverse continuity at H and the exact sample normal equations give the
coefficient limit. A polynomial bound in ||betaHat-beta|| controls the fitted-meat
change. Adapt `m7_proof` and `m10_proof`; use `meat_difference_norm_bound`,
`normalized_dyad_count_le`, and `inProbability_ae_norm_le`. No inverse moments are needed. -/
def T10_L4 : Prop :=
  ∀ {U : Type u} [MeasurableSpace U] {k : ℕ} (R : RepeatedKernel U k)
    (K : Kernel U k) (dir : ∀ N : ℕ, (d : Dyad N) → Fin (R.T N d) → Bool)
    (v : ∀ N : ℕ, (d : Dyad N) → Fin (R.T N d) → ℝ) (C : ℝ) (H : Mat k),
    W1DirectedSetting R K dir v C H → RecordRegular (Bridge.toRepeated R) →
    GramLLN (Bridge.toRepeated R) v → ScoreLLN (Bridge.toRepeated R) v (populationBeta K) →
    CoefConsistent (Bridge.toRepeated R) v (populationBeta K) ∧
      SubstitutionNull (Bridge.toRepeated R) v (populationBeta K)

/-- Concentration of the population-score meat for possibly empty directed blocks.
Adapt `m9_proof`: overlap products have at most three unit arguments; at most O(N^5)
ordered pairs of such products depend on common units. Boundedness and `g3_proof`,
`g4_proof`, `g5_proof` yield variance O(1/N) after N/D^2 scaling. Empty blocks have zero scores. -/
def T10_L5 : Prop :=
  ∀ {U : Type u} [MeasurableSpace U] {k : ℕ} (R : RepeatedKernel U k)
    (K : Kernel U k) (dir : ∀ N : ℕ, (d : Dyad N) → Fin (R.T N d) → Bool)
    (v : ∀ N : ℕ, (d : Dyad N) → Fin (R.T N d) → ℝ) (C : ℝ) (H : Mat k),
    W1DirectedSetting R K dir v C H → RecordRegular (Bridge.toRepeated R) →
    MeatLLN (Bridge.toRepeated R) v (populationBeta K)

/-- Exact expected meat and bounded scaled covariance, permitting empty directed blocks.
Adapt `m8_proof` and `m11_proof`: centered block scores and disjoint-unit independence
identify E[meat] with Var(sum q); the O(N^3) covariance count bounds the scaled matrix.
Use `variance_sparse_identity`, `g2_proof`, `g4_proof`. For N<2 the scaling is zero.
All integrability follows from the supplied regularity and the finite count bound. -/
def T10_L6 : Prop :=
  ∀ {U : Type u} [MeasurableSpace U] {k : ℕ} (R : RepeatedKernel U k)
    (K : Kernel U k) (dir : ∀ N : ℕ, (d : Dyad N) → Fin (R.T N d) → Bool)
    (v : ∀ N : ℕ, (d : Dyad N) → Fin (R.T N d) → ℝ) (C : ℝ) (H : Mat k),
    W1DirectedSetting R K dir v C H → RecordRegular (Bridge.toRepeated R) →
    (∀ N (d : Dyad N), meanVec (repeatedLaw R N)
      (fun ω => recordWeightedBlockScore R (v N) (populationBeta K) ω d) = 0) →
    (∀ N : ℕ, 2 ≤ N →
      meanMat (repeatedLaw R N) (scaledMeatAt (Bridge.toRepeated R) v N (populationBeta K)) =
        targetMeat (Bridge.toRepeated R) v (populationBeta K) N) ∧
    (∃ B : ℝ, ∀ N : ℕ, ‖targetMeat (Bridge.toRepeated R) v (populationBeta K) N‖ ≤ B)

/-- Exact deterministic witness that stacked centering does not control overlap means.
For N=2n the first n labels give n(n-1)/2 one-record pairs; the rest have two records.
L=n(7n-3)/2, beta=(n-1)/(7n-3), and each unit incidence score is plus or minus
2(n-1)(2n-1)/(7n-3). Apply `overlap_meat_identity` and subtract the sum of squared
block scores to obtain the rational expression. Prove general-N H=1 and stacked centering
by the scalar normal equations. Under the point-mass law sample and population fits agree,
the target covariance is zero, and the scaled sandwich equals the overlap mean matrix.
These facts also certify failure of consistency, not just failure of the mean condition. -/
def T10_L7 : Prop :=
  RepeatedStanding W1MeanWitness ∧
  (∀ N d, W1MeanWitness.T N d ≤ 2) ∧
  (∃ fX : ℕ → Unit → Unit → Vec 1, ∃ fY : ℕ → Unit → Unit → ℝ,
    ∀ N d (t : Fin (W1MeanWitness.T N d)) u v,
      W1MeanWitness.X N d t u v = fX t.val u v ∧
      W1MeanWitness.Y N d t u v = fY t.val u v) ∧
  (∀ N : ℕ, 2 ≤ N → repeatedH W1MeanWitness N = 1 ∧
    (∑ d : Dyad N, meanVec (repeatedLaw W1MeanWitness N)
      (fun ω => repeatedBlockScore W1MeanWitness (repeatedBeta W1MeanWitness N) ω d)) = 0) ∧
  (∀ n : ℕ, 1 ≤ n →
    W1MeanOverlap (2*n) 0 0 =
      32*((n : ℝ)-1)*(2*(n : ℝ)-1)*(4*(n : ℝ)^2-9*(n : ℝ)+3)/(7*(n : ℝ)-3)^4) ∧
  (∀ N : ℕ, 2 ≤ N → ∀ ω : Fin N → Unit,
    (N : ℝ) • repeatedVariance W1MeanWitness ω-repeatedTarget W1MeanWitness N =
      W1MeanOverlap N)

/-- Exact scalar-model conditional moments and estimator reductions. The constant design
has trivial sigma-algebra; use `MeasureTheory.condExp_bot`, `appendixB_coord_mean`, and
`appendixB_coord_product` to get overlap-cardinality covariances. `dyad_counts_proof`
gives the unsummed row 2N-2. `printed_fit` supplies OLS; finite singleton record sums
and unit weights identify the repeated and weighted estimators with the scalar sandwich.
Split the proof locally into conditional-moment and finite-reduction helpers. -/
def T11_L1 : Prop := W1T11ScalarMoments

/-- Complete the exact sample and mean sandwich formulas at N=3. For N>=4 use
`printed_scaled_sandwich` and `appendixB_variance_mean`. At N=3 all dyads overlap,
so fitted-score centering makes the meat zero; the displayed factor N-3 is zero too.
Integrability is automatic on the finite sign sample space. -/
def T11_L2 : Prop := W1T11SampleFormula

/-- T identical records: compute L, both block Grams, beta, and the total score T times
the ordinary sign score. Use `appendixB_scoreSum`, `printed_S_variance`, and covariance
scaling to get Omega_r. Finite 1x1 inverses yield 4/T^2 with the unnormalized block Gram
and 4 with H_r=1. T>=1 and N>=3 supply every nonzero denominator. -/
def T11_L3 : Prop := W1T11Repeated

/-- Construct and evaluate the mixed uniform/sign population model: bounded symmetric
kernel, beta=0, Q=diag(1,2/3), shared-endpoint cross-Gram diag(1,1/3), and E[X'X]=5/3.
Use `uniform_unit_moments`, fair-sign centering, product integrals, and product-law
independence. Establish boundedness/integrability before splitting integrals.
This leaf supplies the actual probability model, not just numerical matrices. -/
def T11_L4 : Prop :=
  Standing W1MixedKernel ∧ populationBeta W1MixedKernel = 0 ∧
  populationGram W1MixedKernel = !![1,0;0,2/3] ∧
  W1CrossGram W1MixedKernel = !![1,0;0,1/3] ∧
  (∫ uv, dot (W1MixedKernel.X uv.1 uv.2) (W1MixedKernel.X uv.1 uv.2)
    ∂W1MixedKernel.μ.prod W1MixedKernel.μ) = 5/3

/-- Same-dyad and projection score moments of the mixed model. Given the preceding
population certificates, factor independent uniform and sign moments to get
H=diag(2,4/3), Gamma=diag(1,1/3). One can compute the unit projection explicitly as
(sign u, z u * sign u); `vc3_shared_integral` also identifies Gamma via three-unit
cross moments. Uniform support gives all required integrability. -/
def T11_L5 : Prop := T11_L4 →
  scoreH W1MixedKernel = !![2,0;0,4/3] ∧ projectionGamma W1MixedKernel = !![1,0;0,1/3]

/-- Mixed-model dyad rows, including the printed conditional expression. The entire
sign array is independent of the entire regressor array. Conditional sign covariance
is therefore overlap cardinality; use `MeasureTheory.condExp_indep_eq` and finite
product factorization. Transport same/shared score moments with `vc3_same_moment`,
`vc3_overlap_moment`, then count 2(N-2) distinct neighbors. This identifies both
conditional and unconditional score rows; an unconditional moment alone is insufficient. -/
def T11_L6 : Prop := W1T11MixedMoments → W1T11MixedRows

/-- Existing finite certificates plus global strict concavity give the whole logistic claim. -/
theorem T13_assembly (h1 : T13_L1) : T13WholeStatement := ⟨existing_T13,h1⟩

/-- The corrected inference claim already has complete proved donors. -/
theorem T8_assembly : T8WholeStatement := T8_existing_whole

/-- Complete concentrated-weight counterexample; existing finite identities are reused. -/
theorem T9_assembly (h1 : T9_L1) (h2 : T9_L2) (h3 : T9_L3) : T9WholeStatement := by
  refine ⟨existing_T9,h1,?_,h2,h3,?_,?_,concentrated_limits h3,?_,repetitions_unbounded⟩
  · intro N
    exact ⟨AronowAudit.P018.Wave1.concentrated_weights_S_formula N,
      AronowAudit.P018.Wave1.concentrated_weights_W_formula N,
      AronowAudit.P018.Wave1.concentrated_weights_variance N,
      fun ω => AronowAudit.P018.Wave1.concentrated_weights_ols_linear ω⟩
  · intro N hN
    refine ⟨AronowAudit.P018.Wave1.concentrated_weights_event_probability hN,
      AronowAudit.P018.Wave1.concentrated_weights_W_lower (by omega),?_⟩
    intro ω hω
    have he := AronowAudit.P018.Wave1.concentrated_weights_sandwich_small hN ω hω
    change |(weightedVariance signKernel concentratedWeight ω) 0 0| ≤ 1/16 at he
    have hv := AronowAudit.P018.Wave1.concentrated_weights_variance_lower (N := N) (by omega)
    refine ⟨he,?_⟩
    have ha := le_abs_self ((weightedVariance signKernel concentratedWeight ω) 0 0)
    have hb := neg_le_abs ((weightedVariance signKernel concentratedWeight ω) 0 0-W1WeightVariance N)
    change (9/16 : ℝ) ≤ W1WeightVariance N at hv
    linarith
  · intro N _ ω
    have he := AronowAudit.P018.Wave1.concentrated_weights_variance_scalar ω
    change (weightedVariance signKernel concentratedWeight ω) 0 0 =
      (W1W N)⁻¹ * (∑ d : Dyad N, ∑ f : Dyad N,
        if overlap d f then W1WeightScore ω d * W1WeightScore ω f else 0) * (W1W N)⁻¹ at he
    rw [he]
    simp only [_root_.zpow_neg, zpow_ofNat, pow_two, _root_.mul_inv_rev]
    ring
  · intro N _ ω
    exact AronowAudit.P018.Wave1.concentrated_repetitions_pair_identity ω

/-- Whole corrected repeated/weighted consistency. The six analytic leaves generalize
only the empty-block case; existing probability calculus supplies the final passage. -/
theorem T10_assembly (h1 : T10_L1.{u}) (h2 : T10_L2.{u}) (h3 : T10_L3.{u})
    (h4 : T10_L4.{u}) (h5 : T10_L5.{u}) (h6 : T10_L6.{u}) (h7 : T10_L7) :
    T10WholeStatement.{u} := by
  refine ⟨existing_T10.{u,u,u}.1,?_,?_,existing_T10.{u,u,u}.2.2.2,
    h7.1,h7.2.1,h7.2.2.1,h7.2.2.2.1,?_⟩
  · intro U _ k R K hK dir hRK w a ha hw H hH hlim
    obtain ⟨C,hC⟩ := hw
    let v : ∀ N : ℕ, (d : Dyad N) → Fin (R.T N d) → ℝ := fun N d t => w N d t/a N
    have hS : W1DirectedSetting R K dir v C H := ⟨hK,hRK,hC,hH,hlim⟩
    have : IsProbabilityMeasure R.μ := by rw [hRK.1]; exact hK.1
    have : ∀ N : ℕ, IsProbabilityMeasure (repeatedLaw R N) := fun N => by
      unfold repeatedLaw
      infer_instance
    obtain ⟨hreg,hmom⟩ := h1 R K dir v C H hS
    obtain ⟨_,hcent,N0,hβ⟩ := h2 R K dir v C H hS hreg hmom
    obtain ⟨hgram,hscore⟩ := h3 R K dir v C H hS hreg hcent
    have hsub := (h4 R K dir v C H hS hreg hgram hscore).2
    have hmeat := h5 R K dir v C H hS hreg
    obtain ⟨hmean,hbounded⟩ := h6 R K dir v C H hS hreg hcent
    obtain ⟨gAddM,_,gDet,gEqM,_,_⟩ := g6_proof (repeatedLaw R)
    obtain ⟨gInvDet,gInvProb⟩ := g7_proof H hH.det_pos.ne'
    have hM : inProbability (repeatedLaw R) (fun N ω =>
        scaledMeatAt (Bridge.toRepeated R) v N (recordWeightedOLS R (v N) ω) ω -
          targetMeat (Bridge.toRepeated R) v (populationBeta K) N) := by
      apply gEqM _ _ ⟨2, fun N hN ω => ?_⟩ (gAddM _ _ hsub hmeat)
      change scaledMeatAt (Bridge.toRepeated R) v N (recordWeightedOLS R (v N) ω) ω -
          scaledMeatAt (Bridge.toRepeated R) v N (populationBeta K) ω +
          (scaledMeatAt (Bridge.toRepeated R) v N (populationBeta K) ω -
            meanMat (repeatedLaw R N) (scaledMeatAt (Bridge.toRepeated R) v N (populationBeta K))) = _
      rw [hmean N hN]
      abel
    have hG : inProbability (repeatedLaw R)
        (fun N ω => normGram (Bridge.toRepeated R) v N ω-H) := by
      apply gEqM _ _ ⟨0, fun N _ ω => ?_⟩
        (gAddM _ _ hgram (gDet _ (tendsto_sub_nhds_zero_iff.mpr hlim)))
      change normGram (Bridge.toRepeated R) v N ω-recordWeightedH R (v N) +
        (recordWeightedH R (v N)-H) = _
      abel
    have hB := gInvProb (repeatedLaw R) (normGram (Bridge.toRepeated R) v) hG
    have hB0 := gInvDet (fun N => recordWeightedH R (v N)) hlim
    have hsand := g8_proof (repeatedLaw R)
      (fun N ω => (normGram (Bridge.toRepeated R) v N ω)⁻¹)
      (fun N ω => scaledMeatAt (Bridge.toRepeated R) v N (recordWeightedOLS R (v N) ω) ω)
      (fun N => (recordWeightedH R (v N))⁻¹)
      (targetMeat (Bridge.toRepeated R) v (populationBeta K)) H⁻¹ hB hB0 hbounded hM
    have hcore : inProbability (repeatedLaw R) (fun N ω =>
        (N : ℝ) • recordWeightedVariance R (v N) ω-recordWeightedTarget R (v N)) := by
      apply gEqM _ _ ⟨max 2 N0, fun N hN ω => ?_⟩ hsand
      change AronowAudit.P018.sandwich (normGram (Bridge.toRepeated R) v N ω)⁻¹
          (scaledMeatAt (Bridge.toRepeated R) v N (AronowAudit.P018.recordWeightedOLS (Bridge.toRepeated R) (v N) ω) ω) -
          AronowAudit.P018.sandwich (AronowAudit.P018.recordWeightedH (Bridge.toRepeated R) (v N))⁻¹
            (targetMeat (Bridge.toRepeated R) v (populationBeta K) N) =
          (N : ℝ) • AronowAudit.P018.recordWeightedVariance (Bridge.toRepeated R) (v N) ω -
            AronowAudit.P018.recordWeightedTarget (Bridge.toRepeated R) (v N)
      rw [variance_rescale (Bridge.toRepeated R) (v N) ω (by omega),
        target_rescale (Bridge.toRepeated R) (v N) (populationBeta K) (hβ N (by omega))]
      rfl
    have hs (N : ℕ) (ω : Fin N → U) :=
      AronowAudit.P018.weighted_scale_invariance (Bridge.toRepeated R) (v N) (a N) (ha N) ω
    have hwscale (N : ℕ) : (fun d t => a N * v N d t) = w N := by
      funext d t
      dsimp [v]
      field_simp [(ha N).ne']
    have hv (N : ℕ) (ω : Fin N → U) :
        recordWeightedVariance R (v N) ω = recordWeightedVariance R (w N) ω := by
      have hh : recordWeightedVariance R (fun d t => a N * v N d t) ω =
          recordWeightedVariance R (v N) ω := (hs N ω).2.1
      rw [hwscale N] at hh
      exact hh.symm
    have ht (N : ℕ) : recordWeightedTarget R (v N) = recordWeightedTarget R (w N) := by
      have hh := (hs N (Classical.choice (show Nonempty (Fin N → U) from
        ⟨fun _ => Classical.choice (MeasureTheory.nonempty_of_isProbabilityMeasure R.μ)⟩))).2.2
      change recordWeightedTarget R (fun d t => a N * v N d t) = recordWeightedTarget R (v N) at hh
      rw [hwscale N] at hh
      exact hh.symm
    simpa only [hv,ht] using hcore
  · intro U _ k N R _ w a ha hN ω hG hH
    exact existing_T10.{u,u,u}.2.2.1 R w a ha hN ω hG hH
  · have hn : ¬Tendsto W1MeanOverlap atTop (𝓝 0) := by
      intro hz
      have heven : Tendsto (fun n : ℕ => 2*n) atTop atTop := by
        apply tendsto_atTop_mono (f := fun n : ℕ => n) (fun n => by omega)
        exact tendsto_id
      have hc : Continuous (fun M : Mat 1 => M 0 0) :=
        (continuous_apply (0 : Fin 1)).comp (continuous_apply (0 : Fin 1))
      have hzero : Tendsto (fun n : ℕ => W1MeanOverlap (2*n) 0 0) atTop (𝓝 (0 : ℝ)) :=
        (hc.tendsto (0 : Mat 1)).comp (hz.comp heven)
      have hpositive : Tendsto (fun n : ℕ => W1MeanOverlap (2*n) 0 0)
          atTop (𝓝 (256/2401 : ℝ)) := by
        apply Filter.Tendsto.congr' _ mean_overlap_rational_limit
        filter_upwards [eventually_ge_atTop 1] with n hn
        exact (h7.2.2.2.2.1 n hn).symm
      have heq := tendsto_nhds_unique hzero hpositive
      norm_num at heq

    refine ⟨hn,?_⟩
    intro hp
    have : ∀ N : ℕ, IsProbabilityMeasure (repeatedLaw W1MeanWitness N) := fun N => by
      unfold repeatedLaw W1MeanWitness
      infer_instance
    have hm : AronowAudit.P018.inProbability (repeatedLaw W1MeanWitness)
        (fun N (_ : Fin N → Unit) => W1MeanOverlap N) :=
      inProbability_eventually_eq (repeatedLaw W1MeanWitness)
        (by filter_upwards [eventually_ge_atTop 2] with N hN; exact h7.2.2.2.2.2 N hN) hp
    exact hn (deterministic_limit_of_inProbability (repeatedLaw W1MeanWitness) W1MeanOverlap hm)

/-- Whole scalar and multivariate printed-target counterexamples. -/
theorem T11_assembly (h1 : T11_L1) (h2 : T11_L2) (h3 : T11_L3)
    (h4 : T11_L4) (h5 : T11_L5) (h6 : T11_L6) : T11WholeStatement := by
  have hm : W1T11MixedMoments :=
    ⟨h4.1,h4.2.1,h4.2.2.1,h4.2.2.2.1,h4.2.2.2.2,(h5 h4).1,(h5 h4).2⟩
  refine ⟨existing_T11,h1,h2,?_,?_,?_,h3,?_,hm,h6 hm,?_⟩
  · intro N hN
    have hv : varMat (unitSampleLaw signKernel N) (scoreSum signKernel) =
        !![(N : ℝ)*((N : ℝ)-1)^2] := by
      ext a b
      fin_cases a
      fin_cases b
      change covariance (fun ω => scoreSum signKernel ω 0)
        (fun ω => scoreSum signKernel ω 0) (unitSampleLaw signKernel N) = _
      have he (ω : Fin N → Bool) : scoreSum signKernel ω 0 =
          ((N : ℝ)-1)*AronowAudit.P018.Wave1.printed_S ω :=
        AronowAudit.P018.Wave1.appendixB_scoreSum ω
      simp_rw [he]
      have hs : variance (fun ω : Fin N → Bool => AronowAudit.P018.Wave1.printed_S ω)
          (unitSampleLaw signKernel N) = (N : ℝ) := AronowAudit.P018.Wave1.printed_S_variance N
      rw [covariance_self (measurable_of_countable _).aemeasurable,variance_const_mul,hs]
      simp
      ring
    refine ⟨hv,?_,?_⟩
    · dsimp [Dreal]
      ring
    · dsimp [Dreal]
      field_simp
      ring
  · apply Filter.Tendsto.congr' _ (show Tendsto (fun N : ℕ => 4-4/Dreal N)
        atTop (𝓝 (4 : ℝ)) from by simpa using tendsto_const_nhds.sub existing_T11.1.2.1)
    filter_upwards [eventually_ge_atTop 3] with N hN
    rw [existing_T11.1.1 N hN]
  · have : ∀ N : ℕ, IsProbabilityMeasure (unitSampleLaw signKernel N) := fun N => by
      unfold unitSampleLaw signKernel fairLaw
      infer_instance
    have hd : Tendsto (fun N : ℕ => -(4/Dreal N)) atTop (𝓝 (0 : ℝ)) := by
      simpa using existing_T11.1.2.1.neg
    have hp := inProbability_add (unitSampleLaw signKernel) existing_T11.1.2.2
      (inProbability_deterministic (unitSampleLaw signKernel) _ hd)
    have he (N : ℕ) (ω : Fin N → Bool) :
        (N : ℝ)*(sampleVariance members (design signKernel ω) (response signKernel ω)) 0 0-4 +
          -(4/Dreal N) = W1ScaledSignSandwich ω-4/Dreal N-4 := by
      dsimp [W1ScaledSignSandwich]
      ring
    simpa only [SAP.P018a.inProbability,AronowAudit.P018.inProbability,he] using hp
  · intro N hN d
    have hh := (h3 2 N (by omega) hN).2.2.2.2.1 d
    constructor
    · rw [hh.2]
      change (!![1,1;1,1] : Mat 2).det = 0
      norm_num [Matrix.det_fin_two]
    · simpa using hh.1
  · intro N hN d
    have hG := hm.2.2.1
    have hrow := (h6 hm N hN d).1
    have hi : (populationGram W1MixedKernel)⁻¹ = !![1,0;0,3/2] := by
      apply Matrix.inv_eq_left_inv
      rw [hG]
      norm_num [Matrix.mul_apply,Fin.sum_univ_succ,funext_iff,
        ← Matrix.ext_iff,Fin.forall_fin_succ]
    have hn : (3 : ℝ) ≤ N := by exact_mod_cast hN
    have hn0 : (N : ℝ) ≠ 0 := by linarith
    have hn1 : (N : ℝ)-1 ≠ 0 := by linarith
    constructor <;> rw [hi,hrow] <;> ext i j <;> fin_cases i <;> fin_cases j <;>
      simp [sandwich,Dreal] <;>
      field_simp <;> ring

end SAP.P018a.WH.W1
