import SAP.P018b.WH.W1.Support
import AronowAudit.P018.Wave1.Gap.GLP0181B1
import AronowAudit.P018.Wave1.Gap.GLP0182B3

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SAP.P018b.WH.W1
open Finset Matrix MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology ENNReal Matrix.Norms.Elementwise
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

/-- Six-edge spectrum with multiplicities. Exhibit the eigenbasis with columns
1, (1,0,0,0,0,-1), (0,1,0,0,-1,0), (0,0,1,-1,0,0), wholeCycle,
(1,0,-1,-1,0,1). Verify its rational inverse and diagonalization, then use
Matrix.charpoly_units_conj and Matrix.charpoly_diagonal. About 150 lines. -/
def T17_L1 : Prop :=
  wholeOverlap4.charpoly =
    (Polynomial.X - Polynomial.C 5) * (Polynomial.X - Polynomial.C 1)^3 *
      (Polynomial.X + Polynomial.C 1)^2

/-- Intercept-only fit on the six labelled edges. The Gram is the nonzero scalar
6, the outcome sum is zero, and c'Wc=-4. Verify the scalar inverse by
Matrix.inv_eq_left_inv and expand the six finite sums. About 80 lines. -/
def T17_L2 : Prop :=
  (sampleGram (wholeInterceptX (Fin 6))).det = 6 ∧
  sampleOLS (wholeInterceptX (Fin 6)) wholeCycle = 0 ∧
  (∀ d, fittedResidual (wholeInterceptX (Fin 6)) wholeCycle d = wholeCycle d) ∧
  sampleVariance sixMembers (wholeInterceptX (Fin 6)) wholeCycle 0 0 = -1/9

/-- Zero-padded intercept witness at every N>4. Embed the six subsets of the
first four units into Dyad N. Sum only the four supported outcomes: their sum is
zero and their overlap quadratic form is -4. Use printed_card_real for the Gram,
prove D>0, and calculate its 1-by-1 inverse. About 200 lines; no asymptotics. -/
def T17_L3 : Prop :=
  ∀ N : ℕ, 4 < N →
    (sampleGram (wholeInterceptX (Dyad N))).det = Dreal N ∧ 0 < Dreal N ∧
    sampleOLS (wholeInterceptX (Dyad N)) wholePaddedY = 0 ∧
    (∀ d, fittedResidual (wholeInterceptX (Dyad N)) wholePaddedY d = wholePaddedY d) ∧
    sampleVariance members (wholeInterceptX (Dyad N)) wholePaddedY 0 0 = -4/(Dreal N)^2

/-- The N=20 normal-input point has the displayed Gram and OLS fit. Enumerate
edges by pairs i<j; group the sixteen identical covariates, giving sum z=74,
sum z²=100, sum Y=74 and sum zY=98. Verify the rational two-by-two inverse.
About 180 lines; use interval_cases and rational arithmetic rather than a
190-by-190 expansion. -/
def T17_L4 : Prop :=
  sampleGram (wholeSimulationDesign wholeTwentyPoint) = !![190,74;74,100] ∧
  sampleOLS (wholeSimulationDesign wholeTwentyPoint) (wholeSimulationResponse wholeTwentyPoint) =
    ![37/3381,3286/3381]

/-- Exact slope sandwich at the N=20 point. Use overlap_meat_identity to reduce
the 190² ordered pairs to twenty squared unit-score sums minus 190 dyad squares.
Reuse the finite Gram certificate from L4 and verify its inverse. About 250 lines of finite rational arithmetic. -/
def T17_L5 : Prop :=
  wholeSimulationSlope wholeTwentyPoint = -31032915283/43557147269307

/-- Continuity at any full-rank N=20 input. Absolute difference, finite sums,
products and determinant are continuous; apply continuousAt_matrix_inv on the
nonsingular Gram, or its explicit two-by-two inverse. Include fitted residuals
and the outer bread factors. About 120 lines. Full Gaussian support is already
proved in simulation_positive_of_nhds and is not a leaf. -/
def T17_L6 : Prop :=
  ∀ ω : SimulationIndex 20 1 → ℝ,
    (sampleGram (wholeSimulationDesign ω)).det ≠ 0 →
    ContinuousAt (fun x => (sampleGram (wholeSimulationDesign x)).det) ω ∧
    ContinuousAt wholeSimulationSlope ω

/-- Whole T17, with finite donor certificates and local full-support glue proved here. -/
theorem T17_assembly (h1 : T17_L1) (h2 : T17_L2) (h3 : T17_L3)
    (h4 : T17_L4) (h5 : T17_L5) (h6 : T17_L6) : T17WholeStatement := by
  have hs : negativeSampleFacts := AronowAudit.P018.negative_ols_certificate
  have hp : negativePopulationFacts := AronowAudit.P018.Wave1.negative_sample_population_proof
  have hm := hs.2.2.2.2.2.1
  have hdet : (sampleGram (wholeSimulationDesign wholeTwentyPoint)).det = 13524 := by
    rw [h4.1]
    norm_num [Matrix.det_fin_two]
  have hvalue := h5
  have hneg : wholeSimulationSlope wholeTwentyPoint < 0 := by rw [hvalue]; norm_num
  refine ⟨h1, ?_, ?_, ?_, h2.1, h2.2.1, h2.2.2.1, h2.2.2.2, ?_, ?_, hs, ?_,
    ?_, ?_, ?_, ?_, ?_, hp, ?_, ?_, AronowAudit.P018.Wave1.negative_population_gamma,
    ?_, ?_, h4.1, hdet, h4.2, hvalue, hneg, ?_,
    AronowAudit.P018.Wave1.inferenceB3_target_limit (Bridge.toKernel finiteNegativeKernel) hp.1,
    AronowAudit.P018.Wave1.inferenceB3_vector_clt (Bridge.toKernel finiteNegativeKernel) hp.1⟩
  · ext d
    fin_cases d <;> norm_num [wholeOverlap4, wholeCycle, sixMembers, Matrix.mulVec,
      dotProduct, Fin.sum_univ_succ]
  · norm_num [wholeCycle, Fin.sum_univ_succ]
  · norm_num [wholeCycle, Fin.sum_univ_succ]
  · rw [h2.2.2.2]; norm_num
  · intro N hN
    obtain ⟨hg, hd, hb, he, hv⟩ := h3 N hN
    refine ⟨hg, hd, hb, he, hv, ?_⟩
    rw [hv]
    exact div_neg_of_neg_of_pos (by norm_num) (sq_pos_of_pos hd)
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [meat, sixMembers, negativeX, negativeE, score, outer, Fin.sum_univ_succ]
  · rw [hm]; norm_num [Matrix.det_fin_two]
  · rw [hm]; norm_num [Matrix.det_fin_two]
  · rw [hm]; norm_num [Matrix.trace, Fin.sum_univ_succ]
  · rw [hm]
    convert AronowAudit.P018.positive_definite_two (17/50) (-21/125) (58/625)
      (by norm_num) (by norm_num) using 1 <;>
      ext i j <;> fin_cases i <;> fin_cases j <;> norm_num
  · intro j ⟨r, hr⟩
    have hn : sampleVariance sixMembers negativeX negativeY j j < 0 := by
      fin_cases j
      · exact hs.2.2.2.2.2.2.1
      · exact hs.2.2.2.2.2.2.2
    linarith [sq_nonneg r]
  · rintro ⟨t,a⟩ ⟨s,b⟩
    fin_cases t <;> fin_cases s <;> cases a <;> cases b <;>
      norm_num [finiteNegativeKernel, heterogeneityTable, signValue]
  · rw [hp.2.1]; norm_num [Matrix.det_fin_two]
  · rw [hp.2.2.2.1]; norm_num [Matrix.det_fin_two]
  · intro ω hω
    exact ⟨fun d => congrFun (AronowAudit.P018.Wave1.negative_population_eventDesign ω hω) d,
      fun d => congrFun (AronowAudit.P018.Wave1.negative_population_eventResponse ω hω) d⟩
  · obtain ⟨hc, hv⟩ := h6 wholeTwentyPoint (by rw [hdet]; norm_num)
    apply simulation_positive_of_nhds (ω := wholeTwentyPoint)
    have hd : {x : SimulationIndex 20 1 → ℝ |
        (sampleGram (wholeSimulationDesign x)).det ≠ 0} ∈ 𝓝 wholeTwentyPoint :=
      hc.preimage_mem_nhds (isOpen_compl_singleton.mem_nhds (by simpa [hdet]))
    have hn : {x | wholeSimulationSlope x < 0} ∈ 𝓝 wholeTwentyPoint :=
      hv.preimage_mem_nhds (isOpen_Iio.mem_nhds hneg)
    exact Filter.inter_mem hd hn

/-- Full T18; all new clauses here are short algebra, order, or measure bounds. -/
theorem T18_assembly : T18WholeStatement := by
  have hs : negativeSampleFacts := AronowAudit.P018.negative_ols_certificate
  have hp : negativePopulationFacts := AronowAudit.P018.Wave1.negative_sample_population_proof
  have hold : T18Statement := by
    refine ⟨?_, AronowAudit.P018.standard_error_domain, AronowAudit.P018.truncation_contraction,
      AronowAudit.P018.scaled_truncation, AronowAudit.P018.negative_implies_deviation, ?_,
      @AronowAudit.P018.truncation_keeps_consistency, @AronowAudit.P018.negative_diagonals_vanish⟩
    · intro V E _ _ _ _ s hs hi k q P hP
      exact ⟨AronowAudit.P018.incidence_meat_structure s hs hi q,
        (AronowAudit.P018.standard_error_correction s hs hi q P hP).2.1,
        AronowAudit.P018.sandwich_difference_of_grams s hs hi q P hP⟩
    · intro Ω _ μ _ N hN v V hV
      apply ENNReal.toReal_mono (measure_ne_top μ _)
      exact measure_mono (fun ω hω => AronowAudit.P018.negative_implies_deviation N hN (v ω) V hV hω)
  refine ⟨hold, ?_, by rw [hs.2.1]; norm_num, ?_, ?_, ?_, ?_, ?_⟩
  · intro N k hN X e
    have hsym : (sampleGram X).transpose = sampleGram X := by
      ext a b
      simp only [sampleGram, Matrix.transpose_apply, Matrix.sum_apply, outer]
      apply Finset.sum_congr rfl
      intros; ring
    have hP : ((sampleGram X)⁻¹).transpose = (sampleGram X)⁻¹ := by
      rw [Matrix.transpose_nonsing_inv, hsym]
    have hex : wholeExpandedMeat X e = meat members (fun d => score (X d) (e d)) := by
      rw [wholeExpandedMeat, meat]
      apply Finset.sum_congr rfl
      intro d hd
      have hself : overlap d d := by
        simp only [overlap, inter_self]
        exact Finset.card_pos.mp (by rw [members_card]; norm_num)
      have hn : (members d).Nonempty := Finset.card_pos.mp (by rw [members_card]; norm_num)
      ext a b
      simp only [AronowAudit.P018.matrix_ite_apply, Matrix.zero_apply, Matrix.add_apply, Matrix.sum_apply, Matrix.smul_apply, outer, smul_eq_mul,
        score, Pi.smul_apply]
      have he (f : Dyad N) :
          (if (members d ∩ members f).Nonempty then
            e d * X d a * (e f * X f b) else 0) =
          (if f=d then (e d)^2*(X d a*X d b) else 0) +
          (if f ∈ neighbors d then (e d*e f)*(X d a*X f b) else 0) := by
        by_cases hf : f=d
        · subst f; simp [hn, neighbors]; ring
        · by_cases ho : (members d ∩ members f).Nonempty
          · have hneigh : f ∈ neighbors d := by simp [neighbors, hf, ho]
            simp only [if_pos ho, if_neg hf, if_pos hneigh, zero_add]
            ring
          · have hneigh : f ∉ neighbors d := by simp [neighbors, ho]
            simp only [if_neg ho, if_neg hf, if_neg hneigh, add_zero]
      simp_rw [he, Finset.sum_add_distrib]
      simp [Finset.sum_filter]
      congr 1
      ext q
      simp
    refine ⟨hex, hP, ?_⟩
    rw [hex]
    exact (hold.1 members members_card (fun _ _ h => Subtype.ext h)
      (fun d => score (X d) (e d)) (sampleGram X)⁻¹ hP).2.1
  · intro hpsd
    have : 0 ≤ sampleVariance sixMembers negativeX negativeY 0 0 := hpsd.diag_nonneg
    linarith [hs.2.2.2.2.2.2.1]
  · intro Ω _ μ hμ v V ⟨c,hc,hbound⟩ hprob
    have ht := hprob c hc
    apply squeeze_zero' (Filter.Eventually.of_forall (fun N => ENNReal.toReal_nonneg)) _ ht
    filter_upwards [hbound] with N hN
    letI : IsProbabilityMeasure (μ N) := hμ N
    apply ENNReal.toReal_mono (measure_ne_top (μ N) _)
    apply measure_mono
    intro ω hω
    have hv := AronowAudit.P018.negative_implies_deviation (N : ℝ) (Nat.cast_nonneg N)
      (v N ω) (V N) (lt_of_lt_of_le hc hN) hω
    simpa only [Set.mem_setOf_eq, Real.norm_eq_abs] using hN.trans hv
  · intro v
    refine ⟨fun hv => by simp [standardError, hv], ?_⟩
    intro hv
    refine ⟨by simp [standardError, not_le.mpr hv], ?_, by simp [max_eq_right hv.le]⟩
    rintro ⟨r,hr⟩
    linarith [sq_nonneg r]
  · intro m v
    apply congrArg Finset.card
    apply Finset.ext
    intro j
    by_cases hv : 0 ≤ v j
    · simp [standardError, hv, not_lt.mpr hv]
    · simp [standardError, hv, not_le.mp hv]
  · intro c
    let μ := unitSampleLaw finiteNegativeKernel 4
    letI : IsProbabilityMeasure finiteNegativeKernel.μ := hp.1.1
    letI : IsProbabilityMeasure μ := by dsimp [μ, unitSampleLaw]; infer_instance
    have hb := hp.2.2.2.2.2.1
    change (μ _).toReal ≥ _
    rw [← hb]
    apply ENNReal.toReal_mono (measure_ne_top μ _)
    apply measure_mono
    intro ω hω
    obtain ⟨hg,hv⟩ := hp.2.2.2.2.2.2 ω hω
    have hD : (fun d : Fin 6 => design finiteNegativeKernel ω
        (AronowAudit.P018.Wave1.negative_population_dyadEquiv d)) = negativeX :=
      AronowAudit.P018.Wave1.negative_population_eventDesign ω hω
    have hY : (fun d : Fin 6 => response finiteNegativeKernel ω
        (AronowAudit.P018.Wave1.negative_population_dyadEquiv d)) = negativeY :=
      AronowAudit.P018.Wave1.negative_population_eventResponse ω hω
    have hOLS : sampleOLS (fun d : Fin 6 => design finiteNegativeKernel ω
        (AronowAudit.P018.Wave1.negative_population_dyadEquiv d))
        (fun d => response finiteNegativeKernel ω (AronowAudit.P018.Wave1.negative_population_dyadEquiv d)) =
        sampleOLS (design finiteNegativeKernel ω) (response finiteNegativeKernel ω) :=
      AronowAudit.P018.Wave1.negative_population_olsReindex
      AronowAudit.P018.Wave1.negative_population_dyadEquiv (design finiteNegativeKernel ω)
      (response finiteNegativeKernel ω)
    rw [hD, hY] at hOLS
    have hbfit : sampleOLS (design finiteNegativeKernel ω) (response finiteNegativeKernel ω) = ![3,2/5] :=
      hOLS.symm.trans hs.2.2.1
    simp only [Set.mem_setOf_eq]
    rw [hbfit, hp.2.2.1, hv]
    norm_num

/-- Conditional mean zero for every rare-model record given the full design.
Simultaneously flip both signs on every unit. The atomic unit law and its finite
products are invariant; the design is fixed and each response is negated. Thus
its integral on every design-measurable event is zero. Apply conditional-expectation
uniqueness. This avoids construction of a conditional law. About 180 lines. -/
def T19_L1 : Prop := wholeRareConditionalMean rareModel

/-- Expected observation-normalized Gram of the actual rare model. Use
TailB_rare_gram, repeatedL=2D, the iid pair law, and boundedness of s² to exchange
the finite sum and integral. The pair expectation is rareQ. No inverse moments
are needed. About 100 lines. -/
def T19_L2 : Prop :=
  ∀ N : ℕ, 2 ≤ N →
    wholeRepeatedH (wholeRareKernel rareModel) N = !![1,1;1,1+wholeRareQ rareModel]

/-- Exact probability of all levels m and distinct labels. Sum the atoms over
injective Fin N -> Fin(m+1) labelings and all signs, using card_embedding_eq and
Measure.pi_singleton. Here m is printed M-1; N<=m+1 gives strict positivity.
About 180 lines. -/
def T19_L3 : Prop :=
  ∀ N m : ℕ, 2 ≤ N → N ≤ m+1 →
    (repeatedLaw (wholeRareKernel rareModel) N (wholeRareEvent rareModel N m)).toReal =
      (2 : ℝ)^(-((m+1 : ℤ)*N)) * (Nat.descFactorial (m+1) N : ℝ) / (m+1 : ℝ)^N ∧
    0 < repeatedLaw (wholeRareKernel rareModel) N (wholeRareEvent rareModel N m)

/-- Conditional second moment of the slope on each finite-category event.
Use TailB_rare_event_slope, integrate independent fair signs to get E[Abar²]=1/N,
and divide by the positive event probability. The restricted slope square is
integrable because delta_(m+1)>0 and the signs are bounded. About 150 lines. -/
def T19_L4 : Prop :=
  ∀ N m : ℕ, 3 ≤ N → N ≤ m+1 →
    Integrable (fun ω => (repeatedOLS (wholeRareKernel rareModel) ω 1)^2)
      ((repeatedLaw (wholeRareKernel rareModel) N).restrict (wholeRareEvent rareModel N m)) ∧
    (∫ ω, (repeatedOLS (wholeRareKernel rareModel) ω 1)^2
      ∂ (repeatedLaw (wholeRareKernel rareModel) N).restrict (wholeRareEvent rareModel N m)) /
      (repeatedLaw (wholeRareKernel rareModel) N (wholeRareEvent rareModel N m)).toReal =
        4 / ((N : ℝ)*(wholeRareDelta (m+1))^2)

/-- Collision bound and explicit exponential lower bounds. The union bound for
N(N-1)/2 label collisions gives distinct-label probability >=1/2 when m+1>=N(N-1).
Combine L3--L4, the integrable nonnegative restricted square, and delta's formula.
Use integer exponents throughout the difference 2(m+1)²-(m+1)N; prove the final
power inequality by monotonicity, not truncated natural subtraction. About 220 lines. -/
def T19_L5 : Prop := wholeRareGrowth rareModel

/-- Unconditional and event-conditional mean of the sign dispersion. Expand
sum(A_i-Abar)²=N-N*Abar² and use independent fair signs, also independent of each
category event. Event probabilities are positive when N<=m+1. About 120 lines.
The pointwise sandwich formula and complement bound are existing donors and
are assembled separately. -/
def T19_L6 : Prop :=
  ∀ N : ℕ, 2 ≤ N →
    (∫ ω, wholeRareDispersion rareModel ω ∂ repeatedLaw (wholeRareKernel rareModel) N) = N-1 ∧
    (∀ m, N ≤ m+1 →
      (∫ ω, wholeRareDispersion rareModel ω
        ∂ (repeatedLaw (wholeRareKernel rareModel) N).restrict (wholeRareEvent rareModel N m)) /
        (repeatedLaw (wholeRareKernel rareModel) N (wholeRareEvent rareModel N m)).toReal = N-1)

/-- Summability of the printed H series. Every nonnegative term is bounded by
2^(-3(m+1)), since 0<delta_(m+1)<=1 and 0<=1-1/(m+1)<=1. Compare with a geometric
series of ratio 1/8. About 60 lines; positivity is already tb09_rare_H_pos. -/
def T19_L7 : Prop := Summable wholeRareHterm

/-- The auxiliary uniforms are almost surely all distinct, and the plus/minus
record permutation preserves the actual unit-weight WLS and overlap sandwich.
Use atomlessness and the finite union over pairs for ties. On tie-free samples,
reindex each Fin 2 record sum by identity or Fin.rev; the block scores and Gram
are unchanged. About 200 lines, including the empty N=0 case. -/
def T19_L8 : Prop := wholeRareDirectedEquality rareModel

/-- Moment and limit transport to the independent-uniform directed model.
Projection of the product unit law preserves the original law; apply
measurePreserving_pi to measurePreserving_fst. Use L8's estimator equalities,
lintegral_map for the positive/negative moments, and integral_map for bounded
continuous test functions. Deviation probabilities are identical. Existing
rareModel_moments and rareModel_limits supply the source results. About 200 lines.
This is transport of proved source results, not a new limit or tail theorem. -/
def T19_L9 : Prop :=
  wholeRareDirectedMoments rareModel ∧ wholeRareDirectedLimits rareModel

/-- Whole T19. All rank, exact-fit, pointwise sandwich and tail/limit donors are
used directly; only genuinely missing population/event/direction steps are inputs. -/
theorem T19_assembly (h1 : T19_L1) (h2 : T19_L2) (h3 : T19_L3)
    (h4 : T19_L4) (h5 : T19_L5) (h6 : T19_L6) (h7 : T19_L7)
    (h8 : T19_L8) (h9 : T19_L9) : T19WholeStatement := by
  refine ⟨AronowAudit.P018.RareUnit, inferInstance, rareModel, rareModel_law,
    AronowAudit.P018.Wave1.TailB_rare_standing, rareModel_bounds, h1, ?_, rareModel_finite,
    ?_, h5, rareModel_moments, ?_, h7, AronowAudit.P018.Wave1.tb09_rare_H_pos,
    rareModel_limits, h8, h9.1, h9.2⟩
  · refine ⟨AronowAudit.P018.Wave1.tb09_rare_population_beta,
      AronowAudit.P018.Wave1.tb09_rare_Q_bounds.1,
      AronowAudit.P018.Wave1.tb09_rare_Q_bounds.2, ?_⟩
    intro N hN
    refine ⟨h2 N hN, ?_⟩
    rw [h2 N hN]
    norm_num [Matrix.det_fin_two]
  · intro N m hN hm
    exact ⟨(h3 N m (by omega) hm).1, (h3 N m (by omega) hm).2,
      fun _ hω => AronowAudit.P018.Wave1.TailB_rare_event_slope (by omega) hω,
      (h4 N m hN hm).1, (h4 N m hN hm).2⟩
  · intro N hN
    refine ⟨fun _ _ hω => AronowAudit.P018.Wave1.TailB_rare_event_variance hN hω,
      (h6 N hN).1, (h6 N hN).2, ?_⟩
    intro ω hω
    obtain he | hg := AronowAudit.P018.Wave1.TailB_rare_small_or_count hN ω
    · obtain ⟨m, hm⟩ := he
      exact (hω m hm).elim
    · exact AronowAudit.P018.Wave1.TailB_rare_variance_abs_bound hN ω hg

/-- Finite L2 of the linear approximations for bounded finite record arrays.
No coefficient-estimator moment is assumed: only the expected inverse is fixed.
Transport the pair essential bounds to sampled coordinates, take finite sums,
products and fixed linear combinations. A generic lemma for weighted records
also proves the unweighted case. About 200 lines. Covariance identities are
existing donors and are not part of this leaf. -/
def T20_L1 : Prop :=
  ∀ {U : Type} [MeasurableSpace U] {k N : ℕ} (R : RepeatedKernel U k)
    (w : (d : Dyad N) → Fin (R.T N d) → ℝ),
    wholeRepeatedAtSize R N →
    ∀ (P : Mat k) (c : ℝ) (β : Vec k) (a : Fin k),
    MemLp (fun ω => (P.mulVec (c •
      (∑ d : Dyad N, wholeWeightedBlockScore R w β ω d))) a) 2 (repeatedLaw R N)

/-- The actual rare model has positive expected and sample rank, but neither
finite slope moments nor UI of the scaled squares. Use T19_L2's finite expected
Gram calculation and q>0, the proved infinite coefficient integrals, and
MemLp iff finite nonnegative square integral. Unit weights give identical
OLS/population projection. UI includes each member's L2, contradicting N=3.
About 150 lines. No assumption of UI or finite estimator moments is added. -/
def T20_L2 : Prop :=
  (∀ N, 2 ≤ N → (wholeRepeatedH (wholeRareKernel rareModel) N).det > 0) ∧
  (∀ N, 3 ≤ N →
    ¬ MemLp (fun ω => repeatedOLS (wholeRareKernel rareModel) ω 1 -
      repeatedBeta (wholeRareKernel rareModel) N 1) 2 (repeatedLaw (wholeRareKernel rareModel) N) ∧
    ¬ Integrable (fun ω => wholeWeightedOLS (wholeRareKernel rareModel) (fun _ _ => 1) ω 1 -
      wholeWeightedBeta (N := N) (wholeRareKernel rareModel) (fun _ _ => 1) 1)
      (repeatedLaw (wholeRareKernel rareModel) N)) ∧
  ¬ uiSquares (repeatedLaw (wholeRareKernel rareModel)) (fun N ω =>
    Real.sqrt N • (repeatedOLS (wholeRareKernel rareModel) ω - repeatedBeta (wholeRareKernel rareModel) N))

/-- The auxiliary-uniform model is an actual common directed-kernel example.
Take direction labels t=0/1. Define the common ordered kernel by plus for increasing
auxiliary labels, minus for decreasing labels, and plus on ties. Symmetry of the
original rare pair functions proves the pointwise reversal identity. Transport
boundedness, expected Gram and zero population score through projection, using
tie probability zero and the record permutation from T19_L8. The normalized
weighted Gram is twice the per-record expected Gram. Use q>0 for positive
definiteness and original sample rank for almost-sure directed rank. About 220 lines. -/
def T20_L3 : Prop := wholeDirectedAdmissibility rareModel

/-- Moment failure in that admissible directed example. Use T19_L9's transported
infinite first and second coefficient moments, the zero population projection
from T20_L3, and MemLp.integrable_sq. UI includes L2 of the scaled slope at N=3;
rescaling by its nonzero square root yields a contradiction. About 80 lines.
The sibling leaves' proved helpers may be reused; no new tail construction. -/
def T20_L4 : Prop := wholeDirectedMomentFailure rareModel

/-- Whole T20, including both finite targets, both consistency contracts, the
scaled covariance identity and the deterministic interpretation. The repeated
contract retains the explicit vanishing N/L_N^2-scaled ordered-overlap sum of
products of expected block scores in T20WholeStatement. It is a substantive
assumption and is not inferred from the normal equations. -/
theorem T20_assembly (h1 : T20_L1) (h2 : T20_L2) (h3 : T20_L3) (h4 : T20_L4) : T20WholeStatement := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro U _ k N R hR hN hH
    have h := AronowAudit.P018.Wave1.repeated_target_correction_proof (Bridge.toRepeated R) hR hN hH
    refine ⟨h.1, h.2.2.1, h.2.1, h.2.2.2, ?_⟩
    intro a
    simpa only [wholeWeightedBlockScore, repeatedBlockScore, one_mul] using
      h1 R (fun _ _ => 1) hR (wholeRepeatedH R N)⁻¹
        (Real.sqrt N/repeatedL R N) (repeatedBeta R N) a
  · intro U _ k N R w hR hN hH
    have h := AronowAudit.P018.Wave1.weighted_target_correction_proof (Bridge.toRepeated R) hR hN w hH
    exact ⟨h.1, h.2.2.1, h.2.1, h.2.2.2, h1 R w hR (wholeWeightedH R w)⁻¹
      (Real.sqrt N/Dreal N) (wholeWeightedBeta R w)⟩
  · intro U _ k R hR hCommon hT H hH hlim hMean
    exact AronowAudit.P018.Wave1.repeated_consistency_with_overlap_mean_control
      (Bridge.toRepeated R) hR hCommon hT H hH hlim hMean
  · intro U _ k R hR hT X Y dir hi hdata w a ha hw H hH hlim
    exact AronowAudit.P018.Wave1.weighted_consistency_common_directed_kernel
      (Bridge.toRepeated R) hR hT X Y dir hi hdata w a ha hw H hH hlim
  · intro Ω _ k μ hμ e ν ξ _heL2 hweak hui hL2 hzero
    have hm := AronowAudit.P018.Wave1.variance_limit_with_UI_proof μ hμ ξ ν hweak hui hL2 hzero
    have heq (N : ℕ) : (N : ℝ) • varMat (μ N) (e N) = varMat (μ N) (ξ N) := by
      have h := AronowAudit.P018.covariance_score_scale (μ N) (e N) (Real.sqrt N)
      rw [Real.sq_sqrt (Nat.cast_nonneg N)] at h
      exact h.symm
    have hv : Tendsto (fun N : ℕ => (N : ℝ) • varMat (μ N) (e N)) atTop (𝓝 (varMat ν id)) := by
      have hh : Tendsto (fun N : ℕ => varMat (μ N) (ξ N)) atTop (𝓝 (varMat ν id)) := hm.2
      exact hh.congr' (Filter.Eventually.of_forall (fun N => (heq N).symm))
    refine ⟨hm.1, heq, hv, ?_⟩
    intro V hV
    simpa only [sub_self] using hv.sub hV
  · refine ⟨AronowAudit.P018.RareUnit, inferInstance, wholeRareKernel rareModel,
      AronowAudit.P018.Wave1.TailB_rare_standing, h2.1, ?_, h2.2.1, h2.2.2⟩
    intro N hN ω
    exact AronowAudit.P018.Wave1.TailB_rare_gram_pos hN ω
  · exact ⟨AronowAudit.P018.RareUnit, inferInstance, rareModel, rareModel_law, h3, h4⟩
  · intro Ω _ k μ hμ A
    letI : ∀ N, IsProbabilityMeasure (μ N) := hμ
    constructor
    · exact AronowAudit.P018.Wave1.WeightedConsistency.inProbability_deterministic μ A
    · intro hprob
      apply Metric.tendsto_nhds.mpr
      intro ε hε
      filter_upwards [(hprob ε hε).eventually (gt_mem_nhds (by norm_num : (0 : ℝ)<1/2))] with N hN
      by_contra h
      have hn : ε ≤ ‖A N‖ := by simpa only [dist_zero_right] using le_of_not_gt h
      have he : {ω : Ω N | ε ≤ ‖A N‖} = Set.univ := by ext; simp [hn]
      simp only [he, measure_univ, ENNReal.toReal_one] at hN
      norm_num at hN

/-- Whole T21, assembled entirely from proved counts, sparse variance and the
explicit bounded nonlinear witness. No new mathematical leaf is required. -/
theorem T21_assembly : T21WholeStatement := by
  obtain ⟨hS, _hrank, _hQ, _hdet, hβ, _hH, _hG, _hGP, hcond, hV, _hrest⟩ :=
    AronowAudit.P018.Wave1.nonlinear_counterexample_proof
  have hz := (hcond 3 (by norm_num)).2.1
  refine ⟨AronowAudit.P018.Wave1.dyad_counts_proof, ?_, ?_, hS, hβ, hz, hV, ?_⟩
  · intro U _ k N K _ _
    exact AronowAudit.P018.expectation_placement_correction (Bridge.toKernel K)
  · intro U _ k N K hK
    have h := AronowAudit.P018.Wave1.vc3_sparse_variance (N := N) (Bridge.toKernel K) hK
    rw [AronowAudit.P018.Wave1.vc3_corrected_expand (N := N) (Bridge.toKernel K) hK] at h
    refine h.trans ?_
    unfold wholeCorrectedSigma
    apply Finset.sum_congr rfl
    intro d hd
    apply Finset.sum_congr rfl
    intro f hf
    by_cases ho : overlap d f
    · simp only [show AronowAudit.P018.overlap d f from ho, ho, if_true]
      ext a b
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun ω => by
        change (epsilon K ω d * design K ω d a) * (epsilon K ω f * design K ω f b) =
          (epsilon K ω d * epsilon K ω f) * (design K ω d a * design K ω f b)
        ring)
    · simp only [show ¬ AronowAudit.P018.overlap d f from ho, ho, if_false]
  · have hz' : printedSigma wholeNonlinearKernel 3 = 0 := hz
    have hV' : varMat (unitSampleLaw wholeNonlinearKernel 3) (scoreSum wholeNonlinearKernel) =
        !![12/5,24/5;24/5,4712/315] := hV
    rw [hz', hV']
    intro h
    have he := congrArg (fun M : Mat 2 => M 0 0) h
    norm_num at he

end SAP.P018b.WH.W1
