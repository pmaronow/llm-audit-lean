import SAP.P011a.Defs.WholeW1
import SAP.P011a.Bridge

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P011a.WH.W1

open MeasureTheory ProbabilityTheory Filter Finset
open scoped BigOperators Topology Classical Matrix NNReal ENNReal
noncomputable section
set_option maxHeartbeats 1500000
set_option maxRecDepth 4000

/-- Finite homoskedastic covariance and scalar comparison without row nesting.
Use weighted_memLp, common_variance, covariance_abs_le_common and covariance_support.
Bound Cov(X_i,X_j) by sigma squared on the diagonal/edges and by zero off support;
sum using degree_row_sum and beta_variance. The g bounds follow by summing degrees.
The V2 identity and the entire remainder gap chain are scalar algebra, with
nonnegative mean spread. No correlation or auxiliary estimator is needed.
Expected proof size: 100--160 lines. -/
def T12_L1 : Prop :=
  ∀ {n : ℕ}, 0 < n → ∀ (m : Model n) (c d : ℝ), 0 < c → 0 < d →
    Dependency m →
    (∀ᵐ y ∂m.law, ∀ i, |weighted m y i-beta m| ≤ c) →
    (∀ i, (degree m.G i : ℝ) ≤ d) → Homoskedastic m →
    WholeHomoskedasticComparison m d

/-- Quadratic expansion and PSD conservativeness for arbitrary observed rows.
Replay DenseLimitCompletion.limit_clauses_from_variance with WholeScaling fields.
The explicit O(n) variance premise is already proved below from sample_variance_bound.
Use quadratic_centered_memLp and rowCP_of_variance for concentration,
finite_expectation_error for the O(1/n) deterministic error, oracle_trace and
beta_variance for centering, and trace_psd_covariance for the PSD conclusion.
No cross-row embeddings or monotonicity is used. Expected proof size: 130--200 lines. -/
def T6_L1 : Prop := WholeQuadraticLimit

/-- Transfer the bounded capped Young majorant to the original degree-only maximum.
Assuming the quadratic-limit kernel, set c_i=min(d_i',ceil(c2)), use the finite
comparisonCaps_valid/comparison_psd/comparison_norm/comparison_form lemmas, and
apply that kernel to the diagonal matrix 1+diag(c). Then replay
Wave1.degree_only_conservative_proof using GP011B2b_uniform_comparison and the
finite beta_error_bound to bound residuals by 2c1. The supplied caps remain
unbounded; the comparison cap is fixed. Expected proof size: 100--180 lines. -/
def T7_L1 : Prop := WholeQuadraticLimit → WholeDegreeOnlyConservative

/-- Uniqueness of the two-sign-clique optimizer on a nonconstant sign sample.
Use unbounded_caps_pair_domination and unbounded_caps_witness_max. Maximality
forces equality of the sums of pair contributions, hence equality at every pair
(sum_eq_sum_iff_of_le, twice). The mean lies strictly between -1 and 1, so all
same-sign residual products are positive and all cross-sign products negative.
Each differing adjacency entry would give a strict loss. Expected size: 100--180 lines. -/
def T7_L2 : Prop := WholeSignOptimizer

/-- Dependency-graph CLT under WholeScaling, without observed nesting.
Replay ProbabilityCompletion.dependency_graph_clt_completed, replacing the
Scaling destructuring by WholeScaling fields. modelDep gives the dependency
graph; own_centred_bound gives 2c1; degrees are bounded by ceil(c2)+1; the positive
variance limit supplies the eventual lower variance bound. Apply
bounded_degree_dependency_clt_ae and depSum_standardized. Zero early variances
need no exclusion. Expected proof size: 60--100 lines. -/
def T7_L3 : Prop := WholeCLT

/-- Clipped conservative Wald coverage from the row CLT.
Replay CoverageCompletion.consistent_coverage using the supplied WholeCLT instead
of dependency_graph_clt; its remaining inputs are variance_limit and c3_pos.
Use rowCP_moving_center, rowCP_continuous_pair, row_random_width_interval,
quantile_positive, quantile_mass and scaled_width. Then replay conservative_coverage:
truncate at the true variance, prove scaled consistency by truncation_identity,
and use interval_containment and le_liminf_iff. All estimator functions here are
explicitly measurable; no selector measurability is assumed. Expected size: 170--240 lines. -/
def T7_L4 : Prop := WholeCLT → WholeWald

/-- The original oracle is conservative when liminf meanBias is nonnegative.
Apply the quadratic kernel to M=I+A, using the oracle degree norm bound.
The expansion center is meanBias because the matrix difference is zero.
Replay MeanCompletion.bias_bound with own_mean_bound and quadratic_bound to bound
meanBias above and below, then use conservative_centres. Uniform variance is
available from the finite sample_variance_bound. Expected size: 80--140 lines. -/
def T8_L1 : Prop := WholeQuadraticLimit →
  ∀ (F : Family) (c1 c2 c3 c4 : ℝ), WholeScaling F c1 c2 c3 c4 →
    0 ≤ Filter.liminf (fun k => meanBias (F.model k)) atTop →
    Conservative F (fun k y => V1 (F.model k).G (weighted (F.model k) y))

/-- Dropping the extra observed-nesting conjunct from the old hypothesis. -/
theorem scaling_to_whole (F : Family) (c1 c2 c3 c4 : ℝ)
    (h : Scaling F c1 c2 c3 c4) : WholeScaling F c1 c2 c3 c4 := by
  rcases h with ⟨_,h1,h2,h3,h4,hd,hb,hg,hv,ht⟩
  exact ⟨h1,h2,h3,h4,hd,hb,hg,hv,ht⟩

/-- The existing finite concentration estimate supplies the kernel's variance input. -/
theorem quadratic_variance (F : Family) (c1 c2 c3 c4 K : ℝ)
    (h : WholeScaling F c1 c2 c3 c4)
    (M : ∀ k, Matrix (Fin (F.size k)) (Fin (F.size k)) ℝ)
    (hM : ∀ k i j, M k i j = M k j i) (hK : ∀ k, operatorNorm (M k) ≤ K) :
    WholeQuadraticVariance F M := by
  let C := 2*(144*(1+c2)^3+2*(1+c2)^2)*(2*c1)^4+8*(1+c2)*c1^4
  have hC : 0 ≤ C := by dsimp [C]; positivity [h.c2_pos]
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hK 0)
  refine ⟨C*K^2, by positivity, 0, ?_⟩
  intro k _
  have hv := AronowAudit.P011.DenseSampleCompletion.sample_variance_bound
    (F.positive k) (Bridge.model (F.model k)) c1 (1+c2) h.c1_pos.le
    (by linarith [h.c2_pos]) (h.dependency k) (h.bounded k)
    (fun i => by
      have hi : (AronowAudit.P011.degree (Bridge.model (F.model k)).G i : ℝ) ≤ c2 := h.degrees k i
      linarith) (M k) (hM k)
  have hk : operatorNorm (M k)^2 ≤ K^2 :=
    (sq_le_sq₀ (norm_nonneg _) hK0).mpr (hK k)
  exact hv.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hk hC) (Nat.cast_nonneg _))

/-- Apply the common quadratic kernel to a deterministic PSD majorant. -/
theorem psd_conservative (hq : WholeQuadraticLimit)
    (F : Family) (c1 c2 c3 c4 K : ℝ) (h : WholeScaling F c1 c2 c3 c4)
    (M : ∀ k, Matrix (Fin (F.size k)) (Fin (F.size k)) ℝ)
    (hp : ∀ k, PSD (M k) ∧ PSD (M k-oracleMatrix (F.model k).G))
    (hn : ∀ k, operatorNorm (M k) ≤ K) :
    Conservative F (fun k y => varianceForm (M k) (weighted (F.model k) y)) := by
  exact ((hq F c1 c2 c3 c4 K h M (fun k => (hp k).1.1) hn
    (quadratic_variance F c1 c2 c3 c4 K h M (fun k => (hp k).1.1) hn)).2 hp).2

/-- Spectral clipping has bounded norm under the true-degree bound. -/
theorem spectral_conservative (hq : WholeQuadraticLimit)
    (F : Family) (c1 c2 c3 c4 : ℝ) (h : WholeScaling F c1 c2 c3 c4) :
    Conservative F (fun k y => VPositive (F.model k).G (weighted (F.model k) y)) := by
  let M := fun k => positivePart (oracleMatrix (F.model k).G)
  have hp (k : ℕ) : PSD (M k) ∧ PSD (M k-oracleMatrix (F.model k).G) := by
    have hf := Bridge.PositivePartFinite_proved (F.positive k) (F.model k).G
    exact ⟨hf.1,hf.2.1⟩
  have hn (k : ℕ) : operatorNorm (M k) ≤ 1+c2 := by
    have hf := Bridge.PositivePartFinite_proved (F.positive k) (F.model k).G
    apply hf.2.2.1.trans
    have hs : ((Finset.univ.sup (fun i => degree (F.model k).G i) : ℕ) : ℝ) ≤ c2 := by
      obtain ⟨i,hi⟩ := Finset.exists_mem_eq_sup
        (s := (Finset.univ : Finset (Fin (F.size k))))
        (f := fun i => degree (F.model k).G i)
        (by exact ⟨⟨0,F.positive k⟩,Finset.mem_univ _⟩)
      rw [hi.2]
      exact h.degrees k i
    linarith
  exact psd_conservative hq F c1 c2 c3 c4 (1+c2) h M hp hn

/-- Assembly of every finite and asymptotic clause of T6. -/
theorem T6_assembly (h1 : T6_L1) : T6WholeStatement := by
  refine ⟨Bridge.PositivePartFinite_proved, spectral_conservative h1,
    Bridge.PositivePartUnique_proved, Bridge.PositivePartCycle_proved,
    Bridge.PositivePartNonaffine_proved, Bridge.CycleSpectrum_proved, ?_, ?_,
    Bridge.SpectralDifference_proved⟩
  · intro x
    have hq := AronowAudit.P011.SpectralConfidence.cycle_actual_positive_quadratic x
    exact ⟨hq,hq.trans (AronowAudit.P011.cycle_positive_identity x)⟩
  · intro k
    exact (AronowAudit.P011.Wave1.cycle_counterexample_proof.2.2.2.1 k).2.1

/-- Assembly of all T12 finite moments, scalar comparisons, finite tail rates and limit. -/
theorem T12_assembly (h1 : T12_L1) : T12WholeStatement := by
  intro F c1 c2 c3 c4 h hs
  have hfinite (k : ℕ) : WholeHomoskedasticMoments (F.model k) c1 c2 ∧
      WholeHomoskedasticComparison (F.model k) c2 ∧
      WholeHomoskedasticTail (F.model k) c1 c2 := by
    let m := F.model k
    let : IsProbabilityMeasure m.law := m.probability
    have hn : 0 < (F.size k : ℝ) := by exact_mod_cast F.positive k
    have hd (i : Fin (F.size k)) : (degree m.G i : ℝ)+1 ≤ 1+c2 := by
      linarith [h.degrees k i]
    have hR := AronowAudit.P011.HomoskedasticCompletion.remainder_memLp_two
      (F.positive k) (Bridge.model m) c1 (h.bounded k)
    have hRs := AronowAudit.P011.HomoskedasticCompletion.remainder_second_bound
      (F.positive k) (Bridge.model m) c1 (1+c2) h.c1_pos.le
      (h.dependency k) (h.bounded k) hd
    have hc := h1 (F.positive k) m c1 c2 h.c1_pos h.c2_pos
      (h.dependency k) (h.bounded k) (h.degrees k) (hs k)
    refine ⟨⟨?_,?_,?_,?_,?_,hRs⟩,hc,?_⟩
    · exact AronowAudit.P011.SampleCompletion.sample_center_identity (F.positive k) (Bridge.model m)
    · exact AronowAudit.P011.SampleCompletion.U_mean (Bridge.model m) c1 (h.bounded k)
    · exact AronowAudit.P011.SampleCompletion.U_variance_bound
        (F.positive k) (Bridge.model m) c1 (1+c2) h.c1_pos.le
        (h.dependency k) (h.bounded k) hd
    · exact AronowAudit.P011.ExpectationCompletion.beta_variance_bound
        (F.positive k) (Bridge.model m) c1 (1+c2) h.c1_pos.le
        (h.dependency k) (h.bounded k) hd
    · exact AronowAudit.P011.HomoskedasticCompletion.beta_fourth_bound
        (F.positive k) (Bridge.model m) c1 (1+c2) h.c1_pos.le
        (h.dependency k) (h.bounded k) hd
    · intro ε hε
      have hd0 : 0 < 1+c2 := by linarith [h.c2_pos]
      have hpoint (y : Fin (F.size k) → ℝ) :
          (F.size k : ℝ)*var m (betaHat m)-(F.size k : ℝ)*V2 m.G (weighted m y) ≤
            (1+c2)*|varianceRemainder m y| := by
        have hy := hc.2.2.2.2.2.2 y
        exact hy.2.1.trans (hy.2.2.1.le.trans hy.2.2.2)
      have hsub : {y | (F.size k : ℝ)*var m (betaHat m)-
          (F.size k : ℝ)*V2 m.G (weighted m y) > ε} ⊆
          {y | |varianceRemainder m y| > ε/(1+c2)} := by
        intro y hy
        change ε < (F.size k : ℝ)*var m (betaHat m)-
          (F.size k : ℝ)*V2 m.G (weighted m y) at hy
        apply (div_lt_iff₀ hd0).mpr
        nlinarith [hpoint y]
      calc
        _ ≤ m.law.real {y | |varianceRemainder m y| > ε/(1+c2)} :=
          measureReal_mono (μ := m.law) hsub (measure_ne_top _ _)
        _ ≤ (∫ y, varianceRemainder m y^2 ∂m.law)/(ε/(1+c2))^2 :=
          AronowAudit.P011.HomoskedasticCompletion.second_moment_tail m.law
            (varianceRemainder m) hR _ (div_pos hε hd0)
        _ ≤ (4*(1+c2)*c1^4/(F.size k : ℝ))/(ε/(1+c2))^2 :=
          div_le_div_of_nonneg_right hRs (sq_nonneg _)
        _ = _ := by field_simp
  refine ⟨hfinite,?_⟩
  intro ε hε
  have hN : Tendsto (fun k => (F.size k : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp F.grows
  apply squeeze_zero (fun _ => measureReal_nonneg) (fun k => ?_)
    (hN.const_div_atTop (4*(1+c2)^3*c1^4/ε^2))
  have hr := (hfinite k).2.2 ε hε
  have he : 4*(1+c2)^3*c1^4/((F.size k : ℝ)*ε^2) =
      (4*(1+c2)^3*c1^4/ε^2)/(F.size k : ℝ) := by ring
  rw [he] at hr
  simpa only [mul_sub,probability] using hr

/-- The row bound implies the sample residual bound used in T7. -/
theorem centered_bound (F : Family) (c1 c2 c3 c4 : ℝ)
    (h : WholeScaling F c1 c2 c3 c4) (k : ℕ) :
    ∀ᵐ y ∂(F.model k).law, maxAbs (centered (weighted (F.model k) y)) ≤ 2*c1 := by
  have ha := AronowAudit.P011.HomoskedasticCompletion.beta_error_bound
    (F.positive k) (Bridge.model (F.model k)) c1 (h.bounded k)
  filter_upwards [h.bounded k,ha] with y hy hay
  change |betaHat (F.model k) y-beta (F.model k)| ≤ c1 at hay
  have he (i : Fin (F.size k)) : |centered (weighted (F.model k) y) i| ≤ 2*c1 := by
    have hid : centered (weighted (F.model k) y) i =
        (weighted (F.model k) y i-beta (F.model k))-
          (betaHat (F.model k) y-beta (F.model k)) := by
      unfold centered betaHat
      ring
    rw [hid]
    exact (abs_sub _ _).trans (by linarith [hy i])
  change ((Finset.univ.sup (fun i => (⟨|centered (weighted (F.model k) y) i|,
    abs_nonneg _⟩ : ℝ≥0)) : ℝ≥0) : ℝ) ≤
      ((⟨2*c1,by linarith [h.c1_pos]⟩ : ℝ≥0) : ℝ)
  apply NNReal.coe_le_coe.mpr
  exact Finset.sup_le (fun i _ => he i)

/-- The maximum's scalar value is measurable even for arbitrary tie choices. -/
theorem maximum_measurable (F : Family) (hv : Valid F)
    (A : ∀ k, (Fin (F.size k) → ℝ) → Graph (F.size k))
    (hm : ∀ k y, Maximizes (F.model k).R (F.model k).d
      (fun B => V1 B (weighted (F.model k) y)) (A k y)) :
    ∀ k, Measurable (fun y => V1 (A k y) (weighted (F.model k) y)) := by
  intro k
  exact AronowAudit.P011.Wave1.GP011B2b_revised_corollaries_maximum_measurable
    (Bridge.model (F.model k)) (hv k) _
    (AronowAudit.P011.Wave1.GP011B2b_revised_corollaries_V1_measurable
      (Bridge.model (F.model k))) (A k) (hm k)

/-- Assembly of the degree-only comparisons, coverage and sign-optimizer clauses. -/
theorem T7_assembly (h6 : T6_L1) (h1 : T7_L1) (h2 : T7_L2)
    (h3 : T7_L3) (h4 : T7_L4) : T7WholeStatement := by
  refine ⟨Bridge.DegreeOnlyIdentity_proved, Bridge.DegreeOnlyBounds_proved, ?_,
    Bridge.UnboundedDegreeGap_proved, Bridge.SignWitnessFacts_proved,h2⟩
  intro F c1 c2 c3 c4 h hv hr A hm
  have hc := h1 h6 F c1 c2 c3 c4 h hv hr A hm
  exact ⟨hc,h4 h3 F c1 c2 c3 c4 h _ (maximum_measurable F hv A hm) hc,
    centered_bound F c1 c2 c3 c4 h⟩

/-- The corrected oracle and true-degree Young form are bounded PSD majorants.
Supplied degree bounds can grow because these two matrices use only true degrees. -/
theorem corrected_base_conservative (hq : WholeQuadraticLimit)
    (F : Family) (c1 c2 c3 c4 : ℝ) (h : WholeScaling F c1 c2 c3 c4) (hv : Valid F) :
    Conservative F (fun k y => V1plus (F.model k).d (F.model k).G (weighted (F.model k) y)) ∧
    Conservative F (fun k y => VYoung (F.model k).d (weighted (F.model k) y)) := by
  let MC := fun k => correctedMatrix (F.model k).d (F.model k).G
  let MY := fun k => (1 : Matrix (Fin (F.size k)) (Fin (F.size k)) ℝ)+
    Matrix.diagonal (fun i => (degree (F.model k).G i : ℝ))
  have hCP (k : ℕ) : PSD (MC k) ∧ PSD (MC k-oracleMatrix (F.model k).G) := by
    have hp := Bridge.CorrectedMatrix_proved (F.positive k) (F.model k).R
      (F.model k).G (F.model k).d (hv k) (fun _ => 0)
    exact ⟨hp.1,hp.2.1⟩
  have hYP (k : ℕ) : PSD (MY k) ∧ PSD (MY k-oracleMatrix (F.model k).G) :=
    AronowAudit.P011.CorrectedAsymptoticCompletion.young_true_psd _
  have hCN (k : ℕ) : operatorNorm (MC k) ≤ 1+2*c2 := by
    apply AronowAudit.P011.SchurSupport.operatorNorm_le_abs_row_sum _
      (hCP k).1.1 (1+2*c2) (by linarith [h.c2_pos])
    exact AronowAudit.P011.CorrectedAsymptoticCompletion.corrected_row_bound
      (F.model k).R (F.model k).G (F.model k).d (hv k) c2 (h.degrees k)
  have hYN (k : ℕ) : operatorNorm (MY k) ≤ 1+c2 := by
    apply AronowAudit.P011.SchurSupport.operatorNorm_le_abs_row_sum _
      (hYP k).1.1 (1+c2) (by linarith [h.c2_pos])
    exact AronowAudit.P011.CorrectedAsymptoticCompletion.young_row_bound
      (F.model k).G c2 (h.degrees k)
  have hC0 := psd_conservative hq F c1 c2 c3 c4 (1+2*c2) h MC hCP hCN
  have hY0 := psd_conservative hq F c1 c2 c3 c4 (1+c2) h MY hYP hYN
  constructor
  · have he (k : ℕ) (y : Fin (F.size k) → ℝ) :
        V1plus (F.model k).d (F.model k).G (weighted (F.model k) y) =
          varianceForm (MC k) (weighted (F.model k) y) :=
      (Bridge.CorrectedMatrix_proved (F.positive k) (F.model k).R
        (F.model k).G (F.model k).d (hv k) _).2.2.1
    simpa only [← he] using hC0
  · exact AronowAudit.P011.CorollaryCompletion.conservative_mono
      (Bridge.family F) _ _ hY0 (fun k y =>
        AronowAudit.P011.CorrectedAsymptoticCompletion.young_true_le
          (F.model k).R (F.model k).G (F.model k).d (hv k) (weighted (F.model k) y))

/-- Assumption 2 gives a genuine uniform bound on the real sequence meanBias,
so its real limit inferior is not a value assigned to an unbounded sequence. -/
theorem bias_bound (F : Family) (c1 c2 c3 c4 : ℝ)
    (h : WholeScaling F c1 c2 c3 c4) (k : ℕ) :
    |meanBias (F.model k)| ≤ (1+c2)*c1^2 := by
  have hL2 := AronowAudit.P011.ProbabilityCompletion.weighted_memLp
    (Bridge.model (F.model k)) c1 (h.bounded k)
  have hu (i : Fin (F.size k)) : |delta (F.model k) i| ≤ c1 :=
    AronowAudit.P011.ProbabilityCompletion.own_mean_bound
      (Bridge.model (F.model k)) c1 hL2 (h.bounded k) i
  have hd (i : Fin (F.size k)) :
      (AronowAudit.P011.degree (F.model k).G i : ℝ)+1 ≤ 1+c2 := by
    have hi : (AronowAudit.P011.degree (F.model k).G i : ℝ) ≤ c2 := h.degrees k i
    linarith
  have hq := AronowAudit.P011.MeanCompletion.quadratic_bound
    (F.model k).G c1 (1+c2) h.c1_pos.le hd (delta (F.model k)) hu
  change |quadratic (oracleMatrix (F.model k).G) (delta (F.model k))| ≤
    (F.size k : ℝ)*(1+c2)*c1^2 at hq
  have hn : 0 < (F.size k : ℝ) := by exact_mod_cast F.positive k
  unfold meanBias
  rw [abs_div,abs_of_pos hn]
  exact (div_le_iff₀ hn).mpr (by nlinarith [hq])

/-- Equal means or clique components imply the bias condition in the estimator list. -/
theorem special_bias (F : Family) (c1 c2 c3 c4 : ℝ)
    (h : WholeScaling F c1 c2 c3 c4)
    (hs : (∀ k i, expectation (F.model k) (fun y => weighted (F.model k) y i) = beta (F.model k)) ∨
      (∀ k, CliqueUnion (F.model k).G)) :
    0 ≤ Filter.liminf (fun k => meanBias (F.model k)) atTop := by
  have hp (k : ℕ) : 0 ≤ meanBias (F.model k) := by
    rcases hs with he | hc
    · have hz (i : Fin (F.size k)) : delta (F.model k) i = 0 := by
        simp only [delta,he k i,sub_self]
      simp [meanBias,quadratic,hz]
    · have hpsd : PSD (oracleMatrix (F.model k).G) :=
        (Bridge.CliqueCharacterization_proved (F.positive k) (F.model k).G).1.mpr (hc k)
      exact div_nonneg (hpsd.2 _) (Nat.cast_nonneg _)
  have hbelow : atTop.IsBoundedUnder (· ≥ ·) (fun k => meanBias (F.model k)) :=
    isBoundedUnder_of ⟨0,hp⟩
  have habove : atTop.IsBoundedUnder (· ≤ ·) (fun k => meanBias (F.model k)) :=
    isBoundedUnder_of ⟨(1+c2)*c1^2,fun k => (abs_le.mp (bias_bound F c1 c2 c3 c4 h k)).2⟩
  apply (le_liminf_iff habove.isCoboundedUnder_flip hbelow).mpr
  intro t ht
  exact Eventually.of_forall (fun k => ht.trans_le (hp k))

/-- The nonnegative branches of the corrected list are nonnegative sample by sample. -/
theorem corrected_nonnegative : WholeCorrectedNonnegative := by
  intro n hn R G d hv x A hm
  have hG := (Bridge.CorrectedMatrix_proved hn R G d hv x).2.2.2
  have hA := (Bridge.CorrectedMatrix_proved hn R A d hm.1 x).2.2.2
  have hY : 0 ≤ VYoung d x := by
    unfold VYoung
    exact div_nonneg (Finset.sum_nonneg (fun i _ => mul_nonneg
      (by positivity) (sq_nonneg _))) (sq_nonneg _)
  have hP : 0 ≤ VPositive G x := (le_max_right (V1 G x) 0).trans
    ((Bridge.PositivePartFinite_proved hn G).2.2.2.1 x)
  exact ⟨hG,hA,hY,le_min hA hY,hP⟩

/-- All corrected-list branches, their coverage, special cases and counterexamples. -/
theorem T8_assembly (h6 : T6_L1) (h7 : T7_L1) (hclt : T7_L3)
    (hwald : T7_L4) (h1 : T8_L1) : T8WholeStatement := by
  refine ⟨?_,special_bias,corrected_nonnegative,
    Bridge.CycleCounterexample_proved,Bridge.PathCounterexample_proved⟩
  intro F c1 c2 c3 c4 h V hV
  have hmeas : ∀ k, Measurable (V k) :=
    AronowAudit.P011.Wave1.GP011B2b_revised_corollaries_class_measurable
      (Bridge.family F) V hV
  have hcon : Conservative F V := by
    rcases hV with ⟨hv,hcases⟩ | rfl | ⟨hv,hr,A,hm,rfl⟩ | ⟨hv,hbias,hcases⟩
    · obtain ⟨hC,hY⟩ := corrected_base_conservative h6 F c1 c2 c3 c4 h hv
      rcases hcases with rfl | rfl | ⟨A,hm,hcases⟩
      · exact hC
      · exact hY
      · have hsel : Conservative F (fun k y => V1plus (F.model k).d
            (A k y) (weighted (F.model k) y)) :=
          AronowAudit.P011.CorollaryCompletion.conservative_mono
            (Bridge.family F) _ _ hC (fun k y => (hm k y).2 _ (hv k))
        rcases hcases with rfl | rfl
        · exact hsel
        · exact AronowAudit.P011.CorrectedAsymptoticCompletion.conservative_min
            (Bridge.family F) _ _ hsel hY
    · exact spectral_conservative h6 F c1 c2 c3 c4 h
    · exact h7 h6 F c1 c2 c3 c4 h hv hr A hm
    · have ho := h1 h6 F c1 c2 c3 c4 h hbias
      rcases hcases with rfl | ⟨A,hm,rfl⟩
      · exact ho
      · exact AronowAudit.P011.CorollaryCompletion.conservative_mono
          (Bridge.family F) _ _ ho (fun k y => (hm k y).2 _ (hv k))
  exact ⟨hcon,hwald hclt F c1 c2 c3 c4 h V hmeas hcon⟩

end
end SAP.P011a.WH.W1
