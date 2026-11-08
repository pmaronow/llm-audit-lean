import SAP.P029b.Defs.WholeW1
import SAP.P029b.Bridge

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P029b.WH.W1

universe u v

open scoped BigOperators Classical Topology
open MeasureTheory ProbabilityTheory Filter Set

noncomputable section

/-- Closed one-cell binomial optimization, including zero and all successes.
For 0<k<n use the log tangent inequality at k/n, with strictness unless equal.
Treat k=0 and k=n by strict monotonicity of powers on [0,1]; at the remaining
endpoints the likelihood is zero. `weighted_cell_unique_max` supplies the
interior log certificate. Expected size: 100–180 lines. -/
def T14_L1 : Prop :=
  ∀ n k : ℕ, 0 < n → k ≤ n →
    0 < BinomialKernelW1 n k ((k : ℝ)/n) ∧
    ∀ p ∈ Icc (0 : ℝ) 1,
      BinomialKernelW1 n k p ≤ BinomialKernelW1 n k ((k : ℝ)/n) ∧
      (BinomialKernelW1 n k p = BinomialKernelW1 n k ((k : ℝ)/n) ↔ p = (k : ℝ)/n)

/-- Pooled optimization when the control rate exceeds the treated rate.
The pooled t lies strictly between 0 and 1. Compare log likelihoods using
`Real.log_le_sub_one_of_pos`; their difference is bounded by
(k1-n1*t)*(p-q)/(t*(1-t)) ≤ 0 on q≤p. Strict log tangency forces p=q=t.
Handle boundary competitors with zero success/failure factors separately;
do not assume q>0 or p<1 for the competitor. Expected size: 180–300 lines. -/
def T14_L2 : Prop :=
  ∀ n1 n0 k1 k0 : ℕ, 0 < n1 → 0 < n0 → k1 ≤ n1 → k0 ≤ n0 →
    (k1 : ℝ)/n1 < (k0 : ℝ)/n0 →
    let t := ((k1 : ℝ)+k0)/(n1+n0)
    (t,t) ∈ ReceiptTriangleW1 ∧
    ∀ v ∈ ReceiptTriangleW1,
      SaturatedLikelihoodW1 n1 n0 k1 k0 v ≤ SaturatedLikelihoodW1 n1 n0 k1 k0 (t,t) ∧
      (SaturatedLikelihoodW1 n1 n0 k1 k0 v = SaturatedLikelihoodW1 n1 n0 k1 k0 (t,t) ↔
        v = (t,t))

/-- Lift the existing per-stratum binomial tail probabilities to any common
probability space with these marginals. Sum over the finite count fibers,
then use the finite union bound and a finite sum of sequences tending to zero.
No cross-stratum independence is needed; the empty family has zero error event.
Expected size: 80–150 lines. -/
def T14_L3 : Prop := JointStratumConsistencyW1.{u,v}

/-- Finite generalized-inverse quantile certificate. Sort the vector and take
the ceil((n+1)*level)-th order statistic (one-based). Its CDF superlevel set
is the closed ray from that statistic, so `csInf_Ici` identifies the inverse.
Strictly fewer than ceil((n+1)*level) entries lie below it, even with ties,
giving changed fraction < level. Includes level one and singleton vectors.
Expected size: 120–220 lines. -/
def T16_L1 : Prop :=
  ∀ {n : ℕ} (s : Fin (n+1) → ℝ) (level : ℝ), level ∈ Ioc (0 : ℝ) 1 →
    (∃ c, InverseEmpiricalQuantileW1 s level c) ∧
    ∀ c, InverseEmpiricalQuantileW1 s level c →
      (∃ i, c = s i) ∧ (belowCount s c : ℝ)/(n+1) < level

/-- On a finite profile space the normalized cell formulas are conditional
expectation versions, including arbitrary/null cells. Prove the defining
set-integral equalities on unions of profile fibers and apply conditional-
expectation uniqueness. Measurability is automatic on a finite space with
measurable singletons. The product c*m is handled without dividing on null
or zero-complier cells. Expected size: 120–220 lines. -/
def T16_L2 : Prop :=
  ∀ {Ω : Type u} {X : Type v} [MeasurableSpace Ω] [Fintype X]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (U : Ω → PotentialUnit X)
    (Z : Ω → Bool), IVAssumptions μ U Z →
    ScoreVersions μ U (scoreAt μ U) (complierAt μ U)

/-- Transport the finite-profile versions and support overlap across identical
joint draw laws, constructing the existing ICSWConditions from the raw printed
assumptions. Equality of laws gives equality of profile and complier masses and
integrals of the complier effect, hence the canonical scores and means agree.
Use `wcl_ae_positive_cell` to discard null profiles in each draw. The other
fields are copied directly; no extra independence of fitted scores is needed.
Expected size: 100–180 lines. -/
def T16_L3 : Prop :=
  ∀ {Ω : Type u} {X : Type v} [MeasurableSpace Ω] [Fintype X]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (U : ℕ → Ω → PotentialUnit X)
    (Z : ℕ → Ω → Bool) (s : ℕ → ℕ → Ω → ℝ),
    FiniteSampleConditionsW1 μ U Z s →
    (∀ i, ScoreVersions μ (U i) (scoreAt μ (U i)) (complierAt μ (U i))) →
    ICSWConditions μ U Z (scoreAt μ (U 0)) (complierAt μ (U 0)) s

/-- All local profile identities, without a positive-AC guard. Use the Boolean
type partition almost everywhere to add the conditional masses. Randomization
factors each profile/type/assignment intersection. Dividing by the positive
profile and arm masses proves the assignment-conditioned formula and averaging
over the two arms proves the marginal receipt formula. A null global D0 event
has null intersection with every profile. Expected size: 150–250 lines. -/
def T18_L1 : Prop :=
  ∀ {Ω : Type u} {X : Type v} [MeasurableSpace Ω] [MeasurableSpace X]
    [MeasurableSingletonClass X] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (U : Ω → PotentialUnit X) (Z : Ω → Bool), ReceiptConditionsW1 μ U Z →
    ∀ x, 0 < mP μ {ω | (U ω).x = x} → ReceiptProfileConclusionW1 μ U Z x

/-- Weighted outcome-arm difference with actual L1 hypotheses in place of a
uniform weight bound. Apply `GP029B3b_appendix_observed_mean` separately to
b(X), b(X)*Y(1), and b(X)*Y(0). The unit ITT identity, outside the null defier
event, gives integrability and the integral of b(X)*C*tau from the difference
of the two weighted latent outcomes. Expected size: 80–140 lines. -/
def T18_L2 : Prop :=
  ∀ {Ω : Type u} {X : Type v} [MeasurableSpace Ω] [MeasurableSpace X]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (U : Ω → PotentialUnit X)
    (Z : Ω → Bool) (b : X → ℝ), IVAssumptions μ U Z → Measurable b →
    Integrable (fun ω => b (U ω).x) μ →
    (∀ z, Integrable (fun ω => b (U ω).x*(U ω).outcome z) μ) →
    (∫ ω, b (U ω).x ∂μ) ≠ 0 →
    Integrable (fun ω => b (U ω).x*(if (U ω).complier then (U ω).tau else 0)) μ ∧
    (mArm μ Z (fun ω => b (U ω).x) (fun ω => (U ω).outcome (Z ω)) true -
      mArm μ Z (fun ω => b (U ω).x) (fun ω => (U ω).outcome (Z ω)) false) =
      (∫ ω, b (U ω).x*(if (U ω).complier then (U ω).tau else 0) ∂μ) /
        (∫ ω, b (U ω).x ∂μ)

/-- Conditional-expectation pull-out for the possibly unbounded inverse score,
followed by covariate pushforward and cancellation. Use the actual integrability
of w*C*tau and of C*tau in the unbounded pull-out theorem. Its conditional
expectation equals w*c*m=m almost everywhere, proving integrability of m as
well as the integral identities. No lower bound epsilon is available or needed.
Expected size: 60–120 lines. -/
def T18_L3 : Prop :=
  ∀ {Ω : Type u} {X : Type v} [MeasurableSpace Ω] [MeasurableSpace X]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (U : Ω → PotentialUnit X)
    (Z : Ω → Bool) (c m : X → ℝ), IVAssumptions μ U Z → ScoreVersions μ U c m →
    (∀ᵐ ω ∂μ, 0 < c (U ω).x) →
    Integrable (fun ω => (1/c (U ω).x)*
      (if (U ω).complier then (U ω).tau else 0)) μ →
    Integrable m (Measure.map (fun ω => (U ω).x) μ) ∧
    (∫ ω, (1/c (U ω).x)*(if (U ω).complier then (U ω).tau else 0) ∂μ) =
      (∫ x, (c x*m x)/c x ∂Measure.map (fun ω => (U ω).x) μ) ∧
    (∫ x, (c x*m x)/c x ∂Measure.map (fun ω => (U ω).x) μ) =
      ∫ x, m x ∂Measure.map (fun ω => (U ω).x) μ

/-- The power quantile level is well-defined also for the singleton sample. -/
theorem powerLevelW1 (α : ℝ) (hα : 0 < α) (n : ℕ) :
    ((n+1 : ℕ) : ℝ)^(-α) ∈ Ioc (0 : ℝ) 1 := by
  exact ⟨Real.rpow_pos_of_pos (by positivity) _,
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_cast; omega) (by linarith)⟩

/-- Constant vectors give a closed-ray CDF superlevel set. -/
theorem constantInverseW1 {n : ℕ} (a level : ℝ) (hlevel : level ∈ Ioc (0 : ℝ) 1) :
    InverseEmpiricalQuantileW1 (fun _ : Fin (n+1) => a) level a ∧
    ∀ c, InverseEmpiricalQuantileW1 (fun _ : Fin (n+1) => a) level c → c = a := by
  have hset : {t | level ≤ EmpiricalCDFW1 (fun _ : Fin (n+1) => a) t} = Ici a := by
    ext t
    by_cases h : a ≤ t
    · simp [EmpiricalCDFW1, h, hlevel.2, show (n : ℝ)+1 ≠ 0 by positivity]
    · simp [EmpiricalCDFW1, h, not_le.mpr hlevel.1]
  have he : InverseEmpiricalQuantileW1 (fun _ : Fin (n+1) => a) level a := by
    unfold InverseEmpiricalQuantileW1
    rw [hset]
    exact ⟨nonempty_Ici, bddBelow_Ici, (csInf_Ici (a := a)).symm⟩
  exact ⟨he, fun c hc => hc.2.2.trans he.2.2.symm⟩

/-- Assembly of the global ML characterization and the already proved bias bounds. -/
theorem T14_assembly (h1 : T14_L1) (h2 : T14_L2) (h3 : T14_L3.{u,v}) :
    T14WholeStatement.{u,v} := by
  refine ⟨?_, ?_, ?_, ?_, h3, ?_⟩
  · intro n1 n0 k1 k0 hn1 hn0 hk1 hk0
    have hr1 : (k1 : ℝ)/n1 ∈ Icc (0 : ℝ) 1 :=
      ⟨by positivity, (div_le_one (by positivity)).mpr (by exact_mod_cast hk1)⟩
    have hr0 : (k0 : ℝ)/n0 ∈ Icc (0 : ℝ) 1 :=
      ⟨by positivity, (div_le_one (by positivity)).mpr (by exact_mod_cast hk0)⟩
    by_cases ho : (k0 : ℝ)/n0 ≤ (k1 : ℝ)/n1
    · dsimp [MLConclusionW1, SaturatedFitW1]
      simp only [ho, ite_true]
      refine ⟨⟨hr0.1, ho, hr1.2⟩, ?_, ?_⟩
      · intro v hv
        have ha := h1 n1 k1 hn1 hk1
        have hb := h1 n0 k0 hn0 hk0
        have hv1 : v.1 ∈ Icc (0 : ℝ) 1 := ⟨hv.1.trans hv.2.1, hv.2.2⟩
        have hv0 : v.2 ∈ Icc (0 : ℝ) 1 := ⟨hv.1, hv.2.1.trans hv.2.2⟩
        have hna : 0 ≤ BinomialKernelW1 n1 k1 v.1 := by
          exact mul_nonneg (pow_nonneg hv1.1 _) (pow_nonneg (sub_nonneg.mpr hv1.2) _)
        have hnb : 0 ≤ BinomialKernelW1 n0 k0 v.2 := by
          exact mul_nonneg (pow_nonneg hv0.1 _) (pow_nonneg (sub_nonneg.mpr hv0.2) _)
        have hba := (ha.2 v.1 hv1).1
        have hbb := (hb.2 v.2 hv0).1
        refine ⟨mul_le_mul hba hbb hnb ha.1.le, ?_⟩
        constructor
        · intro he
          change BinomialKernelW1 n1 k1 v.1 * BinomialKernelW1 n0 k0 v.2 =
            BinomialKernelW1 n1 k1 ((k1 : ℝ)/n1) *
              BinomialKernelW1 n0 k0 ((k0 : ℝ)/n0) at he
          have hea : BinomialKernelW1 n1 k1 v.1 = BinomialKernelW1 n1 k1 ((k1 : ℝ)/n1) := by
            nlinarith [mul_le_mul_of_nonneg_left hbb hna]
          have heb : BinomialKernelW1 n0 k0 v.2 = BinomialKernelW1 n0 k0 ((k0 : ℝ)/n0) := by
            nlinarith [mul_le_mul_of_nonneg_right hba hnb]
          exact Prod.ext ((ha.2 v.1 hv1).2.mp hea) ((hb.2 v.2 hv0).2.mp heb)
        · rintro rfl; rfl
      · exact (max_eq_left (sub_nonneg.mpr ho)).symm
    · have hh := h2 n1 n0 k1 k0 hn1 hn0 hk1 hk0 (lt_of_not_ge ho)
      dsimp [MLConclusionW1, SaturatedFitW1]
      simp only [ho, ite_false]
      exact ⟨hh.1, hh.2, by simp [positiveScore, max_eq_right (sub_nonpos.mpr (le_of_not_ge ho))]⟩
  · intro p q hq hqp hp
    exact AronowAudit.P029.nested_receipt_parameters p q hq hqp hp
  · refine ⟨@Bridge.saturated_binomial_bias_bound_proof, ?_,
      @Bridge.saturated_score_consistency_proof, @Bridge.one_sided_saturated_unbiasedness_proof⟩
    intro n1 n0 _ _ p1 p0 _ horder _ k
    exact Bridge.positive_part_error_bound _ _ (sub_nonneg.mpr horder)
  · intro n1 n0 _ _ p1 p0 _ _ _
    constructor
    · let k : Fin (n1+1) × Fin (n0+1) := (⟨0, Nat.zero_lt_succ _⟩, ⟨n0, Nat.lt_succ_self _⟩)
      have hevent : ∀ j : Fin (n1+1) × Fin (n0+1),
          (j.1.val = 0 ∧ j.2.val = n0) ↔ j = k := by
        intro j
        constructor
        · rintro ⟨h, h'⟩; exact Prod.ext (Fin.ext h) (Fin.ext h')
        · rintro rfl; exact ⟨rfl, rfl⟩
      unfold fP
      simp only [hevent, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
      simp [binomialArmLaw, binomialMass, k]
    · intro hp0 hp1
      exact mul_pos (pow_pos (sub_pos.mpr hp1) _) (pow_pos hp0 _)
  · intro n hn p _
    have hcount : (∑ k : Fin (n+1), (k.val : ℝ)*binomialMass n p k) = (n : ℝ)*p := by
      have h := congrArg (fun P : Polynomial ℝ => Polynomial.eval p P)
        (bernsteinPolynomial.sum_smul ℝ n)
      simp only [nsmul_eq_mul, bernsteinPolynomial, Polynomial.eval_finsetSum,
        Polynomial.eval_mul, Polynomial.eval_natCast, Polynomial.eval_pow,
        Polynomial.eval_X, Polynomial.eval_sub, Polynomial.eval_one] at h
      simpa only [Finset.sum_range, binomialMass] using h
    calc
      _ = (∑ k : Fin (n+1), (k.val : ℝ)*binomialMass n p k)/n := by
        unfold fE
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro k _; ring
      _ = p := by rw [hcount]; exact mul_div_cancel_left₀ p (by positivity)

/-- All additional constant-law calculations are short and proved here. -/
theorem T15_assembly : T15WholeStatement := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨Bridge.constant_score_counterexample_law, ?_, ?_, ?_⟩
    · obtain ⟨_, _, _, _, _, _, hc, _, _, _⟩ := Bridge.winsorization_cutoff_counterexample
      exact ⟨hc, Bridge.cutoff_not_zero.1⟩
    · intro n level hlevel
      exact Bridge.constant_quantile (n := n) (1/2) level hlevel
    · exact ⟨Bridge.cutoff_not_zero.2.2, by norm_num⟩
  · norm_num [fCE, fE, fP, sixMass, randomized, typeMass, constantUnit,
      PotentialUnit.receipt, bit, Fintype.sum_prod_type, Fintype.sum_bool, Fin.sum_univ_succ]
  · intro i; simp [constantUnit, PotentialUnit.tau]
  · intro n level hlevel
    exact constantInverseW1 (n := n) (1/2) level hlevel
  · intro α hα n
    have hl := powerLevelW1 α hα n
    exact ⟨(Bridge.constant_quantile (n := n) (1/2) _ ⟨hl.1.le, hl.2⟩).1,
      (constantInverseW1 (n := n) (1/2) _ hl).1, by norm_num⟩
  · intro n Y D Z
    exact ⟨fun _ => by norm_num, by norm_num⟩

/-- Floor export, constant cutoffs and finite bounds are glue. The existing
probability-limit theorem applies after the two finite-profile adapter leaves. -/
theorem T16_assembly (h1 : T16_L1) (h2 : T16_L2.{u,v}) (h3 : T16_L3.{u,v}) :
    T16WholeStatement.{u,v} := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n s level c b hl hq hb
    have hc := Bridge.quantile_count_and_lower_bound s level c b hl hq hb
    have hh : 0 ≤ 1+(n : ℝ)*level :=
      add_nonneg zero_le_one (mul_nonneg (Nat.cast_nonneg _) hl.1.le)
    exact ⟨(Nat.le_floor_iff hh).mpr hc.1, Nat.floor_le hh, hc.2⟩
  · intro n s level hl
    refine ⟨(h1 s level hl).1, ?_⟩
    intro c b hq hb
    obtain ⟨⟨i, hi⟩, hf⟩ := (h1 s level hl).2 c hq
    have hn : (0 : ℝ) < n+1 := by positivity
    have hc : (belowCount s c : ℝ) < level*(n+1) := (div_lt_iff₀ hn).mp hf
    have hh : (belowCount s c : ℝ) ≤ 1+n*level := by nlinarith [hl.2]
    have hh0 : 0 ≤ 1+(n : ℝ)*level := by
      exact add_nonneg zero_le_one (mul_nonneg (Nat.cast_nonneg _) hl.1.le)
    refine ⟨(Nat.le_floor_iff hh0).mpr hh, ?_, ?_⟩
    · exact hf.le.trans (le_add_of_nonneg_right (by positivity))
    · rw [hi]; exact hb i
  · intro s c α hα hq
    refine squeeze_zero' (Eventually.of_forall (fun n => by positivity)) ?_
      (AronowAudit.P029.Wave1.wcl_quantile_level_bound α hα)
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have hl : (((n+1 : ℕ) : ℝ)^(-α)) ∈ Ioo (0 : ℝ) 1 :=
      ⟨(powerLevelW1 α hα n).1, Real.rpow_lt_one_of_one_lt_of_neg
        (by exact_mod_cast (show 1 < n+1 by omega)) (neg_lt_zero.mpr hα)⟩
    rcases hq n with ht | hi
    · let b : ℝ := Finset.univ.inf' Finset.univ_nonempty (s n)
      exact (Bridge.quantile_count_and_lower_bound (s n) _ (c n) b hl ht
        (fun i => Finset.inf'_le _ (Finset.mem_univ i))).2.1
    · exact ((h1 (s n) _ ⟨hl.1, hl.2.le⟩).2 _ hi).2.le.trans
        (le_add_of_nonneg_right (by positivity))
  · intro n s V level c b K hl hq hb hs hK hV
    refine ⟨fun i => Bridge.weight_change_bound (s i) c b hb (hs i).1, ?_⟩
    exact (Bridge.bounded_weighted_mean_change s V c b K hb (fun i => (hs i).1) hK hV).trans
      (mul_le_mul_of_nonneg_left
        (Bridge.quantile_count_and_lower_bound s level c b hl hq (fun i => (hs i).1)).2.1
        (div_nonneg hK hb.le))
  · refine ⟨?_, ?_, Bridge.cutoff_not_zero.1⟩
    · intro n level hl; exact Bridge.constant_quantile (n := n) (1/2) level hl
    · intro α hα n
      have hl := powerLevelW1 α hα n
      exact (Bridge.constant_quantile (n := n) (1/2) _ ⟨hl.1.le, hl.2⟩).1
  · intro Ω X _ _ _ _ μ _ U Z s cutoff h α hα hc hq
    have hadapt := h3 μ U Z s h (fun i => h2 μ (U i) (Z i) (h.1 i))
    exact Bridge.winsorization_corrected_limit_proof μ U Z _ _ s cutoff hadapt α hα
      h.2.2.2.2.2.1 hc hq

/-- Boolean case analysis proves the omitted additive-factor formulas directly. -/
theorem T17_assembly : T17WholeStatement.{u,v} := by
  refine ⟨?_, ?_⟩
  · refine ⟨?_, ?_, Bridge.printed_one_sided_factor_countercheck⟩
    · intro π z d _; exact Bridge.one_sided_unit_likelihood π z d
    · intro I Θ _ π Z D _ hside
      have heq := fun θ => Bridge.one_sided_likelihood_reduction (π θ) Z D hside
      refine ⟨heq, ?_⟩
      intro θ; simp only [heq]
  · intro π z d hπ
    cases d <;> cases z <;> constructor <;> norm_num [bit] <;> linarith [hπ.1, hπ.2]

/-- Combine local probability identities, unbounded L1 weighted-mean reduction,
conditional pull-out, and the elementary single-hat display expansion. -/
theorem T18_assembly (h1 : T18_L1.{u,v}) (h2 : T18_L2.{u,v}) (h3 : T18_L3.{u,v}) :
    T18WholeStatement.{u,v} := by
  refine ⟨?_, @Bridge.nested_probability_range, @Bridge.corrected_equation_nine_integrand,
    ?_, ?_⟩
  · intro Ω X _ _ _ μ _ U Z h
    rcases h with ⟨hx, hd0, hd1, hz, hmon, hind, he0, he1⟩
    refine ⟨?_, ?_⟩
    · filter_upwards [measure_eq_zero_iff_ae_notMem.mp hmon] with ω hω
      exact Bridge.compliance_type_partition (U ω) hω
    · intro x hxp
      have hp := h1 μ U Z ⟨hx, hd0, hd1, hz, hmon, hind, he0, he1⟩ x hxp
      refine ⟨hp, ?_, ?_⟩
      · intro hAC
        have hn := Bridge.corrected_nested_receipt_model_proof μ U Z hx hd0 hd1 hz
          hmon hind he0 he1 x hxp hAC
        exact ⟨hn.1, hn.2.1, fun z => (hn.2.2 z).2⟩
      · intro hzero hc he
        have ha0 := hp.2.2.2 hzero
        refine ⟨?_, ?_⟩
        · rw [hp.2.2.1, ha0, hc, he]; norm_num
        · intro z; rw [hc, ha0]; cases z <;> norm_num [bit]
  · intro Ω X _ _ μ _ U Z c m hiv hv hpos hwi hYi hwne
    have hw := h2 μ U Z (fun x => 1/c x) hiv (measurable_const.div hv.1) hwi hYi hwne
    have hi := h3 μ U Z c m hiv hv hpos hw.1
    refine ⟨hi.1, ?_, ?_⟩
    · rw [hw.2, hi.2.1]; ring
    · rw [hi.2.2]
  · intro n s Y D Z _ _
    have harm (V : Fin n → ℝ) (z : Bool) :
        sampleArm (fun i => 1/s i) V Z z =
          (∑ i, (1/s i)*(if z then bit (Z i) else 1-bit (Z i))*V i) /
          (∑ i, (1/s i)*(if z then bit (Z i) else 1-bit (Z i))) := by
      unfold sampleArm
      congr 1 <;> apply Finset.sum_congr rfl <;> intro i _ <;>
        cases z <;> cases Z i <;> simp [bit]
    simp only [sampleWald, harm, SingleHatEstimatorW1,
      Bool.false_eq_true, ite_true, ite_false]

end
end SAP.P029b.WH.W1
