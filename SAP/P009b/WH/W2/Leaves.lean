import SAP.P009b.Defs.WholeW2
import SAP.P009b.Bridge
import AronowAudit.P009.P009_CommonCompletion
import AronowAudit.P009.P009_OutcomeCompletion

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators Topology
open Filter

namespace SAP.P009b.WH.W2
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Upgrade standing regularity in the fair one-source model to observed order four.
First use BernoulliCompletion.mean_abs_of_moment to bound E|Y_i| by k. On the
control arm Y_i=c_i, and oneSourceFormulas_one_numerator gives its contribution
|c_i|/2, so |c_i| <= 2k. Every outcome, including every updated potential, is then
bounded by 2k+2. The fair marginal is 1/2; use mean_le_constant for orders 4 and 1.
No source-baseline condition and no independence beyond the stated fair law are needed.
Expected proof: 80–150 lines. -/
def T22_L1 : Prop :=
  ∀ {n : ℕ} (_hn : 0 < n) (E : Experiment n) (k q s : ℝ), Regular E k q s →
    ∀ (b : ℕ) (c : Fin n → ℝ),
    E.design = fairLaw n → E.outcome = oneSourceOutcome b c →
    Regular E (2 * k + 2) 4 1

/-- A uniform floor-error estimate for the corrected centre, valid in every regime.
For N>0 and b=floor(a)>=1, put m=b-1, so 0<=m and 1<=a-m<2.
Compare (N-m²)/(N+m(m+1)) first with (N-m²)/(N+m²), then with
(N-a²)/(N+a²). The errors are O(1/sqrt(N)) uniformly in a: use
2*m*sqrt(N)<=N+m², the floor error <2, and positive denominators. The
first error is at most 1/(2*sqrt(N)); the second is at most 4/sqrt(N).
For the second bound expand a²-m²=(a-m)(a+m), and apply
2*x*sqrt(N)<=N+x² separately at x=a and x=m. An overall bound 5/sqrt(N)
therefore suffices. Squeeze using N -> infinity and Real.tendsto_sqrt_atTop. This proves the
limit without requiring bounded a/sqrt(N), so it also covers large a.
Expected proof: 120–220 lines. -/
def T22_L2 : Prop :=
  ∀ (N : ℕ → ℕ), (∀ t, 0 < N t) → Tendsto N atTop atTop →
    ∀ (a : ℕ → ℝ), (∀ t, 1 ≤ ⌊a t⌋₊ ∧ ⌊a t⌋₊ ≤ N t) →
    Tendsto (fun t => w2CorrectedCenter (N t : ℝ) ⌊a t⌋₊ -
      w2RatioCenter (a t / Real.sqrt (N t : ℝ))) atTop (nhds 0)

/-- Every positive comparable-order ratio is attainable with a valid floor cutoff.
For ell>0 choose a natural M with M>=1, M>=ell and ell*M>=1. Take
N_t=(t+M)² and a_t=ell*(t+M). Then 1<=floor(a_t)<=N_t and the ratio
a_t/sqrt(N_t) is exactly ell. Prove growth by elementary natural-number
inequalities and simplify sqrt of a nonnegative square.
Expected proof: 60–120 lines; the assembly supplies the actual experiments. -/
def T22_L3 : Prop :=
  ∀ ell : ℝ, 0 < ell → ∃ (N : ℕ → ℕ) (a : ℕ → ℝ),
    (∀ t, 0 < N t) ∧ Tendsto N atTop atTop ∧
    (∀ t, 1 ≤ ⌊a t⌋₊ ∧ ⌊a t⌋₊ ≤ N t) ∧
    Tendsto (fun t => a t / Real.sqrt (N t : ℝ)) atTop (nhds ell)

/-- Standing regularity bounds every full-cube no-interference outcome, even under
dependent assignment. By SparseCompletion.noI_interferes the incoming-mask event
in OutcomeCompletion.moment_atom_lower is just the own-arm event. Its probability
is at least 1/k by BernoulliCompletion.regular_marginal_bounds, which has no
Bernoulli-design premise. Thus |y_i(z)|^q <= k^(q+1). Take the positive q-th
root and use q>=2 and regular_k_ge_two to compare exponents 1+1/q<=3/2.
Do not use incoming_outcome_bound: that donor requires an independent design.
Expected proof: 70–140 lines. -/
def T26_L1 : Prop :=
  ∀ {n : ℕ} (_hn : 0 < n) (E : Experiment n) (k q s : ℝ),
    Regular E k q s → NoInterference E →
    (∀ i z, |E.outcome i z| ≤ Real.rpow k (1 + 1 / q)) ∧
      Real.rpow k (1 + 1 / q) ≤ Real.rpow k (3 / 2)

private theorem size_pos (S : Study) (t : ℕ) : 0 < size S t := by
  dsimp [size]
  exact_mod_cast S.positive t

private theorem size_grows (S : Study) : Tendsto (size S) atTop atTop := by
  exact tendsto_natCast_atTop_iff.mpr S.grows

/-- Transfer convergence in probability by a deterministic vanishing shift. -/
private theorem probability_shift (S : Study)
    (X : (t : ℕ) → Assignment (S.N t) → ℝ) (c e : ℕ → ℝ)
    (hX : InProbability S (fun t z => X t z - c t))
    (hce : Tendsto (fun t => c t - e t) atTop (nhds 0)) :
    InProbability S (fun t z => X t z - e t) := by
  intro ε hε
  have habs : Tendsto (fun t => |c t - e t|) atTop (nhds 0) := by
    simpa using hce.abs
  have hevent : ∀ᶠ t in atTop, |c t - e t| < ε / 2 :=
    (tendsto_order.1 habs).2 _ (by linarith)
  apply squeeze_zero'
    (Eventually.of_forall (fun t =>
      AronowAudit.P009.probability_nonnegative (Bridge.toLaw (S.experiment t).design) _))
    _ (hX (ε / 2) (by linarith))
  filter_upwards [hevent] with t ht
  apply AronowAudit.P009.finite_probability_mono (Bridge.toLaw (S.experiment t).design)
  intro z hz
  have htri : |X t z - e t| ≤ |X t z - c t| + |c t - e t| := by
    calc
      _ = |(X t z - c t) + (c t - e t)| := by congr 1; ring
      _ ≤ _ := abs_add_le _ _
  linarith

private theorem printed_correction_tends_zero (S : Study) (b : ℕ → ℕ)
    (hb : ∀ t, 1 ≤ b t ∧ b t ≤ S.N t) :
    Tendsto (fun t => w2CorrectedCenter (size S t) (b t) -
      w2PrintedCenter (size S t) (b t)) atTop (nhds 0) := by
  have hbound (t : ℕ) := AronowAudit.P009.Wave1.oneSourceFormulas_correction_bound
    (size S t) ((b t : ℝ) - 1) (size_pos S t)
      (by
        have h : (1 : ℝ) ≤ b t := by exact_mod_cast (hb t).1
        linarith)
  have heq (t : ℕ) : w2CorrectedCenter (size S t) (b t) -
      w2PrintedCenter (size S t) (b t) =
      2 * ((b t : ℝ) - 1) / (size S t + ((b t : ℝ) - 1 + 1) * ((b t : ℝ) - 1)) := by
    dsimp [w2CorrectedCenter, w2PrintedCenter]
    ring
  simp_rw [heq]
  exact squeeze_zero (fun t => (hbound t).1) (fun t => (hbound t).2)
    ((Real.tendsto_sqrt_atTop.comp (size_grows S)).const_div_atTop 1)

private theorem ratio_center_tendsto (r : ℕ → ℝ) (ell : ℝ)
    (hr : Tendsto r atTop (nhds ell)) :
    Tendsto (fun t => w2RatioCenter (r t)) atTop (nhds (w2RatioCenter ell)) := by
  exact (tendsto_const_nhds.sub (hr.pow 2)).div
    (tendsto_const_nhds.add (hr.pow 2)) (by positivity)

private theorem large_ratio_center_tendsto (S : Study) (a : ℕ → ℝ)
    (ha : ∀ t, 1 ≤ ⌊a t⌋₊)
    (hsmall : Tendsto (fun t => size S t / (a t) ^ 2) atTop (nhds 0)) :
    Tendsto (fun t => w2RatioCenter (a t / Real.sqrt (size S t)))
      atTop (nhds (-1)) := by
  have heq (t : ℕ) : w2RatioCenter (a t / Real.sqrt (size S t)) =
      (size S t / (a t) ^ 2 - 1) / (size S t / (a t) ^ 2 + 1) := by
    have ha0 : 0 < a t := lt_of_lt_of_le zero_lt_one (Nat.floor_pos.mp (ha t))
    have hnpos := size_pos S t
    dsimp [w2RatioCenter]
    rw [div_pow, Real.sq_sqrt (size_pos S t).le]
    have hd : (a t) ^ 2 + size S t ≠ 0 := by positivity
    have hd' : 1 + (a t) ^ 2 / size S t ≠ 0 := by positivity
    field_simp [ha0.ne', (size_pos S t).ne', hd, hd']
  simp_rw [heq]
  convert (hsmall.sub tendsto_const_nhds).div (hsmall.add tendsto_const_nhds)
    (by norm_num : (0 : ℝ) + 1 ≠ 0) using 1; norm_num

/-- Assembly of the whole one-source claim. Only the model regularity upgrade,
uniform floor estimate, and attainable-ratio construction remain as leaves. -/
theorem T22_assembly (h1 : T22_L1) (h2 : T22_L2) (h3 : T22_L3) :
    T22WholeStatement := by
  have hfinite : T22FiniteStatement := Bridge.T22Finite_transport
    (@AronowAudit.P009.Wave1.corrected_one_source_formulas_proof)
  refine ⟨hfinite, ?_, ?_, ?_, ?_, ?_⟩
  · intro n b hn hb
    ring
  · intro n hn b hb c
    constructor
    · intro i j hij u v
      exact ⟨AronowAudit.P009.Wave1.oneSourceFormulas_two_prob n i j hij u v,
        AronowAudit.P009.Wave1.oneSourceFormulas_ccov hn b c i j hij u v⟩
    · intro hc
      have hB1 := (hfinite hn b hb c).2.2.2.1
      rw [hc] at hB1
      convert hB1 using 1; ring
  · intro S k q s hReg a c hModel
    rcases hModel with ⟨hb, hsource, hlaw, houtcome⟩
    let C := fun t => w2CorrectedCenter (size S t) ⌊a t⌋₊
    let P := fun t => w2PrintedCenter (size S t) ⌊a t⌋₊
    let r := fun t => a t / Real.sqrt (size S t)
    have hReg4 : RegularSequence S (2 * k + 2) 4 1 := fun t =>
      h1 (S.positive t) (S.experiment t) k q s (hReg t) ⌊a t⌋₊ (c t)
        (hlaw t) (houtcome t)
    have hC : InProbability S (fun t z => w2NormalizedGap S t z - C t) :=
      Bridge.T22Limit_transport (@AronowAudit.P009.Wave1.corrected_one_source_limit_proof)
        S (2 * k + 2) 4 1 hReg4 (by norm_num) (fun t => ⌊a t⌋₊) hb c
          hsource hlaw houtcome
    have hCP : Tendsto (fun t => C t - P t) atTop (nhds 0) :=
      printed_correction_tends_zero S _ hb
    have hCF : Tendsto (fun t => C t - w2RatioCenter (r t)) atTop (nhds 0) :=
      h2 S.N S.positive S.grows a hb
    have finish (L : ℝ)
        (hF : Tendsto (fun t => w2RatioCenter (r t)) atTop (nhds L)) :
        Tendsto C atTop (nhds L) ∧ Tendsto P atTop (nhds L) ∧
          InProbability S (fun t z => w2NormalizedGap S t z - L) := by
      have hCL : Tendsto C atTop (nhds L) := by
        simpa only [sub_add_cancel, zero_add] using hCF.add hF
      have hPL : Tendsto P atTop (nhds L) := by
        have h := hCL.sub hCP
        simp only [sub_zero] at h
        convert h using 1
        ext t
        ring
      refine ⟨hCL, hPL, probability_shift S (w2NormalizedGap S) C (fun _ => L) hC ?_⟩
      simpa only [sub_self] using hCL.sub
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => L) atTop (nhds L))
    refine ⟨hC, probability_shift S (w2NormalizedGap S) C P hC hCP, ?_, ?_, ?_, ?_⟩
    · intro hr
      simpa [w2RatioCenter] using finish (w2RatioCenter 0) (ratio_center_tendsto r 0 hr)
    · intro hlarge
      exact finish (-1) (large_ratio_center_tendsto S a (fun t => (hb t).1) hlarge)
    · intro ell hell hr
      exact finish (w2RatioCenter ell) (ratio_center_tendsto r ell hr)
    · intro hcomparable
      exact probability_shift S (w2NormalizedGap S) C (fun t => w2RatioCenter (r t)) hC hCF
  · intro ell hell
    obtain ⟨N, a, hN, hgrow, hb, hratio⟩ := h3 ell hell
    let c : (t : ℕ) → Fin (N t) → ℝ := fun _ _ => -1 / 4
    let S : Study := ⟨N, hN, hgrow,
      fun t => fairExperiment (N t) (oneSourceOutcome ⌊a t⌋₊ (c t))⟩
    refine ⟨S, a, c, ⟨hb, by intro t; rfl, by intro t; rfl, by intro t; rfl⟩, ?_, hratio⟩
    intro t
    apply AronowAudit.P009.SparseCompletion.fair_regular_bounded
    intro i z
    dsimp [oneSourceOutcome, c]
    split_ifs
    all_goals cases z i <;> simp only [bit, Bool.false_eq_true, ite_false, ite_true]
    all_goals try split_ifs
    all_goals norm_num
  · intro ell hell
    have hd : 0 < 1 + ell ^ 2 := by positivity
    constructor
    · rw [w2RatioCenter, div_pos_iff]
      constructor
      · rintro (⟨h, _⟩ | ⟨_, h⟩)
        · nlinarith
        · linarith
      · intro h
        left
        exact ⟨by nlinarith, hd⟩
    constructor
    · rw [w2RatioCenter, div_eq_zero_iff]
      constructor
      · rintro (h | h)
        · nlinarith
        · linarith
      · intro h
        left
        rw [h]
        norm_num
    · rw [w2RatioCenter, div_neg_iff]
      constructor
      · rintro (⟨_, h⟩ | ⟨h, _⟩)
        · linarith
        · nlinarith
      · intro h
        right
        exact ⟨by nlinarith, hd⟩

private theorem mean_constant {Ω : Type*} [Fintype Ω] (P : Law Ω) (x : ℝ) :
    mean P (fun _ => x) = x := AronowAudit.P009.mean_const (Bridge.toLaw P) x

private theorem alpha_constant_right {Ω A B : Type*} [Fintype Ω]
    (P : Law Ω) (X : Ω → A) (b : B) : alpha P X (fun _ => b) = 0 := by
  apply le_antisymm
  · apply AronowAudit.P009.MixingBasics.alpha_le_of_event_bound (Bridge.toLaw P)
    intro U V
    change |prob P (fun z => X z ∈ U ∧ b ∈ V) -
      prob P (fun z => X z ∈ U) * prob P (fun _ => b ∈ V)| ≤ 0
    by_cases hv : b ∈ V <;> simp [hv, prob, mean_constant]
  · exact AronowAudit.P009.MixingBasics.alpha_nonnegative (Bridge.toLaw P) X _

private theorem no_interference_facts {n : ℕ} (E : Experiment n) (hNo : NoInterference E) :
    (∀ i j, I E i j = (if i = j then 1 else 0) ∧
      d E i j = (if i = j then 1 else 0)) ∧
    (∀ i z, maskedOthers E i z = fun _ => false) ∧
    (∀ θ : ℝ, w2AlphaInt E θ = 0) := by
  have hi (i j : Fin n) : Interferes E i j ↔ i = j :=
    AronowAudit.P009.SparseCompletion.noI_interferes (Bridge.toExperiment E) hNo i j
  have hm (i : Fin n) : maskedOthers E i = fun _ _ => false := by
    funext z j
    simp only [maskedOthers, masked, hi, Function.update_apply]
    split_ifs <;> simp_all
  refine ⟨?_, fun i z => congrFun (hm i) z, ?_⟩
  · intro i j
    exact ⟨by simp only [I, hi],
      AronowAudit.P009.SparseCompletion.noI_d (Bridge.toExperiment E) hNo i j⟩
  · intro θ
    simp only [w2AlphaInt, hm, alpha_constant_right, mixPower, ite_true,
      Finset.sum_const_zero]

private theorem regular_of_uniform_bound {n : ℕ} (E : Experiment n) (k q s K r u : ℝ)
    (hReg : Regular E k q s) (hK : 0 < K) (hkK : k ≤ K)
    (hy : ∀ i z, |E.outcome i z| ≤ K) (hr : 2 ≤ r) (hu : 1 ≤ u) :
    Regular E K r u := by
  have hinv : K⁻¹ ≤ k⁻¹ := (inv_le_inv₀ hK hReg.1).2 hkK
  refine ⟨hK, hr, hu, ?_, ?_, ?_⟩
  · intro i
    have hp := hReg.2.2.2.1 i
    constructor <;> linarith
  · intro i
    apply AronowAudit.P009.SparseCompletion.mean_le_constant (Bridge.toLaw E.design)
    intro z
    exact Real.rpow_le_rpow (abs_nonneg _) (hy i z) (by linarith)
  · intro i b
    apply AronowAudit.P009.SparseCompletion.mean_le_constant (Bridge.toLaw E.design)
    intro z
    exact Real.rpow_le_rpow (abs_nonneg _) (hy i (Function.update z i b)) (by linarith)

private theorem common_self_alpha {n : ℕ} (hn : 0 < n) (E : Experiment n)
    (p : ℝ) (hp : 0 < p ∧ p < 1) (hCommon : W2CommonAssignment E p) (i : Fin n) :
    alpha E.design (fun z => z i) (fun z => z i) = p * (1 - p) := by
  have hprob (A : Assignment n → Prop) : prob E.design A =
      p * (if A (fun _ => true) then 1 else 0) +
      (1 - p) * (if A (fun _ => false) then 1 else 0) :=
    AronowAudit.P009.CommonCompletion.common_prob hn (Bridge.toExperiment E) p hCommon A
  have hp0 : 0 < p * (1 - p) := mul_pos hp.1 (by linarith)
  apply le_antisymm
  · apply AronowAudit.P009.MixingBasics.alpha_le_of_event_bound (Bridge.toLaw E.design)
    intro U V
    change |prob E.design (fun z => z i ∈ U ∧ z i ∈ V) -
      prob E.design (fun z => z i ∈ U) * prob E.design (fun z => z i ∈ V)| ≤ _
    simp_rw [hprob]
    by_cases hu1 : true ∈ U <;> by_cases hu0 : false ∈ U <;>
      by_cases hv1 : true ∈ V <;> by_cases hv0 : false ∈ V <;>
      simp [hu1, hu0, hv1, hv0, abs_of_pos hp.1,
        abs_of_pos (sub_pos.mpr hp.2)] <;>
      first | nlinarith | (apply abs_le.mpr; constructor <;> nlinarith)
  · have h := AronowAudit.P009.MixingBasics.event_abs_le_alpha (Bridge.toLaw E.design)
      (fun z => z i) (fun z => z i) {true} {true}
    change |prob E.design (fun z => z i ∈ ({true} : Set Bool) ∧ z i ∈ ({true} : Set Bool)) -
      prob E.design (fun z => z i ∈ ({true} : Set Bool)) *
        prob E.design (fun z => z i ∈ ({true} : Set Bool))| ≤ _ at h
    simp_rw [hprob] at h
    simp only [Set.mem_singleton_iff, Bool.false_eq_true,
      and_self, ite_true, ite_false, mul_one, mul_zero, add_zero] at h
    rw [show p - p * p = p * (1 - p) by ring, abs_of_pos hp0] at h
    exact h

private theorem quarter_normalization (S : Study) (f : ℕ → ℝ) (c : ℝ)
    (h : Tendsto (fun t => f t / size S t) atTop (nhds c)) :
    Tendsto (fun t => f t / (size S t / 4)) atTop (nhds (4 * c)) := by
  convert h.const_mul 4 using 1
  ext t
  ring

/-- A concrete common-assignment design, used to exhibit failure of Assumption 5. -/
private def common_zero_law (n : ℕ) (hn : 0 < n) : Law (Assignment n) where
  mass z := if z = (fun _ => true) then 1 / 3
    else if z = (fun _ => false) then 2 / 3 else 0
  nonneg z := by split_ifs <;> norm_num
  total := by
    have hne : (fun _ : Fin n => true) ≠ (fun _ => false) := by
      intro h
      have hbad := congrFun h ⟨0, hn⟩
      contradiction
    have heq (z : Assignment n) :
        (if z = (fun _ => true) then (1 / 3 : ℝ)
          else if z = (fun _ => false) then 2 / 3 else 0) =
        (if z = (fun _ => true) then 1 / 3 else 0) +
        (if z = (fun _ => false) then 2 / 3 else 0) := by
      split_ifs <;> simp_all
    simp_rw [heq]
    norm_num [Finset.sum_add_distrib]

private def common_zero_study : Study where
  N t := t + 1
  positive t := Nat.succ_pos t
  grows := tendsto_atTop_mono (fun t : ℕ => Nat.le_succ t) tendsto_id
  experiment t := ⟨common_zero_law (t + 1) (Nat.succ_pos t), fun _ _ => 0⟩

private theorem common_zero_model :
    RegularSequence common_zero_study 3 2 1 ∧
    (∀ t, NoInterference (common_zero_study.experiment t)) ∧
    (∀ t, W2CommonAssignment (common_zero_study.experiment t) (1 / 3)) := by
  have hcommon (t : ℕ) : W2CommonAssignment (common_zero_study.experiment t) (1 / 3) := by
    intro z
    dsimp [common_zero_study, common_zero_law]
    norm_num
  refine ⟨?_, by intro t i z w h; rfl, hcommon⟩
  intro t
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, ?_, ?_⟩
  · intro i
    have h := AronowAudit.P009.CommonCompletion.common_prob (Nat.succ_pos t)
      (Bridge.toExperiment (common_zero_study.experiment t)) (1 / 3) (hcommon t)
      (fun z => z i = true)
    simp only [Bool.false_eq_true, ite_true, ite_false, mul_one, mul_zero, add_zero] at h
    have hm : marginal (common_zero_study.experiment t) i true = 1 / 3 := h
    rw [hm]
    norm_num
  · intro i
    apply AronowAudit.P009.SparseCompletion.mean_le_constant
      (Bridge.toLaw (common_zero_study.experiment t).design)
    intro z
    change Real.rpow |(0 : ℝ)| 2 ≤ Real.rpow 3 2
    norm_num
  · intro i b
    apply AronowAudit.P009.SparseCompletion.mean_le_constant
      (Bridge.toLaw (common_zero_study.experiment t).design)
    intro z
    change Real.rpow |(0 : ℝ)| 1 ≤ Real.rpow 3 1
    norm_num

/-- Assembly of all no-interference and common-assignment clauses.
Only the full-cube uniform outcome bound is a leaf; every mixing computation,
maximal-moment assertion, order comparison and rational specialization is proved here. -/
theorem T26_assembly (h1 : T26_L1) : T26WholeStatement := by
  refine ⟨fun E hNo => no_interference_facts E hNo, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro S hNo θ
    have hz (t : ℕ) := (no_interference_facts (S.experiment t) (hNo t)).2.2 θ
    simp only [LittleO, hz, zero_div]
    exact tendsto_const_nhds
  · intro n hn E k q s hReg hNo
    obtain ⟨hy, hpower⟩ := h1 hn E k q s hReg hNo
    exact ⟨hy, hpower, fun i b z => (hy i (Function.update z i b)).trans hpower⟩
  · intro S k q s hReg hNo
    let K := Real.rpow k (3 / 2)
    have hk : 0 < k := (hReg 0).1
    have hk2 : 2 ≤ k := AronowAudit.P009.BernoulliCompletion.regular_k_ge_two
      (S.positive 0) (Bridge.toExperiment (S.experiment 0)) k q s (hReg 0)
    have hK : 0 < K := Real.rpow_pos_of_pos hk _
    have hkK : k ≤ K := by
      calc
        k = Real.rpow k 1 := (Real.rpow_one k).symm
        _ ≤ K := Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
    have hy (t : ℕ) (i : Fin (S.N t)) (z : Assignment (S.N t)) :
        |(S.experiment t).outcome i z| ≤ K := by
      have h := h1 (S.positive t) (S.experiment t) k q s (hReg t) (hNo t)
      exact (h.1 i z).trans h.2
    refine ⟨?_, ?_, rfl⟩
    · intro r u hr hu t
      exact regular_of_uniform_bound (S.experiment t) k q s K r u (hReg t) hK hkK
        (hy t) hr hu
    · refine ⟨?_, by simp, ?_, by simp⟩
      · refine ⟨by simp, K, hK, ?_⟩
        intro t i z hz
        exact hy t i z
      · refine ⟨by simp, K, hK, ?_⟩
        intro t i b z hz
        exact hy t i (Function.update z i b)
  · intro n hn E p hp hNo hCommon
    have h (θ : ℝ) := AronowAudit.P009.CommonCompletion.common_assignment_mixing_completed
      hn (Bridge.toExperiment E) p θ hp hNo hCommon
    refine ⟨common_self_alpha hn E p hp hCommon, ?_, fun θ => (h θ).2.1,
      (h 1).2.2, ?_, ?_⟩
    · intro i j hij
      rw [common_self_alpha hn E p hp hCommon i]
      exact (h 1).1 i j hij
    · intro hpHalf
      have hv : alphaExt E 1 = ((n : ℝ) - 1) * p * (1 - p) := (h 1).2.2
      rw [hv, hpHalf]
      ring
    · intro hpThird
      have hv : alphaExt E 1 = ((n : ℝ) - 1) * p * (1 - p) := (h 1).2.2
      rw [hv, hpThird]
      ring
  · intro S p hp hNo hCommon
    have heq (t : ℕ) (θ : ℝ) : alphaExt (S.experiment t) θ =
        (size S t - 1) * Real.rpow (p * (1 - p)) θ :=
      (AronowAudit.P009.CommonCompletion.common_assignment_mixing_completed
        (S.positive t) (Bridge.toExperiment (S.experiment t)) p θ hp (hNo t) (hCommon t)).2.1
    have hlimits (θ : ℝ) : Tendsto (fun t => alphaExt (S.experiment t) θ / size S t)
        atTop (nhds (Real.rpow (p * (1 - p)) θ)) := by
      have hi := (size_grows S).const_div_atTop (Real.rpow (p * (1 - p)) θ)
      have he (t : ℕ) : alphaExt (S.experiment t) θ / size S t =
          Real.rpow (p * (1 - p)) θ - Real.rpow (p * (1 - p)) θ / size S t := by
        rw [heq]
        field_simp [(size_pos S t).ne']
      simpa only [he, sub_zero] using tendsto_const_nhds.sub hi
    have hpp : 0 < p * (1 - p) := mul_pos hp.1 (by linarith)
    refine ⟨?_, ?_, ?_⟩
    · intro θ hθ0 hθ1
      have hc : 0 < Real.rpow (p * (1 - p)) θ := Real.rpow_pos_of_pos hpp θ
      refine ⟨hlimits θ, hc, ?_, ?_⟩
      · refine ⟨Real.rpow (p * (1 - p)) θ / 2,
          2 * Real.rpow (p * (1 - p)) θ, by positivity, by positivity, ?_⟩
        filter_upwards [(size_grows S).eventually (eventually_ge_atTop (2 : ℝ))] with t ht
        rw [heq]
        constructor <;> nlinarith
      · intro hzero
        have he := tendsto_nhds_unique (hlimits θ) hzero
        linarith
    · intro hpHalf
      have hquarter := quarter_normalization S (fun t => alphaExt (S.experiment t) 1)
        (Real.rpow (p * (1 - p)) 1) (hlimits 1)
      norm_num [hpHalf] at hquarter
      exact hquarter
    · intro hpThird
      have hquarter := quarter_normalization S (fun t => alphaExt (S.experiment t) 1)
        (Real.rpow (p * (1 - p)) 1) (hlimits 1)
      have hratio : Tendsto (fun t => alphaExt (S.experiment t) 1 / (size S t / 4))
          atTop (nhds (8 / 9)) := by
        norm_num [hpThird] at hquarter
        exact hquarter
      refine ⟨hratio, ?_⟩
      intro hone
      have hbad := tendsto_nhds_unique hratio hone
      norm_num at hbad
  · obtain ⟨hReg, hNo, hCommon⟩ := common_zero_model
    refine ⟨common_zero_study, hReg, hNo, hCommon, ?_, ?_⟩
    · have hz (t : ℕ) := (no_interference_facts (common_zero_study.experiment t) (hNo t)).2.2 1
      simp only [LittleO, hz, zero_div]
      exact tendsto_const_nhds
    · exact (AronowAudit.P009.CommonCompletion.common_assignment_mixing_sequence
        (Bridge.toStudy common_zero_study) (1 / 3) (by norm_num) hNo hCommon).2

end
end SAP.P009b.WH.W2
