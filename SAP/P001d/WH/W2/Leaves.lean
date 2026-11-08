import SAP.P001d.WH.W2.Support
import SAP.P001d.WH.W2.Population
import SAP.P001d.WH.W2.Moments
import SAP.P001d.WH.W2.Triangle

set_option autoImplicit false
set_option relaxedAutoImplicit false

set_option maxHeartbeats 1600000
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology

noncomputable section
namespace SAP.P001d.WH.W2

universe u

local instance instDecidableLeaves (p : Prop) : Decidable p := Classical.propDecidable p

/-- Integrate the negative lobe, including its endpoints. Rewrite signedKernel as
the difference of interval indicators (signed_kernel_indicator), use interval volumes,
and translate with integral_affine_iic. Endpoint singleton sets have volume zero.
This is one piecewise constant integral calculation, not a differentiation argument. -/
def T58_L1 : Prop :=
  ∀ a t : ℝ, t ∈ Set.Icc (a-2) (a-1) →
    kernelCDF signedKernel 1 (fun _ : Fin 1 => a) t = -(t-a+2)/2

/-- Exact heavy-law survival function. On 0<u<1 solve 2^(1/u²)≥x, x≥2,
as u≤1/sqrt(log x/log 2), then apply map_apply and volume_Icc to Uniform[0,1].
The endpoint u=0 is null. The other two mixture components contribute zero.
Use Real.log_rpow, positivity of log 2 and Real.sqrt_sq. -/
def T61_L1 : Prop :=
  ∀ x : ℝ, 2 ≤ x → prob heavyBootstrapLaw (Set.Ici x) =
    1/(4*Real.sqrt (Real.log x / Real.log 2))

/-- The two endpoints omitted by heavyMedian_local_cdf. Evaluate the central uniform
component at -1 and 1. The positive and negative tail components stay outside [-1,1]
except for the null endpoint u=0, so the endpoint CDF values are 1/4 and 3/4. -/
def T61_L2 : Prop :=
  cdf heavyBootstrapLaw id (-1) = 1/4 ∧ cdf heavyBootstrapLaw id 1 = 3/4

/-- Empirical half-quantile and its domain for every positive size, with the lower
middle convention at even sizes. Prove threshold counts using medianCounts_sorted_rank
and medianCounts_sorted_filter_card, then use le_csInf/csInf_le. CDF validity and
boundedness follow from finite minima and maxima; a constant sample has quantile c.
At odd sizes the lower and upper middle ranks coincide. This identifies the actual
functional without asserting the false even-size equality to regularHeavyStatistic. -/
def T61_L3 : Prop :=
  (∀ {n : ℕ}, 0 < n → ∀ x : Fin n → ℝ,
    WholeCDF (wholeEmpiricalCDF x) ∧
    ({t : ℝ | 1/2 ≤ wholeEmpiricalCDF x t}).Nonempty ∧
    BddBelow {t : ℝ | 1/2 ≤ wholeEmpiricalCDF x t} ∧
    sInf {t : ℝ | 1/2 ≤ wholeEmpiricalCDF x t} = wholeLowerMedian x ∧
    (Odd n → wholeRegularStatistic x = regularHeavyStatistic x)) ∧
  (∀ {n : ℕ}, 0 < n → ∀ c : ℝ, wholeRegularStatistic (fun _ : Fin n => c) = c)

/-- Full-sequence marginal limit of the exact CDF functional. Apply the ordinary CLT
to 1{X_i≤0}-1/2, whose variance is 1/4. Empirical-CDF consistency makes the event
outside [1/4,3/4] negligible. Transfer the CDF limit using regular_cd_agree_off,
as in regular_sign_normal_limit, before its odd-size reindexing. The fallback can
be arbitrarily large on this exceptional event and needs no population moment. -/
def T61_L4 : Prop :=
  ∀ (Ω : Type*) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ), IID μ X → cdf μ (X 0) 0 = 1/2 →
    CD μ (fun k ω => Real.sqrt (k+1 : ℕ)*wholeRegularStatistic
      (firstSample X (k+1) ω)) (gaussianReal 0 (1/4))

/-- Full conditional Bernoulli bootstrap CLT at success probability 1/2. Given the
sample, the threshold count is Binomial(n,p_n), p_n=Fhat_n(0)→p1/2.
Use bootstrap_threshold_count_law, random_binomial_moving_cdf, and
medianTransport_test_cp to obtain bounded continuous tests. This proves the
Bernoulli case directly; it does not assume a generic bootstrap CLT contract. -/
def T61_L5 : Prop :=
  ∀ (Ω : Type*) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ), IID μ X → cdf μ (X 0) 0 = 1/2 →
    BootstrapWeakCP μ X (fun k => k+1) (fun {n} => @wholeSignStatistic n)
      (gaussianReal 0 (1/4))

/-- Transfer conditional weak tests from the centered sign fraction to the exact
functional. On p_n∈[3/8,5/8] the original sample uses the affine branch and the
conditional probability that p_n* leaves [1/4,3/4] is at most 16/n by the binomial
variance bound and Chebyshev. The complement has probability tending to zero.
For a test bounded by C the difference is at most 2C times this conditional bad
probability. No restriction on tail moments, nor on the quantile fallback, is needed. -/
def T61_L6 : Prop :=
  ∀ (Ω : Type*) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ), (∀ i, Measurable (X i)) →
    CP μ (fun k ω => wholeEmpiricalCDF (firstSample X (k+1) ω) 0) (1/2) →
    BootstrapWeakCP μ X (fun k => k+1) (fun {n} => @wholeSignStatistic n)
      (gaussianReal 0 (1/4)) →
    BootstrapWeakCP μ X (fun k => k+1) (fun {n} => @wholeRegularStatistic n)
      (gaussianReal 0 (1/4))

theorem T70_assembly : T70WholeStatement := by
  refine ⟨restricted70, ?_⟩
  intro n hn J x y
  exact ⟨unsquared_expansion x y, unsquared_limit hn x y, distinct_nodes x⟩

theorem T73_assembly : T73WholeStatement := finite73

theorem T58_assembly (h1 : T58_L1) : T58WholeStatement := by
  have h2 := triangle_certificate
  have hs : ∀ a : ℝ, StrictAntiOn (kernelCDF signedKernel 1 (fun _ : Fin 1 => a))
      (Set.Ioo (a-2) (a-1)) ∧
      ¬ WholeCDF (kernelCDF signedKernel 1 (fun _ : Fin 1 => a)) := by
    intro a
    constructor
    · intro x hx y hy hxy
      rw [h1 a x ⟨hx.1.le, hx.2.le⟩, h1 a y ⟨hy.1.le, hy.2.le⟩]
      linarith
    · intro hc
      have hn := (hc.1 (a-1)).1
      rw [(restricted58.2.2.2 a).2] at hn
      norm_num at hn
  have hcont : Continuous wholeTrianglePDF := by unfold wholeTrianglePDF; fun_prop
  have hpos : ∀ x, 0 ≤ wholeTrianglePDF x := fun x => le_max_left _ _
  have hzero : ∀ x, wholeTrianglePDF x = 0 ↔ x ∉ Set.Ioo (5/4 : ℝ) (7/4) := by
    intro x
    simp only [wholeTrianglePDF, max_eq_left_iff, Set.mem_Ioo, not_and_or, not_lt]
    constructor
    · intro hx
      have ha : 1/4 ≤ |x-3/2| := by linarith
      rcases le_abs.mp ha with h | h <;> (first | left; linarith | right; linarith)
    · rintro (hx | hx)
      · have ha := neg_le_abs (x-3/2); linarith
      · have ha := le_abs_self (x-3/2); linarith
  have hfinite : ∀ {n : ℕ}, 0 < n → ∀ x : Fin n → ℝ,
      (∀ i, x i ∈ Set.Icc (5/4 : ℝ) (7/4)) →
      kernelCDF signedKernel 1 x 0 = (∑ i, (x i-2)/2)/(n : ℝ) ∧
      kernelCDF signedKernel 1 x 0 ∈ Set.Icc (-3/8 : ℝ) (-1/8) := by
    intro n hn x hx
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have he := AronowAudit.P001.kernel_cdf_correct_integrand hn x
      signedKernel restricted58.2.1 1 (by norm_num) 0
    have hi (i : Fin n) : (∫ t in Set.Iic ((0-x i)/1), signedKernel t) = (x i-2)/2 := by
      have hh := h1 0 (-x i) (by constructor <;> linarith [(hx i).1, (hx i).2])
      simpa [kernelCDF, kernelDensity, sub_eq_add_neg, add_comm] using hh
    have heq : kernelCDF signedKernel 1 x 0 = (∑ i, (x i-2)/2)/(n : ℝ) := by
      simpa only [hi, Bridge.kernelCDF_eq] using he
    refine ⟨heq, ?_⟩
    rw [heq]
    constructor
    · apply (le_div_iff₀ hnR).mpr
      calc
        (-3/8 : ℝ)*(n : ℝ) = ∑ _ : Fin n, (-3/8 : ℝ) := by simp; ring
        _ ≤ ∑ i, (x i-2)/2 := Finset.sum_le_sum (fun i _ => by linarith [(hx i).1])
    · apply (div_le_iff₀ hnR).mpr
      calc
        (∑ i, (x i-2)/2) ≤ ∑ _ : Fin n, (-1/8 : ℝ) :=
          Finset.sum_le_sum (fun i _ => by linarith [(hx i).2])
        _ = (-1/8 : ℝ)*(n : ℝ) := by simp; ring
  haveI := h2.2.2.1
  refine ⟨restricted58, hs, hcont, hpos, hzero, h2.1, h2.2.1,
    h2.2.2.1, whole_cdf _, h2.2.2.2.2, hfinite, ?_⟩
  intro Ω mΩ μ hμ X hiid hlaw
  have ha : ∀ i : ℕ, ∀ᵐ ω ∂μ, X i ω ∈ Set.Icc (5/4 : ℝ) (7/4) := by
    intro i
    have hm : μ.map (X i) = wholeTriangleLaw := (hiid.2.2 i).map_eq.trans hlaw
    have hh : ∀ᵐ x ∂(μ.map (X i)), x ∈ Set.Icc (5/4 : ℝ) (7/4) :=
      hm ▸ h2.2.2.2.1
    exact (ae_map_iff (hiid.1 i).aemeasurable measurableSet_Icc).mp hh
  filter_upwards [ae_all_iff.mpr ha] with ω hω
  intro n hn
  have hb := (hfinite hn (firstSample X n ω) (fun i => hω i)).2
  have hneg : kernelCDF signedKernel 1 (firstSample X n ω) 0 < 0 := by linarith [hb.2]
  refine ⟨hb, fun hc => (not_le_of_gt hneg) (hc.1 0).1, ?_⟩
  rintro ⟨r, hr⟩
  nlinarith [sq_nonneg r]

theorem T62_assembly : T62WholeStatement := by
  intro Ω mΩ μ hμ
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro X _ T hT θ φ hφ _ hw
    exact composite_moments μ X T hT φ hφ hw
  · intro n hn x
    exact AronowAudit.P001.bootstrap_sample_mean_exact_variance hn x
  · intro X hiid h2 hv
    have h := AronowAudit.P001.bootstrap_sample_mean_consistency μ X hiid h2 hv
    simp only [AronowAudit.P001.var] at h
    constructor
    · simpa only [Bridge.cp_iff, Bridge.bootVar_eq, Bridge.finiteSampleMean_eq,
        Bridge.firstSample_eq] using Bridge.cp_succ μ _ _ h.1
    · simpa only [Bridge.cp_iff, Bridge.bootVar_eq, Bridge.finiteSampleMean_eq,
        Bridge.firstSample_eq] using Bridge.cp_succ μ _ _ h.2
  · intro X hiid m f δ hδ hf hfn hfm hcont hpos hmed η hη hm
    have h := AronowAudit.P001.Wave1.TailA.bootstrap_median_primitive_moment_condition_final
      μ X hiid m f δ hδ hf hfn hfm hcont hpos hmed η hη hm
    constructor
    · simpa only [Bridge.cp_iff, Bridge.bootVar_eq, Bridge.sampleMedian_eq,
        Bridge.firstSample_eq] using Bridge.cp_succ μ _ _ h.1
    · simpa only [Bridge.cp_iff, Bridge.bootVar_eq, Bridge.sampleMedian_eq,
        Bridge.firstSample_eq] using Bridge.cp_succ μ _ _ h.2

theorem T61_assembly (h1 : T61_L1) (h2 : T61_L2) (h3 : T61_L3)
    (h4 : T61_L4.{u}) (h5 : T61_L5.{u}) (h6 : T61_L6.{u}) : T61WholeStatement.{u} := by
  haveI := heavy_probability
  have hz := heavy_unique_median.1
  have hlocal : ∀ G : ℝ → ℝ, (∀ x, |G x-cdf heavyBootstrapLaw id x| < 1/4) →
      regularHeavyFunctional G - regularHeavyFunctional (cdf heavyBootstrapLaw id) =
        G 0-cdf heavyBootstrapLaw id 0 := by
    intro G hG
    exact AronowAudit.P001.Wave1.regular_local_subtraction _ _ hz hG
  have hfun : regularHeavyFunctional (cdf heavyBootstrapLaw id) = 0 := by
    unfold regularHeavyFunctional
    rw [hz]
    norm_num
  have hclosed : ∀ x : ℝ, |x| ≤ 1 → cdf heavyBootstrapLaw id x = 1/2+x/4 := by
    intro x hx
    by_cases hl : x = -1
    · subst x; rw [h2.1]; norm_num
    by_cases hr : x = 1
    · subst x; rw [h2.2]; norm_num
    exact AronowAudit.P001.Wave1.TailA.heavyMedian_local_cdf x
      ⟨lt_of_le_of_ne (abs_le.mp hx).1 (Ne.symm hl), lt_of_le_of_ne (abs_le.mp hx).2 hr⟩
  have hthreshold : ∀ j : ℕ, 0 < j →
      prob heavyBootstrapLaw (Set.Ici ((2 : ℝ)^(j^2))) = 1/(4*j) := by
    intro j hj
    have hj1 : 1 ≤ j^2 := by nlinarith
    have hp : (2 : ℝ) ≤ (2 : ℝ)^(j^2) := by
      simpa using pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hj1
    rw [h1 _ hp, Real.log_pow, mul_div_cancel_right₀ _ (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne',
      Nat.cast_pow, Real.sqrt_sq (Nat.cast_nonneg j)]
  refine ⟨heavy_probability, whole_cdf _, h1, hclosed, heavy_unique_median, hthreshold,
    hfun, hlocal, local_hadamard _ hz, h3.1, h3.2, ?_, ?_⟩
  · intro n hn x i
    refine ⟨h3.2 hn (x i), ?_⟩
    unfold wholeResampleProb
    dsimp only
    rw [Finset.sum_eq_single (fun _ : Fin n => i)]
    · simp
    · intro a _ ha
      exact ite_eq_right ha
    · simp
  · intro Ω mΩ μ hμ X hiid hlaw
    have hhalf : cdf μ (X 0) 0 = 1/2 := by
      change (μ (X 0 ⁻¹' Set.Iic 0)).toReal = 1/2
      rw [← Measure.map_apply (hiid.1 0) measurableSet_Iic, hlaw]
      exact hz
    have hcp := AronowAudit.P001.empirical_cdf_consistency μ X hiid 0
    have hp : CP μ (fun k ω => wholeEmpiricalCDF (firstSample X (k+1) ω) 0) (1/2) := by
      have hcc := Bridge.cp_succ μ _ _ hcp
      change CP μ (fun n => AronowAudit.P001.sampleMean
        (fun i ω => if X i ω ≤ 0 then (1 : ℝ) else 0) (n+1)) (cdf μ (X 0) 0) at hcc
      rw [hhalf] at hcc
      convert hcc using 1
      funext k ω
      exact AronowAudit.P001.Wave1.regular_sign_count X (k+1) ω
    have heq (n : ℕ) (hn : 0 < n) (ho : Odd n) :
        @wholeRegularStatistic n = @regularHeavyStatistic n := by
      funext x
      exact (h3.1 hn x).2.2.2.2 ho
    have hb := restricted61 (Ω := Ω) μ X hiid hlaw
    refine ⟨restricted61, h4 Ω μ X hiid hhalf,
      h6 Ω μ X hiid.1 hp (h5 Ω μ X hiid hhalf), ?_, ?_⟩
    · intro n ho hn
      simpa only [heq n (by omega) ho] using hb.2.2.2.1 n ho hn
    · intro hc
      have ht : Tendsto (fun k : ℕ => 2*k) atTop atTop :=
        tendsto_atTop_mono (fun k => by dsimp; omega) tendsto_id
      have hodd : CP μ (fun k ω => (2*k+1 : ℕ)*bootVar wholeRegularStatistic
          (firstSample X (2*k+1) ω)) (1/4) := by
        intro ε hε
        exact (hc ε hε).comp ht
      apply hb.2.2.2.2
      convert hodd using 1
      funext k ω
      rw [heq (2*k+1) (by omega) ⟨k, by omega⟩]

end SAP.P001d.WH.W2
