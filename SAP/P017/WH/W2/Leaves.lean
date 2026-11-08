import SAP.P017.Defs.WholeW2
import SAP.P017.Bridge
import AronowAudit.P017.Wave1.Gap.GLP017B2
import AronowAudit.P017.Wave1.Gap.GLP017B4
import AronowAudit.P017.Wave1.Gap.GP017B1
import AronowAudit.P017.Wave1.Gap.GP017B1b

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P017.WH.W2

open MeasureTheory ProbabilityTheory Filter Set AronowAudit.P017
open scoped BigOperators Topology ENNReal NNReal Classical

noncomputable section

/-- Standard Gaussian second-density moment and its positive half-tail formula.
For integrability use integrable_rpow_mul_exp_neg_mul_sq at exponent 2 and
coefficient 1/2, and unfold gaussianPDFReal. For the identity specialize
normal_tail_identity_proof to n = 1 and sigma = 1, identify the integrands,
and simplify the square-root constants. Alternatively reproduce the short
integration-by-parts argument in GP017B1 using the derivative of z times the
standard density. No private declaration needs to be referenced. -/
def T11_L1 : Prop :=
  Integrable (fun z : ℝ => z ^ 2 * gaussianPDFReal 0 1 z) ∧
  ∀ a : ℝ, 0 < a →
    (∫ z in Ioi a, z ^ 2 * gaussianPDFReal 0 1 z) =
      a * gaussianPDFReal 0 1 a + SAP.P017.normalCDF (-a)

/-- Positive scaling of the Lebesgue tail, including genuine integrability.
Set s = sigma/sqrt(n), substitute x = s*z with
integral_comp_mul_left_Ioi', and use (sqrt(n))^2 = n. The integrand becomes
s times z^2 times the standard Gaussian density. Its integrability follows
from the Gaussian exponential moment bound; transport it by positive scaling.
The private rescaling proof in GP017B1 is a readable model, not an importable
donor. This leaf deliberately has no standardized-tail identity as a premise. -/
def T11_L2 : Prop :=
  ∀ (n : ℕ), 1 ≤ n → ∀ c σ : ℝ, 0 < c → 0 < σ →
    IntegrableOn (wholeTailIntegrand n σ) (Ioi c) ∧
    SAP.P017.normalTail n c σ =
      2 * (σ / SAP.P017.sqrtN n) ^ 2 *
        (∫ z in Ioi (c / (σ / SAP.P017.sqrtN n)), z ^ 2 * gaussianPDFReal 0 1 z)

/-- A normally distributed random variable has the displayed truncated second
moment, with both expectations integrable. Pull back the Gaussian square
moment using memLp_id_gaussianReal and integral_map; the truncation is an
indicator of a measurable set. Reflect the negative tail using
gaussianReal_map_neg, add the two disjoint tails (c > 0), and write the positive
tail using integral_gaussianReal_eq_integral_smul. Unfold gaussianPDFReal and
use sqrt(s^2) = s for s = sigma/sqrt(n) > 0. The Gaussian symmetry and density
calculations in GLP017B4 provide a model. No integrability premise is added. -/
def T11_L3 : Prop :=
  ∀ (n : ℕ), 1 ≤ n → ∀ c σ : ℝ, 0 < c → 0 < σ →
    let s := σ / SAP.P017.sqrtN n
    ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (W : Ω → ℝ), Measurable W →
      P.map W = gaussianReal 0 ⟨s ^ 2, sq_nonneg s⟩ →
      Integrable (fun ω => W ω ^ 2) P ∧
      Integrable (fun ω => if |W ω| > c then W ω ^ 2 else 0) P ∧
      (∫ ω, if |W ω| > c then W ω ^ 2 else 0 ∂P) = SAP.P017.normalTail n c σ

/-- Measurability, square integrability and the central Gaussian bound for the
explicit rare-outlier statistics, at each positive sample size and for any p.
Use the scaled normal-mean law from arbitrary_outlier_sequence_proof (one may
specialize its probability sequence to slowP), then divide by sqrt(n).
Transport the Gaussian second moment to obtain E[barX_n^2] = 1/n, and integrate
(1/4) times the indicator of {|barX_n| > 1/2} to obtain the bound 4/n.
The clipped mean and flag are bounded measurable functions, so MemLp.of_bound
and MemLp.integrable_sq give the two remaining square integrability claims.
All these arguments are finite-sample: no assumption on p or on p at zero is
needed. The private finite-moment proofs in GLP017B2 and GP017B1b are models. -/
def T12_L1 : Prop :=
  ∀ (p : ℕ → ℝ) (n : ℕ), 1 ≤ n → RareFiniteCertificate p n

/-- The finite-real identity and limits are existing public proofs; the three
leaves add the missing density, scaling and arbitrary Gaussian moment forms. -/
theorem T11_assembly (h1 : T11_L1) (h2 : T11_L2) (h3 : T11_L3) :
    T11WholeStatement := by
  have hbase : T11Statement := SAP.P017.Bridge.T11_correspondence.mpr
    ⟨@AronowAudit.P017.Wave1.normal_tail_identity_proof,
      @AronowAudit.P017.Wave1.normal_tail_limits_proof⟩
  refine ⟨hbase, h1, ?_, ?_, ?_⟩
  · intro n hn c σ hc hσ
    let s := σ / SAP.P017.sqrtN n
    have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hs : 0 < s := div_pos hσ (Real.sqrt_pos.mpr hnR)
    have ha : 0 < c / s := div_pos hc hs
    obtain ⟨hi, hscale⟩ := h2 n hn c σ hc hσ
    refine ⟨hs, ha, hi, hscale, ?_, h3 n hn c σ hc hσ⟩
    change SAP.P017.normalTail n c σ =
      2 * c * s * gaussianPDFReal 0 1 (c / s) + 2 * s ^ 2 * SAP.P017.normalCDF (-c / s)
    calc
      SAP.P017.normalTail n c σ =
          2 * s ^ 2 * ((c / s) * gaussianPDFReal 0 1 (c / s) +
            SAP.P017.normalCDF (-(c / s))) :=
        hscale.trans (congrArg (fun t : ℝ => 2 * s ^ 2 * t) (h1.2 (c / s) ha))
      _ = _ := by rw [neg_div]; field_simp [hs.ne']
  · intro n hn c σ hc hσ
    have he : {x : ℝ | ENNReal.ofReal c < ENNReal.ofReal x} = Ioi c := by
      ext x
      exact ENNReal.ofReal_lt_ofReal_iff_of_nonneg hc.le
    simp only [extendedNormalTail, he, SAP.P017.normalTail, wholeTailIntegrand]
  · have htop : ∀ (n : ℕ) (σ : ℝ), extendedNormalTail n ⊤ σ = 0 := by
      intro n σ
      simp [extendedNormalTail]
    refine ⟨htop, ?_, ?_⟩
    · intro Ω mΩ P W
      simp
    · intro σ
      constructor
      · simpa only [htop, mul_zero] using
          (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
      · intro k hk
        simpa only [htop, mul_zero] using
          (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))

private theorem retainedT12 : SAP.P017.T12Statement := by
  apply SAP.P017.Bridge.T12_correspondence.mpr
  refine ⟨@AronowAudit.P017.Wave1.arbitrary_outlier_sequence_proof,
    AronowAudit.P017.Wave1.slow_outlier_counterexample_proof, ?_, ?_⟩
  · intro p n hn s
    have hb := clipReal_bounds 0 (1 / 2) (AronowAudit.P017.smallNormalMean n s) (by norm_num)
    have hf := rare_estimator_finite (AronowAudit.P017.smallNormalMean n s)
    change AronowAudit.P017.clipReal 0 1 (AronowAudit.P017.smallNormalClip n s) = AronowAudit.P017.smallNormalClip n s ∧
      (19 / 2 : ℝ) ≤ AronowAudit.P017.smallNormalClip n s + 10 ∧ AronowAudit.P017.smallNormalClip n s + 10 ≤ 21 / 2 ∧
      AronowAudit.P017.clipReal 0 1 (AronowAudit.P017.smallNormalClip n s + 10) = 1 ∧
      (17 / 2 : ℝ) ≤ AronowAudit.P017.smallNormalClip n s + 9 ∧ AronowAudit.P017.smallNormalClip n s + 9 ≤ 19 / 2 at hf
    refine ⟨by simpa only [AronowAudit.P017.smallNormalClip, zero_sub, zero_add] using hb, ?_, ?_⟩
    · intro hflag
      simp only [AronowAudit.P017.rareEstimator, hflag, mul_one, hf.2.2.2.1]
      constructor <;> linarith [hf.2.2.2.2.1, hf.2.2.2.2.2]
    · intro hcentral hflag
      have heq : AronowAudit.P017.smallNormalClip n s = AronowAudit.P017.smallNormalMean n s := by
        apply (clipReal_eq_self_iff 0 (1 / 2) _ (by norm_num)).mpr
        simpa only [sub_zero] using hcentral
      simp [AronowAudit.P017.rareRemainder, heq, hflag]
  · obtain ⟨hp, hlim, hroot, hm, hi, hmu, hS, hc, hfail, h1000, hlarge,
      hdyadic, hpower, hnotpoly, hrest⟩ := AronowAudit.P017.Wave1.slow_outlier_counterexample_proof
    obtain ⟨hmN, hiN, hmuN, hSN, hcN, hrootN, hremN, hrateN, hN, hrestN⟩ :=
      AronowAudit.P017.Wave1.normal_shift_probability_counterexample_proof
    rintro ⟨C, hC, hbound⟩
    apply hnotpoly 1 (by norm_num)
    refine ⟨C, hC, ?_⟩
    filter_upwards [hbound, eventually_ge_atTop 1] with n hbn hn
    have ht := (hN n hn).2.2.2.2.2.2
    simpa only [Real.rpow_one, mul_one_div] using
      hbn.trans (mul_le_mul_of_nonneg_left ht hC.le)

/-- The empirical functional, finite event bounds and capped-square-root
certificate are proved here; the one new leaf supplies the finite moments. -/
theorem T12_assembly (h1 : T12_L1) : T12WholeStatement := by
  have hbase := retainedT12
  refine ⟨hbase, ?_, ?_, ?_, ?_⟩
  · unfold SAP.P017.slowObserved SAP.P017.slowY1 SAP.P017.slowY0
    fun_prop
  · intro p n hn
    refine ⟨h1 p n hn, ?_⟩
    intro s
    have hcoord : ∀ f : (ℝ × (ℝ × (ℝ × ℝ))) → ℝ,
        (∫ z, f z ∂SAP.P017.empiricalObserved SAP.P017.slowObserved n s) =
          (∑ i ∈ Finset.range n, f (SAP.P017.slowObserved (s i))) / (n : ℝ) := by
      intro f
      unfold SAP.P017.empiricalObserved
      rw [integral_smul_measure, integral_finsetSum_measure]
      · simp only [integral_dirac, ENNReal.toReal_div, ENNReal.toReal_one,
          ENNReal.toReal_natCast, smul_eq_mul]
        ring
      · intro i hi
        exact integrable_dirac (by simp)
    have hX : (∫ z, z.1 ∂SAP.P017.empiricalObserved SAP.P017.slowObserved n s) =
        SAP.P017.smallNormalMean n s := by
      simpa only [SAP.P017.slowObserved, SAP.P017.smallNormalMean, SAP.P017.sampleMean]
        using hcoord (fun z => z.1)
    have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
    have hU : (n : ℝ) *
        (∫ z, z.2.1 ∂SAP.P017.empiricalObserved SAP.P017.slowObserved n s) =
          ∑ i ∈ Finset.range n, (s i).2.1 := by
      rw [hcoord]
      simp only [SAP.P017.slowObserved]
      field_simp
    simp only [SAP.P017.rareEstimator, SAP.P017.smallNormalClip,
      rareEmpiricalFunctional, hX, hU, SAP.P017.rareFlag, SAP.P017.rareUniform]
    rfl
  · intro p hp hlim n hn δ hδ
    obtain ⟨hm, hi, hmu, hS, hc, hnormal, hN, hrest⟩ := hbase.1 p hp hlim
    obtain ⟨hu, hflag, hind, hZ, hdec, hrem, hnotS, hout, hnonzero,
      hprob, hsupport, hzero, hone, hmsel, hmseu⟩ := hN n hn
    have hsub : {s | |SAP.P017.rareRemainder p n s| > δ} ⊆
        {s | |SAP.P017.smallNormalMean n s| > 1 / 2} ∪
          {s | SAP.P017.rareFlag p n s = 1} := by
      intro s hs
      by_cases hcentral : |SAP.P017.smallNormalMean n s| > 1 / 2
      · exact Or.inl hcentral
      by_cases hflag1 : SAP.P017.rareFlag p n s = 1
      · exact Or.inr hflag1
      have hflag0 : SAP.P017.rareFlag p n s = 0 := by
        unfold SAP.P017.rareFlag at *
        split_ifs at * <;> simp_all
      have hz := (hbase.2.2.1 p n hn s).2.2 (le_of_not_gt hcentral) hflag0
      change δ < |SAP.P017.rareRemainder p n s| at hs
      rw [hz, abs_zero] at hs
      exact False.elim ((not_lt_of_ge hδ.le) hs)
    have hrembound : SAP.P017.pr (SAP.P017.iidSamples SAP.P017.slowPopulation)
        {s | |SAP.P017.rareRemainder p n s| > δ} ≤
          SAP.P017.pr (SAP.P017.iidSamples SAP.P017.slowPopulation)
            {s | |SAP.P017.smallNormalMean n s| > 1 / 2} + p n := by
      calc
        _ ≤ SAP.P017.pr (SAP.P017.iidSamples SAP.P017.slowPopulation)
            ({s | |SAP.P017.smallNormalMean n s| > 1 / 2} ∪
              {s | SAP.P017.rareFlag p n s = 1}) :=
          measureReal_mono hsub (measure_ne_top _ _)
        _ ≤ _ := by
          rw [← hflag]
          exact measureReal_union_le (μ := SAP.P017.iidSamples SAP.P017.slowPopulation)
            {s | |SAP.P017.smallNormalMean n s| > 1 / 2}
            {s | SAP.P017.rareFlag p n s = 1}
    refine ⟨hrembound, ?_, ?_⟩
    · linarith [(h1 p n hn).2.2.2.2.2.2.2.2.2]
    have herror : {s | SAP.P017.sqrtN n *
        |SAP.P017.rareEstimator p n s - SAP.P017.clipReal 0 1 (SAP.P017.rareEstimator p n s)| > δ} ⊆
        {s | SAP.P017.rareEstimator p n s ≠ SAP.P017.clipReal 0 1 (SAP.P017.rareEstimator p n s)} := by
      intro s hs heq
      change δ < SAP.P017.sqrtN n *
        |SAP.P017.rareEstimator p n s - SAP.P017.clipReal 0 1 (SAP.P017.rareEstimator p n s)| at hs
      rw [sub_eq_zero.mpr heq, abs_zero, mul_zero] at hs
      exact (not_lt_of_ge hδ.le) hs
    exact (measureReal_mono herror (measure_ne_top _ _)).trans_eq hprob
  · intro r hr hrlim
    have hp (n : ℕ) (hn : 1 ≤ n) :
        0 < sqrtFailureRate r n ∧ sqrtFailureRate r n ≤ 1 := by
      exact ⟨lt_min (by norm_num) (Real.sqrt_pos.mpr (hr n hn)), min_le_left _ _⟩
    have hsqrt : Tendsto (fun n => Real.sqrt (r n)) atTop (𝓝 0) := by
      simpa only [Real.sqrt_zero] using hrlim.sqrt
    have hplim : Tendsto (sqrtFailureRate r) atTop (𝓝 0) := by
      change Tendsto (fun n => min 1 (Real.sqrt (r n))) atTop (𝓝 0)
      simpa only [min_eq_right (by norm_num : (0 : ℝ) ≤ 1)] using
        (tendsto_const_nhds (x := (1 : ℝ))).min hsqrt
    have hevent : ∀ᶠ n in atTop, sqrtFailureRate r n = Real.sqrt (r n) := by
      filter_upwards [hrlim.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))]
        with n hn
      exact min_eq_right (Real.sqrt_le_one.mpr hn.le)
    have hsqrt' : Tendsto (fun n => Real.sqrt (r n)) atTop (𝓝[>] 0) := by
      apply tendsto_nhdsWithin_iff.mpr
      refine ⟨hsqrt, ?_⟩
      filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
      exact Real.sqrt_pos.mpr (hr n hn)
    have hratio : Tendsto (fun n => sqrtFailureRate r n / r n) atTop atTop := by
      apply (tendsto_inv_nhdsGT_zero.comp hsqrt').congr'
      filter_upwards [eventually_ge_atTop (1 : ℕ), hevent] with n hn heq
      rw [heq]
      change (Real.sqrt (r n))⁻¹ = Real.sqrt (r n) / r n
      have hrpos := hr n hn
      have hspos : 0 < Real.sqrt (r n) := Real.sqrt_pos.mpr hrpos
      have hsquare := Real.sq_sqrt hrpos.le
      field_simp [ne_of_gt hrpos, ne_of_gt hspos]
      nlinarith
    obtain ⟨hm, hi, hmu, hS, hc, hnormal, hN, hrest⟩ := hbase.1 (sqrtFailureRate r) hp hplim
    refine ⟨hp, hplim, hevent, hratio, hnormal, ?_⟩
    intro n hn
    exact (hN n hn).2.2.2.2.2.2.2.2.2.1

end
end SAP.P017.WH.W2

