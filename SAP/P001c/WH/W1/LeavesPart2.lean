import SAP.P001c.Defs.WholeW1
import SAP.P001c.Bridge
import AronowAudit.P001.Wave1.Gap.TailA.CDFDelta

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P001c.WH.W1

universe u

open MeasureTheory ProbabilityTheory Filter
open AronowAudit.P001.Wave1
open scoped BigOperators ENNReal NNReal Topology Classical

noncomputable section

private theorem integrable_wlln {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ)
    (hiid : isIID μ X) (hint : Integrable (X 0) μ) :
    convergesInProbability μ (sampleAverage X) (expectation μ (X 0)) := by
  have hm (n : ℕ) : Measurable (sampleAverage X n) := by
    exact (Finset.measurable_sum _ (fun i _ => hiid.1 i)).div_const _
  exact tendstoInMeasure_iff_measureReal_dist.mp
    (tendstoInMeasure_of_tendsto_ae (fun n => (hm n).aestronglyMeasurable)
      (strong_law_ae_real X hint (fun i j hij => hiid.2.1.indepFun hij) hiid.2.2))

private theorem pair_probability_limit {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (S T : ℕ → Ω → ℝ) (a b : ℝ)
    (hS : convergesInProbability μ S a) (hT : convergesInProbability μ T b) :
    convergesInProbability μ (fun n ω => (S n ω, T n ω)) (a,b) := by
  intro ε hε
  have hb (n : ℕ) : probability μ {ω | ε ≤ dist (S n ω, T n ω) (a,b)} ≤
      probability μ {ω | ε ≤ dist (S n ω) a} +
      probability μ {ω | ε ≤ dist (T n ω) b} := by
    have he : {ω | ε ≤ dist (S n ω, T n ω) (a,b)} =
        {ω | ε ≤ dist (S n ω) a} ∪ {ω | ε ≤ dist (T n ω) b} := by
      ext ω
      simp only [Prod.dist_eq, Set.mem_ofPred_eq, Set.mem_union, le_max_iff]
    rw [he]
    exact measureReal_union_le _ _
  exact squeeze_zero (fun _ => ENNReal.toReal_nonneg) hb
    (by simpa only [add_zero] using (hS ε hε).add (hT ε hε))

theorem T54_assembly : T54WholeStatement := by
  refine ⟨?_, ?_, ?_⟩
  · intro Ω mΩ μ pμ Z hiid hint
    exact integrable_wlln μ Z hiid hint
  · intro Ω mΩ μ pμ S T a b _ _ hS hT g hg
    exact AronowAudit.P001.probability_convergence_continuous_at μ
      (fun n ω => (S n ω, T n ω)) (a,b) g
      (pair_probability_limit μ S T a b hS hT) hg.continuousAt
  · intro Ω mΩ μ pμ X hiid h2 hv
    have hsq : isIID μ (fun i ω => (X i ω)^2) := by
      refine ⟨fun i => (hiid.1 i).pow_const 2, ?_, ?_⟩
      · exact hiid.2.1.comp (fun _ (x : ℝ) => x^2) (fun _ => by fun_prop)
      · intro i
        exact (hiid.2.2 i).comp (by fun_prop : Measurable (fun x : ℝ => x^2))
    obtain ⟨he, hc⟩ := AronowAudit.P001.sample_variance_unbiased_factor_and_consistency
      μ X hiid h2 hv
    exact ⟨integrable_wlln μ X hiid (h2.integrable (by norm_num)),
      integrable_wlln μ _ hsq h2.integrable_sq, (variance_eq_sub h2).symm, he, hc⟩

/-- Realize the finite moment sums as actual moments of the geometric power-tail
law. Its singleton mass is (1/8)^k*(7/8)=powerTailMass k; injectivity of 2^k
identifies transformed atoms. Use integrable_geometricMeasure_iff and
integral_geometricMeasure', with squares_missing_wlln_hypothesis as the exact
series donor, then variance_eq_sub. The absolute first moment equals the mean
because all values are positive. About 100–160 lines. -/
def T53_L1 : Prop :=
  (∀ k : ℕ, probability powerTailLaw {j | powerTailValue j = (2 : ℝ)^k} =
    powerTailMass k) ∧
  MemLp powerTailValue 2 powerTailLaw ∧
  expectation powerTailLaw (fun k => |powerTailValue k|) = 7/6 ∧
  expectation powerTailLaw powerTailValue = 7/6 ∧
  expectation powerTailLaw (fun k => (powerTailValue k)^2) = 7/4 ∧
  variance powerTailValue powerTailLaw = 7/18

/-- Give the divergent fourth-moment series its measure-theoretic meaning.
Unfold geometricMeasure_eq and use lintegral_sum_measure, lintegral_smul_measure,
and lintegral_dirac' to match the ENNReal sum in squares_missing_wlln_hypothesis.
If the squared variable were L2, integrable_geometricMeasure_iff would make the
weighted fourth moments summable, contradicting that infinite nonnegative sum.
Conclude evariance_eq_top using measurability on N. Do not use the totalized real
variance to express infinity. About 100–180 lines. -/
def T53_L2 : Prop :=
  (∫⁻ k, ENNReal.ofReal ((powerTailValue k)^4) ∂powerTailLaw) = ∞ ∧
  ¬ MemLp (fun k => (powerTailValue k)^2) 2 powerTailLaw ∧
  evariance (fun k => (powerTailValue k)^2) powerTailLaw = ∞

theorem T53_assembly (h1 : T53_L1) (h2 : T53_L2) : T53WholeStatement.{u} := by
  have hseries : T53Statement := by
    obtain ⟨hs, hm, h1s, h2s, hm1, hm2, h4, hv⟩ :=
      AronowAudit.P001.squares_missing_wlln_hypothesis
    refine ⟨fun k => by unfold powerTailMass; positivity,
      hs, hm, h1s, h2s, hm1, hm2, h4, hv, by norm_num⟩
  have : IsProbabilityMeasure powerTailLaw := by unfold powerTailLaw; infer_instance
  have : IsProbabilityMeasure powerTailProduct := by unfold powerTailProduct; infer_instance
  have hm : Measurable powerTailValue := measurable_of_countable _
  have hmarg (i : ℕ) : IdentDistrib (powerTailSample i) powerTailValue
      powerTailProduct powerTailLaw := by
    refine ⟨hm.comp (measurable_pi_apply i) |>.aemeasurable, hm.aemeasurable, ?_⟩
    change powerTailProduct.map (powerTailValue ∘ (fun ω : ℕ → ℕ => ω i)) = _
    rw [← Measure.map_map hm (measurable_pi_apply i)]
    simp only [powerTailProduct, Measure.infinitePi_map_eval]
  have hiid : isIID powerTailProduct powerTailSample := by
    refine ⟨fun i => hm.comp (measurable_pi_apply i), ?_, ?_⟩
    · exact iIndepFun_infinitePi (P := fun _ : ℕ => powerTailLaw)
        (X := fun _ => powerTailValue) (fun _ => hm)
    · intro i
      exact (hmarg i).trans (hmarg 0).symm
  have hmom (i : ℕ) :
      (∀ k : ℕ, probability powerTailProduct {ω | powerTailSample i ω = (2 : ℝ)^k} =
        powerTailMass k) ∧
      MemLp (powerTailSample i) 2 powerTailProduct ∧
      expectation powerTailProduct (fun ω => |powerTailSample i ω|) = 7/6 ∧
      expectation powerTailProduct (powerTailSample i) = 7/6 ∧
      Integrable (fun ω => (powerTailSample i ω)^2) powerTailProduct ∧
      expectation powerTailProduct (fun ω => (powerTailSample i ω)^2) = 7/4 ∧
      variance (powerTailSample i) powerTailProduct = 7/18 ∧
      (∫⁻ ω, ENNReal.ofReal ((powerTailSample i ω)^4) ∂powerTailProduct) = ∞ ∧
      ¬ MemLp (fun ω => (powerTailSample i ω)^2) 2 powerTailProduct ∧
      evariance (fun ω => (powerTailSample i ω)^2) powerTailProduct = ∞ := by
    have hd := hmarg i
    have hdabs := hd.comp (by fun_prop : Measurable (fun x : ℝ => |x|))
    have hdsq := hd.comp (by fun_prop : Measurable (fun x : ℝ => x^2))
    have hd4 := hd.comp (by fun_prop : Measurable (fun x : ℝ => ENNReal.ofReal (x^4)))
    have hx2 := hd.symm.memLp_snd h1.2.1
    refine ⟨?_, hx2, hdabs.integral_eq.trans h1.2.2.1,
      hd.integral_eq.trans h1.2.2.2.1, hx2.integrable_sq,
      hdsq.integral_eq.trans h1.2.2.2.2.1, hd.variance_eq.trans h1.2.2.2.2.2,
      hd4.lintegral_eq.trans h2.1, ?_, hdsq.evariance_eq.trans h2.2.2⟩
    · intro k
      have he := hd.measure_mem_eq (measurableSet_singleton ((2 : ℝ)^k))
      change powerTailProduct {ω | powerTailSample i ω = (2 : ℝ)^k} =
        powerTailLaw {j | powerTailValue j = (2 : ℝ)^k} at he
      exact (congrArg ENNReal.toReal he).trans (h1.1 k)
    · intro hh
      exact h2.2.1 (hdsq.memLp_snd hh)
  have hgeneral : ∀ (Ω : Type u) [MeasurableSpace Ω] (μ : Measure Ω)
      [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ), isIID μ X → MemLp (X 0) 2 μ →
      0 < variance (X 0) μ →
      convergesInProbability μ (sampleAverage X) (expectation μ (X 0)) ∧
      (∀ n : ℕ, 0 < n → expectation μ (pluginVariance X n) =
        ((n : ℝ)-1)/n * variance (X 0) μ) ∧
      convergesInProbability μ (pluginVariance X) (variance (X 0) μ) := by
    intro Ω mΩ μ pμ X hx hx2 hv
    exact ⟨AronowAudit.P001.weak_law_finite_variance μ X hx hx2,
      AronowAudit.P001.sample_variance_unbiased_factor_and_consistency μ X hx hx2 hv⟩
  have hv0 := (hmom 0).2.2.2.2.2.2.1
  have hvpos : 0 < variance (powerTailSample 0) powerTailProduct := by
    rw [hv0]
    norm_num
  obtain ⟨he, hc⟩ := AronowAudit.P001.sample_variance_unbiased_factor_and_consistency
    powerTailProduct powerTailSample hiid (hmom 0).2.1 hvpos
  change (∀ n : ℕ, 0 < n → expectation powerTailProduct (pluginVariance powerTailSample n) =
    ((n : ℝ)-1)/n * variance (powerTailSample 0) powerTailProduct) at he
  change convergesInProbability powerTailProduct (pluginVariance powerTailSample)
    (variance (powerTailSample 0) powerTailProduct) at hc
  refine ⟨hseries, inferInstance, hiid, hmom, hgeneral, ?_, ?_, ?_, ?_⟩
  · simpa only [hv0] using he
  · simpa only [hv0] using hc
  · simpa only [(hmom 0).2.2.2.1] using
      integrable_wlln powerTailProduct powerTailSample hiid
        ((hmom 0).2.1.integrable (by norm_num))
  · have hsq : isIID powerTailProduct (fun i ω => (powerTailSample i ω)^2) := by
      refine ⟨fun i => (hiid.1 i).pow_const 2, ?_, ?_⟩
      · exact hiid.2.1.comp (fun _ (x : ℝ) => x^2) (fun _ => by fun_prop)
      · intro i
        exact (hiid.2.2 i).comp (by fun_prop : Measurable (fun x : ℝ => x^2))
    simpa only [(hmom 0).2.2.2.2.2.1] using
      integrable_wlln powerTailProduct _ hsq (hmom 0).2.2.2.2.1

/-- Automatic L2 integrability of every continuous linear bridge image, with no
moment premise. Use ta18_cdf_linear_approx, the supplied Gaussian finite-coordinate
laws, and ta18_centered_gaussian_ae_limit with L.continuous.aemeasurable. Pull back
memLp_id_gaussianReal along the resulting map law by MemLp.comp_of_map. This is
the pre-moment part of cdf_bridge_linear_gaussian, about 50–80 lines. -/
def T57_L1 : Prop :=
  ∀ [MeasurableSpace CDFSpace] [BorelSpace CDFSpace]
    (P : Measure ℝ) [IsProbabilityMeasure P]
    (ν : Measure CDFSpace) [IsProbabilityMeasure ν],
    isCDFBridge (cdfAt P id) ν → ∀ L : CDFSpace →L[ℝ] ℝ,
    MemLp (fun h => L h) 2 ν

/-- Compact concentration inside an arbitrary almost-sure tangent set. First
enclose H-complement in a measurable null set, then approximate its complement
from inside by a closed set using MeasurableSet.exists_isClosed_sdiff_lt. Intersect
that closed subset of H with a compact set from tightness, budgeting eta/2 for
each complement. Handle eta=infinity directly. No closedness or measurability of
H is assumed. About 50–100 lines in this Borel metric space. -/
def T57_L2 : Prop :=
  ∀ [MeasurableSpace CDFSpace] [BorelSpace CDFSpace]
    (ν : Measure CDFSpace) [IsProbabilityMeasure ν] (H : Set CDFSpace),
    ν Hᶜ = 0 → IsTightMeasureSet ({ν} : Set (Measure CDFSpace)) →
    ∀ η : ℝ≥0∞, 0 < η →
      ∃ K : Set CDFSpace, IsCompact K ∧ K ⊆ H ∧ ν Kᶜ ≤ η

/-- Hadamard remainder in outer probability, using compact concentration rather
than a closed tangent set. Adapt delta_hadamard_remainder_CP verbatim, replacing
its call to delta_tight_compact_tangent by the supplied compact-concentration
premise. The remaining donors are delta_hadamard_uniform_compact, outer portmanteau,
and delta_outer_mass_eq. All perturbations are eventually in the domain. No
measurability of the empirical process or remainder is needed. About 80–130 lines. -/
def T57_L3 : Prop :=
  ∀ (Ω : Type u) [MeasurableSpace Ω]
    [MeasurableSpace CDFSpace] [BorelSpace CDFSpace]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (D H : Set CDFSpace) (θ : CDFSpace)
    (T : CDFSpace → ℝ) (L : CDFSpace →L[ℝ] ℝ),
    hadamardDerivative D H T θ L →
    ∀ (Z : ℕ → Ω → CDFSpace), (∀ᶠ n in atTop, ∀ ω, Z n ω ∈ D) →
    ∀ (r : ℕ → ℝ), Tendsto r atTop atTop →
    ∀ (ν : Measure CDFSpace) [IsProbabilityMeasure ν],
    (∀ η : ℝ≥0∞, 0 < η →
      ∃ K : Set CDFSpace, IsCompact K ∧ K ⊆ H ∧ ν Kᶜ ≤ η) →
    outerWeakConvergence μ (fun n ω => r n • (Z n ω - θ)) ν →
    convergesInProbability μ (fun n ω => r n * (T (Z n ω) - T θ) -
      L (r n • (Z n ω - θ))) 0

theorem T57_assembly (h1 : T57_L1) (h2 : T57_L2) (h3 : T57_L3.{u}) :
    T57WholeStatement.{u} := by
  intro Ω mΩ mK bK μ pμ X hiid
  obtain ⟨ν, hp, ht, hb, hw⟩ := TailA.cdf_donsker_supported μ X hiid
  have : IsProbabilityMeasure ν := hp
  refine ⟨ν, hp, ht, hb, hw, ?_⟩
  intro H ell T hνH hd _
  obtain ⟨L, hL, _⟩ := exists_extension_norm_eq H ell
  have hd' : hadamardDerivative cdfSet (H : Set CDFSpace) (cdfFunctionalValue T)
      (embedCDF (cdfAt μ (X 0))) L := by
    intro h hh t hn htpos ht0 hhn hD
    simpa only [hL ⟨h, hh⟩] using hd ⟨h, hh⟩ t hn htpos ht0 hhn hD
  have hD : ∀ᶠ n in atTop, ∀ ω, empiricalCDF X n ω ∈ cdfSet := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    intro ω
    have : IsProbabilityMeasure (empiricalLaw X n ω) :=
      CondP001cd_empirical_probability X hn ω
    exact CondP001cd_cdf_domain (empiricalLaw X n ω)
  have hr : Tendsto (fun n : ℕ => Real.sqrt n) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have hrem := h3 Ω μ cdfSet (H : Set CDFSpace) (embedCDF (cdfAt μ (X 0)))
    (cdfFunctionalValue T) L hd' (empiricalCDF X) hD (fun n => Real.sqrt n) hr ν
    (h2 ν (H : Set CDFSpace) hνH ht) hw
  let U : ℕ → Ω → ℝ := fun n ω =>
    L (Real.sqrt n • (empiricalCDF X n ω - embedCDF (cdfAt μ (X 0))))
  let V : ℕ → Ω → ℝ := fun n ω => Real.sqrt n *
    (cdfFunctionalValue T (empiricalCDF X n ω) -
      cdfFunctionalValue T (embedCDF (cdfAt μ (X 0))))
  have hw' := (TailA.outer_weak_donor_iff μ _ ν).mp hw
  have hU : AsymptoticStatistics.WeakConvergesOuter (fun _ => μ) U (ν.map L) :=
    hw'.continuous_comp L.continuous
  have hdist : ∀ δ > 0, Tendsto
      (fun n => μ.real {ω | δ ≤ dist (U n ω) (V n ω)}) atTop (nhds 0) := by
    intro δ hδ
    have heq (n : ℕ) : {ω | δ ≤ dist (U n ω) (V n ω)} =
        {ω | δ ≤ dist (V n ω - U n ω) 0} := by
      ext ω
      simp only [Real.dist_eq, sub_zero, abs_sub_comm]
    simpa only [heq, Measure.real, probability, U, V] using hrem δ hδ
  have hV := hU.slutsky_of_tendstoInOuterProbability_dist hdist
  have hcd : convergesInDistribution μ V (ν.map L) := TailA.outer_weak_real_CD μ V
    (ν.map L) ((TailA.outer_weak_donor_iff μ V (ν.map L)).mpr hV)
  have hF := CondP001cd_cdf_law μ (X 0) (hiid.1 0)
  have hb' : isCDFBridge (cdfAt (μ.map (X 0)) id) ν := by
    change AronowAudit.P001.IsCDFBridge (AronowAudit.P001.cdf (μ.map (X 0)) id) ν
    exact hF ▸ hb
  have hL2 := h1 (μ.map (X 0)) ν hb' L
  have hgauss := TailA.cdf_bridge_linear_gaussian (μ.map (X 0)) ν (hF ▸ hb) L hL2
  change ν.map L = gaussianReal 0 (variance (fun h => L h) ν).toNNReal at hgauss
  have hmean : expectation ν (fun h => L h) = 0 := by
    change (∫ h, L h ∂ν) = 0
    calc
      (∫ h, L h ∂ν) = ∫ x, id x ∂ν.map L :=
        (integral_map L.continuous.aemeasurable measurable_id.aestronglyMeasurable).symm
      _ = 0 := by rw [hgauss]; exact integral_id_gaussianReal
  refine ⟨L, hL, hL2, hmean, variance_nonneg _ _, hgauss, hcd, ?_, ?_, ?_⟩
  · intro hzero
    rw [hgauss]
    rw [hzero]
    simp
  · intro hv
    refine ⟨Real.sqrt (variance (fun h => L h) ν), Real.sqrt_pos.mpr hv,
      Real.sq_sqrt hv.le, ?_⟩
    have heq : gaussianReal 0
        ⟨(Real.sqrt (variance (fun h => L h) ν))^2, sq_nonneg _⟩ = ν.map L := by
      rw [hgauss]
      congr 1
      apply Subtype.ext
      simp only [Real.sq_sqrt hv.le, Real.toNNReal_of_nonneg hv.le]
      rfl
    rw [heq]
    exact hcd
  · intro L' hL'
    apply Measure.map_congr
    filter_upwards [ae_iff.mpr hνH] with h hh
    have hh' : h ∈ H := hh
    exact (hL' ⟨h, hh'⟩).trans (hL ⟨h, hh'⟩).symm

end
end SAP.P001c.WH.W1
