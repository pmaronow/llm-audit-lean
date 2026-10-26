import AronowAudit.P017.Wave1.PropositionOne.N2
import AronowAudit.P017.Wave1.PropositionOne.N5
import Mathlib.Probability.CentralLimitTheorem
import Mathlib.Probability.Independence.InfinitePi

/-! The complete uniform-effect IPW counterexample, including exact support,
finite-sample moments, and the obstruction for weights on the full data space. -/

set_option autoImplicit false

namespace AronowAudit.P017.Wave1

open AronowAudit.P017 MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal

noncomputable section

theorem t1_effect_law : ipwPopulation.map ipwEffect = uniform01 := by
  rw [PropositionOne.effect_eq_fst, PropositionOne.fst_law]

theorem t1_effect_interval :
    ∀ᵐ ω ∂ipwPopulation, 0 < ipwEffect ω ∧ ipwEffect ω < 1 := by
  have h : ∀ᵐ u ∂ipwPopulation.map ipwEffect, u ∈ Ioo (0 : ℝ) 1 := by
    rw [t1_effect_law]
    exact PropositionOne.uniform_mem
  exact ae_of_ae_map PropositionOne.n1_proof.1.aemeasurable h

theorem t1_support : effectSupport ipwPopulation ipwEffect = Icc 0 1 := by
  apply Set.Subset.antisymm
  · rw [effectSupport, t1_effect_law]
    exact Measure.support_subset_of_isClosed isClosed_Icc
      (PropositionOne.uniform_mem.mono fun _ h => ⟨h.1.le, h.2.le⟩)
  · rw [← closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)]
    exact closure_minimal PropositionOne.n2_proof Measure.isClosed_support

theorem t1_radius : effectRadius ipwPopulation ipwEffect = (1 / 2 : ℝ≥0∞) := by
  have hinf : supportInf (Icc (0 : ℝ) 1) = (0 : EReal) := by
    apply le_antisymm
    · exact sInf_le ⟨0, by norm_num, by simp⟩
    · apply le_sInf
      rintro _ ⟨x, hx, rfl⟩
      exact EReal.coe_le_coe hx.1
  have hsup : supportSup (Icc (0 : ℝ) 1) = (1 : EReal) := by
    apply le_antisymm
    · apply sSup_le
      rintro _ ⟨x, hx, rfl⟩
      exact EReal.coe_le_coe hx.2
    · exact le_sSup ⟨1, by norm_num, by simp⟩
  rw [effectRadius, t1_support, PropositionOne.n1_proof.2.2, hinf, hsup]
  have he : (1 : EReal) - ((1 / 2 : ℝ) : EReal) = ((1 / 2 : ℝ) : EReal) := by
    rw [← EReal.coe_one, ← EReal.coe_sub]
    norm_num
  rw [he]
  norm_num [EReal.real_coe_toENNReal, ENNReal.ofReal_div_of_pos]

theorem t1_effect_atom (a : ℝ) : pr ipwPopulation {ω | ipwEffect ω = a} = 0 := by
  have hz : uniform01 {a} = 0 := by
    rw [uniform01, Measure.restrict_apply (measurableSet_singleton a)]
    exact measure_mono_null inter_subset_left (measure_singleton a)
  unfold pr Measure.real
  change (ipwPopulation (ipwEffect ⁻¹' {a})).toReal = 0
  rw [← Measure.map_apply PropositionOne.n1_proof.1 (measurableSet_singleton a),
    t1_effect_law, hz, ENNReal.toReal_zero]

theorem t1_fair_ae (a b : ℝ) : ∀ᵐ x ∂fairPair a b, x = a ∨ x = b := by
  have ha : ∀ᵐ x ∂Measure.dirac a, x = a ∨ x = b := by simp [ae_dirac_eq]
  have hb : ∀ᵐ x ∂Measure.dirac b, x = a ∨ x = b := by simp [ae_dirac_eq]
  rw [fairPair, ae_add_measure_iff]
  exact ⟨Measure.ae_smul_measure ha (1 / 2 : ℝ≥0∞),
    Measure.ae_smul_measure hb (1 / 2 : ℝ≥0∞)⟩

theorem t1_good : ∀ᵐ ω ∂ipwPopulation,
    0 < ipwEffect ω ∧ ipwEffect ω < 1 ∧ |ipwSummand ω| < 4 := by
  have hg : ∀ᵐ ω ∂ipwPopulation,
      ω.1 ∈ Ioo (0 : ℝ) 1 ∧
        (ω.2.1 = -1 ∨ ω.2.1 = 1) ∧ (ω.2.2 = 0 ∨ ω.2.2 = 1) := by
    change ∀ᵐ ω ∂uniform01.prod ((fairPair (-1) 1).prod (fairPair 0 1)), _
    apply (Measure.ae_prod_iff_ae_ae (by measurability)).mpr
    filter_upwards [PropositionOne.uniform_mem] with u hu
    apply (Measure.ae_prod_iff_ae_ae (by measurability)).mpr
    filter_upwards [t1_fair_ae (-1) 1] with b hb
    filter_upwards [t1_fair_ae 0 1] with t ht
    exact ⟨hu, hb, ht⟩
  filter_upwards [hg, t1_effect_interval] with ω hω he
  refine ⟨he.1, he.2, ?_⟩
  rcases ω with ⟨u, b, t⟩
  rcases hω with ⟨⟨hu0, hu1⟩, hb, ht⟩
  simp only at hu0 hu1 hb ht
  rcases hb with rfl | rfl <;> rcases ht with rfl | rfl <;>
    simp only [ipwSummand, ipwObserved, ipwY1, ipwY0] <;>
    apply abs_lt.mpr <;> constructor <;> nlinarith

theorem t1_second_moment : (∫ ω, ipwSummand ω ^ 2 ∂ipwPopulation) = 14 / 3 := by
  have hv := variance_eq_sub PropositionOne.n5_proof.2.1
  rw [PropositionOne.n5_proof.2.2.1, PropositionOne.n5_proof.2.2.2] at hv
  simp only [Pi.pow_apply] at hv
  linarith

theorem t1_centered_moment :
    (∫ ω, (ipwSummand ω - 1 / 2) ^ 2 ∂ipwPopulation) = 53 / 12 := by
  have hv := variance_eq_integral (μ := ipwPopulation) PropositionOne.n5_proof.1.aemeasurable
  rw [PropositionOne.n5_proof.2.2.1, PropositionOne.n5_proof.2.2.2] at hv
  exact hv.symm

theorem t1_coordinate_law (i : ℕ) :
    IdentDistrib (fun s : ℕ → ℝ × (ℝ × ℝ) => ipwSummand (s i)) ipwSummand
      (iidSamples ipwPopulation) ipwPopulation := by
  have heval : IdentDistrib (fun s : ℕ → ℝ × (ℝ × ℝ) => s i) id
      (iidSamples ipwPopulation) ipwPopulation :=
    ⟨(measurable_pi_apply i).aemeasurable, measurable_id.aemeasurable, by
      rw [iidSamples,
        (measurePreserving_eval_infinitePi (fun _ : ℕ => ipwPopulation) i).map_eq,
        Measure.map_id]⟩
  exact heval.comp PropositionOne.n5_proof.1

theorem t1_independent :
    iIndepFun (fun i (s : ℕ → ℝ × (ℝ × ℝ)) => ipwSummand (s i))
      (iidSamples ipwPopulation) :=
  iIndepFun_infinitePi (fun _ => PropositionOne.n5_proof.1)

theorem t1_sample_moments (n : ℕ) (hn : 1 ≤ n) :
    populationMean (iidSamples ipwPopulation) (sampleMean ipwSummand n) = 1 / 2 ∧
    (∫ s, (sampleMean ipwSummand n s - 1 / 2) ^ 2 ∂iidSamples ipwPopulation) =
      53 / (12 * (n : ℝ)) := by
  let P := iidSamples ipwPopulation
  let X : ℕ → (ℕ → ℝ × (ℝ × ℝ)) → ℝ := fun i s => ipwSummand (s i)
  have hLp (i : ℕ) : MemLp (X i) 2 P :=
    (t1_coordinate_law i).memLp_iff.mpr PropositionOne.n5_proof.2.1
  have hmean (i : ℕ) : (∫ s, X i s ∂P) = 1 / 2 :=
    (t1_coordinate_law i).integral_eq.trans PropositionOne.n5_proof.2.2.1
  have hvar (i : ℕ) : variance (X i) P = 53 / 12 :=
    (t1_coordinate_law i).variance_eq.trans PropositionOne.n5_proof.2.2.2
  have hsum : (∫ s, ∑ i ∈ Finset.range n, X i s ∂P) = (n : ℝ) * (1 / 2) := by
    rw [integral_finsetSum _ (fun i _ => (hLp i).integrable (by norm_num))]
    simp [hmean]
  have hnR : (n : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_zero_of_lt (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hm : (∫ s, sampleMean ipwSummand n s ∂P) = 1 / 2 := by
    change (∫ s, (∑ i ∈ Finset.range n, X i s) / (n : ℝ) ∂P) = _
    rw [integral_div, hsum]
    field_simp
  refine ⟨hm, ?_⟩
  have hvsum : variance (fun s => ∑ i ∈ Finset.range n, X i s) P =
      (n : ℝ) * (53 / 12) := by
    have hv := IndepFun.variance_sum (s := Finset.range n) (fun i _ => hLp i)
      (fun i _ j _ hij => t1_independent.indepFun hij)
    simpa only [Finset.sum_fn, hvar, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul] using hv
  have hv : variance (sampleMean ipwSummand n) P = 53 / (12 * (n : ℝ)) := by
    change variance (fun s => (∑ i ∈ Finset.range n, X i s) / (n : ℝ)) P = _
    simp only [div_eq_mul_inv]
    rw [variance_mul_const, hvsum]
    field_simp
  have hmeas : Measurable (sampleMean ipwSummand n) := by
    have hXm (i : ℕ) :
        Measurable (fun s : ℕ → ℝ × (ℝ × ℝ) => ipwSummand (s i)) :=
      PropositionOne.n5_proof.1.comp (measurable_pi_apply i)
    unfold sampleMean
    fun_prop
  rw [variance_eq_integral hmeas.aemeasurable, hm] at hv
  exact hv

theorem t1_clt :
    TendstoInDistribution (fun n s => sqrtN n * (sampleMean ipwSummand n s - 1 / 2))
      atTop (fun x : ℝ => x) (fun _ => iidSamples ipwPopulation)
      (gaussianReal 0 (53 / 12)) := by
  let P := iidSamples ipwPopulation
  let X : ℕ → (ℕ → ℝ × (ℝ × ℝ)) → ℝ := fun i s => ipwSummand (s i)
  have hx : MemLp (X 0) 2 P :=
    (t1_coordinate_law 0).memLp_iff.mpr PropositionOne.n5_proof.2.1
  have hv : variance (X 0) P = (53 / 12 : ℝ) :=
    (t1_coordinate_law 0).variance_eq.trans PropositionOne.n5_proof.2.2.2
  have hm : (∫ s, X 0 s ∂P) = 1 / 2 :=
    (t1_coordinate_law 0).integral_eq.trans PropositionOne.n5_proof.2.2.1
  have hy : HasLaw id (gaussianReal 0 (variance (X 0) P).toNNReal)
      (gaussianReal 0 (53 / 12)) := by
    rw [hv]
    have hc : (53 / 12 : ℝ).toNNReal = (53 / 12 : ℝ≥0) := by
      apply NNReal.eq
      rw [Real.coe_toNNReal _ (by norm_num)]
      norm_num
    rw [hc]
    exact ⟨measurable_id.aemeasurable, Measure.map_id⟩
  have hc := tendstoInDistribution_inv_sqrt_mul_sum_sub hy hx t1_independent
    (fun i => (t1_coordinate_law i).trans (t1_coordinate_law 0).symm)
  refine hc.congr (fun n => ae_of_all _ fun s => ?_) (ae_of_all _ fun _ => rfl)
  rw [hm]
  change (Real.sqrt (n : ℝ))⁻¹ *
      ((∑ i ∈ Finset.range n, ipwSummand (s i)) - (n : ℝ) * (1 / 2)) =
    Real.sqrt (n : ℝ) * ((∑ i ∈ Finset.range n, ipwSummand (s i)) / (n : ℝ) - 1 / 2)
  by_cases hn : n = 0
  · simp [hn]
  · have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn
    have hs : Real.sqrt (n : ℝ) ≠ 0 := Real.sqrt_ne_zero'.mpr (by positivity)
    have hsq := Real.sq_sqrt (show (0 : ℝ) ≤ n by positivity)
    field_simp
    rw [hsq]

theorem t1_weight_interval (w : (ℝ × (ℝ × ℝ)) → ℝ) (hm : Measurable w)
    (hn : ∀ ω, 0 ≤ w ω) (hi : Integrable w ipwPopulation)
    (hp : 0 < ∫ ω, w ω ∂ipwPopulation) :
    0 < weightedMean ipwPopulation ipwEffect w ∧
      weightedMean ipwPopulation ipwEffect w < 1 := by
  have hprod : Integrable (fun ω => w ω * ipwEffect ω) ipwPopulation := by
    apply hi.mono' (hm.mul PropositionOne.n1_proof.1).aestronglyMeasurable
    filter_upwards [t1_effect_interval] with ω hω
    change ‖w ω * ipwEffect ω‖ ≤ w ω
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hn ω) hω.1.le)]
    exact mul_le_of_le_one_right (hn ω) hω.2.le
  have hnonneg : 0 ≤ᵐ[ipwPopulation] (fun ω => w ω * ipwEffect ω) := by
    filter_upwards [t1_effect_interval] with ω hω
    exact mul_nonneg (hn ω) hω.1.le
  have hpos : 0 < ∫ ω, w ω * ipwEffect ω ∂ipwPopulation := by
    apply lt_of_le_of_ne (integral_nonneg_of_ae hnonneg)
    intro hz
    have hae := (integral_eq_zero_iff_of_nonneg_ae hnonneg hprod).mp hz.symm
    have hwzero : w =ᵐ[ipwPopulation] 0 := by
      filter_upwards [hae, t1_effect_interval] with ω he hω
      exact (mul_eq_zero.mp he).resolve_right (ne_of_gt hω.1)
    have : (∫ ω, w ω ∂ipwPopulation) = 0 := by
      simpa using integral_congr_ae hwzero
    linarith
  exact ⟨div_pos hpos hp, unattainable_upper_endpoint ipwPopulation ipwEffect w
    hi hprod (ae_of_all _ hn) (t1_effect_interval.mono fun _ h => h.2) hp⟩

theorem t1_empirical_constant {Ω D : Type*} [MeasurableSpace D]
    (O : Ω → D) (n : ℕ) (hn : 1 ≤ n) (s : ℕ → Ω) (d : D)
    (hs : ∀ i ∈ Finset.range n, O (s i) = d) :
    empiricalObserved O n s = Measure.dirac d := by
  have he : (∑ i ∈ Finset.range n, Measure.dirac (O (s i))) =
      (n : ℝ≥0∞) • Measure.dirac d := by
    calc
      _ = ∑ i ∈ Finset.range n, Measure.dirac d :=
        Finset.sum_congr rfl (fun i hi => congrArg Measure.dirac (hs i hi))
      _ = _ := by
        simp only [Finset.sum_const, Finset.card_range]
        ext A hA
        simp [Measure.smul_apply, nsmul_eq_mul]
  have hn0 : (n : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast Nat.ne_zero_of_lt (lt_of_lt_of_le Nat.zero_lt_one hn)
  rw [empiricalObserved, he, smul_smul, one_div,
    ENNReal.inv_mul_cancel hn0 (by simp), one_smul]

theorem t1_not_representable (t : ℝ) (ht : t = 0 ∨ t = 1) :
    ¬ Representable ipwPopulation ipwEffect t := by
  rintro ⟨w, hw, he⟩
  have hb := t1_weight_interval w hw.1 hw.2.1 hw.2.2.1 hw.2.2.2.1
  rw [he] at hb
  rcases ht with rfl | rfl <;> linarith [hb.1, hb.2]

theorem uniform_ipw_counterexample_proof :
    Measurable ipwEffect ∧ Integrable ipwEffect ipwPopulation ∧
    populationMean ipwPopulation ipwEffect = 1 / 2 ∧
    effectSupport ipwPopulation ipwEffect = Icc 0 1 ∧
    effectRadius ipwPopulation ipwEffect = (1 / 2 : ℝ≥0∞) ∧
    0 < effectRadius ipwPopulation ipwEffect ∧
    pr ipwPopulation {ω | ipwEffect ω = 0} = 0 ∧
    pr ipwPopulation {ω | ipwEffect ω = 1} = 0 ∧
    (∀ᵐ ω ∂ipwPopulation, 0 < ipwEffect ω ∧ ipwEffect ω < 1 ∧ |ipwSummand ω| < 4) ∧
    populationMean ipwPopulation ipwSummand = 1 / 2 ∧
    (∫ ω, ipwSummand ω ^ 2 ∂ipwPopulation) = 14 / 3 ∧
    (∫ ω, (ipwSummand ω - 1 / 2) ^ 2 ∂ipwPopulation) = 53 / 12 ∧
    (∀ n : ℕ, 1 ≤ n →
      populationMean (iidSamples ipwPopulation) (sampleMean ipwSummand n) = 1 / 2 ∧
      (∫ s, (sampleMean ipwSummand n s - 1 / 2) ^ 2 ∂iidSamples ipwPopulation) =
        53 / (12 * (n : ℝ))) ∧
    TendstoInDistribution (fun n s => sqrtN n * (sampleMean ipwSummand n s - 1 / 2))
      atTop (fun x : ℝ => x) (fun _ => iidSamples ipwPopulation)
      (gaussianReal 0 (53 / 12)) ∧
    (∀ w : (ℝ × (ℝ × ℝ)) → ℝ, Measurable w → (∀ ω, 0 ≤ w ω) →
      Integrable w ipwPopulation → 0 < (∫ ω, w ω ∂ipwPopulation) →
      0 < weightedMean ipwPopulation ipwEffect w ∧ weightedMean ipwPopulation ipwEffect w < 1) ∧
    (∀ n : ℕ, 1 ≤ n →
      pr (iidSamples ipwPopulation) (ipwBadEvent (-1) n) = (1 / 4 : ℝ) ^ n ∧
      pr (iidSamples ipwPopulation) (ipwBadEvent 1 n) = (1 / 4 : ℝ) ^ n ∧
      0 < (1 / 4 : ℝ) ^ n ∧ Disjoint (ipwBadEvent (-1) n) (ipwBadEvent 1 n) ∧
      (∀ s ∈ ipwBadEvent (-1) n,
        (∀ i ∈ Finset.range n, ipwSummand (s i) = 2) ∧ sampleMean ipwSummand n s = 2 ∧
        clipTarget (populationMean ipwPopulation ipwEffect) (effectRadius ipwPopulation ipwEffect)
          (sampleMean ipwSummand n s) = 1 ∧
        empiricalObserved ipwObserved n s = Measure.dirac (0, -1) ∧
        ¬ Representable ipwPopulation ipwEffect
          (clipTarget (populationMean ipwPopulation ipwEffect) (effectRadius ipwPopulation ipwEffect)
            (sampleMean ipwSummand n s))) ∧
      (∀ s ∈ ipwBadEvent 1 n,
        (∀ i ∈ Finset.range n, ipwSummand (s i) = -2) ∧ sampleMean ipwSummand n s = -2 ∧
        clipTarget (populationMean ipwPopulation ipwEffect) (effectRadius ipwPopulation ipwEffect)
          (sampleMean ipwSummand n s) = 0 ∧
        empiricalObserved ipwObserved n s = Measure.dirac (0, 1) ∧
        ¬ Representable ipwPopulation ipwEffect
          (clipTarget (populationMean ipwPopulation ipwEffect) (effectRadius ipwPopulation ipwEffect)
            (sampleMean ipwSummand n s)))) := by
  refine ⟨PropositionOne.n1_proof.1, PropositionOne.n1_proof.2.1,
    PropositionOne.n1_proof.2.2, t1_support, t1_radius, ?_,
    t1_effect_atom 0, t1_effect_atom 1, t1_good, PropositionOne.n5_proof.2.2.1,
    t1_second_moment, t1_centered_moment, t1_sample_moments, t1_clt,
    t1_weight_interval, ?_⟩
  · rw [t1_radius]
    norm_num
  · intro n hn
    refine ⟨ipw_bad_event_probability (-1) (Or.inl rfl) n,
      ipw_bad_event_probability 1 (Or.inr rfl) n, by positivity,
      ipw_bad_events_disjoint n hn, ?_, ?_⟩
    · intro s hs
      have hx : sampleMean ipwSummand n s = 2 := by
        simpa using ipw_bad_event_estimator (-1) n hn s hs
      have hc : clipTarget (populationMean ipwPopulation ipwEffect)
          (effectRadius ipwPopulation ipwEffect) (sampleMean ipwSummand n s) = 1 := by
        rw [PropositionOne.n1_proof.2.2, t1_radius, hx]
        norm_num [clipTarget, clipReal]
      refine ⟨?_, hx, hc, ?_, ?_⟩
      · intro i hi
        rcases hs i hi with ⟨hB, hT⟩
        norm_num [ipwSummand, ipwObserved, ipwY0, ipwY1, hB, hT]
      · apply t1_empirical_constant ipwObserved n hn
        intro i hi
        rcases hs i hi with ⟨hB, hT⟩
        simp [ipwObserved, ipwY0, ipwY1, hB, hT]
      · rw [hc]
        exact t1_not_representable 1 (Or.inr rfl)
    · intro s hs
      have hx : sampleMean ipwSummand n s = -2 := by
        simpa using ipw_bad_event_estimator 1 n hn s hs
      have hc : clipTarget (populationMean ipwPopulation ipwEffect)
          (effectRadius ipwPopulation ipwEffect) (sampleMean ipwSummand n s) = 0 := by
        rw [PropositionOne.n1_proof.2.2, t1_radius, hx]
        norm_num [clipTarget, clipReal]
      refine ⟨?_, hx, hc, ?_, ?_⟩
      · intro i hi
        rcases hs i hi with ⟨hB, hT⟩
        norm_num [ipwSummand, ipwObserved, ipwY0, ipwY1, hB, hT]
      · apply t1_empirical_constant ipwObserved n hn
        intro i hi
        rcases hs i hi with ⟨hB, hT⟩
        simp [ipwObserved, ipwY0, ipwY1, hB, hT]
      · rw [hc]
        exact t1_not_representable 0 (Or.inl rfl)

end

end AronowAudit.P017.Wave1
