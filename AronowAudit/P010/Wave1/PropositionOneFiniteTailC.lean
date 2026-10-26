import AronowAudit.P010.Wave1.Lib.QuantileTransportTailC
import AronowAudit.P010.Wave1.Lib.CompatibleLawTailC

namespace AronowAudit.P010.Wave1

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology

set_option maxRecDepth 4096
set_option maxHeartbeats 800000

/-- Every observed passer law is a probability measure. -/
theorem tcFinite_passer_probability {K d : ℕ} (μ : Measure (State K d))
    (h : Assumptions μ) (a : Fin K) : IsProbabilityMeasure (passerLaw μ a) := by
  let tcFinite_original_probability := h.1
  have hp := passing_event_positive μ h a
  let N := (μ (passEvent ∩ armEvent a))⁻¹ • μ.restrict (passEvent ∩ armEvent a)
  let tcFinite_conditional_probability : IsProbabilityMeasure N :=
    cond_isProbabilityMeasure hp.ne'
  have he : N.map observedY = passerLaw μ a :=
    Measure.map_smul _ measurable_observedY.aemeasurable
  exact he ▸ (inferInstance : IsProbabilityMeasure (N.map observedY))

/-- The first moment of the conditional outcome law is its event mean. -/
theorem tcFinite_eventLaw_integral {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (f : Ω → ℝ) (hf : Measurable f) (E : Set Ω) :
    (∫ y, y ∂eventLaw μ f E) = eventMean μ f E := by
  unfold eventLaw eventMean
  rw [integral_smul_measure, integral_map hf.aemeasurable measurable_id'.aestronglyMeasurable]
  simp only [smul_eq_mul, ENNReal.toReal_inv, div_eq_mul_inv]
  exact mul_comm _ _

/-- An event with full probability has the whole-law mean. -/
theorem tcFinite_mean_full {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → ℝ)
    (E : Set Ω) (hE : MeasurableSet E) (hm : (μ E).toReal = 1) :
    eventMean μ f E = ∫ ω, f ω ∂μ := by
  have he : μ E = 1 := (ENNReal.toReal_eq_one_iff _).mp hm
  have ha : E =ᵐ[μ] univ :=
    ae_eq_univ.mpr ((mem_ae_iff_prob_eq_one hE).mpr he)
  rw [eventMean_congr_set μ f ha]
  simp [eventMean]

/-- An upper threshold of no greater mass maximizes the selected mean. -/
theorem tcFinite_threshold_upper {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) [IsProbabilityMeasure ν] (f : Ω → ℝ)
    (hf : Measurable f) (hi : Integrable f ν) (A : Set Ω)
    (hA : MeasurableSet A) (q : ℝ)
    (hp : 0 < ν.real {x | q ≤ f x})
    (hm : ν.real {x | q ≤ f x} ≤ ν.real A) :
    eventMean ν f A ≤ eventMean ν f {x | q ≤ f x} := by
  have hia : Integrable (fun x => f x-q) ν := hi.sub (integrable_const q)
  have he : {x | 0 ≤ f x-q} = {x | q ≤ f x} := by ext x; simp
  have hb := setIntegral_le_nonneg hA (hf.sub measurable_const).stronglyMeasurable hia
  change (∫ x in A, f x-q ∂ν) ≤ ∫ x in {x | 0 ≤ f x-q}, f x-q ∂ν at hb
  rw [he, integral_sub hi.integrableOn (integrable_const q),
    integral_sub hi.integrableOn (integrable_const q), setIntegral_const,
    setIntegral_const] at hb
  simp only [smul_eq_mul] at hb
  have hn : 0 ≤ ∫ x in {x | q ≤ f x}, f x-q ∂ν :=
    setIntegral_nonneg (measurableSet_le measurable_const hf)
      (fun x hx => sub_nonneg.mpr hx)
  rw [integral_sub hi.integrableOn (integrable_const q), setIntegral_const] at hn
  simp only [smul_eq_mul] at hn
  change (∫ x in A, f x ∂ν) / ν.real A ≤
    (∫ x in {x | q ≤ f x}, f x ∂ν) / ν.real {x | q ≤ f x}
  apply (div_le_div_iff₀ (lt_of_lt_of_le hp hm) hp).mpr
  nlinarith

/-- The corresponding lower threshold minimizes the selected mean. -/
theorem tcFinite_threshold_lower {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) [IsProbabilityMeasure ν] (f : Ω → ℝ)
    (hf : Measurable f) (hi : Integrable f ν) (A : Set Ω)
    (hA : MeasurableSet A) (q : ℝ)
    (hp : 0 < ν.real {x | f x ≤ q})
    (hm : ν.real {x | f x ≤ q} ≤ ν.real A) :
    eventMean ν f {x | f x ≤ q} ≤ eventMean ν f A := by
  have he : {x | -q ≤ -f x} = {x | f x ≤ q} := by ext x; simp
  have hh := tcFinite_threshold_upper ν (fun x => -f x) hf.neg hi.neg A hA (-q)
    (by simpa only [he] using hp) (by simpa only [he] using hm)
  rw [he] at hh
  simpa only [eventMean, integral_neg, neg_div, neg_le_neg_iff] using hh

/-- Any selection of mass at least t lies between the two t-tail means. -/
theorem tcFinite_tail_selection {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) [IsProbabilityMeasure ν] (f : Ω → ℝ)
    (hf : Measurable f) (hi : Integrable f ν)
    (hc : Atomless (ν.map f)) (A : Set Ω) (hA : MeasurableSet A)
    (t : ℝ) (ht : 0 < t) (ht1 : t ≤ 1) (hm : t ≤ ν.real A) :
    eventMean (ν.map f) id {y : ℝ | (y : EReal) ≤ quantile (ν.map f) t} ≤
        eventMean ν f A ∧
    eventMean ν f A ≤
      eventMean (ν.map f) id {y : ℝ | quantile (ν.map f) (1-t) ≤ (y : EReal)} := by
  let F := ν.map f
  have hB : MeasurableSet {y : ℝ | (y : EReal) ≤ quantile F t} :=
    measurableSet_le measurable_coe_real_ereal measurable_const
  have hC := upper_tail_proof_corrected_tail_measurable F (1-t)
  have hml : (ν {ω | (f ω : EReal) ≤ quantile F t}).toReal = t := by
    have hh := tcQuantile_lower_mass F hc ht ht1
    rw [Measure.map_apply hf hB] at hh
    exact hh
  have hmu : (ν {ω | quantile F (1-t) ≤ (f ω : EReal)}).toReal = t := by
    have hh := tcQuantile_upper_mass F hc (by linarith : 0 ≤ 1-t)
      (by linarith : 1-t < 1)
    rw [Measure.map_apply hf hC] at hh
    change (ν {ω | quantile F (1-t) ≤ (f ω : EReal)}).toReal = 1-(1-t) at hh
    simpa only [sub_sub_cancel] using hh
  rw [upper_tail_proof_corrected_eventMean_map ν f id hf measurable_id _ hB,
    upper_tail_proof_corrected_eventMean_map ν f id hf measurable_id _ hC]
  change eventMean ν f {ω | (f ω : EReal) ≤ quantile F t} ≤ eventMean ν f A ∧
    eventMean ν f A ≤ eventMean ν f {ω | quantile F (1-t) ≤ (f ω : EReal)}
  rcases lt_or_eq_of_le ht1 with ht1 | rfl
  · obtain ⟨l, hl, _⟩ := upper_tail_proof_corrected_quantile_finite F hc ht ht1
    obtain ⟨u, hu, _⟩ := upper_tail_proof_corrected_quantile_finite F hc
      (by linarith : 0 < 1-t) (by linarith : 1-t < 1)
    have hsl : {ω | (f ω : EReal) ≤ quantile F t} = {ω | f ω ≤ l} := by
      ext ω; simp [hl]
    have hsu : {ω | quantile F (1-t) ≤ (f ω : EReal)} = {ω | u ≤ f ω} := by
      ext ω; simp [hu]
    rw [hsl] at hml ⊢
    rw [hsu] at hmu ⊢
    exact ⟨tcFinite_threshold_lower ν f hf hi A hA l (by simpa only [measureReal_def, hml] using ht)
      (by simpa only [measureReal_def, hml] using hm),
      tcFinite_threshold_upper ν f hf hi A hA u (by simpa only [measureReal_def, hmu] using ht)
      (by simpa only [measureReal_def, hmu] using hm)⟩
  · have hmA : (ν A).toReal = 1 := le_antisymm measureReal_le_one hm
    rw [tcFinite_mean_full ν f A hA hmA,
      tcFinite_mean_full ν f {ω | (f ω : EReal) ≤ quantile F 1} (hf hB) hml,
      tcFinite_mean_full ν f {ω | quantile F (1-1) ≤ (f ω : EReal)} (hf hC) hmu]
    exact ⟨le_rfl, le_rfl⟩

/-- Focal passing rates are probabilities. -/
theorem tcFinite_rate_bounds {K d : ℕ} (μ : Measure (State K d))
    (h : Assumptions μ) (a : Fin K) : 0 < passingRate μ a ∧ passingRate μ a ≤ 1 := by
  let tcFinite_rate_probability := h.1
  refine ⟨h.2.2 a, ?_⟩
  rw [(nonzero_passing_corrected μ h.1 h.2.1).1 a]
  exact measureReal_le_one

/-- The positive Frechet lower mass is feasible in every arm. -/
theorem tcFinite_mass_feasible {K d : ℕ} (μ : Measure (State K d))
    (h : Assumptions μ) (a : Fin K) (hr : trimRatio μ a < 1) :
    let L := 1 - ∑ b : Fin K, (1-passingRate μ b)
    0 < L ∧ L ≤ 1 ∧ (∀ b, L ≤ passingRate μ b) ∧
    0 < 1-trimRatio μ a ∧ 1-trimRatio μ a ≤ 1 ∧
    L / passingRate μ a = 1-trimRatio μ a := by
  dsimp only
  have hid := trimming_mass_identity μ h.2.2 a
  have hs : 0 ≤ ∑ b : Fin K, (1-passingRate μ b) :=
    Finset.sum_nonneg fun b _ => sub_nonneg.mpr (tcFinite_rate_bounds μ h b).2
  have hL := hid.2.mp hr
  have hp := (tcFinite_rate_bounds μ h a).1
  have hr0 : 0 ≤ trimRatio μ a := by
    unfold trimRatio
    apply div_nonneg _ hp.le
    exact Finset.sum_nonneg fun b _ => by
      split_ifs
      · exact sub_nonneg.mpr (tcFinite_rate_bounds μ h b).2
      · exact le_rfl
  refine ⟨hL, by linarith, ?_, by linarith, by linarith, ?_⟩
  · intro b
    have hh : 1-passingRate μ b ≤ ∑ c : Fin K, (1-passingRate μ c) :=
      Finset.single_le_sum (fun c _ => sub_nonneg.mpr (tcFinite_rate_bounds μ h c).2)
        (Finset.mem_univ b)
    linarith
  · rw [← hid.1, mul_div_cancel_left₀ _ hp.ne']

/-- Validity for an arbitrary population law under the exact focal assumptions. -/
theorem tcFinite_validity {K d : ℕ} (μ : Measure (State K d))
    (h : Assumptions μ) (a : Fin K) (hA : 0 < μ alwaysPass)
    (hc : Atomless (passerLaw μ a))
    (hi : Integrable observedY (μ.restrict (passEvent ∩ armEvent a)))
    (hr : trimRatio μ a < 1) :
    lowerBound μ a ≤ eventMean μ (potentialY a) alwaysPass ∧
    eventMean μ (potentialY a) alwaysPass ≤ upperBound μ a := by
  let tcFinite_valid_probability := h.1
  let P := potentialPass (d := d) a
  let f := potentialY (d := d) a
  have hPA : (alwaysPass : Set (State K d)) ⊆ P := fun ω hω => hω a
  have hP : 0 < μ P := hA.trans_le (measure_mono hPA)
  let N := (μ P)⁻¹ • μ.restrict P
  let tcFinite_valid_conditional_probability : IsProbabilityMeasure N :=
    cond_isProbabilityMeasure hP.ne'
  have hf : Measurable f := measurable_potentialY a
  have hmap : N.map f = passerLaw μ a := by
    rw [Measure.map_smul _ hf.aemeasurable]
    exact conditional_law_consistency μ h a
  have hif : Integrable f N :=
    ((compatible_focal_integrable μ μ h ⟨h, hA, rfl⟩ a hi).1).smul_measure
      (ENNReal.inv_ne_top.mpr hP.ne')
  have hfeas := tcFinite_mass_feasible μ h a hr
  have hp := (tcFinite_rate_bounds μ h a).1
  have hmass : 1-trimRatio μ a ≤ N.real alwaysPass := by
    have he : N.real alwaysPass = (μ alwaysPass).toReal / passingRate μ a := by
      simp only [N, measureReal_def, Measure.smul_apply, smul_eq_mul,
        Measure.restrict_apply measurableSet_always, inter_eq_left.mpr hPA,
        ENNReal.toReal_mul, ENNReal.toReal_inv,
        (nonzero_passing_corrected μ h.1 h.2.1).1 a]
      ring
    rw [he, le_div_iff₀ hp, mul_comm]
    rw [(trimming_mass_identity μ h.2.2 a).1]
    exact always_passer_union_bound μ h
  have hh := tcFinite_tail_selection N f hf hif (by rwa [hmap])
    alwaysPass measurableSet_always (1-trimRatio μ a) hfeas.2.2.2.1
    hfeas.2.2.2.2.1 hmass
  have hmean : eventMean N f alwaysPass = eventMean μ f alwaysPass := by
    rw [upper_tail_proof_corrected_cond_mean μ f P alwaysPass hP measurableSet_always,
      inter_eq_left.mpr hPA]
  rw [hmap, hmean, sub_sub_cancel] at hh
  rw [(passer_tail_mean_formula μ h a).1, (passer_tail_mean_formula μ h a).2]
  exact hh

/-- Normalize a measurable outcome slice and realize it as the always-pass law. -/
theorem tcFinite_slice_attained {K d : ℕ} (μ : Measure (State K d))
    (h : Assumptions μ) (a : Fin K) (hr : trimRatio μ a < 1)
    (B : Set ℝ) (_hB : MeasurableSet B)
    (hm : ((passerLaw μ a) B).toReal = 1-trimRatio μ a) :
    eventMean (passerLaw μ a) id B ∈ identifiedMeans μ a := by
  let tcFinite_attain_probability := h.1
  let tcFinite_attain_passer_probability := tcFinite_passer_probability μ h a
  let F := passerLaw μ a
  let L := 1 - ∑ b : Fin K, (1-passingRate μ b)
  have hp := (tcFinite_rate_bounds μ h a).1
  obtain ⟨hL, hL1, hLp, ht, ht1, hratio⟩ := tcFinite_mass_feasible μ h a hr
  have hmass : F B = ENNReal.ofReal (1-trimRatio μ a) := by
    rw [← hm, ENNReal.ofReal_toReal (measure_ne_top F B)]
  have hFB : F B ≠ 0 := by rw [hmass]; exact (ENNReal.ofReal_pos.mpr ht).ne'
  let G := (F B)⁻¹ • F.restrict B
  let tcFinite_attain_slice_probability : IsProbabilityMeasure G :=
    cond_isProbabilityMeasure hFB
  have hscalar : ENNReal.ofReal L * (F B)⁻¹ = ENNReal.ofReal (passingRate μ a) := by
    have he : L = passingRate μ a * (1-trimRatio μ a) :=
      (trimming_mass_identity μ h.2.2 a).1.symm
    rw [he, ENNReal.ofReal_mul hp.le, hmass, mul_assoc,
      ENNReal.mul_inv_cancel (ENNReal.ofReal_pos.mpr ht).ne' ENNReal.ofReal_ne_top,
      mul_one]
  have hdom : ENNReal.ofReal L • G ≤ ENNReal.ofReal (passingRate μ a) • F := by
    dsimp only [G]
    rw [smul_smul, hscalar]
    exact smul_le_smul_left _ Measure.restrict_le_self
  obtain ⟨ν, hv, hνA, hνG⟩ := compatible_localized_law μ h a L hL hL1 hLp le_rfl G hdom
  refine ⟨ν, hv, ?_⟩
  calc
    eventMean ν (potentialY a) alwaysPass = ∫ y, y ∂G := by
      rw [← hνG, tcFinite_eventLaw_integral ν (potentialY a) (measurable_potentialY a)]
    _ = eventMean F id B := by
      simp only [G, eventMean, integral_smul_measure, smul_eq_mul,
        ENNReal.toReal_inv, div_eq_mul_inv, id_eq]
      exact mul_comm _ _

/-- All compatible laws have the same trimming ratio and the same bounds. -/
theorem tcFinite_compatible_bounds {K d : ℕ} (μ ν : Measure (State K d))
    (h : Assumptions μ) (hc : Compatible μ ν) (a : Fin K) :
    trimRatio ν a = trimRatio μ a ∧ lowerBound ν a = lowerBound μ a ∧
      upperBound ν a = upperBound μ a := by
  have hp : passingRate ν = passingRate μ := funext fun b =>
    (compatible_passer_invariants μ ν h hc b).1
  have hF := (compatible_passer_invariants μ ν h hc a).2
  have hr : trimRatio ν a = trimRatio μ a := by unfold trimRatio; rw [hp]
  refine ⟨hr, ?_, ?_⟩
  · rw [(passer_tail_mean_formula ν hc.1 a).1, (passer_tail_mean_formula μ h a).1, hr, hF]
  · rw [(passer_tail_mean_formula ν hc.1 a).2, (passer_tail_mean_formula μ h a).2, hr, hF]

/-- At zero trimming the exact extended endpoint conventions retain the
entire conditional passer law. -/
theorem tcFinite_zero_bounds {K d : ℕ} (μ : Measure (State K d))
    (h : Assumptions μ) (a : Fin K) (hc : Atomless (passerLaw μ a))
    (hr : trimRatio μ a = 0) :
    lowerBound μ a = eventMean μ observedY (passEvent ∩ armEvent a) ∧
    upperBound μ a = eventMean μ observedY (passEvent ∩ armEvent a) := by
  let tcFinite_zero_passer_probability := tcFinite_passer_probability μ h a
  have hl := (passer_tail_mean_formula μ h a).1
  have hu := (passer_tail_mean_formula μ h a).2
  rw [hr, sub_zero] at hl
  rw [hr] at hu
  have hmean : (∫ y, y ∂passerLaw μ a) =
      eventMean μ observedY (passEvent ∩ armEvent a) :=
    tcFinite_eventLaw_integral μ observedY measurable_observedY _
  constructor
  · rw [hl, tcFinite_mean_full _ id _
      (measurableSet_le measurable_coe_real_ereal measurable_const)
      (tcQuantile_lower_mass _ hc zero_lt_one le_rfl)]
    exact hmean
  · rw [hu]
    simpa [tailUpper, upper_tail_proof_corrected_quantile_zero, eventMean] using hmean

/-- The two actual outcome-tail means equal the interval quantile integrals. -/
theorem tcFinite_integral_formulas {K d : ℕ} (μ : Measure (State K d))
    (h : Assumptions μ) (a : Fin K) (hc : Atomless (passerLaw μ a))
    (hi : Integrable observedY (μ.restrict (passEvent ∩ armEvent a)))
    (hr : trimRatio μ a < 1) :
    (let L := 1 - ∑ b : Fin K, (1 - passingRate μ b)
     lowerBound μ a = passingRate μ a / L *
       ∫ u in (0 : ℝ)..(L / passingRate μ a), quantileReal (passerLaw μ a) u) ∧
    (let L := 1 - ∑ b : Fin K, (1 - passingRate μ b)
     upperBound μ a = passingRate μ a / L *
       ∫ u in (1 - L / passingRate μ a)..(1 : ℝ), quantileReal (passerLaw μ a) u) := by
  let tcFinite_integrals_probability := h.1
  let tcFinite_integrals_passer_probability := tcFinite_passer_probability μ h a
  let F := passerLaw μ a
  have hp := (tcFinite_rate_bounds μ h a).1
  have hf := tcFinite_mass_feasible μ h a hr
  have ht := hf.2.2.2.1
  have ht1 := hf.2.2.2.2.1
  have hratio := hf.2.2.2.2.2
  have hiF : Integrable id F := by
    unfold F passerLaw eventLaw
    apply Integrable.smul_measure _ (ENNReal.inv_ne_top.mpr
      (passing_event_positive μ h a).ne')
    exact (integrable_map_measure measurable_id.aestronglyMeasurable
      measurable_observedY.aemeasurable).mpr hi
  have htails := (quantile_tail_integrals F hc hiF).2 (1-trimRatio μ a) ht ht1
  have hscalar : (1-trimRatio μ a)⁻¹ =
      passingRate μ a / (1 - ∑ b : Fin K, (1-passingRate μ b)) := by
    rw [← (trimming_mass_identity μ h.2.2 a).1]
    field_simp [hp.ne', ht.ne']
  dsimp only
  constructor
  · rw [(passer_tail_mean_formula μ h a).1]
    unfold eventMean
    simp only [id_eq]
    rw [tcQuantile_lower_mass F hc ht ht1, htails.1, hratio,
      div_eq_mul_inv, mul_comm _ ((1-trimRatio μ a)⁻¹), hscalar]
  · rw [(passer_tail_mean_formula μ h a).2]
    unfold tailUpper eventMean
    simp only [id_eq]
    have hmass := tcQuantile_upper_mass F hc
      (by linarith : 0 ≤ 1-(1-trimRatio μ a)) (by linarith : 1-(1-trimRatio μ a) < 1)
    simp only [sub_sub_cancel] at htails hmass
    rw [hmass, htails.2, hratio, div_eq_mul_inv,
      mul_comm _ ((1-trimRatio μ a)⁻¹), hscalar]
    simp only [sub_sub_cancel]
    rfl

/-- The full corrected finite-branch Proposition 1, including sharpness. -/
theorem proposition_one_finite_proof {K d : ℕ} (μ : Measure (State K d))
    (h : Assumptions μ) (a : Fin K) (hA : 0 < μ alwaysPass)
    (hc : Atomless (passerLaw μ a))
    (hi : Integrable observedY (μ.restrict (passEvent ∩ armEvent a)))
    (hr : trimRatio μ a < 1) :
    lowerBound μ a ≤ eventMean μ (potentialY a) alwaysPass ∧
    eventMean μ (potentialY a) alwaysPass ≤ upperBound μ a ∧
    lowerBound μ a ∈ identifiedMeans μ a ∧ upperBound μ a ∈ identifiedMeans μ a ∧
    (∀ m ∈ identifiedMeans μ a, lowerBound μ a ≤ m ∧ m ≤ upperBound μ a) ∧
    passingRate μ a * (1 - trimRatio μ a) = 1 - ∑ b : Fin K, (1 - passingRate μ b) ∧
    ((trimRatio μ a < 1) ↔ 0 < 1 - ∑ b : Fin K, (1 - passingRate μ b)) ∧
    (trimRatio μ a = 0 → lowerBound μ a = eventMean μ observedY (passEvent ∩ armEvent a) ∧
      upperBound μ a = eventMean μ observedY (passEvent ∩ armEvent a)) ∧
    (let L := 1 - ∑ b : Fin K, (1 - passingRate μ b)
     lowerBound μ a = passingRate μ a / L *
       ∫ u in (0 : ℝ)..(L / passingRate μ a), quantileReal (passerLaw μ a) u) ∧
    (let L := 1 - ∑ b : Fin K, (1 - passingRate μ b)
     upperBound μ a = passingRate μ a / L *
       ∫ u in (1 - L / passingRate μ a)..(1 : ℝ), quantileReal (passerLaw μ a) u) := by
  let tcFinite_final_passer_probability := tcFinite_passer_probability μ h a
  have hvalid := tcFinite_validity μ h a hA hc hi hr
  have hf := tcFinite_mass_feasible μ h a hr
  have ht := hf.2.2.2.1
  have ht1 := hf.2.2.2.2.1
  have hl : lowerBound μ a ∈ identifiedMeans μ a := by
    rw [(passer_tail_mean_formula μ h a).1]
    exact tcFinite_slice_attained μ h a hr _
      (measurableSet_le measurable_coe_real_ereal measurable_const)
      (tcQuantile_lower_mass _ hc ht ht1)
  have hu : upperBound μ a ∈ identifiedMeans μ a := by
    rw [(passer_tail_mean_formula μ h a).2]
    exact tcFinite_slice_attained μ h a hr _
      (upper_tail_proof_corrected_tail_measurable _ _)
      (tcQuantile_upper_mass _ hc (by linarith) hr)
  have huniv : ∀ m ∈ identifiedMeans μ a, lowerBound μ a ≤ m ∧ m ≤ upperBound μ a := by
    rintro m ⟨ν, hv, rfl⟩
    have hb := tcFinite_compatible_bounds μ ν h hv a
    have hF := (compatible_passer_invariants μ ν h hv a).2
    have hbounds := tcFinite_validity ν hv.1 a hv.2.1 (by rwa [hF])
      (compatible_observed_integrable μ ν hv a hi) (by rwa [hb.1])
    rwa [hb.2.1, hb.2.2] at hbounds
  exact ⟨hvalid.1, hvalid.2, hl, hu, huniv,
    (trimming_mass_identity μ h.2.2 a).1, (trimming_mass_identity μ h.2.2 a).2,
    tcFinite_zero_bounds μ h a hc, (tcFinite_integral_formulas μ h a hc hi hr).1,
    (tcFinite_integral_formulas μ h a hc hi hr).2⟩

end AronowAudit.P010.Wave1
