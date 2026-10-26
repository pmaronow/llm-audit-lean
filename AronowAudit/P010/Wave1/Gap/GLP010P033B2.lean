import AronowAudit.P010.P010_Population
import Mathlib.Probability.CDF

namespace AronowAudit.P010.Wave1

set_option maxRecDepth 4096
set_option maxHeartbeats 800000

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Classical Topology

/-! P010-T14: atomless quantile tails, extremal selection, and the potential upper bound. -/

/-- The singleton-mass argument proves CDF continuity. -/
lemma upper_tail_proof_corrected_cdf_continuous (F : Measure ℝ)
    [IsProbabilityMeasure F] (hc : Atomless F) : Continuous (cdf F) := by
  let instNullSingletonUpperTailCDF : NullSingletonClass F := ⟨hc⟩
  apply continuous_iff_continuousAt.mpr
  intro t
  have hm : Monotone (cdf F) := monotone_cdf F
  rw [hm.continuousAt_iff_leftLim_eq_rightLim]
  have hr : Function.rightLim (cdf F) t = cdf F t :=
    (hm.continuousWithinAt_Ioi_iff_rightLim_eq).1
      (((cdf F).right_continuous t).mono Set.Ioi_subset_Ici_self)
  have hl : Function.leftLim (cdf F) t ≤ cdf F t := hm.leftLim_le le_rfl
  have hg : cdf F t ≤ Function.leftLim (cdf F) t := by
    have h0 := (cdf F).measure_singleton t
    rw [measure_cdf, measure_singleton, eq_comm, ENNReal.ofReal_eq_zero, sub_nonpos] at h0
    exact h0
  rw [le_antisymm hl hg, hr]

lemma upper_tail_proof_corrected_quantile_zero (F : Measure ℝ) : quantile F 0 = ⊥ := by
  unfold quantile
  have hs : {x : EReal | 0 ≤ (F {y : ℝ | (y : EReal) ≤ x}).toReal} = univ := by
    ext x
    simp only [mem_setOf_eq, mem_univ, iff_true]
    exact ENNReal.toReal_nonneg
  rw [hs, sInf_univ]

lemma upper_tail_proof_corrected_quantile_finite (F : Measure ℝ)
    [IsProbabilityMeasure F] (hc : Atomless F) {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    ∃ c : ℝ, quantile F p = (c : EReal) ∧ cdf F c = p := by
  let C : Set ℝ := {x | p ≤ cdf F x}
  obtain ⟨b, hb⟩ := ((tendsto_cdf_atTop F).eventually_const_lt hp1).exists
  have hne : C.Nonempty := ⟨b, hb.le⟩
  obtain ⟨a, ha⟩ := ((tendsto_cdf_atBot F).eventually (eventually_lt_nhds hp)).exists
  have hbd : BddBelow C := by
    refine ⟨a, ?_⟩
    intro x hx
    by_contra hn
    have hx' : x ≤ a := (lt_of_not_ge hn).le
    have hca := (monotone_cdf F hx').trans_lt ha
    exact (not_lt_of_ge hx) hca
  let c : ℝ := sInf C
  have hcont := upper_tail_proof_corrected_cdf_continuous F hc
  have hcl : IsClosed C := isClosed_le continuous_const hcont
  have hcp : p ≤ cdf F c := hcl.csInf_mem hne hbd
  have hlt : ∀ x < c, cdf F x < p := by
    intro x hx
    apply lt_of_not_ge
    intro h
    exact (not_le_of_gt hx) (csInf_le hbd h)
  have hpc : cdf F c ≤ p := by
    have ht : Tendsto (cdf F) (𝓝[<] c) (𝓝 (cdf F c)) :=
      hcont.continuousAt.mono_left nhdsWithin_le_nhds
    exact le_of_tendsto ht (eventually_of_mem self_mem_nhdsWithin (fun x hx => (hlt x hx).le))
  refine ⟨c, ?_, le_antisymm hpc hcp⟩
  apply le_antisymm
  · apply sInf_le
    simpa only [mem_setOf_eq, EReal.coe_le_coe_iff, Set.Iic_def,
      cdf_eq_real, measureReal_def] using hcp
  · apply le_sInf
    intro z hz
    induction z using EReal.rec with
    | bot =>
      have he : {y : ℝ | (y : EReal) ≤ ⊥} = ∅ := by ext y; simp
      simp only [mem_setOf_eq, he, measure_empty, ENNReal.toReal_zero] at hz
      exact False.elim ((not_le_of_gt hp) hz)
    | coe x =>
      have hx : p ≤ cdf F x := by
        simpa only [mem_setOf_eq, EReal.coe_le_coe_iff, Set.Iic_def,
          cdf_eq_real, measureReal_def] using hz
      exact EReal.coe_le_coe_iff.mpr (csInf_le hbd hx)
    | top => exact le_top

lemma upper_tail_proof_corrected_tail_measurable (F : Measure ℝ) (p : ℝ) :
    MeasurableSet {y : ℝ | quantile F p ≤ (y : EReal)} :=
  measurableSet_le measurable_const measurable_coe_real_ereal

lemma upper_tail_proof_corrected_tail_mass (F : Measure ℝ) [IsProbabilityMeasure F]
    (hc : Atomless F) {p : ℝ} (hp : 0 ≤ p) (hp1 : p < 1) :
    (F {y : ℝ | quantile F p ≤ (y : EReal)}).toReal = 1 - p := by
  rcases hp.eq_or_lt with hp | hp
  · subst p
    simp [upper_tail_proof_corrected_quantile_zero]
  · obtain ⟨c, hq, hcp⟩ := upper_tail_proof_corrected_quantile_finite F hc hp hp1
    let instNullSingletonUpperTailMass : NullSingletonClass F := ⟨hc⟩
    have he : {y : ℝ | quantile F p ≤ (y : EReal)} = Ici c := by
      ext y
      simp [hq]
    rw [he, ← measureReal_def,
      measureReal_congr (Ioi_ae_eq_Ici' (hc c)).symm,
      ← compl_Iic, measureReal_compl measurableSet_Iic, probReal_univ,
      ← cdf_eq_real, hcp]

lemma upper_tail_proof_corrected_eventMean_map {Ω B : Type*}
    [MeasurableSpace Ω] [MeasurableSpace B] (μ : Measure Ω)
    (f : Ω → B) (g : B → ℝ) (hf : Measurable f) (hg : Measurable g)
    (E : Set B) (hE : MeasurableSet E) :
    eventMean (μ.map f) g E = eventMean μ (fun ω => g (f ω)) (f ⁻¹' E) := by
  unfold eventMean
  rw [setIntegral_map hE hg.aestronglyMeasurable hf.aemeasurable,
    Measure.map_apply hf hE]

lemma upper_tail_proof_corrected_true_mass (γ : Measure (ℝ × Bool))
    [IsProbabilityMeasure γ] {p : ℝ}
    (hp : (γ {ω | ω.2 = false}).toReal = p) :
    (γ {ω | ω.2 = true}).toReal = 1 - p := by
  have he : {ω : ℝ × Bool | ω.2 = true} = {ω : ℝ × Bool | ω.2 = false}ᶜ := by
    ext ω
    cases ω.2 <;> simp
  have hE : MeasurableSet {ω : ℝ × Bool | ω.2 = false} :=
    measurable_snd (measurableSet_singleton false)
  rw [he, ← measureReal_def, measureReal_compl hE, probReal_univ, measureReal_def, hp]

lemma upper_tail_proof_corrected_max (F : Measure ℝ) [IsProbabilityMeasure F]
    (hc : Atomless F) (hi : Integrable id F) {p : ℝ} (hp : 0 ≤ p) (hp1 : p < 1)
    (γ : Measure (ℝ × Bool)) (hγ : TailCoupling F p γ) :
    eventMean γ Prod.fst {ω | ω.2 = true} ≤ tailUpper F p := by
  have instProbabilityUpperTailCoupling : IsProbabilityMeasure γ := hγ.1
  have ht := upper_tail_proof_corrected_true_mass γ hγ.2.2
  have hE : MeasurableSet {ω : ℝ × Bool | ω.2 = true} :=
    measurable_snd (measurableSet_singleton true)
  have hfm : γ.map Prod.fst = F := hγ.2.1
  have him : Integrable id (γ.map Prod.fst) := by rw [hfm]; exact hi
  have hif : Integrable Prod.fst γ :=
    (integrable_map_measure measurable_id.aestronglyMeasurable measurable_fst.aemeasurable).mp him
  have hmean := upper_tail_proof_corrected_eventMean_map γ Prod.fst id
    measurable_fst measurable_id {y : ℝ | quantile F p ≤ (y : EReal)}
    (upper_tail_proof_corrected_tail_measurable F p)
  rw [hfm] at hmean
  change tailUpper F p = eventMean γ Prod.fst
    {ω | quantile F p ≤ (ω.1 : EReal)} at hmean
  rw [hmean]
  rcases hp.eq_or_lt with hp | hp
  · subst p
    have hm : γ {ω : ℝ × Bool | ω.2 = true} = 1 :=
      (ENNReal.toReal_eq_one_iff _).mp (by simpa using ht)
    have hae : {ω : ℝ × Bool | ω.2 = true} =ᵐ[γ] univ :=
      ae_eq_univ.mpr ((mem_ae_iff_prob_eq_one hE).mpr hm)
    rw [eventMean_congr_set γ Prod.fst hae]
    simp [upper_tail_proof_corrected_quantile_zero]
  · obtain ⟨c, hq, _⟩ := upper_tail_proof_corrected_quantile_finite F hc hp hp1
    have he : {ω : ℝ × Bool | quantile F p ≤ (ω.1 : EReal)} =
        {ω : ℝ × Bool | c ≤ ω.1} := by ext ω; simp [hq]
    rw [he]
    have hm : γ {ω : ℝ × Bool | ω.2 = true} = γ {ω : ℝ × Bool | c ≤ ω.1} := by
      apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp
      have htail := upper_tail_proof_corrected_tail_mass F hc hp.le hp1
      have hmap := Measure.map_apply (μ := γ) measurable_fst
        (upper_tail_proof_corrected_tail_measurable F p)
      rw [hfm] at hmap
      rw [hmap] at htail
      change (γ {ω : ℝ × Bool | quantile F p ≤ (ω.1 : EReal)}).toReal = 1-p at htail
      rw [he] at htail
      exact ht.trans htail.symm
    have hpos : 0 < γ {ω : ℝ × Bool | ω.2 = true} := by
      exact (ENNReal.toReal_pos_iff.mp (by rw [ht]; exact sub_pos.mpr hp1)).1
    exact (upper_tail_fixed_mass γ Prod.fst measurable_fst hif _ hE c hm hpos).2

lemma upper_tail_proof_corrected_graph (F : Measure ℝ) [IsProbabilityMeasure F]
    (hc : Atomless F) {p : ℝ} (hp : 0 ≤ p) (hp1 : p < 1) :
    let γ := F.map
      (fun y : ℝ => (y, decide (quantile F p ≤ (y : EReal))))
    TailCoupling F p γ ∧ eventMean γ Prod.fst {ω | ω.2 = true} = tailUpper F p := by
  let g : ℝ → ℝ × Bool := fun y => (y, decide (quantile F p ≤ (y : EReal)))
  have hB := upper_tail_proof_corrected_tail_measurable F p
  have hg : Measurable g := by
    apply measurable_id.prodMk
    apply measurable_to_bool
    simpa only [preimage, mem_singleton_iff, decide_eq_true_eq] using hB
  have hfalse : g ⁻¹' {ω : ℝ × Bool | ω.2 = false} =
      {y : ℝ | quantile F p ≤ (y : EReal)}ᶜ := by ext y; simp [g]
  have htrue : g ⁻¹' {ω : ℝ × Bool | ω.2 = true} =
      {y : ℝ | quantile F p ≤ (y : EReal)} := by ext y; simp [g]
  have hEf : MeasurableSet {ω : ℝ × Bool | ω.2 = false} :=
    measurable_snd (measurableSet_singleton false)
  have hEt : MeasurableSet {ω : ℝ × Bool | ω.2 = true} :=
    measurable_snd (measurableSet_singleton true)
  change TailCoupling F p (F.map g) ∧ _
  constructor
  · refine ⟨inferInstance, ?_, ?_⟩
    · rw [Measure.map_map measurable_fst hg]
      change F.map id = F
      exact Measure.map_id
    · rw [Measure.map_apply hg hEf,
        hfalse, ← measureReal_def, measureReal_compl hB, probReal_univ, measureReal_def,
        upper_tail_proof_corrected_tail_mass F hc hp hp1]
      ring
  · change eventMean (F.map g) Prod.fst {ω | ω.2 = true} = _
    rw [upper_tail_proof_corrected_eventMean_map F g Prod.fst hg measurable_fst _ hEt, htrue]
    rfl

lemma upper_tail_proof_corrected_monotone (F : Measure ℝ) [IsProbabilityMeasure F]
    (hc : Atomless F) (hi : Integrable id F) (p q : ℝ)
    (hp : 0 ≤ p) (hpq : p ≤ q) (hq1 : q < 1) : tailUpper F p ≤ tailUpper F q := by
  by_cases hpq' : p = q
  · subst q
    exact le_rfl
  have hq : 0 < q := lt_of_le_of_lt hp (lt_of_le_of_ne hpq hpq')
  obtain ⟨c, hcq, _⟩ := upper_tail_proof_corrected_quantile_finite F hc hq hq1
  have hcut : {y : ℝ | quantile F q ≤ (y : EReal)} = {y : ℝ | c ≤ y} := by
    ext y
    simp [hcq]
  have hpm := upper_tail_proof_corrected_tail_mass F hc hp (hpq.trans_lt hq1)
  have hqm := upper_tail_proof_corrected_tail_mass F hc hq.le hq1
  rw [hcut] at hqm
  have hg : Integrable (fun y : ℝ => y-c) F := hi.sub (integrable_const c)
  have hgm : StronglyMeasurable (fun y : ℝ => y-c) := by fun_prop
  have hzero : {y : ℝ | 0 ≤ y-c} = {y : ℝ | c ≤ y} := by ext y; simp
  have hb := setIntegral_le_nonneg (upper_tail_proof_corrected_tail_measurable F p) hgm hg
  have hii : Integrable (fun y : ℝ => y) F := hi
  rw [hzero, integral_sub hii.integrableOn (integrable_const c),
    integral_sub hii.integrableOn (integrable_const c), setIntegral_const, setIntegral_const] at hb
  simp only [smul_eq_mul, measureReal_def, hpm, hqm] at hb
  have hbase : c * (1-q) ≤ ∫ y in {y : ℝ | c ≤ y}, y ∂F := by
    have h := setIntegral_ge_of_const_le_real
      (measurableSet_le measurable_const measurable_id) (measure_ne_top F _)
      (f := fun y : ℝ => y) (s := {y : ℝ | c ≤ y})
      (fun y hy => hy) (hii.integrableOn : IntegrableOn (fun y : ℝ => y) {y : ℝ | c ≤ y} F)
    simpa only [measureReal_def, hqm] using h
  unfold tailUpper eventMean
  rw [hcut, hpm, hqm]
  simp only [id_eq]
  apply (div_le_div_iff₀ (sub_pos.mpr (hpq.trans_lt hq1)) (sub_pos.mpr hq1)).mpr
  nlinarith [mul_nonneg (sub_nonneg.mpr hpq) (sub_nonneg.mpr hbase),
    mul_le_mul_of_nonneg_right hb (sub_pos.mpr hq1).le]

lemma upper_tail_proof_corrected_selection {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) [IsProbabilityMeasure ν] (f : Ω → ℝ) (hf : Measurable f)
    (hi : Integrable f ν) (U : Set Ω) (hU : MeasurableSet U)
    (hc : Atomless (ν.map f)) (hp : (ν Uᶜ).toReal < 1) :
    eventMean ν f U ≤ tailUpper (ν.map f) (ν Uᶜ).toReal := by
  let g : Ω → ℝ × Bool := fun ω => (f ω, decide (ω ∈ U))
  have hg : Measurable g := by
    apply hf.prodMk
    apply measurable_to_bool
    simpa only [preimage, mem_singleton_iff, decide_eq_true_eq, setOf_mem_eq] using hU
  have hEt : MeasurableSet {ω : ℝ × Bool | ω.2 = true} :=
    measurable_snd (measurableSet_singleton true)
  have hEf : MeasurableSet {ω : ℝ × Bool | ω.2 = false} :=
    measurable_snd (measurableSet_singleton false)
  have hfalse : g ⁻¹' {ω : ℝ × Bool | ω.2 = false} = Uᶜ := by ext ω; simp [g]
  have htrue : g ⁻¹' {ω : ℝ × Bool | ω.2 = true} = U := by ext ω; simp [g]
  have hcouple : TailCoupling (ν.map f) (ν Uᶜ).toReal (ν.map g) := by
    refine ⟨inferInstance, ?_, ?_⟩
    · rw [Measure.map_map measurable_fst hg]
      rfl
    · rw [Measure.map_apply hg hEf, hfalse]
  have hiF : Integrable id (ν.map f) :=
    (integrable_map_measure measurable_id.aestronglyMeasurable hf.aemeasurable).mpr hi
  have hb := upper_tail_proof_corrected_max (ν.map f) hc hiF
    ENNReal.toReal_nonneg hp (ν.map g) hcouple
  rw [upper_tail_proof_corrected_eventMean_map ν g Prod.fst hg measurable_fst _ hEt,
    htrue] at hb
  exact hb

lemma upper_tail_proof_corrected_cond_mean {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → ℝ) (P U : Set Ω)
    (hP : 0 < μ P) (hU : MeasurableSet U) :
    eventMean ((μ P)⁻¹ • μ.restrict P) f U = eventMean μ f (U ∩ P) := by
  have hc : ((μ P)⁻¹).toReal ≠ 0 := by
    rw [ENNReal.toReal_inv]
    exact inv_ne_zero (ne_of_gt (ENNReal.toReal_pos hP.ne' (measure_ne_top μ P)))
  unfold eventMean
  rw [Measure.restrict_smul, integral_smul_measure, Measure.restrict_restrict hU,
    Measure.smul_apply, Measure.restrict_apply hU]
  simp only [smul_eq_mul, ENNReal.toReal_mul]
  exact mul_div_mul_left _ _ hc

lemma upper_tail_proof_corrected_potential_bound {K d : ℕ} (μ : Measure (State K d))
    (hp : IsProbabilityMeasure μ) (a : Fin K) (hA : 0 < μ alwaysPass)
    (hc : Atomless (eventLaw μ (potentialY a) (potentialPass a)))
    (hi : Integrable (potentialY a) (μ.restrict (potentialPass a)))
    (hr : potentialTrim μ a < 1) :
    eventMean μ (potentialY a) alwaysPass ≤
      tailUpper (eventLaw μ (potentialY a) (potentialPass a)) (potentialTrim μ a) := by
  have instProbabilityUpperTailBound : IsProbabilityMeasure μ := hp
  have hP : 0 < μ (potentialPass a) :=
    hA.trans_le (measure_mono (by rw [always_pass_focal a]; exact inter_subset_right))
  have hU : MeasurableSet (otherPass a : Set (State K d)) := by
    have he : (otherPass a : Set (State K d)) =
        ⋂ b : Fin K, ⋂ (_ : b ≠ a), potentialPass b := by
      ext ω
      simp [otherPass, potentialPass]
    rw [he]
    exact MeasurableSet.iInter fun b => MeasurableSet.iInter fun _ =>
      measurableSet_potentialPass b
  let ν : Measure (State K d) := (μ (potentialPass a))⁻¹ • μ.restrict (potentialPass a)
  have instProbabilityUpperTailBoundConditional : IsProbabilityMeasure ν :=
    cond_isProbabilityMeasure hP.ne'
  have hF : ν.map (potentialY a) = eventLaw μ (potentialY a) (potentialPass a) := by
    exact Measure.map_smul (μ (potentialPass a))⁻¹ (measurable_potentialY a).aemeasurable
  have instProbabilityUpperTailBoundLaw :
      IsProbabilityMeasure (eventLaw μ (potentialY a) (potentialPass a)) := hF ▸ inferInstance
  have hiν : Integrable (potentialY a) ν := hi.smul_measure (ENNReal.inv_ne_top.mpr hP.ne')
  have hiF : Integrable id (eventLaw μ (potentialY a) (potentialPass a)) := by
    rw [← hF]
    exact (integrable_map_measure measurable_id.aestronglyMeasurable
      (measurable_potentialY a).aemeasurable).mpr hiν
  have hcF : Atomless (ν.map (potentialY a)) := by rw [hF]; exact hc
  have hp0 : (ν (otherPass a)ᶜ).toReal =
      (μ ((otherPass a)ᶜ ∩ potentialPass a)).toReal / (μ (potentialPass a)).toReal := by
    simp only [ν, Measure.smul_apply, Measure.restrict_apply hU.compl, smul_eq_mul,
      ENNReal.toReal_mul, ENNReal.toReal_inv, div_eq_mul_inv, mul_comm]
  have hp0r : (ν (otherPass a)ᶜ).toReal ≤ potentialTrim μ a := by
    rw [hp0]
    exact other_arm_conditional_union_bound μ hp a hP
  have hsel := upper_tail_proof_corrected_selection ν (potentialY a)
    (measurable_potentialY a) hiν (otherPass a) hU hcF (hp0r.trans_lt hr)
  rw [hF, upper_tail_proof_corrected_cond_mean μ (potentialY a)
    (potentialPass a) (otherPass a) hP hU, ← always_pass_focal a] at hsel
  exact hsel.trans (upper_tail_proof_corrected_monotone _ hc hiF _ _
    ENNReal.toReal_nonneg hp0r hr)

theorem upper_tail_proof_corrected_proof {K d : ℕ} (μ : Measure (State K d))
    (hp : IsProbabilityMeasure μ) (a : Fin K) (hA : 0 < μ alwaysPass)
    (hc : Atomless (eventLaw μ (potentialY a) (potentialPass a)))
    (hi : Integrable (potentialY a) (μ.restrict (potentialPass a))) :
    (∀ p : ℝ, 0 ≤ p → p < 1 →
      (∀ γ : Measure (ℝ × Bool), TailCoupling (eventLaw μ (potentialY a) (potentialPass a)) p γ →
        eventMean γ Prod.fst {ω | ω.2 = true} ≤
          tailUpper (eventLaw μ (potentialY a) (potentialPass a)) p) ∧
      (let γ := (eventLaw μ (potentialY a) (potentialPass a)).map
          (fun y : ℝ => (y, decide (quantile (eventLaw μ (potentialY a) (potentialPass a)) p ≤ (y : EReal))))
       TailCoupling (eventLaw μ (potentialY a) (potentialPass a)) p γ ∧
       eventMean γ Prod.fst {ω | ω.2 = true} = tailUpper (eventLaw μ (potentialY a) (potentialPass a)) p)) ∧
    (∀ p q : ℝ, 0 ≤ p → p ≤ q → q < 1 →
      tailUpper (eventLaw μ (potentialY a) (potentialPass a)) p ≤
      tailUpper (eventLaw μ (potentialY a) (potentialPass a)) q) ∧
    (μ ((otherPass a)ᶜ ∩ potentialPass a)).toReal / (μ (potentialPass a)).toReal ≤ potentialTrim μ a ∧
    (potentialTrim μ a < 1 → eventMean μ (potentialY a) alwaysPass ≤
      tailUpper (eventLaw μ (potentialY a) (potentialPass a)) (potentialTrim μ a)) := by
  have instProbabilityUpperTailFinal : IsProbabilityMeasure μ := hp
  have hP : 0 < μ (potentialPass a) :=
    hA.trans_le (measure_mono (by rw [always_pass_focal a]; exact inter_subset_right))
  let ν : Measure (State K d) := (μ (potentialPass a))⁻¹ • μ.restrict (potentialPass a)
  have instProbabilityUpperTailFinalConditional : IsProbabilityMeasure ν :=
    cond_isProbabilityMeasure hP.ne'
  have hF : ν.map (potentialY a) = eventLaw μ (potentialY a) (potentialPass a) := by
    exact Measure.map_smul (μ (potentialPass a))⁻¹ (measurable_potentialY a).aemeasurable
  have instProbabilityUpperTailFinalLaw :
      IsProbabilityMeasure (eventLaw μ (potentialY a) (potentialPass a)) := hF ▸ inferInstance
  have hiν : Integrable (potentialY a) ν := hi.smul_measure (ENNReal.inv_ne_top.mpr hP.ne')
  have hiF : Integrable id (eventLaw μ (potentialY a) (potentialPass a)) := by
    rw [← hF]
    exact (integrable_map_measure measurable_id.aestronglyMeasurable
      (measurable_potentialY a).aemeasurable).mpr hiν
  refine ⟨?_, ?_, other_arm_conditional_union_bound μ hp a hP, ?_⟩
  · intro p hp0 hp1
    exact ⟨upper_tail_proof_corrected_max _ hc hiF hp0 hp1,
      upper_tail_proof_corrected_graph _ hc hp0 hp1⟩
  · exact upper_tail_proof_corrected_monotone _ hc hiF
  · exact upper_tail_proof_corrected_potential_bound μ hp a hA hc hi

end AronowAudit.P010.Wave1
