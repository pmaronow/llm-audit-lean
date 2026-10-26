import AronowAudit.P010.Wave1.Lib.CompatibleLawTailC
import AronowAudit.P010.Wave1.Lib.EssentialMeanTailC

namespace AronowAudit.P010.Wave1

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators

set_option maxHeartbeats 800000

/-- The observed focal passer law is a probability measure. -/
theorem tcElse_passer_probability {K d : ℕ} (μ : Measure (State K d))
    (h : Assumptions μ) (a : Fin K) : IsProbabilityMeasure (passerLaw μ a) := by
  letI tcElse_passer_original_probability := h.1
  exact tcElse_event_probability μ observedY measurable_observedY _
    (measurableSet_pass.inter (measurableSet_arm a)) (passing_event_positive μ h a)

/-- Any compatible always-passer law is an integrable probability law
absolutely continuous with respect to the fixed observed passer law. -/
theorem tcElse_compatible_mean_law {K d : ℕ} (μ ν : Measure (State K d))
    (h : Assumptions μ) (hv : Compatible μ ν) (a : Fin K)
    (hi : Integrable observedY (μ.restrict (passEvent ∩ armEvent a))) :
    IsProbabilityMeasure (eventLaw ν (potentialY a) alwaysPass) ∧
      eventLaw ν (potentialY a) alwaysPass ≪ passerLaw μ a ∧
      Integrable (id : ℝ → ℝ) (eventLaw ν (potentialY a) alwaysPass) := by
  letI tcElse_compatible_probability := hv.1.1
  have hp := (nonzero_passing_corrected ν hv.1.1 hv.1.2.1).2.mp hv.1.2.2 a
  have hsub : (alwaysPass : Set (State K d)) ⊆ potentialPass a := fun ω hω => hω a
  have hac := tcElse_event_ac_subset ν (potentialY a) (measurable_potentialY a)
    alwaysPass (potentialPass a) hsub hp
  rw [conditional_law_consistency ν hv.1 a,
    (compatible_passer_invariants μ ν h hv a).2] at hac
  exact ⟨tcElse_event_probability ν (potentialY a) (measurable_potentialY a)
    alwaysPass measurableSet_always hv.2.1, hac,
    tcElse_event_integrable ν (potentialY a) (measurable_potentialY a)
      alwaysPass hv.2.1 (compatible_focal_integrable μ ν h hv a hi).2⟩

/-- Universal endpoint bounds and finite-endpoint strictness for all
compatible laws, using only focal integrability and observed atomlessness. -/
theorem tcElse_compatible_mean_bounds {K d : ℕ} (μ ν : Measure (State K d))
    (h : Assumptions μ) (hv : Compatible μ ν) (a : Fin K)
    (hc : Atomless (μ.map observedY))
    (hi : Integrable observedY (μ.restrict (passEvent ∩ armEvent a))) :
    (passerInf μ a ≤ (eventMean ν (potentialY a) alwaysPass : EReal) ∧
      (eventMean ν (potentialY a) alwaysPass : EReal) ≤ passerSup μ a) ∧
    (∀ l : ℝ, passerInf μ a = (l : EReal) → l < eventMean ν (potentialY a) alwaysPass) ∧
    (∀ u : ℝ, passerSup μ a = (u : EReal) → eventMean ν (potentialY a) alwaysPass < u) := by
  obtain ⟨hp, hac, hint⟩ := tcElse_compatible_mean_law μ ν h hv a hi
  letI tcElse_mean_probability := hp
  have he := tcElse_event_integral ν (potentialY a) (measurable_potentialY a) alwaysPass
  refine ⟨?_, ?_, ?_⟩
  · simpa only [he, passerInf, passerSup] using
      tcElse_essential_mean_bounds (passerLaw μ a) _ hac hint
  · intro l hl
    simpa only [he] using tcElse_essential_mean_strict_lower (passerLaw μ a) _
      hac (passer_atomless μ a hc) hint l hl
  · intro u hu
    simpa only [he] using tcElse_essential_mean_strict_upper (passerLaw μ a) _
      hac (passer_atomless μ a hc) hint u hu

/-- In the else branch every positive measurable passer event can be
localized in a compatible population with positive always-passer mass. -/
theorem tcElse_localized_event {K d : ℕ} (μ : Measure (State K d))
    (h : Assumptions μ) (a : Fin K) (hr : 1 ≤ trimRatio μ a)
    (E : Set ℝ) (hE : MeasurableSet E) (hq : 0 < passerLaw μ a E) :
    eventMean (passerLaw μ a) id E ∈ identifiedMeans μ a := by
  classical
  letI tcElse_local_original_probability := h.1
  letI tcElse_local_passer_probability := tcElse_passer_probability μ h a
  let G := eventLaw (passerLaw μ a) id E
  letI tcElse_local_event_probability : IsProbabilityMeasure G :=
    tcElse_event_probability _ id measurable_id E hE hq
  let p := passingRate μ
  have hp (b : Fin K) : 0 < p b := h.2.2 b
  have hp1 (b : Fin K) : p b ≤ 1 := by
    change passingRate μ b ≤ 1
    rw [(nonzero_passing_corrected μ h.1 h.2.1).1 b]
    exact measureReal_le_one
  have hne : (Finset.univ : Finset (Fin K)).Nonempty := ⟨a, Finset.mem_univ a⟩
  let m : ℝ := Finset.univ.inf' hne p
  have hm : 0 < m := (Finset.lt_inf'_iff _).mpr fun b _ => hp b
  have hmp (b : Fin K) : m ≤ p b := Finset.inf'_le p (Finset.mem_univ b)
  have hqR : 0 < (passerLaw μ a E).toReal :=
    ENNReal.toReal_pos hq.ne' (measure_ne_top _ _)
  let α : ℝ := min m (p a * (passerLaw μ a E).toReal) / 2
  have hα0 : 0 < α := div_pos (lt_min hm (mul_pos (hp a) hqR)) (by norm_num)
  have hαm : α ≤ m := by
    have := min_le_left m (p a * (passerLaw μ a E).toReal)
    dsimp [α]
    linarith [lt_min hm (mul_pos (hp a) hqR)]
  have hαq : α ≤ p a * (passerLaw μ a E).toReal := by
    have := min_le_right m (p a * (passerLaw μ a E).toReal)
    dsimp [α]
    linarith [lt_min hm (mul_pos (hp a) hqR)]
  have hαp (b : Fin K) : α ≤ p b := hαm.trans (hmp b)
  have hL : 1 - ∑ b : Fin K, (1 - passingRate μ b) ≤ α := by
    have hmass := (trimming_mass_identity μ h.2.2 a).1
    have hn := mul_nonpos_of_nonneg_of_nonpos (hp a).le (sub_nonpos.mpr hr)
    linarith
  have hdom : ENNReal.ofReal α • G ≤ ENNReal.ofReal (p a) • passerLaw μ a := by
    have hc : ENNReal.ofReal α * (passerLaw μ a E)⁻¹ ≤ ENNReal.ofReal (p a) := by
      rw [← ENNReal.ofReal_toReal (measure_ne_top (passerLaw μ a) E),
        ← ENNReal.ofReal_inv_of_pos hqR, ← ENNReal.ofReal_mul hα0.le]
      apply ENNReal.ofReal_le_ofReal
      exact (div_le_iff₀ hqR).mpr hαq
    change ENNReal.ofReal α •
      ((passerLaw μ a E)⁻¹ • ((passerLaw μ a).restrict E).map id) ≤ _
    rw [Measure.map_id, smul_smul]
    intro B
    simp only [Measure.smul_apply, smul_eq_mul]
    exact mul_le_mul' hc (Measure.restrict_le_self B)
  obtain ⟨ν, hv, hνA, hνG⟩ := compatible_localized_law μ h a α hα0
    ((hαp a).trans (hp1 a)) hαp hL G hdom
  refine ⟨ν, hv, ?_⟩
  rw [← tcElse_event_integral ν (potentialY a) (measurable_potentialY a) alwaysPass,
    hνG]
  exact tcElse_event_integral (passerLaw μ a) id measurable_id E

/-- Bounded lower and upper slices give the exact greatest lower and least
upper bounds of all compatible means, without endpoint attainment. -/
theorem tcElse_endpoint_extrema {K d : ℕ} (μ : Measure (State K d))
    (h : Assumptions μ) (a : Fin K) (hc : Atomless (μ.map observedY))
    (hi : Integrable observedY (μ.restrict (passEvent ∩ armEvent a)))
    (hr : 1 ≤ trimRatio μ a) :
    IsGLB (extendedMeans μ a) (passerInf μ a) ∧
      IsLUB (extendedMeans μ a) (passerSup μ a) := by
  letI tcElse_extrema_original_probability := h.1
  letI tcElse_extrema_passer_probability := tcElse_passer_probability μ h a
  have hb (m : ℝ) (hm : m ∈ identifiedMeans μ a) :
      passerInf μ a ≤ (m : EReal) ∧ (m : EReal) ≤ passerSup μ a := by
    obtain ⟨ν, hv, he⟩ := hm
    simpa only [he] using (tcElse_compatible_mean_bounds μ ν h hv a hc hi).1
  constructor
  · constructor
    · rintro x ⟨m, hm, rfl⟩
      exact (hb m hm).1
    · intro b hbound
      by_contra hn
      obtain ⟨M, hM, hMb⟩ := EReal.exists_between_coe_real (lt_of_not_ge hn)
      obtain ⟨n, hn, hmean⟩ := tcElse_lower_bounded_tail (passerLaw μ a) M hM
      have hmem := tcElse_localized_event μ h a hr
        (Iio M ∩ Icc (-(n : ℝ)) (n : ℝ)) (measurableSet_Iio.inter measurableSet_Icc) hn
      have hext : ((eventMean (passerLaw μ a) id
          (Iio M ∩ Icc (-(n : ℝ)) (n : ℝ)) : ℝ) : EReal) ∈ extendedMeans μ a :=
        ⟨_, hmem, rfl⟩
      exact not_lt_of_ge (hbound hext)
        ((EReal.coe_lt_coe_iff.mpr hmean).trans hMb)
  · constructor
    · rintro x ⟨m, hm, rfl⟩
      exact (hb m hm).2
    · intro b hbound
      by_contra hn
      obtain ⟨M, hbM, hM⟩ := EReal.exists_between_coe_real (lt_of_not_ge hn)
      obtain ⟨n, hn, hmean⟩ := tcElse_upper_bounded_tail (passerLaw μ a) M hM
      have hmem := tcElse_localized_event μ h a hr
        (Ioi M ∩ Icc (-(n : ℝ)) (n : ℝ)) (measurableSet_Ioi.inter measurableSet_Icc) hn
      have hext : ((eventMean (passerLaw μ a) id
          (Ioi M ∩ Icc (-(n : ℝ)) (n : ℝ)) : ℝ) : EReal) ∈ extendedMeans μ a :=
        ⟨_, hmem, rfl⟩
      exact not_lt_of_ge (hbound hext)
        (hbM.trans (EReal.coe_lt_coe_iff.mpr hmean))

/-- Corrected Proposition 1, else branch: strict essential endpoint bounds,
sharp infimum and supremum, finite nonattainment, and infinite-tail criterion. -/
theorem proposition_one_else_proof {K d : ℕ} (μ : Measure (State K d))
    (h : Assumptions μ) (a : Fin K) (hA : 0 < μ alwaysPass)
    (hc : Atomless (μ.map observedY))
    (hi : Integrable observedY (μ.restrict (passEvent ∩ armEvent a)))
    (hr : 1 ≤ trimRatio μ a) :
    ((1 ≤ trimRatio μ a) ↔ (∑ b : Fin K, passingRate μ b) ≤ (K:ℝ)-1) ∧
    (passerInf μ a ≤ (eventMean μ (potentialY a) alwaysPass : EReal) ∧
      (eventMean μ (potentialY a) alwaysPass : EReal) ≤ passerSup μ a) ∧
    (∀ l : ℝ, passerInf μ a = (l : EReal) → l < eventMean μ (potentialY a) alwaysPass) ∧
    (∀ u : ℝ, passerSup μ a = (u : EReal) → eventMean μ (potentialY a) alwaysPass < u) ∧
    IsGLB (extendedMeans μ a) (passerInf μ a) ∧ IsLUB (extendedMeans μ a) (passerSup μ a) ∧
    (∀ l : ℝ, passerInf μ a = (l : EReal) → l ∉ identifiedMeans μ a) ∧
    (∀ u : ℝ, passerSup μ a = (u : EReal) → u ∉ identifiedMeans μ a) ∧
    ((IsGLB (extendedMeans μ a) ⊥ ∧ IsLUB (extendedMeans μ a) ⊤) ↔
      ((∀ M : ℝ, 0 < passerLaw μ a (Iio M)) ∧
       (∀ M : ℝ, 0 < passerLaw μ a (Ioi M)))) := by
  have hself : Compatible μ μ := ⟨h, hA, rfl⟩
  obtain ⟨hb, hl, hu⟩ := tcElse_compatible_mean_bounds μ μ h hself a hc hi
  obtain ⟨hglb, hlub⟩ := tcElse_endpoint_extrema μ h a hc hi hr
  refine ⟨else_branch_criterion μ h.2.2 a, hb, hl, hu, hglb, hlub, ?_, ?_, ?_⟩
  · intro l hle hm
    obtain ⟨ν, hv, he⟩ := hm
    have hs := (tcElse_compatible_mean_bounds μ ν h hv a hc hi).2.1 l hle
    rw [he] at hs
    exact lt_irrefl l hs
  · intro u hue hm
    obtain ⟨ν, hv, he⟩ := hm
    have hs := (tcElse_compatible_mean_bounds μ ν h hv a hc hi).2.2 u hue
    rw [he] at hs
    exact lt_irrefl u hs
  · constructor
    · rintro ⟨hbot, htop⟩
      exact (tcElse_infinite_endpoints_iff (passerLaw μ a)).mp
        ⟨hglb.unique hbot, hlub.unique htop⟩
    · intro ht
      obtain ⟨hbot, htop⟩ := (tcElse_infinite_endpoints_iff (passerLaw μ a)).mpr ht
      exact ⟨hbot ▸ hglb, htop ▸ hlub⟩

end AronowAudit.P010.Wave1

