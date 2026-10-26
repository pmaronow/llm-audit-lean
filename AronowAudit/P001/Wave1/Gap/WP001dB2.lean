import AronowAudit.P001.P001_Foundations

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology
noncomputable section
set_option maxHeartbeats 800000
set_option maxRecDepth 3000
namespace AronowAudit.P001.Wave1

/-- Density calculation for two normalized sections; the base measure need not be sigma finite. -/
lemma t8_section_kl {A : Type*} [MeasurableSpace A] (m : Measure A)
    (f g : A → ℝ) (hf : Measurable f) (hg : Measurable g)
    (hfn : ∀ a, 0 ≤ f a) (hgn : ∀ a, 0 ≤ g a)
    (hF : (∫⁻ a, ENNReal.ofReal (f a) ∂m) = 1)
    (hG : (∫⁻ a, ENNReal.ofReal (g a) ∂m) = 1)
    (hdom : ∀ᵐ a ∂m, 0 < f a → 0 < g a)
    (hi : Integrable (fun a => f a * Real.log (f a) - f a * Real.log (g a)) m) :
    InformationTheory.klDiv (m.withDensity (fun a => ENNReal.ofReal (f a)))
      (m.withDensity (fun a => ENNReal.ofReal (g a))) =
      ENNReal.ofReal (∫ a, f a * Real.log (f a) - f a * Real.log (g a) ∂m) ∧
    0 ≤ ∫ a, f a * Real.log (f a) - f a * Real.log (g a) ∂m := by
  let F := fun a => ENNReal.ofReal (f a)
  let G := fun a => ENNReal.ofReal (g a)
  let P := m.withDensity F
  let Q := m.withDensity G
  have hFm : Measurable F := hf.ennreal_ofReal
  have hGm : Measurable G := hg.ennreal_ofReal
  have hRm : Measurable (fun a => F a / G a) := hFm.div hGm
  have hP : IsProbabilityMeasure P := by
    constructor
    simpa only [P, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] using hF
  have hQ : IsProbabilityMeasure Q := by
    constructor
    simpa only [Q, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] using hG
  letI instT8SectionP : IsProbabilityMeasure P := hP
  letI instT8SectionQ : IsProbabilityMeasure Q := hQ
  have hrep : Q.withDensity (fun a => F a / G a) = P := by
    change (m.withDensity G).withDensity (fun a => F a / G a) = P
    rw [← withDensity_mul m hGm hRm]
    apply withDensity_congr_ae
    filter_upwards [hdom] with a ha
    change G a * (F a / G a) = F a
    by_cases hfa : 0 < f a
    · have hga : G a ≠ 0 := (ENNReal.ofReal_pos.mpr (ha hfa)).ne'
      exact ENNReal.mul_div_cancel hga (ENNReal.ofReal_ne_top)
    · have hz : F a = 0 := ENNReal.ofReal_eq_zero.mpr (le_of_not_gt hfa)
      simp [hz]
  have hac : P ≪ Q := by
    rw [← hrep]
    exact withDensity_absolutelyContinuous _ _
  have hrn : P.rnDeriv Q =ᵐ[P] fun a => F a / G a :=
    hac.ae_eq (by simpa only [hrep] using (Measure.rnDeriv_withDensity Q hRm))
  have hp : ∀ᵐ a ∂P, 0 < f a ∧ 0 < g a := by
    apply (ae_withDensity_iff hFm).mpr
    filter_upwards [hdom] with a ha hfa
    have hpos : 0 < f a := ENNReal.ofReal_pos.mp (pos_iff_ne_zero.mpr hfa)
    exact ⟨hpos, ha hpos⟩
  have hllr : llr P Q =ᵐ[P] fun a => Real.log (f a) - Real.log (g a) := by
    filter_upwards [hrn, hp] with a ha hb
    rw [llr, ha, ENNReal.toReal_div, ENNReal.toReal_ofReal (hfn a),
      ENNReal.toReal_ofReal (hgn a), Real.log_div hb.1.ne' hb.2.ne']
  have hint : Integrable (fun a => Real.log (f a) - Real.log (g a)) P := by
    apply (integrable_withDensity_iff hFm (ae_of_all m (fun a => ENNReal.ofReal_lt_top))).mpr
    simpa only [F, ENNReal.toReal_ofReal (hfn _), sub_mul, mul_sub, mul_comm] using hi
  have hllri : Integrable (llr P Q) P := hint.congr hllr.symm
  have hval : (∫ a, llr P Q a ∂P) =
      ∫ a, f a * Real.log (f a) - f a * Real.log (g a) ∂m := by
    rw [integral_congr_ae hllr,
      integral_withDensity_eq_integral_toReal_smul hFm (ae_of_all m (fun a => ENNReal.ofReal_lt_top))]
    simp only [F, ENNReal.toReal_ofReal (hfn _), smul_eq_mul, mul_sub]
  have hn := InformationTheory.integral_llr_add_sub_measure_univ_nonneg hac hllri
  have he := InformationTheory.klDiv_of_ac_of_integrable hac hllri
  simp only [measureReal_def, measure_univ, ENNReal.toReal_one, add_sub_cancel_right] at hn he
  exact ⟨by simpa only [hval] using he, by simpa only [hval] using hn⟩

/-- Finite averaged divergence and its entropy-minus-expectation identity. -/
lemma t8_finite_identity {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {K τ : ℕ} (X : Ω → Fin K → ℝ) (Y : Ω → ℝ)
    (hXY : Measurable (fun ω => (X ω, Y ω)))
    (νX : Measure (Fin K → ℝ)) [IsProbabilityMeasure νX]
    (κ : Measure ℝ) [SFinite κ] (f : ℝ → (Fin K → ℝ) → ℝ)
    (g : ℝ → (Fin K → ℝ) → (Fin τ → ℝ) → ℝ) (t : Fin τ → ℝ)
    (hf : Measurable (fun xy : (Fin K → ℝ) × ℝ => f xy.2 xy.1))
    (hg : Measurable (fun xy : (Fin K → ℝ) × ℝ => g xy.2 xy.1 t))
    (hfn : ∀ y x, 0 ≤ f y x) (hgn : ∀ y x, 0 ≤ g y x t)
    (hfnorm : ∀ x, (∫⁻ y, ENNReal.ofReal (f y x) ∂κ) = 1)
    (hgnorm : ∀ x, (∫⁻ y, ENNReal.ofReal (g y x t) ∂κ) = 1)
    (htrue : μ.map (fun ω => (X ω,Y ω)) =
      (νX.prod κ).withDensity (fun xy => ENNReal.ofReal (f xy.2 xy.1)))
    (hdom : ∀ᵐ xy ∂(νX.prod κ), 0 < f xy.2 xy.1 → 0 < g xy.2 xy.1 t)
    (hent : Integrable (fun xy : (Fin K → ℝ) × ℝ =>
      f xy.2 xy.1 * Real.log (f xy.2 xy.1)) (νX.prod κ))
    (hcross : Integrable (fun xy : (Fin K → ℝ) × ℝ =>
      f xy.2 xy.1 * Real.log (g xy.2 xy.1 t)) (νX.prod κ)) :
    averageKLExt νX κ f g t ≠ ∞ ∧
    (averageKLExt νX κ f g t).toReal =
      (∫ xy : (Fin K → ℝ) × ℝ, f xy.2 xy.1 * Real.log (f xy.2 xy.1) ∂(νX.prod κ)) -
        expectedLogLikelihood μ X Y g t := by
  let H := fun xy : (Fin K → ℝ) × ℝ =>
    f xy.2 xy.1 * Real.log (f xy.2 xy.1) - f xy.2 xy.1 * Real.log (g xy.2 xy.1 t)
  have hi : Integrable H (νX.prod κ) := hent.sub hcross
  have hsec : ∀ᵐ x ∂νX,
      InformationTheory.klDiv (κ.withDensity (fun y => ENNReal.ofReal (f y x)))
        (κ.withDensity (fun y => ENNReal.ofReal (g y x t))) =
        ENNReal.ofReal (∫ y, H (x,y) ∂κ) ∧ 0 ≤ ∫ y, H (x,y) ∂κ := by
    filter_upwards [hi.prod_right_ae, Measure.ae_ae_of_ae_prod hdom] with x hix hdx
    exact t8_section_kl κ (fun y => f y x) (fun y => g y x t)
      (hf.comp (measurable_const.prodMk measurable_id))
      (hg.comp (measurable_const.prodMk measurable_id))
      (fun y => hfn y x) (fun y => hgn y x) (hfnorm x) (hgnorm x) hdx hix
  have hD : averageKLExt νX κ f g t = ENNReal.ofReal (∫ xy, H xy ∂(νX.prod κ)) := by
    unfold averageKLExt
    rw [lintegral_congr_ae (hsec.mono (fun _ h => h.1)),
      ← ofReal_integral_eq_lintegral_ofReal hi.integral_prod_left (hsec.mono (fun _ h => h.2)),
      integral_integral hi]
  have hnonneg : 0 ≤ ∫ xy, H xy ∂(νX.prod κ) := by
    rw [← integral_integral (f := fun x y => H (x,y)) hi]
    exact integral_nonneg_of_ae (hsec.mono (fun _ h => h.2))
  have hM : expectedLogLikelihood μ X Y g t =
      ∫ xy : (Fin K → ℝ) × ℝ, f xy.2 xy.1 * Real.log (g xy.2 xy.1 t) ∂(νX.prod κ) := by
    unfold expectedLogLikelihood mean
    rw [← integral_map hXY.aemeasurable hg.log.aestronglyMeasurable, htrue,
      integral_withDensity_eq_integral_toReal_smul hf.ennreal_ofReal
        (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
    simp only [ENNReal.toReal_ofReal (hfn _ _), smul_eq_mul]
  refine ⟨by rw [hD]; exact ENNReal.ofReal_ne_top, ?_⟩
  rw [hD, ENNReal.toReal_ofReal hnonneg, hM]
  exact integral_sub hent hcross

theorem separated_averaged_kl_approximate_ml_consistency {Ω : Type*} [MeasurableSpace Ω]
  (μ : Measure Ω) [IsProbabilityMeasure μ] {K τ : ℕ}
  (X : ℕ → Ω → Fin K → ℝ) (Y : ℕ → Ω → ℝ)
  (hiid : IID μ (fun i ω => (X i ω,Y i ω)))
  (νX : Measure (Fin K → ℝ)) [IsProbabilityMeasure νX] (κ : Measure ℝ) [SFinite κ]
  (f : ℝ → (Fin K → ℝ) → ℝ)
  (g : ℝ → (Fin K → ℝ) → (Fin τ → ℝ) → ℝ)
  (hf : Measurable (fun xy : (Fin K → ℝ) × ℝ => f xy.2 xy.1))
  (hfn : ∀ y x, 0 ≤ f y x) (hfnorm : ∀ x, (∫⁻ y, ENNReal.ofReal (f y x) ∂κ)=1)
  (htrue : μ.map (fun ω => (X 0 ω,Y 0 ω)) =
    (νX.prod κ).withDensity (fun xy => ENNReal.ofReal (f xy.2 xy.1)))
  (Θ : Set (Fin τ → ℝ))
  (hg : ∀ t ∈ Θ, Measurable (fun xy : (Fin K → ℝ) × ℝ => g xy.2 xy.1 t))
  (hgn : ∀ t ∈ Θ, ∀ y x, 0 ≤ g y x t)
  (hgnorm : ∀ t ∈ Θ, ∀ x, (∫⁻ y, ENNReal.ofReal (g y x t) ∂κ)=1)
  (hdom : ∀ t ∈ Θ, ∀ᵐ xy ∂(νX.prod κ), 0 < f xy.2 xy.1 → 0 < g xy.2 xy.1 t)
  (hlog : ∀ t ∈ Θ, Integrable (fun ω => Real.log (g (Y 0 ω) (X 0 ω) t)) μ)
  (tstar : Fin τ → ℝ) (ht : tstar ∈ Θ)
  (hsep : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ t ∈ Θ,
    ε ≤ dist t tstar → expectedLogLikelihood μ (X 0) (Y 0) g t ≤
      expectedLogLikelihood μ (X 0) (Y 0) g tstar-δ)
  (that : ℕ → Ω → Fin τ → ℝ) (hm : ∀ n, Measurable (that n))
  (hthat : ∀ n ω, that n ω ∈ Θ)
  (e Δ : ℕ → Ω → ℝ) (hen : ∀ n ω, 0 ≤ e n ω)
  (he : CP μ e 0) (hΔ : CP μ Δ 0)
  (hbound : ∀ n ω t, t ∈ Θ →
    |sampleLogLikelihood X Y g n ω t-expectedLogLikelihood μ (X 0) (Y 0) g t| ≤ Δ n ω)
  (hmax : (∀ n ω t, t ∈ Θ →
    sampleLikelihood X Y g n ω t ≤ sampleLikelihood X Y g n ω (that n ω)) ∨
    (∀ n ω t, t ∈ Θ → sampleLogLikelihood X Y g n ω t-e n ω ≤
      sampleLogLikelihood X Y g n ω (that n ω))) :
  CP μ that tstar ∧
  ((Integrable (fun xy : (Fin K → ℝ) × ℝ =>
      f xy.2 xy.1*Real.log (f xy.2 xy.1)) (νX.prod κ) ∧
    ∀ t ∈ Θ, Integrable (fun xy : (Fin K → ℝ) × ℝ =>
      f xy.2 xy.1*Real.log (g xy.2 xy.1 t)) (νX.prod κ)) →
    ∀ t ∈ Θ, averageKLExt νX κ f g tstar ≤ averageKLExt νX κ f g t ∧
      (averageKLExt νX κ f g t = averageKLExt νX κ f g tstar → t=tstar))  := by
  have hp0 : ∀ᵐ ω ∂μ, 0 < g (Y 0 ω) (X 0 ω) tstar := by
    have hd : ∀ᵐ xy ∂(νX.prod κ).withDensity (fun xy => ENNReal.ofReal (f xy.2 xy.1)),
        0 < g xy.2 xy.1 tstar := by
      apply (ae_withDensity_iff hf.ennreal_ofReal).mpr
      filter_upwards [hdom tstar ht] with xy hxy hnz
      exact hxy (ENNReal.ofReal_pos.mp (pos_iff_ne_zero.mpr hnz))
    rw [← htrue] at hd
    exact (ae_map_iff (hiid.1 0).aemeasurable
      (measurableSet_lt measurable_const (hg tstar ht))).mp hd
  have hp := iid_positive_at_parameter μ X Y hiid g tstar (hg tstar ht) hp0
  have hopt : ∀ n, ∀ᵐ ω ∂μ,
      sampleLogLikelihood X Y g n ω tstar - e n ω ≤
        sampleLogLikelihood X Y g n ω (that n ω) := by
    intro n
    rcases hmax with hprod | hlogmax
    · filter_upwards [hp] with ω hω
      by_cases hn : n = 0
      · subst n
        simpa only [sampleLogLikelihood, sampleMean, Nat.cast_zero, Finset.range_zero,
          Finset.sum_empty, div_zero, zero_sub] using neg_nonpos.mpr (hen 0 ω)
      have htruth : 0 < sampleLikelihood X Y g n ω tstar :=
        Finset.prod_pos (fun i _ => hω i)
      have hcmp := hprod n ω tstar ht
      have hfit : 0 < sampleLikelihood X Y g n ω (that n ω) := htruth.trans_le hcmp
      have hfitFactors : ∀ i ∈ Finset.range n, 0 < g (Y i ω) (X i ω) (that n ω) := by
        intro i hi
        exact lt_of_le_of_ne (hgn _ (hthat n ω) _ _)
          (Ne.symm (Finset.prod_ne_zero_iff.mp hfit.ne' i hi))
      have hl := Real.log_le_log htruth hcmp
      unfold sampleLikelihood at hl
      rw [Real.log_prod (fun i _ => (hω i).ne'),
        Real.log_prod (fun i hi => (hfitFactors i hi).ne')] at hl
      have hd := div_le_div_of_nonneg_right hl (Nat.cast_nonneg n)
      exact (sub_le_self _ (hen n ω)).trans hd
    · exact ae_of_all _ (fun ω => hlogmax n ω tstar ht)
  constructor
  · intro ε hε
    obtain ⟨δ, hδ, hs⟩ := hsep ε hε
    have hlim : Tendsto (fun n : ℕ => prob μ {ω | δ/4 ≤ dist (Δ n ω) 0} +
        prob μ {ω | δ/2 ≤ dist (e n ω) 0}) atTop (nhds 0) := by
      simpa only [zero_add] using
        (hΔ (δ/4) (by positivity)).add (he (δ/2) (by positivity))
    have hb (n : ℕ) : prob μ {ω | ε ≤ dist (that n ω) tstar} ≤
        prob μ {ω | δ/4 ≤ dist (Δ n ω) 0} + prob μ {ω | δ/2 ≤ dist (e n ω) 0} := by
      have hm : μ {ω | ε ≤ dist (that n ω) tstar} ≤
          μ ({ω | δ/4 ≤ dist (Δ n ω) 0} ∪ {ω | δ/2 ≤ dist (e n ω) 0}) := by
        apply measure_mono_ae
        filter_upwards [hopt n] with ω hop
        intro hω
        have hg0 := hs (that n ω) (hthat n ω) hω
        have hgap := argmax_finite_gap _ (sampleLogLikelihood X Y g n ω)
          (that n ω) tstar (Δ n ω) (e n ω)
          (hbound n ω _ (hthat n ω)) (hbound n ω tstar ht) hop
        by_contra h
        simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_le,
          Real.dist_eq, sub_zero] at h
        have hdlt := (le_abs_self (Δ n ω)).trans_lt h.1
        have helt := (le_abs_self (e n ω)).trans_lt h.2
        linarith
      exact (ENNReal.toReal_mono (measure_ne_top μ _) hm).trans (measureReal_union_le _ _)
    exact squeeze_zero' (Eventually.of_forall (fun _ => ENNReal.toReal_nonneg))
      (Eventually.of_forall hb) hlim
  · intro hfinite
    have hid (t) (hmem : t ∈ Θ) := t8_finite_identity μ (X 0) (Y 0) (hiid.1 0)
      νX κ f g t hf (hg t hmem) hfn (hgn t hmem) hfnorm (hgnorm t hmem)
      htrue (hdom t hmem) hfinite.1 (hfinite.2 t hmem)
    have hstar := hid tstar ht
    intro t hmem
    have htid := hid t hmem
    by_cases heq : t = tstar
    · subst t
      exact ⟨le_rfl, fun _ => rfl⟩
    · obtain ⟨δ, hδ, hgap⟩ := hsep (dist t tstar) (dist_pos.mpr heq)
      have hstrict := hgap t hmem le_rfl
      have hreal : (averageKLExt νX κ f g tstar).toReal <
          (averageKLExt νX κ f g t).toReal := by
        rw [hstar.2, htid.2]
        linarith
      refine ⟨(ENNReal.toReal_le_toReal hstar.1 htid.1).mp hreal.le, ?_⟩
      intro h
      rw [h] at hreal
      exact False.elim (lt_irrefl _ hreal)

theorem normalized_true_model_unique_kl_target {K τ : ℕ} (νX : Measure (Fin K → ℝ)) [IsProbabilityMeasure νX]
  (κ : Measure ℝ) [SFinite κ]
  (g : ℝ → (Fin K → ℝ) → (Fin τ → ℝ) → ℝ)
  (Θ : Set (Fin τ → ℝ)) (θ tstar : Fin τ → ℝ) (hθ : θ ∈ Θ) (ht : tstar ∈ Θ)
  (hg : ∀ t ∈ Θ, Measurable (fun xy : (Fin K → ℝ) × ℝ => g xy.2 xy.1 t))
  (hgn : ∀ t ∈ Θ, ∀ y x, 0 ≤ g y x t)
  (hnorm : ∀ t ∈ Θ, ∀ x, (∫⁻ y, ENNReal.ofReal (g y x t) ∂κ) = 1)
  (hunique : ∀ t ∈ Θ,
    averageKLExt νX κ (fun y x => g y x θ) g tstar ≤
      averageKLExt νX κ (fun y x => g y x θ) g t ∧
    (averageKLExt νX κ (fun y x => g y x θ) g t =
      averageKLExt νX κ (fun y x => g y x θ) g tstar → t = tstar)) :
  averageKLExt νX κ (fun y x => g y x θ) g θ = 0 ∧
  tstar = θ ∧
  (∀ t ∈ Θ, averageKLExt νX κ (fun y x => g y x θ) g t = 0 ↔ t = θ)  := by
  obtain ⟨hz, heq⟩ := true_model_averaged_kl_zero νX κ g Θ θ tstar hθ ht hg hgn hnorm hunique
  refine ⟨hz, heq, ?_⟩
  intro t hmem
  constructor
  · intro htzero
    have hstar : averageKLExt νX κ (fun y x => g y x θ) g tstar = 0 := by
      simpa only [heq] using hz
    exact ((hunique t hmem).2 (htzero.trans hstar.symm)).trans heq
  · intro h; simpa only [h] using hz

end AronowAudit.P001.Wave1
