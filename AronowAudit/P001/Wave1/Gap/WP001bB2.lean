import AronowAudit.P001.P001_Foundations

open MeasureTheory ProbabilityTheory Filter AronowAudit.P001
open scoped BigOperators ENNReal NNReal Topology

namespace AronowAudit.P001.Wave1
noncomputable section
local instance instDecidableWP001bB2 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 800000

theorem sample_product_mle_consistent {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
   {K τ : ℕ} (X : ℕ → Ω → Fin K → ℝ) (Y : ℕ → Ω → ℝ)
   (hiid : IID μ (fun i ω => (X i ω,Y i ω)))
   (νX : Measure (Fin K → ℝ)) [IsProbabilityMeasure νX] (κ : Measure ℝ) [SFinite κ]
   (g : ℝ → (Fin K → ℝ) → (Fin τ → ℝ) → ℝ) (Θ : Set (Fin τ → ℝ))
   (hc : IsCompact Θ) (θ : Fin τ → ℝ) (hθ : θ∈Θ)
   (hg : ∀ t∈Θ,Measurable (fun xy : (Fin K → ℝ) × ℝ => g xy.2 xy.1 t))
   (hnonneg : ∀ t∈Θ,∀ y x,0 ≤ g y x t)
   (hnorm : ∀ t∈Θ,∀ x,(∫⁻ y,ENNReal.ofReal (g y x t) ∂κ)=1)
   (htrue : μ.map (fun ω => (X 0 ω,Y 0 ω))=conditionalModelLaw νX κ g θ)
   (hlog : ∀ t∈Θ,Integrable (fun ω => Real.log (g (Y 0 ω) (X 0 ω) t)) μ)
   (hpos : ∀ t∈Θ,∀ᵐ ω ∂μ,0 < g (Y 0 ω) (X 0 ω) t)
   (hM : ContinuousOn (expectedLogLikelihood μ (X 0) (Y 0) g) Θ)
   (hunique : ∀ t∈Θ,expectedLogLikelihood μ (X 0) (Y 0) g t ≤ expectedLogLikelihood μ (X 0) (Y 0) g θ ∧
     (expectedLogLikelihood μ (X 0) (Y 0) g t=expectedLogLikelihood μ (X 0) (Y 0) g θ → t=θ))
   (T : (n : ℕ) → (Fin n → (Fin K → ℝ) × ℝ) → Fin τ → ℝ)
   (hTmeas : ∀ n, Measurable (T n))
   (hTvalid : ∀ n s, T n s ∈ Θ)
   (hTmax : ∀ n s t, t ∈ Θ →
     (∏ i, g (s i).2 (s i).1 t) ≤ ∏ i, g (s i).2 (s i).1 (T n s))
   (Δ : ℕ → Ω → ℝ) (hΔ : ∀ n ω t,t∈Θ →
     |sampleLogLikelihood X Y g n ω t-expectedLogLikelihood μ (X 0) (Y 0) g t| ≤ Δ n ω)
   (hΔmeas : ∀ n, Measurable (Δ n))
   (hlim : CP μ Δ 0) : CP μ (fun n ω => T n (fun i => (X i.val ω, Y i.val ω))) θ  := by
  let that := fun n ω => T n (fun i => (X i.val ω, Y i.val ω))
  have hmeas : ∀ n, Measurable (that n) := fun n =>
    (hTmeas n).comp (Measurable.of_eval (fun i : Fin n => hiid.1 i.val))
  apply product_maximum_likelihood_consistency μ X Y hiid νX κ g Θ hc θ hθ
    hg hnonneg hnorm htrue hlog hpos hM hunique that hmeas
    (fun n ω => hTvalid n _) ?_ Δ hΔ hlim
  intro n ω t ht
  have h := hTmax n (fun i => (X i.val ω, Y i.val ω)) t ht
  change (∏ i ∈ Finset.range n, g (Y i ω) (X i ω) t) ≤
    ∏ i ∈ Finset.range n, g (Y i ω) (X i ω) (that n ω)
  simpa only [← Fin.prod_univ_eq_prod_range] using h

/-- The finite-log Gibbs argument retains the possible deficit in ratio mass. -/
lemma trueLog_gibbs {E : Type*} [MeasurableSpace E]
    (P : Measure E) [IsProbabilityMeasure P] (r : E → ℝ)
    (hp : ∀ᵐ z ∂P, 0 < r z) (hi : Integrable r P)
    (hl : Integrable (fun z => Real.log (r z)) P)
    (hm : (∫ z, r z ∂P) ≤ 1) :
    (∫ z, Real.log (r z) ∂P) ≤ 0 ∧
    ((∫ z, Real.log (r z) ∂P) = 0 ↔ r =ᵐ[P] (fun _ => 1)) := by
  let d := fun z => r z - 1 - Real.log (r z)
  have hdi : Integrable d P := (hi.sub (integrable_const 1)).sub hl
  have hd : ∀ᵐ z ∂P, 0 ≤ d z := by
    filter_upwards [hp] with z hz
    exact sub_nonneg.mpr (Real.log_le_sub_one_of_pos hz)
  have hid : (∫ z, d z ∂P) = (∫ z, r z ∂P) - 1 - ∫ z, Real.log (r z) ∂P := by
    dsimp [d]
    rw [integral_sub (f := fun z => r z - 1) (hi.sub (integrable_const 1)) hl,
      integral_sub hi (integrable_const 1)]
    simp
  have hn := integral_nonneg_of_ae hd
  refine ⟨by linarith, ?_⟩
  constructor
  · intro he
    have hd0 : (∫ z, d z ∂P) = 0 := by linarith
    have hae := (integral_eq_zero_iff_of_nonneg_ae hd hdi).mp hd0
    filter_upwards [hp, hae] with z hz hdz
    change r z = 1
    by_contra hne
    have hs := Real.log_lt_sub_one_of_pos hz hne
    change r z - 1 - Real.log (r z) = 0 at hdz
    linarith
  · intro he
    calc
      (∫ z, Real.log (r z) ∂P) = ∫ z, (0 : ℝ) ∂P := integral_congr_ae (by
        filter_upwards [he] with z hz
        simp [hz])
      _ = 0 := integral_zero _ _

/-- On the true support, the density ratio has mass at most one. -/
lemma trueLog_ratio {E : Type*} [MeasurableSpace E]
    (base : Measure E) (f h : E → ℝ) (hf : Measurable f) (hh : Measurable h)
    (hfn : ∀ z, 0 ≤ f z) (hhn : ∀ z, 0 ≤ h z)
    (hhnorm : (∫⁻ z, ENNReal.ofReal (h z) ∂base) = 1)
    (hdom : ∀ᵐ z ∂base, 0 < f z → 0 < h z) :
    let P := base.withDensity (fun z => ENNReal.ofReal (f z))
    (∀ᵐ z ∂P, 0 < f z ∧ 0 < h z) ∧
    Integrable (fun z => h z / f z) P ∧
    (∫ z, h z / f z ∂P) ≤ 1 := by
  let P := base.withDensity (fun z => ENNReal.ofReal (f z))
  have hp : ∀ᵐ z ∂P, 0 < f z ∧ 0 < h z := by
    apply (ae_withDensity_iff hf.ennreal_ofReal).mpr
    filter_upwards [hdom] with z hz hne
    have hfp : 0 < f z := by simpa only [ne_eq, ENNReal.ofReal_eq_zero, not_le] using hne
    exact ⟨hfp, hz hfp⟩
  have hhi : Integrable h base :=
    (lintegral_ofReal_ne_top_iff_integrable hh.aestronglyMeasurable
      (ae_of_all _ hhn)).mp (by rw [hhnorm]; exact ENNReal.one_ne_top)
  have hhmean : (∫ z, h z ∂base) = 1 := by
    rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hhn) hh.aestronglyMeasurable,
      hhnorm, ENNReal.toReal_one]
  have hmul : ∀ z, 0 ≤ f z * (h z / f z) ∧ f z * (h z / f z) ≤ h z := by
    intro z
    by_cases hz : f z = 0
    · simp [hz, hhn z]
    · rw [mul_div_cancel₀ _ hz]
      exact ⟨hhn z, le_rfl⟩
  have hmi : Integrable (fun z => f z * (h z / f z)) base := by
    apply hhi.mono' (hf.mul (hh.div hf)).aestronglyMeasurable
    filter_upwards [] with z
    simpa only [Real.norm_eq_abs, Pi.mul_apply, Pi.div_apply, abs_of_nonneg (hmul z).1] using (hmul z).2
  have hfi : Integrable (fun z => h z / f z) P := by
    apply (integrable_withDensity_iff_integrable_smul' hf.ennreal_ofReal
      (ae_of_all _ (fun z => ENNReal.ofReal_lt_top))).mpr
    simpa only [ENNReal.toReal_ofReal (hfn _), smul_eq_mul] using hmi
  refine ⟨hp, hfi, ?_⟩
  change (∫ z, h z / f z ∂base.withDensity (fun z => ENNReal.ofReal (f z))) ≤ 1
  rw [integral_withDensity_eq_integral_toReal_smul hf.ennreal_ofReal
    (ae_of_all _ (fun z => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (hfn _), smul_eq_mul]
  exact (integral_mono hmi hhi (fun z => (hmul z).2)).trans_eq hhmean

lemma trueLog_density_gibbs {E : Type*} [MeasurableSpace E]
    (base : Measure E) (f h : E → ℝ) (hf : Measurable f) (hh : Measurable h)
    (hfn : ∀ z, 0 ≤ f z) (hhn : ∀ z, 0 ≤ h z)
    (hhnorm : (∫⁻ z, ENNReal.ofReal (h z) ∂base) = 1)
    (hdom : ∀ᵐ z ∂base, 0 < f z → 0 < h z)
    [IsProbabilityMeasure (base.withDensity (fun z => ENNReal.ofReal (f z)))]
    (hlf : Integrable (fun z => Real.log (f z))
      (base.withDensity (fun z => ENNReal.ofReal (f z))))
    (hlh : Integrable (fun z => Real.log (h z))
      (base.withDensity (fun z => ENNReal.ofReal (f z)))) :
    let P := base.withDensity (fun z => ENNReal.ofReal (f z))
    (∫ z, Real.log (h z) ∂P) ≤ (∫ z, Real.log (f z) ∂P) ∧
    ((∫ z, Real.log (h z) ∂P) = (∫ z, Real.log (f z) ∂P) ↔ h =ᵐ[P] f) := by
  let P := base.withDensity (fun z => ENNReal.ofReal (f z))
  obtain ⟨hp, hi, hm⟩ := trueLog_ratio base f h hf hh hfn hhn hhnorm hdom
  have hlogeq : (fun z => Real.log (h z / f z)) =ᵐ[P]
      (fun z => Real.log (h z) - Real.log (f z)) := by
    filter_upwards [hp] with z hz
    exact Real.log_div hz.2.ne' hz.1.ne'
  have hl : Integrable (fun z => Real.log (h z / f z)) P :=
    (hlh.sub hlf).congr hlogeq.symm
  have hmLog : (∫ z, Real.log (h z / f z) ∂P) =
      (∫ z, Real.log (h z) ∂P) - ∫ z, Real.log (f z) ∂P := by
    rw [integral_congr_ae hlogeq, integral_sub hlh hlf]
  obtain ⟨hle, heq⟩ := trueLog_gibbs P (fun z => h z / f z)
    (hp.mono (fun z hz => div_pos hz.2 hz.1)) hi hl hm
  refine ⟨by linarith, ?_⟩
  constructor
  · intro he
    have hr := heq.mp (by rw [hmLog, he, sub_self])
    filter_upwards [hp, hr] with z hz hrz
    exact (div_eq_one_iff_eq hz.1.ne').mp hrz
  · intro he
    exact integral_congr_ae (he.fun_comp Real.log)

theorem true_model_expected_log_maximum_with_support_zeros {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
   {K τ : ℕ} (X : Ω → Fin K → ℝ) (Y : Ω → ℝ) (hX : Measurable X) (hY : Measurable Y)
   (νX : Measure (Fin K → ℝ)) [IsProbabilityMeasure νX] (κ : Measure ℝ) [SFinite κ]
   (g : ℝ → (Fin K → ℝ) → (Fin τ → ℝ) → ℝ)
   (Θ : Set (Fin τ → ℝ)) (θ : Fin τ → ℝ) (hθ : θ∈Θ)
   (hgmeas : ∀ t∈Θ,Measurable (fun xy : (Fin K → ℝ) × ℝ => g xy.2 xy.1 t))
   (hgpos : ∀ t∈Θ,∀ y x,0 ≤ g y x t)
   (hgnorm : ∀ t∈Θ,∀ x,(∫⁻ y,ENNReal.ofReal (g y x t) ∂κ)=1)
   (htrue : μ.map (fun ω => (X ω,Y ω))=conditionalModelLaw νX κ g θ)
   (hdom : ∀ t∈Θ,∀ᵐ xy ∂(νX.prod κ),0 < g xy.2 xy.1 θ → 0 < g xy.2 xy.1 t)
   (hlog : ∀ t∈Θ,Integrable (fun ω => Real.log (g (Y ω) (X ω) t)) μ) :
   ∀ t∈Θ,expectedLogLikelihood μ X Y g t ≤ expectedLogLikelihood μ X Y g θ ∧
     (expectedLogLikelihood μ X Y g t=expectedLogLikelihood μ X Y g θ ↔
       (fun ω => g (Y ω) (X ω) t)=ᵐ[μ](fun ω => g (Y ω) (X ω) θ))  := by
  have hZ : Measurable (fun ω => (X ω, Y ω)) := hX.prodMk hY
  letI trueLog_probability : IsProbabilityMeasure
      ((νX.prod κ).withDensity (fun xy => ENNReal.ofReal (g xy.2 xy.1 θ))) :=
    conditional_model_probability νX κ g θ (hgmeas θ hθ) (hgnorm θ hθ)
  have hlogs (s) (hs : s ∈ Θ) : Integrable
      (fun xy : (Fin K → ℝ) × ℝ => Real.log (g xy.2 xy.1 s))
      (conditionalModelLaw νX κ g θ) := by
    rw [← htrue]
    exact (integrable_map_measure (hgmeas s hs).log.aestronglyMeasurable
      hZ.aemeasurable).mpr (hlog s hs)
  have hmeans (s) (hs : s ∈ Θ) : expectedLogLikelihood μ X Y g s =
      ∫ xy, Real.log (g xy.2 xy.1 s) ∂(conditionalModelLaw νX κ g θ) := by
    rw [← htrue]
    exact (integral_map hZ.aemeasurable (hgmeas s hs).log.aestronglyMeasurable).symm
  intro t ht
  have hnorm : (∫⁻ xy : (Fin K → ℝ) × ℝ,
      ENNReal.ofReal (g xy.2 xy.1 t) ∂(νX.prod κ)) = 1 := by
    rw [lintegral_prod _ (hgmeas t ht).ennreal_ofReal.aemeasurable]
    simp [hgnorm t ht]
  obtain ⟨hle, he⟩ := trueLog_density_gibbs (νX.prod κ)
    (fun xy => g xy.2 xy.1 θ) (fun xy => g xy.2 xy.1 t)
    (hgmeas θ hθ) (hgmeas t ht) (fun xy => hgpos θ hθ _ _)
    (fun xy => hgpos t ht _ _) hnorm (hdom t ht) (hlogs θ hθ) (hlogs t ht)
  refine ⟨?_, ?_⟩
  · rw [hmeans t ht, hmeans θ hθ]
    exact hle
  · rw [hmeans t ht, hmeans θ hθ]
    refine he.trans ?_
    change ((fun xy => g xy.2 xy.1 t) =ᵐ[conditionalModelLaw νX κ g θ]
      (fun xy => g xy.2 xy.1 θ)) ↔ _
    rw [← htrue]
    exact ae_map_iff hZ.aemeasurable (measurableSet_eq_fun (hgmeas t ht) (hgmeas θ hθ))


lemma bounds_transformed_ae_mean {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Z : ℕ → Ω → E) (hiid : IID μ Z)
    (g : E → ℝ) (hg : Measurable g) (C : ℝ)
    (hbound : ∀ᵐ ω ∂μ, |g (Z 0 ω)| ≤ C) :
    (∀ n, 0 < n → mean μ (sampleMean (fun i ω => g (Z i ω)) n) =
      mean μ (fun ω => g (Z 0 ω))) ∧
    CP μ (sampleMean (fun i ω => g (Z i ω))) (mean μ (fun ω => g (Z 0 ω))) := by
  have hi : IID μ (fun i ω => g (Z i ω)) :=
    ⟨fun i => hg.comp (hiid.1 i), hiid.2.1.comp (fun _ => g) (fun _ => hg),
      fun i => (hiid.2.2 i).comp hg⟩
  have h2 : MemLp (fun ω => g (Z 0 ω)) 2 μ :=
    MemLp.of_bound (hg.comp (hiid.1 0)).aestronglyMeasurable C
      (by simpa only [Real.norm_eq_abs] using hbound)
  exact ⟨fun n hn => (iid_sample_mean_finite_moments μ _ hi h2 n hn).1,
    weak_law_finite_variance μ _ hi h2⟩

lemma bounds_endpoint_formula {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Ys R : Ω → ℝ) (c : ℝ)
    (hR : Measurable R) (hbinary : ∀ᵐ ω ∂μ, R ω = 0 ∨ R ω = 1)
    (hi : Integrable (fun ω => missingEndpoint (Ys ω) (R ω) c) μ)
    (hp1 : 0 < prob μ {ω | R ω = 1}) :
    mean μ (fun ω => missingEndpoint (Ys ω) (R ω) c) =
      conditionalMeanAt μ R Ys 1 * prob μ {ω | R ω = 1} +
        c * prob μ {ω | R ω = 0} := by
  let A := {ω | R ω = 1}
  let B := {ω | R ω = 0}
  have hA : MeasurableSet A := hR (measurableSet_singleton 1)
  have hB : MeasurableSet B := hR (measurableSet_singleton 0)
  let u := A.indicator Ys
  let s := B.indicator (fun _ => (1 : ℝ))
  have hui : Integrable u μ := (hi.indicator hA).congr (by
    filter_upwards [] with ω
    by_cases hω : ω ∈ A
    · have hr : R ω = 1 := hω
      simp [u, A, hr, missingEndpoint]
    · simp [u, Set.indicator_of_notMem hω])
  have hsi : Integrable s μ := (integrable_const 1).indicator hB
  have he : (fun ω => missingEndpoint (Ys ω) (R ω) c) =ᵐ[μ]
      (fun ω => u ω + c * s ω) := by
    filter_upwards [hbinary] with ω hω
    rcases hω with hr | hr <;> simp [u, s, A, B, missingEndpoint, hr]
  have hs : (∫ ω, s ω ∂μ) = prob μ {ω | R ω = 0} := by
    simp [s, integral_indicator hB, integral_const, measureReal_def, prob, B]
  change (∫ ω, missingEndpoint (Ys ω) (R ω) c ∂μ) = _
  rw [integral_congr_ae he, integral_add hui (hsi.const_mul c), integral_const_mul, hs]
  dsimp [conditionalMeanAt, u]
  rw [integral_indicator hA, div_mul_cancel₀ _ hp1.ne']

theorem expected_value_bounds_paper_contract
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Y R : ℕ → Ω → ℝ)
    (hYmeas : ∀ i, Measurable (Y i)) (hRmeas : ∀ i, Measurable (R i))
    (a b : ℝ) (hab : a ≤ b)
    (hYbound : ∀ i, ∀ᵐ ω ∂μ, Y i ω ∈ Set.Icc a b)
    (hRbinary : ∀ i, ∀ᵐ ω ∂μ, R i ω = 0 ∨ R i ω = 1)
    (hSupportR : 0 < prob μ {ω | R 0 ω = 0} ∧ 0 < prob μ {ω | R 0 ω = 1})
    (hiid : IID μ (fun i ω => (censored (Y i ω) (R i ω), R i ω))) :
    let Ys := fun i ω => censored (Y i ω) (R i ω)
    let L := fun i ω => missingEndpoint (Ys i ω) (R i ω) a
    let U := fun i ω => missingEndpoint (Ys i ω) (R i ω) b
    let lower := conditionalMeanAt μ (R 0) (Ys 0) 1 * prob μ {ω | R 0 ω = 1}
      + a * prob μ {ω | R 0 ω = 0}
    let upper := conditionalMeanAt μ (R 0) (Ys 0) 1 * prob μ {ω | R 0 ω = 1}
      + b * prob μ {ω | R 0 ω = 0}
    mean μ (L 0) = lower ∧ mean μ (U 0) = upper ∧
    (∀ n, 0 < n → mean μ (sampleMean L n) = lower ∧ mean μ (sampleMean U n) = upper) ∧
    CP μ (sampleMean L) lower ∧ CP μ (sampleMean U) upper  := by
  let Ys := fun i ω => censored (Y i ω) (R i ω)
  let endpoint := fun c i ω => missingEndpoint (Ys i ω) (R i ω) c
  have hg (c : ℝ) : Measurable (fun yr : ℝ × ℝ => missingEndpoint yr.1 yr.2 c) := by
    unfold missingEndpoint
    fun_prop
  have hbound (c : ℝ) (hc : c ∈ Set.Icc a b) :
      ∀ᵐ ω ∂μ, |endpoint c 0 ω| ≤ max |a| |b| := by
    filter_upwards [hYbound 0, hRbinary 0] with ω hy hr
    rcases hr with hr | hr
    · simpa [endpoint, missingEndpoint, Ys, censored, hr] using
        abs_le_max_abs_abs hc.1 hc.2
    · simpa [endpoint, missingEndpoint, Ys, censored, hr] using
        abs_le_max_abs_abs hy.1 hy.2
  have hi (c : ℝ) (hc : c ∈ Set.Icc a b) : Integrable (endpoint c 0) μ := by
    apply (MemLp.of_bound ((hg c).comp (hiid.1 0)).aestronglyMeasurable
      (max |a| |b|) (by simpa only [Real.norm_eq_abs] using hbound c hc) :
      MemLp (endpoint c 0) 2 μ).integrable one_le_two
  have hfa := bounds_endpoint_formula μ (Ys 0) (R 0) a (hRmeas 0) (hRbinary 0)
    (hi a ⟨le_rfl, hab⟩) hSupportR.2
  have hfb := bounds_endpoint_formula μ (Ys 0) (R 0) b (hRmeas 0) (hRbinary 0)
    (hi b ⟨hab, le_rfl⟩) hSupportR.2
  obtain ⟨hEa, hCa⟩ := bounds_transformed_ae_mean μ _ hiid _ (hg a) _
    (hbound a ⟨le_rfl, hab⟩)
  obtain ⟨hEb, hCb⟩ := bounds_transformed_ae_mean μ _ hiid _ (hg b) _
    (hbound b ⟨hab, le_rfl⟩)
  dsimp only
  refine ⟨hfa, hfb, ?_, ?_, ?_⟩
  · intro n hn
    exact ⟨(hEa n hn).trans hfa, (hEb n hn).trans hfb⟩
  · rwa [hfa] at hCa
  · rwa [hfb] at hCb


end
end AronowAudit.P001.Wave1
