import AronowAudit.P001.P001_Foundations
import Mathlib.MeasureTheory.Function.FactorsThrough

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology

namespace AronowAudit.P001.Wave1
noncomputable section
set_option maxHeartbeats 800000

/-- A globally bounded measurable version of the binary conditional mean. -/
lemma t82_bounded_cef {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → E) (R : Ω → Bool)
    (hX : Measurable X) (hR : Measurable R) :
    ∃ p : E → ℝ, Measurable p ∧ (∀ x, p x ∈ Set.Icc (0 : ℝ) 1) ∧
      IsCEF μ X (fun ω => if R ω then (1 : ℝ) else 0) p := by
  classical
  let Z : Ω → ℝ := fun ω => if R ω then 1 else 0
  have hZm : Measurable Z := by
    exact measurable_const.ite (hR (measurableSet_singleton true)) measurable_const
  have hZi : Integrable Z μ := Integrable.of_bound hZm.aestronglyMeasurable 1
    (ae_of_all _ (fun ω => by cases hr : R ω <;> norm_num [Z, hr]))
  obtain ⟨h, hhm, hh⟩ :=
    (stronglyMeasurable_condExp (μ := μ) (m := MeasurableSpace.comap X inferInstance)
      (f := Z)).measurable.exists_eq_measurable_comp
  let p : E → ℝ := fun x => max 0 (min 1 (h x))
  have hpm : Measurable p := measurable_const.max (measurable_const.min hhm)
  have hpr (x : E) : p x ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩
  have hnonneg : 0 ≤ᵐ[μ] μ[Z | MeasurableSpace.comap X inferInstance] :=
    condExp_nonneg (ae_of_all _ (fun ω => by cases hr : R ω <;> norm_num [Z, hr]))
  have hle : μ[Z | MeasurableSpace.comap X inferInstance] ≤ᵐ[μ] (fun _ => (1 : ℝ)) := by
    simpa only [condExp_const hX.comap_le] using
      (condExp_mono (m := MeasurableSpace.comap X inferInstance) hZi (integrable_const 1)
        (ae_of_all μ (fun ω => by cases hr : R ω <;> norm_num [Z, hr])))
  have hpeq : (p ∘ X) =ᵐ[μ] μ[Z | MeasurableSpace.comap X inferInstance] := by
    filter_upwards [hnonneg, hle] with ω hn hl
    rw [hh] at hn hl ⊢
    change max 0 (min 1 (h (X ω))) = h (X ω)
    change 0 ≤ h (X ω) at hn
    change h (X ω) ≤ 1 at hl
    rw [min_eq_right hl, max_eq_right hn]
  have hpi : Integrable (p ∘ X) μ := Integrable.of_bound
    (hpm.comp hX).aestronglyMeasurable 1 (ae_of_all _ (fun ω => by
      change |p (X ω)| ≤ 1
      rw [abs_of_nonneg (hpr (X ω)).1]; exact (hpr (X ω)).2))
  refine ⟨p, hpm, hpr, hpm, hZi, hpi, ?_⟩
  intro A hA
  calc
    (∫ ω in X ⁻¹' A, Z ω ∂μ) =
        ∫ ω in X ⁻¹' A, μ[Z | MeasurableSpace.comap X inferInstance] ω ∂μ :=
      (setIntegral_condExp hX.comap_le hZi ⟨A, hA, rfl⟩).symm
    _ = ∫ ω in X ⁻¹' A, p (X ω) ∂μ :=
      setIntegral_congr_ae (hA.preimage hX) (hpeq.symm.mono (fun _ h _ => h))

/-- The complementary binary indicator has complementary conditional mean. -/
lemma t82_complement_cef {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → E) (R : Ω → Bool)
    (p : E → ℝ) (hp : IsCEF μ X (fun ω => if R ω then (1 : ℝ) else 0) p) :
    IsCEF μ X (fun ω => if R ω = false then (1 : ℝ) else 0) (fun x => 1-p x) := by
  have he : (fun ω => if R ω = false then (1 : ℝ) else 0) =
      (fun ω => 1 - (if R ω then (1 : ℝ) else 0)) := by
    funext ω; cases R ω <;> simp
  rw [he]
  refine ⟨measurable_const.sub hp.1, (integrable_const 1).sub hp.2.1,
    (integrable_const 1).sub hp.2.2.1, ?_⟩
  intro A hA
  change (∫ ω in X ⁻¹' A, 1 - (if R ω then (1 : ℝ) else 0) ∂μ) =
    ∫ ω in X ⁻¹' A, 1 - (p ∘ X) ω ∂μ
  rw [integral_sub (integrable_const 1) hp.2.1.integrableOn,
    integral_sub (integrable_const 1) hp.2.2.1.integrableOn, hp.2.2.2 A hA]
  rfl

/-- Convert a binary CEF event identity into its nonnegative disintegration identity. -/
lemma t82_event_disintegration {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → E) (R : Ω → Bool)
    (hX : Measurable X) (hR : Measurable R) (r : Bool) (p : E → ℝ)
    (hp : IsCEF μ X (fun ω => if R ω = r then (1 : ℝ) else 0) p)
    (hn : ∀ x, 0 ≤ p x) (hb : ∀ x, p x ≤ 1) (A : Set E) (hA : MeasurableSet A) :
    μ {ω | X ω ∈ A ∧ R ω = r} = ∫⁻ x in A, ENNReal.ofReal (p x) ∂(μ.map X) := by
  classical
  have hi : Integrable p (μ.map X) := Integrable.of_bound hp.1.aestronglyMeasurable 1
    (ae_of_all _ (fun x => by rw [Real.norm_eq_abs, abs_of_nonneg (hn x)]; exact hb x))
  rw [← ofReal_integral_eq_lintegral_ofReal hi.integrableOn (ae_of_all _ hn),
    setIntegral_map hA hp.1.aestronglyMeasurable hX.aemeasurable,
    ← hp.2.2.2 A hA]
  have hs : MeasurableSet {ω | R ω = r} := hR (measurableSet_singleton r)
  have he : (fun ω => if R ω = r then (1 : ℝ) else 0) =
      {ω | R ω = r}.indicator (fun _ => (1 : ℝ)) := by
    funext ω; simp [Set.indicator]
  rw [he, integral_indicator hs]
  simp only [integral_const, smul_eq_mul, mul_one, measureReal_def,
    Measure.restrict_restrict hs, Measure.restrict_apply MeasurableSet.univ,
    Set.univ_inter]
  have hset : {ω | R ω = r} ∩ X ⁻¹' A = {ω | X ω ∈ A ∧ R ω = r} := by
    ext ω; simp [and_comm]
  rw [hset, ENNReal.ofReal_toReal (measure_ne_top _ _)]

/-- A bounded response propensity and its normalized binary conditional law exist
for arbitrary measurable covariates. -/
theorem binary_response_conditional_propensity_exists {Ω E : Type*}
    [MeasurableSpace Ω] [MeasurableSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → E) (R : Ω → Bool)
    (hX : Measurable X) (hR : Measurable R)
    (hRpos : 0 < prob μ {ω | R ω = true} ∧ prob μ {ω | R ω = true} < 1) :
    ∃ p : E → ℝ, ∃ κ : E → Measure Bool,
      Measurable p ∧ (∀ x, p x ∈ Set.Icc (0 : ℝ) 1) ∧
      (∀ x, IsProbabilityMeasure (κ x)) ∧
      (∀ B : Set Bool, MeasurableSet B → Measurable (fun x => κ x B)) ∧
      (∀ A : Set E, MeasurableSet A → ∀ B : Set Bool, MeasurableSet B →
        μ {ω | X ω ∈ A ∧ R ω ∈ B} = ∫⁻ x in A, κ x B ∂(μ.map X)) ∧
      (∀ x, kernelPropensity κ x = p x ∧
        mean (κ x) (fun r => if r then (1 : ℝ) else 0) = p x) ∧
      IsCEF μ X (fun ω => if R ω then (1 : ℝ) else 0) p ∧
      (∀ m : E → ℝ, IsCEF μ X (fun ω => if R ω then (1 : ℝ) else 0) m →
        (m ∘ X) =ᵐ[μ] (p ∘ X)) ∧
      (∀ q : ℝ, q ∉ Set.Icc (0 : ℝ) 1 ↔ 1 < q ∨ q < 0) := by
  classical
  obtain ⟨p, hpm, hpr, hp⟩ := t82_bounded_cef μ X R hX hR
  let κ : E → Measure Bool := fun x =>
    ENNReal.ofReal (p x) • Measure.dirac true +
      ENNReal.ofReal (1-p x) • Measure.dirac false
  have hsum (x : E) : ENNReal.ofReal (p x) + ENNReal.ofReal (1-p x) = 1 := by
    rw [← ENNReal.ofReal_add (hpr x).1 (sub_nonneg.mpr (hpr x).2)]
    simp
  have hkapp (x : E) (B : Set Bool) : κ x B =
      ENNReal.ofReal (p x) * (if true ∈ B then 1 else 0) +
      ENNReal.ofReal (1-p x) * (if false ∈ B then 1 else 0) := by
    simp [κ, Measure.add_apply, Measure.smul_apply, Measure.dirac_apply', Set.indicator]
  have hkprob (x : E) : IsProbabilityMeasure (κ x) := by
    constructor
    simpa [hkapp] using hsum x
  have hkm (B : Set Bool) (_hB : MeasurableSet B) : Measurable (fun x => κ x B) := by
    simp_rw [hkapp]
    exact (hpm.ennreal_ofReal.mul_const _).add
      ((measurable_const.sub hpm).ennreal_ofReal.mul_const _)
  have hkt (x : E) : kernelPropensity κ x = p x := by
    simp [kernelPropensity, prob, hkapp, ENNReal.toReal_ofReal (hpr x).1]
  have htcef : IsCEF μ X (fun ω => if R ω = true then (1 : ℝ) else 0) p := by
    exact hp
  have hfcef := t82_complement_cef μ X R p hp
  have hcond : ∀ A : Set E, MeasurableSet A → ∀ B : Set Bool, MeasurableSet B →
      μ {ω | X ω ∈ A ∧ R ω ∈ B} = ∫⁻ x in A, κ x B ∂(μ.map X) := by
    intro A hA B hB
    by_cases ht : true ∈ B <;> by_cases hf : false ∈ B
    · have hBu : B = Set.univ := by ext r; cases r <;> simp_all
      subst B
      simp only [Set.mem_univ, and_true, measure_univ, hkapp, if_pos, mul_one, hsum]
      simp [Measure.map_apply hX hA, Set.preimage]
    · have hBt : B = {true} := by ext r; cases r <;> simp_all
      subst B
      simpa [hkapp] using
        t82_event_disintegration μ X R hX hR true p htcef
          (fun x => (hpr x).1) (fun x => (hpr x).2) A hA
    · have hBf : B = {false} := by ext r; cases r <;> simp_all
      subst B
      simpa [hkapp] using
        t82_event_disintegration μ X R hX hR false (fun x => 1-p x) hfcef
          (fun x => sub_nonneg.mpr (hpr x).2) (fun x => by linarith [(hpr x).1]) A hA
    · have hBe : B = ∅ := by ext r; cases r <;> simp_all
      subst B; simp
  have hbridge := propensity_range_correction μ X R hX hR κ hkprob hkm hcond
  refine ⟨p, κ, hpm, hpr, hkprob, hkm, hcond, ?_, hp, ?_, hbridge.2.2⟩
  · intro x
    exact ⟨hkt x, (hbridge.1 x).1.trans (hkt x)⟩
  · intro m hm
    exact (isCEF_condExp μ X hX _ m hm).trans (isCEF_condExp μ X hX _ p hp).symm

/-- Conditional cell means respect almost-everywhere changes in treatment. -/
lemma t88_cell_congr {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (Y D D' : Ω → ℝ) (he : D' =ᵐ[μ] D) (c : ℝ) :
    conditionalMeanAt μ D' Y c = conditionalMeanAt μ D Y c ∧
      prob μ {ω | D' ω = c} = prob μ {ω | D ω = c} := by
  have hs : {ω | D' ω = c} =ᵐ[μ] {ω | D ω = c} := by
    filter_upwards [he] with ω hω
    simp only [Set.mem_setOf_eq, hω]
  have hp : prob μ {ω | D' ω = c} = prob μ {ω | D ω = c} :=
    congrArg ENNReal.toReal (measure_congr hs)
  exact ⟨by unfold conditionalMeanAt; rw [setIntegral_congr_set hs, hp], hp⟩

/-- The endpoint integral formula only needs almost-sure binary treatment. -/
lemma t88_endpoint_formula_ae {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Y D : Ω → ℝ)
    (hYi : Integrable Y μ) (hD : Measurable D)
    (hbinary : ∀ᵐ ω ∂μ, D ω = 0 ∨ D ω = 1)
    (hp0 : 0 < prob μ {ω | D ω = 0}) (hp1 : 0 < prob μ {ω | D ω = 1})
    (a b : ℝ) :
    mean μ (fun ω => ateLower (Y ω) (D ω) a b) =
      conditionalMeanAt μ D Y 1 * prob μ {ω | D ω = 1} + a * prob μ {ω | D ω = 0} -
        (conditionalMeanAt μ D Y 0 * prob μ {ω | D ω = 0} + b * prob μ {ω | D ω = 1}) := by
  classical
  let D' : Ω → ℝ := fun ω => if D ω = 1 then 1 else 0
  have hDm : Measurable D' := measurable_const.ite (hD (measurableSet_singleton 1)) measurable_const
  have hDb (ω : Ω) : D' ω = 0 ∨ D' ω = 1 := by
    dsimp [D']; split_ifs <;> simp
  have he : D' =ᵐ[μ] D := by
    filter_upwards [hbinary] with ω hω
    rcases hω with hω | hω <;> simp [D', hω]
  have hc0 := t88_cell_congr μ Y D D' he 0
  have hc1 := t88_cell_congr μ Y D D' he 1
  have hf := bound_endpoint_formula μ Y D' hYi hDm hDb
    (hc0.2.symm ▸ hp0) (hc1.2.symm ▸ hp1) a b
  rw [hc0.1, hc1.1, hc0.2, hc1.2] at hf
  refine (integral_congr_ae ?_).trans hf
  filter_upwards [he] with ω hω
  simp only [hω]

/-- Almost-sure support suffices for the sharp causal endpoints, their entire
identified interval, and unbiased and consistent endpoint sample means. -/
theorem ate_sharp_endpoint_estimation_ae_support {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Y0 Y1 D : ℕ → Ω → ℝ)
    (h0 : ∀ i, Measurable (Y0 i)) (h1 : ∀ i, Measurable (Y1 i))
    (hD : ∀ i, Measurable (D i)) (a b : ℝ) (hab : a ≤ b)
    (hsupport : ∀ i, ∀ᵐ ω ∂μ,
      Y0 i ω ∈ Set.Icc a b ∧ Y1 i ω ∈ Set.Icc a b ∧ (D i ω = 0 ∨ D i ω = 1))
    (hpos : 0 < prob μ {ω | D 0 ω = 1} ∧ prob μ {ω | D 0 ω = 1} < 1)
    (hiid : IID μ (fun i ω => (observedOutcome (Y0 i ω) (Y1 i ω) (D i ω), D i ω))) :
    let Y := fun i ω => observedOutcome (Y0 i ω) (Y1 i ω) (D i ω)
    let L := fun i ω => ateLower (Y i ω) (D i ω) a b
    let U := fun i ω => ateUpper (Y i ω) (D i ω) a b
    let p := prob μ {ω | D 0 ω = 1}
    let ℓ := conditionalMeanAt μ (D 0) (Y 0) 1*p + a*(1-p) -
      (conditionalMeanAt μ (D 0) (Y 0) 0*(1-p) + b*p)
    let u := conditionalMeanAt μ (D 0) (Y 0) 1*p + b*(1-p) -
      (conditionalMeanAt μ (D 0) (Y 0) 0*(1-p) + a*p)
    mean μ (L 0) = ℓ ∧ mean μ (U 0) = u ∧ u-ℓ = b-a ∧
    mean μ (fun ω => Y1 0 ω - Y0 0 ω) ∈ Set.Icc ℓ u ∧
    (∀ t ∈ Set.Icc ℓ u, ∃ A0 A1 : Ω → ℝ,
      Measurable A0 ∧ Measurable A1 ∧
      (∀ᵐ ω ∂μ, A0 ω ∈ Set.Icc a b ∧ A1 ω ∈ Set.Icc a b ∧
        observedOutcome (A0 ω) (A1 ω) (D 0 ω) = Y 0 ω) ∧
      mean μ (fun ω => A1 ω-A0 ω) = t) ∧
    (∀ n, 0 < n → mean μ (sampleMean L n) = ℓ ∧ mean μ (sampleMean U n) = u) ∧
    CP μ (sampleMean L) ℓ ∧ CP μ (sampleMean U) u := by
  classical
  let Y := fun i ω => observedOutcome (Y0 i ω) (Y1 i ω) (D i ω)
  let L := fun i ω => ateLower (Y i ω) (D i ω) a b
  let U := fun i ω => ateUpper (Y i ω) (D i ω) a b
  let M := max |a| |b|
  have hy : ∀ᵐ ω ∂μ, |Y 0 ω| ≤ M := by
    filter_upwards [hsupport 0] with ω hω
    rcases hω.2.2 with hd | hd
    · simpa [Y, observedOutcome, hd, M] using abs_le_max_abs_abs hω.1.1 hω.1.2
    · simpa [Y, observedOutcome, hd, M] using abs_le_max_abs_abs hω.2.1.1 hω.2.1.2
  have h2Y : MemLp (Y 0) 2 μ := MemLp.of_bound
    (measurable_fst.comp (hiid.1 0)).aestronglyMeasurable M
    (by simpa only [Real.norm_eq_abs] using hy)
  let gL : ℝ × ℝ → ℝ := fun yd => ateLower yd.1 yd.2 a b
  let gU : ℝ × ℝ → ℝ := fun yd => ateUpper yd.1 yd.2 a b
  have hgL : Measurable gL := by dsimp [gL, ateLower]; fun_prop
  have hgU : Measurable gU := by dsimp [gU, ateUpper]; fun_prop
  have hLiid : IID μ L := ⟨fun i => hgL.comp (hiid.1 i),
    hiid.2.1.comp (fun _ => gL) (fun _ => hgL), fun i => (hiid.2.2 i).comp hgL⟩
  have hUiid : IID μ U := ⟨fun i => hgU.comp (hiid.1 i),
    hiid.2.1.comp (fun _ => gU) (fun _ => hgU), fun i => (hiid.2.2 i).comp hgU⟩
  have ha : |a| ≤ M := le_max_left _ _
  have hb : |b| ≤ M := le_max_right _ _
  have hLb : ∀ᵐ ω ∂μ, |L 0 ω| ≤ 2*M := by
    filter_upwards [hy, hsupport 0] with ω hω hs
    rcases hs.2.2 with hd | hd
    · simp only [L, ateLower, hd, mul_zero, mul_one, sub_zero, zero_sub, zero_add, add_zero]
      nlinarith [abs_sub a (Y 0 ω)]
    · simp only [L, ateLower, hd, mul_zero, mul_one, sub_zero, zero_sub, zero_add, add_zero, sub_self]
      nlinarith [abs_sub (Y 0 ω) b]
  have hUb : ∀ᵐ ω ∂μ, |U 0 ω| ≤ 2*M := by
    filter_upwards [hy, hsupport 0] with ω hω hs
    rcases hs.2.2 with hd | hd
    · simp only [U, ateUpper, hd, mul_zero, mul_one, sub_zero, zero_sub, zero_add, add_zero]
      nlinarith [abs_sub b (Y 0 ω)]
    · simp only [U, ateUpper, hd, mul_zero, mul_one, sub_zero, zero_sub, zero_add, add_zero, sub_self]
      nlinarith [abs_sub (Y 0 ω) a]
  have h2L : MemLp (L 0) 2 μ := MemLp.of_bound (hLiid.1 0).aestronglyMeasurable (2*M)
    (by simpa only [Real.norm_eq_abs] using hLb)
  have h2U : MemLp (U 0) 2 μ := MemLp.of_bound (hUiid.1 0).aestronglyMeasurable (2*M)
    (by simpa only [Real.norm_eq_abs] using hUb)
  have hB : {ω | D 0 ω = 0} =ᵐ[μ] {ω | D 0 ω = 1}ᶜ := by
    filter_upwards [hsupport 0] with ω hω
    rcases hω.2.2 with hd | hd <;> simp [hd]
  have hp0eq : prob μ {ω | D 0 ω = 0} = 1 - prob μ {ω | D 0 ω = 1} := by
    unfold prob
    rw [measure_congr hB]
    simpa only [Set.preimage, Set.mem_singleton_iff, measureReal_def] using
      probReal_compl_eq_one_sub (μ := μ) ((hD 0) (measurableSet_singleton 1))
  have hp0 : 0 < prob μ {ω | D 0 ω = 0} := by rw [hp0eq]; linarith [hpos.2]
  have hLF := t88_endpoint_formula_ae μ (Y 0) (D 0) (h2Y.integrable one_le_two)
    (hD 0) ((hsupport 0).mono (fun _ h => h.2.2)) hp0 hpos.1 a b
  have hUF := t88_endpoint_formula_ae μ (Y 0) (D 0) (h2Y.integrable one_le_two)
    (hD 0) ((hsupport 0).mono (fun _ h => h.2.2)) hp0 hpos.1 b a
  change mean μ (L 0) = _ at hLF
  change mean μ (U 0) = _ at hUF
  rw [hp0eq] at hLF hUF
  let C0 : Ω → ℝ := fun ω => clip a b (Y0 0 ω)
  let C1 : Ω → ℝ := fun ω => clip a b (Y1 0 ω)
  let CD : Ω → ℝ := fun ω => if D 0 ω = 1 then 1 else 0
  have hc_range (x : ℝ) : clip a b x ∈ Set.Icc a b :=
    ⟨le_max_left _ _, max_le hab (min_le_left _ _)⟩
  have hc_eq (x : ℝ) (hx : x ∈ Set.Icc a b) : clip a b x = x := by
    simp only [clip, min_eq_right hx.2, max_eq_right hx.1]
  have hC : ∀ᵐ ω ∂μ, C0 ω = Y0 0 ω ∧ C1 ω = Y1 0 ω ∧ CD ω = D 0 ω := by
    filter_upwards [hsupport 0] with ω hω
    refine ⟨hc_eq _ hω.1, hc_eq _ hω.2.1, ?_⟩
    rcases hω.2.2 with hd | hd <;> simp [CD, hd]
  have hC0 : Measurable C0 := by dsimp [C0, clip]; fun_prop
  have hC1 : Measurable C1 := by dsimp [C1, clip]; fun_prop
  have hCD : Measurable CD :=
    measurable_const.ite ((hD 0) (measurableSet_singleton 1)) measurable_const
  have hCDb (ω : Ω) : CD ω = 0 ∨ CD ω = 1 := by dsimp [CD]; split_ifs <;> simp
  let CY := fun ω => observedOutcome (C0 ω) (C1 ω) (CD ω)
  let CL := fun ω => ateLower (CY ω) (CD ω) a b
  let CU := fun ω => ateUpper (CY ω) (CD ω) a b
  have hCY : CY =ᵐ[μ] Y 0 := by
    filter_upwards [hC] with ω hω
    simp only [CY, Y, hω.1, hω.2.1, hω.2.2]
  have hCL : mean μ CL = mean μ (L 0) := integral_congr_ae (by
    filter_upwards [hCY, hC] with ω hyω hω
    simp only [CL, L, hyω, hω.2.2])
  have hCU : mean μ CU = mean μ (U 0) := integral_congr_ae (by
    filter_upwards [hCY, hC] with ω hyω hω
    simp only [CU, U, hyω, hω.2.2])
  have hCτ : mean μ (fun ω => C1 ω-C0 ω) = mean μ (fun ω => Y1 0 ω-Y0 0 ω) :=
    integral_congr_ae (by
      filter_upwards [hC] with ω hω
      simp only [hω.1, hω.2.1])
  have hs := ate_sharp_bounds_and_width μ C0 C1 CD hC0 hC1 hCD a b
    (fun ω => ⟨hc_range _, hc_range _⟩) hCDb
  change mean μ (fun ω => C1 ω-C0 ω) ∈ Set.Icc (mean μ CL) (mean μ CU) ∧
    mean μ CU-mean μ CL = b-a ∧ _ at hs
  have hUF' : mean μ (U 0) = _ := hUF
  change mean μ (L 0) = _ ∧ mean μ (U 0) = _ ∧ _
  refine ⟨hLF, hUF', ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [hCL, hCU, hLF, hUF'] using hs.2.1
  · simpa only [hCL, hCU, hCτ, hLF, hUF'] using hs.1
  · intro t ht
    have ht' : t ∈ Set.Icc (mean μ CL) (mean μ CU) := by
      rw [hCL, hCU, hLF, hUF']
      exact ht
    obtain ⟨A0, A1, hm0, hm1, hbnd, hobs, hmean⟩ := hs.2.2 t ht'
    refine ⟨A0, A1, hm0, hm1, ?_, hmean⟩
    filter_upwards [hCY, hC] with ω hyω hω
    exact ⟨(hbnd ω).1, (hbnd ω).2, by
      exact (congrArg (fun d => observedOutcome (A0 ω) (A1 ω) d) hω.2.2.symm).trans
        ((congrFun hobs ω).trans hyω)⟩
  · intro n hn
    exact ⟨(iid_sample_mean_finite_moments μ L hLiid h2L n hn).1.trans hLF,
      (iid_sample_mean_finite_moments μ U hUiid h2U n hn).1.trans hUF'⟩
  · rw [← hLF]; exact weak_law_finite_variance μ L hLiid h2L
  · rw [← hUF']; exact weak_law_finite_variance μ U hUiid h2U

end
end AronowAudit.P001.Wave1
