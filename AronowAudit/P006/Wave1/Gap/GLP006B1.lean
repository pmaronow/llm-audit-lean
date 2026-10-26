import AronowAudit.P006.Wave1.Gap.GP006B3
import Mathlib.Probability.Kernel.MeasurableIntegral
import Mathlib.Probability.Kernel.Composition.MeasureCompProd
import Mathlib.Probability.Independence.Integration

/-! P006-T16 and P006-T2. -/
namespace AronowAudit.P006.Wave1

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal Topology

noncomputable section

local instance instDecidableGLP006B1 (p : Prop) : Decidable p := Classical.propDecidable p

/-- Normalizing the nonnegative untreated density also gives its Bochner mean. -/
lemma T16_selected_density_mean {U : Type*} [MeasurableSpace U]
    (ρ : Measure U) [IsProbabilityMeasure ρ] (p m : U → ℝ)
    (hp : Measurable p) (hp01 : ∀ u, 0 ≤ p u ∧ p u ≤ 1)
    (hm : Integrable m ρ) (hq : 0 < ∫ u, 1 - p u ∂ρ) :
    let q := ∫ u, 1 - p u ∂ρ
    let ν := ρ.withDensity (fun u => ENNReal.ofReal ((1 - p u) / q))
    IsProbabilityMeasure ν ∧ Integrable m ν ∧
      (∫ u, m u ∂ν) = (∫ u, m u * (1 - p u) ∂ρ) / q := by
  dsimp only
  let q := ∫ u, 1 - p u ∂ρ
  have hw : Measurable (fun u => 1 - p u) := measurable_const.sub hp
  have hw01 (u : U) : 0 ≤ 1 - p u ∧ 1 - p u ≤ 1 := by
    obtain ⟨h0,h1⟩ := hp01 u
    constructor <;> linarith
  have hwi : Integrable (fun u => 1 - p u) ρ :=
    (integrable_const (1 : ℝ)).mono' hw.aestronglyMeasurable
      (ae_of_all _ fun u => by simpa [Real.norm_eq_abs, abs_of_nonneg (hw01 u).1] using (hw01 u).2)
  have hwm : Integrable (fun u => (1 - p u) * m u) ρ :=
    hm.bdd_mul (c := 1) hw.aestronglyMeasurable (ae_of_all _ fun u => by
      simpa [Real.norm_eq_abs, abs_of_nonneg (hw01 u).1] using (hw01 u).2)
  have hr : Measurable (fun u => (1 - p u) / q) := hw.div_const q
  have hr0 (u : U) : 0 ≤ (1 - p u) / q := div_nonneg (hw01 u).1 hq.le
  have hri : Integrable (fun u => (1 - p u) / q) ρ := hwi.div_const q
  have hrint : (∫ u, (1 - p u) / q ∂ρ) = 1 := by
    rw [integral_div]
    exact div_self hq.ne'
  have hν : IsProbabilityMeasure (ρ.withDensity (fun u => ENNReal.ofReal ((1 - p u) / q))) := by
    constructor
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal hri (ae_of_all _ hr0), hrint]
    norm_num
  have hmν : Integrable m (ρ.withDensity (fun u => ENNReal.ofReal ((1 - p u) / q))) := by
    rw [integrable_withDensity_iff_integrable_smul' hr.ennreal_ofReal
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
    simpa only [ENNReal.toReal_ofReal (hr0 _), smul_eq_mul, div_mul_eq_mul_div] using hwm.div_const q
  refine ⟨hν, hmν, ?_⟩
  rw [integral_withDensity_eq_integral_toReal_smul hr.ennreal_ofReal
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  simp_rw [ENNReal.toReal_ofReal (hr0 _), smul_eq_mul, div_mul_eq_mul_div]
  rw [integral_div]
  congr 1
  apply integral_congr_ae
  exact ae_of_all _ fun u => mul_comm _ _

lemma T16_mean_extrema {U : Type*} [MeasurableSpace U] [Nonempty U]
    (ρ : Measure U) [IsProbabilityMeasure ρ] (m : U → ℝ) (hm : Integrable m ρ)
    (hext : ∃ l h, ∀ u, m l ≤ m u ∧ m u ≤ m h)
    (hmax : ∀ u, ∃ v, ∀ w, |m u - m w| ≤ |m u - m v|) :
    sInf (Set.range m) ≤ (∫ u, m u ∂ρ) ∧
    (∫ u, m u ∂ρ) ≤ sSup (Set.range m) ∧
    ∀ u, |(∫ v, m v ∂ρ) - m u| ≤ sSup (Set.range (fun v => |m u - m v|)) := by
  obtain ⟨l,h,hext⟩ := hext
  have hne : (Set.range m).Nonempty := Set.range_nonempty m
  have hlo : BddBelow (Set.range m) := ⟨m l, by rintro _ ⟨u,rfl⟩; exact (hext u).1⟩
  have hhi : BddAbove (Set.range m) := ⟨m h, by rintro _ ⟨u,rfl⟩; exact (hext u).2⟩
  have hil : m l ≤ ∫ u, m u ∂ρ := by
    simpa using integral_mono (integrable_const (m l)) hm (fun u => (hext u).1)
  have hih : (∫ u, m u ∂ρ) ≤ m h := by
    simpa using integral_mono hm (integrable_const (m h)) (fun u => (hext u).2)
  refine ⟨(csInf_le hlo (Set.mem_range_self l)).trans hil,
    hih.trans (le_csSup hhi (Set.mem_range_self h)), ?_⟩
  intro u
  obtain ⟨v,hv⟩ := hmax u
  have hbd : BddAbove (Set.range (fun w => |m u - m w|)) :=
    ⟨|m u - m v|, by rintro _ ⟨w,rfl⟩; exact hv w⟩
  have hl := le_csSup hbd (Set.mem_range_self (f := fun w => |m u - m w|) l)
  have hh := le_csSup hbd (Set.mem_range_self (f := fun w => |m u - m w|) h)
  apply abs_le.mpr
  constructor
  · have := le_abs_self (m u - m l)
    linarith
  · have := neg_le_abs (m u - m h)
    linarith

lemma T16_baseline_measurable {X U : Type*} [MeasurableSpace X] [MeasurableSpace U]
    (κ : Kernel X U) [IsSFiniteKernel κ] {m π : (X × U) → ℝ}
    (hm : Measurable m) (hp : Measurable π) : Measurable (selectedBaseline κ m π) := by
  exact ((hm.mul (measurable_const.sub hp)).stronglyMeasurable.integral_kernel_prod_right').measurable.div
    ((measurable_const.sub hp).stronglyMeasurable.integral_kernel_prod_right').measurable

theorem T16_corrected_agent_data_bound_proof {Ω X U : Type*} [MeasurableSpace Ω]
    [MeasurableSpace X] [MeasurableSpace U] [Nonempty U] {n : ℕ}
    (E : Experiment Ω (X × U) n) (hS : Standing E)
    (PX : Measure X) (hPX : IsProbabilityMeasure PX)
    (κ : Kernel X U) (hκ : IsMarkovKernel κ) (hjoint : E.PX = PX.compProd κ)
    (PiSet : Set ((X × U) → ℝ)) (hπ : ∀ π ∈ PiSet, Admissible π)
    (hq : ∀ π ∈ PiSet, ∀ᵐ x ∂PX, 0 < untreatedProbability κ π x)
    (hcond : ∀ᵐ x ∂PX, Integrable (fun u => E.μ0 (x,u)) (κ x))
    (hminmax : ∀ x, ∃ umin umax, ∀ u, E.μ0 (x,umin) ≤ E.μ0 (x,u) ∧
      E.μ0 (x,u) ≤ E.μ0 (x,umax))
    (hmax : ∀ c : X × U, ∃ v, ∀ u, |E.μ0 c-E.μ0 (c.1,u)| ≤
      |E.μ0 c-E.μ0 (c.1,v)|)
    (hest : ∀ π ∈ PiSet, ∀ ω c, E.μhat π ω c = selectedBaseline κ E.μ0 π c.1)
    (γ : ℝ) (hint : Integrable (maximumDeviation E.μ0) E.PX)
    (hγ : (∫ c, maximumDeviation E.μ0 c ∂E.PX) ≤ γ)
    (b s : (X × U) → ℝ) (hb : IsBest PiSet E.expectedTT b) (hs : IsBest PiSet E.V s) :
    (∀ π ∈ PiSet,
      (∀ᵐ x ∂PX, IsProbabilityMeasure (untreatedConditionalLaw κ π x) ∧
        selectedBaseline κ E.μ0 π x =
          (∫ u, E.μ0 (x,u) ∂untreatedConditionalLaw κ π x) ∧
        sInf (Set.range (fun u => E.μ0 (x,u))) ≤ selectedBaseline κ E.μ0 π x ∧
        selectedBaseline κ E.μ0 π x ≤ sSup (Set.range (fun u => E.μ0 (x,u))) ∧
        ∀ u, |selectedBaseline κ E.μ0 π x-E.μ0 (x,u)| ≤
          maximumDeviation E.μ0 (x,u)) ∧
      normalizedTT E π = (∫ c, π c*(E.μ1 c-selectedBaseline κ E.μ0 π c.1) ∂E.PX) ∧
      |normalizedTT E π-E.V π| ≤
        (∫ c, |selectedBaseline κ E.μ0 π c.1-E.μ0 c| ∂E.PX) ∧
      (∫ c, |selectedBaseline κ E.μ0 π c.1-E.μ0 c| ∂E.PX) ≤
        (∫ c, maximumDeviation E.μ0 c ∂E.PX)) ∧
    regret PiSet E.V b ≤ 2*γ := by
  have : IsProbabilityMeasure PX := hPX
  have : IsMarkovKernel κ := hκ
  have : IsProbabilityMeasure E.PX := hS.px_probability
  have hpolicy (π : (X × U) → ℝ) (hp : π ∈ PiSet) := by
    have hpa := hπ π hp
    have hB := T16_baseline_measurable κ hS.means_measurable.1 hpa.1
    have hqm : Measurable (untreatedProbability κ π) :=
      (measurable_const.sub hpa.1).stronglyMeasurable.integral_kernel_prod_right' |>.measurable
    have hcm : MeasurableSet {x | Integrable (fun u => E.μ0 (x,u)) (κ x)} :=
      measurableSet_kernel_integrable hS.means_measurable.1.stronglyMeasurable
    have hgm : MeasurableSet {x | 0 < untreatedProbability κ π x ∧
        Integrable (fun u => E.μ0 (x,u)) (κ x)} :=
      (measurableSet_lt measurable_const hqm).inter hcm
    have hg : ∀ᵐ x ∂PX, 0 < untreatedProbability κ π x ∧
        Integrable (fun u => E.μ0 (x,u)) (κ x) := (hq π hp).and hcond
    have hfiber (x : X) (hx : 0 < untreatedProbability κ π x ∧
        Integrable (fun u => E.μ0 (x,u)) (κ x)) :
        IsProbabilityMeasure (untreatedConditionalLaw κ π x) ∧
        selectedBaseline κ E.μ0 π x =
          (∫ u, E.μ0 (x,u) ∂untreatedConditionalLaw κ π x) ∧
        sInf (Set.range (fun u => E.μ0 (x,u))) ≤ selectedBaseline κ E.μ0 π x ∧
        selectedBaseline κ E.μ0 π x ≤ sSup (Set.range (fun u => E.μ0 (x,u))) ∧
        ∀ u, |selectedBaseline κ E.μ0 π x-E.μ0 (x,u)| ≤
          maximumDeviation E.μ0 (x,u) := by
      have hd := T16_selected_density_mean (κ x) (fun u => π (x,u))
        (fun u => E.μ0 (x,u)) (hpa.1.comp measurable_prodMk_left)
        (fun u => hpa.2 (x,u)) hx.2 hx.1
      change IsProbabilityMeasure (untreatedConditionalLaw κ π x) ∧
        Integrable (fun u => E.μ0 (x,u)) (untreatedConditionalLaw κ π x) ∧
        (∫ u, E.μ0 (x,u) ∂untreatedConditionalLaw κ π x) = selectedBaseline κ E.μ0 π x at hd
      have : IsProbabilityMeasure (untreatedConditionalLaw κ π x) := hd.1
      have he := T16_mean_extrema (untreatedConditionalLaw κ π x)
        (fun u => E.μ0 (x,u)) hd.2.1 (hminmax x) (fun u => hmax (x,u))
      rw [hd.2.2] at he
      exact ⟨hd.1, hd.2.2.symm, he⟩
    have hfae := hg.mono fun x hx => hfiber x hx
    have hgj : ∀ᵐ c ∂E.PX, 0 < untreatedProbability κ π c.1 ∧
        Integrable (fun u => E.μ0 (c.1,u)) (κ c.1) := by
      rw [hjoint]
      exact Measure.ae_compProd_of_ae_fst κ hgm hg
    have hbound : ∀ᵐ c ∂E.PX, |selectedBaseline κ E.μ0 π c.1 - E.μ0 c| ≤
        maximumDeviation E.μ0 c := by
      filter_upwards [hgj] with c hc
      exact (hfiber c.1 hc).2.2.2.2 c.2
    have herrm : Measurable (fun c : X × U => selectedBaseline κ E.μ0 π c.1 - E.μ0 c) :=
      (hB.comp measurable_fst).sub hS.means_measurable.1
    have herr : Integrable (fun c : X × U => selectedBaseline κ E.μ0 π c.1 - E.μ0 c) E.PX :=
      hint.mono' herrm.aestronglyMeasurable (by simpa only [Real.norm_eq_abs] using hbound)
    have hBi : Integrable (fun c : X × U => selectedBaseline κ E.μ0 π c.1) E.PX := by
      convert herr.add hS.means_integrable.1 using 1
      ext c
      simp
    have hid : normalizedTT E π =
        ∫ c, π c * (E.μ1 c - selectedBaseline κ E.μ0 π c.1) ∂E.PX := by
      unfold normalizedTT
      rw [T7_actual_treated_score E hS _ (hB.comp measurable_fst) hBi π hpa]
      · exact mul_div_cancel_left₀ _ (Nat.cast_pos.mpr E.hn).ne'
      · intro i
        have hz : (fun ω => bit (E.T π i ω) * (E.μhat π ω (E.X i ω) -
            selectedBaseline κ E.μ0 π (E.X i ω).1)) = fun _ => (0 : ℝ) := by
          funext ω
          rw [hest π hp ω (E.X i ω)]
          ring
        simp only [Function.comp_apply]
        rw [hz]
        change (E.law π)[(0 : Ω → ℝ) | E.covariateSigma i] =ᵐ[E.law π] 0
        rw [condExp_zero]
    have hbias := T8_information_integral_bias_bound E.PX E.μ1 E.μ0
      (fun c => selectedBaseline κ E.μ0 π c.1) π hS.means_integrable.2
      hS.means_integrable.1 hBi hpa
    have he1 : |normalizedTT E π - E.V π| ≤
        ∫ c, |selectedBaseline κ E.μ0 π c.1 - E.μ0 c| ∂E.PX := by
      rw [hid, T7_actual_welfare E hS π hpa]
      change |(∫ c, π c * (E.μ1 c - selectedBaseline κ E.μ0 π c.1) ∂E.PX) -
        (∫ c, π c * (E.μ1 c - E.μ0 c) ∂E.PX)| ≤ _
      rw [hbias.1]
      simpa only [abs_sub_comm] using hbias.2
    have he2 : (∫ c, |selectedBaseline κ E.μ0 π c.1 - E.μ0 c| ∂E.PX) ≤
        ∫ c, maximumDeviation E.μ0 c ∂E.PX := integral_mono_ae herr.abs hint hbound
    exact And.intro hfae (And.intro hid (And.intro he1 he2))
  refine ⟨hpolicy, ?_⟩
  apply uniform_error_regret PiSet (normalizedTT E) E.V b s
    (T8_information_normalized_best E PiSet b hb) hs γ
  intro π hp
  exact ((hpolicy π hp).2.2.1.trans (hpolicy π hp).2.2.2).trans hγ

/-! The reciprocal count omitting the current unit is independent of its mark. -/
def T2_restWeight {n : ℕ} (T : Fin n → Bool) (i : Fin n) : ℝ :=
  (1 + ∑ j ∈ Finset.univ.erase i, bit (T j))⁻¹

lemma T2_bit_nonneg (t : Bool) : 0 ≤ bit t := by cases t <;> norm_num [bit]

lemma T2_count_nonneg {n : ℕ} (T : Fin n → Bool) : 0 ≤ treatedCount T :=
  Finset.sum_nonneg fun i _ => T2_bit_nonneg (T i)

lemma T2_count_zero_iff {n : ℕ} (T : Fin n → Bool) :
    treatedCount T = 0 ↔ ∀ i, T i = false := by
  constructor
  · intro h i
    have hi : bit (T i) ≤ treatedCount T :=
      Finset.single_le_sum (fun j _ => T2_bit_nonneg (T j)) (Finset.mem_univ i)
    cases ht : T i
    · rfl
    · norm_num [ht, bit, h] at hi
  · intro h
    simp [treatedCount, h, bit]

lemma T2_restWeight_bounds {n : ℕ} (T : Fin n → Bool) (i : Fin n) :
    0 ≤ T2_restWeight T i ∧ T2_restWeight T i ≤ 1 := by
  have hs : 0 ≤ ∑ j ∈ Finset.univ.erase i, bit (T j) :=
    Finset.sum_nonneg fun j _ => T2_bit_nonneg (T j)
  unfold T2_restWeight
  exact ⟨inv_nonneg.mpr (by linarith), (inv_le_one₀ (by linarith)).mpr (by linarith)⟩

lemma T2_average_expansion {n : ℕ} (T : Fin n → Bool) (Z : Fin n → ℝ) :
    wATO T Z = ∑ i, (Z i * bit (T i)) * T2_restWeight T i := by
  unfold wATO
  split_ifs with hN
  · rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    cases ht : T i
    · simp [ht, bit]
    · have he : treatedCount T = 1 + ∑ j ∈ Finset.univ.erase i, bit (T j) := by
        have h := Finset.sum_erase_add Finset.univ (fun j => bit (T j)) (Finset.mem_univ i)
        change _ = ∑ j, bit (T j) at h
        simpa [ht, bit, treatedCount, add_comm] using h.symm
      simp only [T2_restWeight, ← he, div_eq_mul_inv]
  · have hz : treatedCount T = 0 := le_antisymm (le_of_not_gt hN) (T2_count_nonneg T)
    have ht := (T2_count_zero_iff T).mp hz
    simp [ht, bit]

lemma T2_one_average {n : ℕ} (T : Fin n → Bool) :
    wATO T (fun _ => 1) = if 0 < treatedCount T then 1 else 0 := by
  unfold wATO
  split_ifs with h
  · simpa only [one_mul, treatedCount] using div_self h.ne'
  · rfl

lemma T2_geometric (n : ℕ) (q : ℝ) : q * emptyFactor n q = 1 - (1-q)^n := by
  induction n with
  | zero => simp [emptyFactor]
  | succ n ih =>
    rw [emptyFactor, Finset.sum_range_succ]
    change q * (emptyFactor n q + (1-q)^n) = _
    rw [mul_add, ih, pow_succ]
    ring

lemma T2_rest_independent {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {n : ℕ}
    (Z : Fin n → Ω → ℝ) (T : Fin n → Ω → Bool)
    (hZ : ∀ i, Measurable (Z i)) (hT : ∀ i, Measurable (T i))
    (hI : iIndepFun (fun i ω => (Z i ω,T i ω)) μ) (i : Fin n) :
    IndepFun (fun ω => Z i ω * bit (T i ω))
      (fun ω => T2_restWeight (fun j => T j ω) i) μ := by
  let W : Fin n → Ω → ℝ × ℝ := fun j ω => (Z j ω, bit (T j ω))
  have hW : ∀ j, Measurable (W j) := fun j =>
    (hZ j).prodMk ((measurable_of_finite bit).comp (hT j))
  have hWI : iIndepFun W μ :=
    hI.comp (fun _ z => (z.1,bit z.2)) (fun _ =>
      measurable_fst.prodMk ((measurable_of_finite bit).comp measurable_snd))
  have hind := hWI.indepFun_finsetSum_of_notMem hW (Finset.notMem_erase i Finset.univ)
  have hc := hind.symm.comp (ψ := fun z : ℝ × ℝ => (1+z.2)⁻¹)
    (measurable_fst.mul measurable_snd) ((measurable_const.add measurable_snd).inv)
  simpa only [W, Function.comp_def, Finset.sum_apply, Prod.snd_sum, T2_restWeight, Pi.mul_apply] using hc

/-- The empty-event probability uses only independence of treatment coordinates. -/
lemma T2_empty_mass {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {n : ℕ} (T : Fin n → Ω → Bool)
    (hT : ∀ i, Measurable (T i)) (hI : iIndepFun T μ) (q : ℝ)
    (hq : ∀ i, (∫ ω, bit (T i ω) ∂μ) = q) :
    (μ {ω | treatedCount (fun i => T i ω) = 0}).toReal = (1-q)^n := by
  have hi (i : Fin n) : (μ {ω | T i ω = false}).toReal = 1-q := by
    have hm : MeasurableSet {ω | T i ω = true} := (hT i) (measurableSet_singleton true)
    have hb : (fun ω => bit (T i ω)) = {ω | T i ω = true}.indicator (fun _ => (1 : ℝ)) := by
      ext ω
      cases ht : T i ω <;> simp [bit,ht]
    have htrue : (μ {ω | T i ω = true}).toReal = q := by
      rw [← hq i, hb]
      change (μ {ω | T i ω = true}).toReal =
        ∫ ω, {ω | T i ω = true}.indicator (fun _ => (1 : ℝ)) ω ∂μ
      simpa only [measureReal_def, smul_eq_mul, mul_one] using
        (integral_indicator_const (μ := μ) (1 : ℝ) hm).symm
    have hcompl : {ω | T i ω = false} = {ω | T i ω = true}ᶜ := by
      ext ω
      cases T i ω <;> simp
    rw [hcompl]
    simpa [measureReal_def, htrue] using (measureReal_compl hm (μ := μ))
  have hset : {ω | treatedCount (fun i => T i ω) = 0} = ⋂ i, {ω | T i ω = false} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iInter, T2_count_zero_iff]
  have hmprod := hI.meas_iInter (s := fun i => {ω | T i ω = false})
    (fun i => (comap_measurable (T i)) (measurableSet_singleton false))
  rw [hset, hmprod, ENNReal.toReal_prod]
  simp only [hi, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

lemma T2_rest_measurable {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (T : Fin n → Ω → Bool) (hT : ∀ i, Measurable (T i)) (i : Fin n) :
    Measurable (fun ω => T2_restWeight (fun j => T j ω) i) :=
  (measurable_of_finite (fun t : Fin n → Bool => T2_restWeight t i)).comp
    (measurable_pi_lambda hT)

lemma T2_factor_average {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {n : ℕ} (Z : Fin n → Ω → ℝ) (T : Fin n → Ω → Bool)
    (hZ : ∀ i, Measurable (Z i)) (hZi : ∀ i, Integrable (Z i) μ)
    (hT : ∀ i, Measurable (T i)) (hI : iIndepFun (fun i ω => (Z i ω,T i ω)) μ)
    (A : ℝ) (hA : ∀ i, (∫ ω, Z i ω * bit (T i ω) ∂μ) = A) :
    Integrable (fun ω => wATO (fun i => T i ω) (fun i => Z i ω)) μ ∧
    (∫ ω, wATO (fun i => T i ω) (fun i => Z i ω) ∂μ) =
      A * ∑ i, ∫ ω, T2_restWeight (fun j => T j ω) i ∂μ := by
  have hbi (i : Fin n) : Integrable (fun ω => Z i ω * bit (T i ω)) μ :=
    (hZi i).mul_bdd ((measurable_of_finite bit).comp (hT i)).aestronglyMeasurable
      (ae_of_all _ fun ω => T7_bit_norm _)
  have hi (i : Fin n) : Integrable
      (fun ω => (Z i ω * bit (T i ω)) * T2_restWeight (fun j => T j ω) i) μ :=
    (hbi i).mul_bdd (T2_rest_measurable T hT i).aestronglyMeasurable
      (ae_of_all _ fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (T2_restWeight_bounds _ i).1]
        exact (T2_restWeight_bounds _ i).2)
  have he : (fun ω => wATO (fun i => T i ω) (fun i => Z i ω)) =
      (fun ω => ∑ i, (Z i ω * bit (T i ω)) * T2_restWeight (fun j => T j ω) i) :=
    funext fun ω => T2_average_expansion _ _
  rw [he]
  refine ⟨integrable_finset_sum _ (fun i _ => hi i), ?_⟩
  rw [integral_finsetSum _ (fun i _ => hi i)]
  simp_rw [(T2_rest_independent Z T hZ hT hI _).integral_fun_mul_eq_mul_integral
    (hbi _).aestronglyMeasurable (T2_rest_measurable T hT _).aestronglyMeasurable, hA]
  exact (Finset.mul_sum _ _ _).symm

lemma T2_nonempty_mass {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {n : ℕ} (T : Fin n → Ω → Bool)
    (hT : ∀ i, Measurable (T i)) (q : ℝ)
    (he : (μ {ω | treatedCount (fun i => T i ω) = 0}).toReal = (1-q)^n) :
    (μ {ω | 0 < treatedCount (fun i => T i ω)}).toReal = 1-(1-q)^n := by
  have hC : Measurable (fun ω => treatedCount (fun i => T i ω)) :=
    (measurable_of_finite treatedCount).comp (measurable_pi_lambda hT)
  have hm : MeasurableSet {ω | treatedCount (fun i => T i ω) = 0} :=
    measurableSet_eq_fun hC measurable_const
  have hcompl : {ω | 0 < treatedCount (fun i => T i ω)} =
      {ω | treatedCount (fun i => T i ω) = 0}ᶜ := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_compl_iff]
    simpa only [ne_eq, eq_comm] using (T2_count_nonneg (fun i => T i ω)).lt_iff_ne
  rw [hcompl]
  simpa only [measureReal_def, measure_univ, ENNReal.toReal_one, he] using (measureReal_compl hm (μ := μ))

lemma T2_marked_average {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {n : ℕ} (hn : 0 < n)
    (Z : Fin n → Ω → ℝ) (T : Fin n → Ω → Bool)
    (hZ : ∀ i, Measurable (Z i)) (hZi : ∀ i, Integrable (Z i) μ)
    (hT : ∀ i, Measurable (T i)) (hI : iIndepFun (fun i ω => (Z i ω,T i ω)) μ)
    (q A : ℝ) (hq0 : 0 ≤ q) (hq : ∀ i, (∫ ω, bit (T i ω) ∂μ) = q)
    (hA : ∀ i, (∫ ω, Z i ω * bit (T i ω) ∂μ) = A) :
    (μ {ω | treatedCount (fun i => T i ω) = 0}).toReal = (1-q)^n ∧
    Integrable (fun ω => wATO (fun i => T i ω) (fun i => Z i ω)) μ ∧
    (∫ ω, wATO (fun i => T i ω) (fun i => Z i ω) ∂μ) = emptyFactor n q * A := by
  have hTI : iIndepFun T μ := hI.comp (fun _ z => z.2) (fun _ => measurable_snd)
  have hempty := T2_empty_mass μ T hT hTI q hq
  have hf := T2_factor_average μ Z T hZ hZi hT hI A hA
  refine ⟨hempty, hf.1, ?_⟩
  by_cases hqpos : 0 < q
  · have hI1 : iIndepFun (fun i ω => ((1 : ℝ), T i ω)) μ :=
      hI.comp (fun _ z => ((1 : ℝ),z.2)) (fun _ => measurable_const.prodMk measurable_snd)
    have hf1 := T2_factor_average μ (fun _ _ => 1) T (fun _ => measurable_const)
      (fun _ => integrable_const 1) hT hI1 q (fun i => by simpa using hq i)
    have hm : MeasurableSet {ω | 0 < treatedCount (fun i => T i ω)} :=
      measurableSet_lt measurable_const
        ((measurable_of_finite treatedCount).comp (measurable_pi_lambda hT))
    have hone : (∫ ω, wATO (fun i => T i ω) (fun _ => 1) ∂μ) =
        (μ {ω | 0 < treatedCount (fun i => T i ω)}).toReal := by
      have heq : (fun ω => wATO (fun i => T i ω) (fun _ => 1)) =
          {ω | 0 < treatedCount (fun i => T i ω)}.indicator (fun _ => (1 : ℝ)) := by
        funext ω
        rw [T2_one_average]
        simp only [Set.indicator_apply, Set.mem_setOf_eq]
      rw [heq]
      simpa only [measureReal_def, smul_eq_mul, mul_one] using
        (integral_indicator_const (μ := μ) (1 : ℝ) hm)
    have hsum : (∑ i, ∫ ω, T2_restWeight (fun j => T j ω) i ∂μ) = emptyFactor n q := by
      apply mul_left_cancel₀ hqpos.ne'
      rw [← hf1.2, hone, T2_nonempty_mass μ T hT q hempty, T2_geometric]
    rw [hf.2, hsum, mul_comm]
  · have hqz : q = 0 := le_antisymm (le_of_not_gt hqpos) hq0
    let i : Fin n := ⟨0,hn⟩
    have hbi : Integrable (fun ω => bit (T i ω)) μ :=
      (integrable_const (1 : ℝ)).mono' ((measurable_of_finite bit).comp (hT i)).aestronglyMeasurable
        (ae_of_all _ fun ω => T7_bit_norm _)
    have hbz : (fun ω => bit (T i ω)) =ᵐ[μ] 0 :=
      (integral_eq_zero_iff_of_nonneg (fun ω => T2_bit_nonneg _) hbi).mp (by rw [hq i,hqz])
    have hAz : A = 0 := by
      rw [← hA i]
      apply integral_eq_zero_of_ae
      filter_upwards [hbz] with ω hω
      simp only [Pi.zero_apply] at hω
      simp [hω]
    rw [hf.2, hAz, zero_mul, mul_zero]

lemma T2_total_moment {Ω : Type*} [mΩ : MeasurableSpace Ω] (μ : Measure Ω)
    [IsFiniteMeasure μ] {G : MeasurableSpace Ω} (hG : G ≤ mΩ) {f g : Ω → ℝ}
    (h : μ[f | G] =ᵐ[μ] g) : (∫ ω, f ω ∂μ) = ∫ ω, g ω ∂μ := by
  have : IsFiniteMeasure (μ.trim hG) := isFiniteMeasure_trim hG
  exact (integral_condExp hG).symm.trans (integral_congr_ae h)

lemma T2_treatment_stats {Ω C : Type*} [MeasurableSpace Ω] [MeasurableSpace C]
    {n : ℕ} (E : Experiment Ω C n) (hS : Standing E) {π : C → ℝ} (hp : Admissible π) :
    0 ≤ E.q π ∧ E.q π ≤ 1 ∧
      ∀ i, (∫ ω, bit (E.T π i ω) ∂E.law π) = E.q π := by
  have : IsProbabilityMeasure E.PX := hS.px_probability
  have : IsProbabilityMeasure (E.law π) := hS.law_probability π hp
  have hpi : Integrable π E.PX :=
    (integrable_const (1 : ℝ)).mono' hp.1.aestronglyMeasurable (ae_of_all _ (T7_policy_norm hp))
  refine ⟨integral_nonneg (fun c => (hp.2 c).1), ?_, ?_⟩
  · change (∫ c, π c ∂E.PX) ≤ 1
    simpa using integral_mono hpi (integrable_const (1 : ℝ)) (fun c => (hp.2 c).2)
  · intro i
    exact (T2_total_moment (E.law π) (hS.measurable_units π hp i).1.comap_le
      (hS.bernoulli π hp i)).trans ((hS.covariate_law π hp i).comp hp.1).integral_eq

lemma T2_unit_mark_moments {Ω C : Type*} [MeasurableSpace Ω] [MeasurableSpace C]
    {n : ℕ} (E : Experiment Ω C n) (hS : Standing E) {π : C → ℝ}
    (hp : Admissible π) (i : Fin n) :
    (∫ ω, E.Y1 i ω * bit (E.T π i ω) ∂E.law π) = E.A E.μ1 π ∧
    (∫ ω, (E.Y1 i ω - E.μ0 (E.X i ω)) * bit (E.T π i ω) ∂E.law π) = E.A E.τ π := by
  have : IsProbabilityMeasure (E.law π) := hS.law_probability π hp
  obtain ⟨hX,hY0,hY1,hT⟩ := hS.measurable_units π hp i
  have hG : E.covariateSigma i ≤ ‹MeasurableSpace Ω› := hX.comap_le
  have hbm : Measurable (fun ω => bit (E.T π i ω)) := (measurable_of_finite bit).comp hT
  have hbi : Integrable (fun ω => bit (E.T π i ω)) (E.law π) :=
    (integrable_const (1 : ℝ)).mono' hbm.aestronglyMeasurable (ae_of_all _ fun ω => T7_bit_norm _)
  have h0i : Integrable (fun ω => E.μ0 (E.X i ω)) (E.law π) :=
    ((hS.covariate_law π hp i).comp hS.means_measurable.1).integrable_iff.mpr hS.means_integrable.1
  have hb0i := T7_bit_mul hT h0i
  have hb1i := T7_bit_mul hT (hS.integrable_units π hp i).2.1
  have h0m : StronglyMeasurable[E.covariateSigma i] (fun ω => E.μ0 (E.X i ω)) :=
    (hS.means_measurable.1.comp (comap_measurable (E.X i))).stronglyMeasurable
  have h0c : (E.law π)[(fun ω => bit (E.T π i ω) * E.μ0 (E.X i ω)) | E.covariateSigma i]
      =ᵐ[E.law π] (fun ω => π (E.X i ω) * E.μ0 (E.X i ω)) :=
    (condExp_mul_of_stronglyMeasurable_right h0m hb0i hbi).trans (by
      filter_upwards [hS.bernoulli π hp i] with ω hω
      exact congrArg (· * E.μ0 (E.X i ω)) hω)
  have h1 : (∫ ω, bit (E.T π i ω) * E.Y1 i ω ∂E.law π) = E.A E.μ1 π := by
    rw [T2_total_moment (E.law π) hG (T7_outcome_condExp E hS π hp i).2]
    simpa only [Experiment.A, Function.comp_apply, Pi.mul_apply, mul_comm] using
      ((hS.covariate_law π hp i).comp (hp.1.mul hS.means_measurable.2)).integral_eq
  have h0 : (∫ ω, bit (E.T π i ω) * E.μ0 (E.X i ω) ∂E.law π) = E.A E.μ0 π := by
    rw [T2_total_moment (E.law π) hG h0c]
    simpa only [Experiment.A, Function.comp_apply, Pi.mul_apply, mul_comm] using
      ((hS.covariate_law π hp i).comp (hp.1.mul hS.means_measurable.1)).integral_eq
  refine ⟨by simpa only [mul_comm] using h1, ?_⟩
  have heq : (fun ω => (E.Y1 i ω - E.μ0 (E.X i ω)) * bit (E.T π i ω)) =
      (fun ω => bit (E.T π i ω) * E.Y1 i ω) -
      (fun ω => bit (E.T π i ω) * E.μ0 (E.X i ω)) := by
    ext ω
    simp only [Pi.sub_apply]
    ring
  rw [heq]
  change (∫ ω, bit (E.T π i ω) * E.Y1 i ω - bit (E.T π i ω) * E.μ0 (E.X i ω) ∂E.law π) = _
  rw [integral_sub hb1i hb0i, h1,h0]
  have hp1 := T7_policy_mul hS.means_integrable.2 hp
  have hp0 := T7_policy_mul hS.means_integrable.1 hp
  simpa only [Experiment.A, Experiment.τ, mul_comm, mul_sub] using (integral_sub hp1 hp0).symm

/-- Coefficients measurable with respect to the complete treatment vector. -/
def T2_coefficient {n : ℕ} (T : Fin n → Bool) (i : Fin n) : ℝ :=
  bit (T i) * T2_restWeight T i

lemma T2_coefficient_bound {n : ℕ} (T : Fin n → Bool) (i : Fin n) :
    ‖T2_coefficient T i‖ ≤ 1 := by
  have hr : ‖T2_restWeight T i‖ ≤ 1 := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (T2_restWeight_bounds T i).1] using
      (T2_restWeight_bounds T i).2
  unfold T2_coefficient
  rw [norm_mul]
  exact (mul_le_mul (T7_bit_norm _) hr (norm_nonneg _) zero_le_one).trans (by norm_num)

lemma T2_average_coefficients {n : ℕ} (T : Fin n → Bool) (Z : Fin n → ℝ) :
    wATO T Z = ∑ i, T2_coefficient T i * Z i := by
  rw [T2_average_expansion]
  apply Finset.sum_congr rfl
  intro i _
  unfold T2_coefficient
  ring

lemma T2_observed_coefficients {Ω C : Type*} [MeasurableSpace Ω] [MeasurableSpace C]
    {n : ℕ} (E : Experiment Ω C n) (π : C → ℝ) (ω : Ω) (a : Fin n → ℝ) :
    wATO (fun i => E.T π i ω) (fun i => E.observed π ω i - a i) =
      ∑ i, T2_coefficient (fun j => E.T π j ω) i * (E.Y1 i ω - a i) := by
  rw [T2_average_coefficients]
  apply Finset.sum_congr rfl
  intro i _
  cases ht : E.T π i ω <;> simp [T2_coefficient, bit, Experiment.observed, ht]

lemma T2_vector_replacement {Ω C : Type*} [MeasurableSpace Ω] [MeasurableSpace C]
    {n : ℕ} (E : Experiment Ω C n) (hS : Standing E) {π : C → ℝ}
    (hp : Admissible π)
    (hU : ∀ i, (E.law π)[(fun ω => E.μhat π ω (E.X i ω)) | E.vectorSigma π]
      =ᵐ[E.law π] (fun ω => E.μ0 (E.X i ω))) :
    E.expectedATT π =
      ∫ ω, wATO (fun i => E.T π i ω) (fun i => E.Y1 i ω - E.μ0 (E.X i ω)) ∂E.law π := by
  have : IsProbabilityMeasure (E.law π) := hS.law_probability π hp
  let a : Fin n → Ω → ℝ := fun i ω => T2_coefficient (fun j => E.T π j ω) i
  have hdesign : Measurable (fun ω => ((fun i => E.X i ω),(fun i => E.T π i ω))) :=
    (measurable_pi_lambda fun i => (hS.measurable_units π hp i).1).prodMk
      (measurable_pi_lambda fun i => (hS.measurable_units π hp i).2.2.2)
  have hG : E.vectorSigma π ≤ ‹MeasurableSpace Ω› := hdesign.comap_le
  have ham (i : Fin n) : Measurable[E.vectorSigma π] (a i) :=
    (measurable_of_finite (fun t : Fin n → Bool => T2_coefficient t i)).comp
      (measurable_snd.comp (comap_measurable (fun ω => ((fun i => E.X i ω),(fun i => E.T π i ω)))))
  have hab (i : Fin n) (ω : Ω) : ‖a i ω‖ ≤ 1 := T2_coefficient_bound _ _
  have hmul (i : Fin n) {f : Ω → ℝ} (hi : Integrable f (E.law π)) :
      Integrable (fun ω => a i ω * f ω) (E.law π) :=
    hi.bdd_mul ((ham i).mono hG le_rfl).aestronglyMeasurable (ae_of_all _ (hab i))
  have h0i (i : Fin n) : Integrable (fun ω => E.μ0 (E.X i ω)) (E.law π) :=
    ((hS.covariate_law π hp i).comp hS.means_measurable.1).integrable_iff.mpr hS.means_integrable.1
  have he (i : Fin n) : (∫ ω, a i ω * E.μhat π ω (E.X i ω) ∂E.law π) =
      ∫ ω, a i ω * E.μ0 (E.X i ω) ∂E.law π := by
    apply T2_total_moment (E.law π) hG
    refine (condExp_mul_of_stronglyMeasurable_left (ham i).stronglyMeasurable
      (hmul i (hS.integrable_units π hp i).2.2) (hS.integrable_units π hp i).2.2).trans ?_
    filter_upwards [hU i] with ω hω
    exact congrArg (a i ω * ·) hω
  have hs (i : Fin n) : (∫ ω, a i ω * (E.Y1 i ω - E.μhat π ω (E.X i ω)) ∂E.law π) =
      ∫ ω, a i ω * (E.Y1 i ω - E.μ0 (E.X i ω)) ∂E.law π := by
    simp_rw [mul_sub]
    rw [integral_sub (hmul i (hS.integrable_units π hp i).2.1)
        (hmul i (hS.integrable_units π hp i).2.2),
      integral_sub (hmul i (hS.integrable_units π hp i).2.1) (hmul i (h0i i)), he i]
  change (∫ ω, wATO (fun i => E.T π i ω)
    (fun i => E.observed π ω i - E.μhat π ω (E.X i ω)) ∂E.law π) = _
  simp_rw [T2_observed_coefficients, T2_average_coefficients]
  have hiH (i : Fin n) : Integrable
      (fun ω => a i ω * (E.Y1 i ω - E.μhat π ω (E.X i ω))) (E.law π) :=
    hmul i ((hS.integrable_units π hp i).2.1.sub (hS.integrable_units π hp i).2.2)
  have hi0 (i : Fin n) : Integrable
      (fun ω => a i ω * (E.Y1 i ω - E.μ0 (E.X i ω))) (E.law π) :=
    hmul i ((hS.integrable_units π hp i).2.1.sub (h0i i))
  change (∫ ω, ∑ i, a i ω * (E.Y1 i ω - E.μhat π ω (E.X i ω)) ∂E.law π) =
    ∫ ω, ∑ i, a i ω * (E.Y1 i ω - E.μ0 (E.X i ω)) ∂E.law π
  rw [integral_finsetSum _ (fun i _ => hiH i), integral_finsetSum _ (fun i _ => hi0 i)]
  exact Finset.sum_congr rfl (fun i _ => hs i)

lemma T2_actual_averages {Ω C : Type*} [MeasurableSpace Ω] [MeasurableSpace C]
    {n : ℕ} (E : Experiment Ω C n) (hS : Standing E) {π : C → ℝ}
    (hp : Admissible π)
    (hU : ∀ i, (E.law π)[(fun ω => E.μhat π ω (E.X i ω)) | E.vectorSigma π]
      =ᵐ[E.law π] (fun ω => E.μ0 (E.X i ω))) :
    (E.law π {ω | treatedCount (fun i => E.T π i ω) = 0}).toReal = (1-E.q π)^n ∧
    E.expectedATO π = E.averageObjective E.μ1 π ∧
    E.expectedATT π = E.averageObjective E.τ π := by
  have : IsProbabilityMeasure (E.law π) := hS.law_probability π hp
  have ht (i : Fin n) := (hS.measurable_units π hp i).2.2.2
  have hI1 : iIndepFun (fun i ω => (E.Y1 i ω,E.T π i ω)) (E.law π) :=
    (hS.iid_independent π hp).comp (fun _ z => (z.2.2.1,z.2.2.2))
      (fun _ => measurable_snd.snd.fst.prodMk measurable_snd.snd.snd)
  have hId : iIndepFun (fun i ω => (E.Y1 i ω - E.μ0 (E.X i ω), E.T π i ω)) (E.law π) :=
    (hS.iid_independent π hp).comp (fun _ z => (z.2.2.1 - E.μ0 z.1,z.2.2.2))
      (fun _ => (measurable_snd.snd.fst.sub (hS.means_measurable.1.comp measurable_fst)).prodMk
        measurable_snd.snd.snd)
  have hdi (i : Fin n) : Integrable (fun ω => E.Y1 i ω - E.μ0 (E.X i ω)) (E.law π) :=
    (hS.integrable_units π hp i).2.1.sub
      (((hS.covariate_law π hp i).comp hS.means_measurable.1).integrable_iff.mpr hS.means_integrable.1)
  have hstats := T2_treatment_stats E hS hp
  have h1 := T2_marked_average (E.law π) E.hn E.Y1 (E.T π)
    (fun i => (hS.measurable_units π hp i).2.2.1) (fun i => (hS.integrable_units π hp i).2.1)
    ht hI1 (E.q π) (E.A E.μ1 π) hstats.1 hstats.2.2 (fun i => (T2_unit_mark_moments E hS hp i).1)
  have hd := T2_marked_average (E.law π) E.hn
    (fun i ω => E.Y1 i ω - E.μ0 (E.X i ω)) (E.T π)
    (fun i => (hS.measurable_units π hp i).2.2.1.sub
      (hS.means_measurable.1.comp (hS.measurable_units π hp i).1)) hdi
    ht hId (E.q π) (E.A E.τ π) hstats.1 hstats.2.2 (fun i => (T2_unit_mark_moments E hS hp i).2)
  refine ⟨h1.1, ?_, ?_⟩
  · have heq (ω : Ω) : wATO (fun i => E.T π i ω) (E.observed π ω) =
        wATO (fun i => E.T π i ω) (fun i => E.Y1 i ω) := by
      simpa only [sub_zero] using (T2_observed_coefficients E π ω (fun _ => 0)).trans
        (T2_average_coefficients _ _).symm
    exact (integral_congr_ae (ae_of_all _ heq)).trans h1.2.2
  · exact (T2_vector_replacement E hS hp hU).trans hd.2.2

lemma T2_objective_formula {Ω C : Type*} [MeasurableSpace Ω] [MeasurableSpace C]
    {n : ℕ} (E : Experiment Ω C n) [IsProbabilityMeasure E.PX] {π : C → ℝ}
    (hp : Admissible π) (m : C → ℝ) :
    E.averageObjective m π =
      (if 0 < E.q π then (1-(1-E.q π)^n)*(E.A m π/E.q π) else 0) := by
  by_cases hq : 0 < E.q π
  · rw [if_pos hq, Experiment.averageObjective, ← T2_geometric n (E.q π)]
    field_simp
  · have hpint : Integrable π E.PX :=
      (integrable_const (1 : ℝ)).mono' hp.1.aestronglyMeasurable (ae_of_all _ (T7_policy_norm hp))
    have hq0 : E.q π = 0 :=
      le_antisymm (le_of_not_gt hq) (integral_nonneg (fun c => (hp.2 c).1))
    have hpz : π =ᵐ[E.PX] 0 :=
      (integral_eq_zero_iff_of_nonneg (fun c => (hp.2 c).1) hpint).mp hq0
    have hAz : E.A m π = 0 := by
      apply integral_eq_zero_of_ae
      filter_upwards [hpz] with c hc
      simp [hc]
    simp only [if_neg hq, Experiment.averageObjective, hAz, mul_zero]

lemma T2_event_mean {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {n : ℕ} (hn : 0 < n) (T : Fin n → Ω → Bool)
    (hT : ∀ i, Measurable (T i)) (q A : ℝ) (hq : 0 < q) (hq1 : q ≤ 1)
    (he : (μ {ω | treatedCount (fun i => T i ω) = 0}).toReal = (1-q)^n)
    (f : Ω → ℝ) (hf : ∀ ω, ¬ 0 < treatedCount (fun i => T i ω) → f ω = 0)
    (hmean : (∫ ω, f ω ∂μ) = emptyFactor n q * A) :
    eventMean μ {ω | 0 < treatedCount (fun i => T i ω)} f = A/q := by
  have hpos : 0 < 1-(1-q)^n := by
    have := pow_lt_one₀ (by linarith : 0 ≤ 1-q) (by linarith : 1-q < 1) hn.ne'
    linarith
  have hformula : emptyFactor n q * A = (1-(1-q)^n)*(A/q) := by
    rw [← T2_geometric n q]
    field_simp
  unfold eventMean
  have hrestrict : (∫ ω in {ω | 0 < treatedCount (fun i => T i ω)}, f ω ∂μ) =
      ∫ ω, f ω ∂μ :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (s := {ω | 0 < treatedCount (fun i => T i ω)}) hf
  rw [hrestrict, hmean,
    T2_nonempty_mass μ T hT q he, hformula]
  exact mul_div_cancel_left₀ _ hpos.ne'

lemma T2_best_congr {P : Type*} (S : Set P) (f g : P → ℝ)
    (h : ∀ p ∈ S, f p = g p) (p : P) : IsBest S f p ↔ IsBest S g p := by
  constructor
  · rintro ⟨hp,hbest⟩
    refine ⟨hp, ?_⟩
    intro r hr
    rw [← h r hr, ← h p hp]
    exact hbest r hr
  · rintro ⟨hp,hbest⟩
    refine ⟨hp, ?_⟩
    intro r hr
    rw [h r hr, h p hp]
    exact hbest r hr

theorem T2_corrected_average_proof {Ω C : Type*} [MeasurableSpace Ω]
    [MeasurableSpace C] [Countable C] [MeasurableSingletonClass C] {n : ℕ}
    (E : Experiment Ω C n) (hS : Standing E)
    (hU : VectorUnbiased E {π | Admissible π}) :
    (∀ π, Admissible π →
      (E.law π {ω | treatedCount (fun i => E.T π i ω) = 0}).toReal =
        (1-E.q π)^n ∧
      E.expectedATO π = E.averageObjective E.μ1 π ∧
      E.expectedATT π = E.averageObjective E.τ π ∧
      E.averageObjective E.μ1 π =
        (if 0 < E.q π then (1-(1-E.q π)^n)*(E.A E.μ1 π/E.q π) else 0) ∧
      E.averageObjective E.τ π =
        (if 0 < E.q π then (1-(1-E.q π)^n)*(E.A E.τ π/E.q π) else 0) ∧
      (0 < E.q π →
        eventMean (E.law π) {ω | 0 < treatedCount (fun i => E.T π i ω)}
          (fun ω => wATO (fun i => E.T π i ω) (E.observed π ω)) =
            E.A E.μ1 π / E.q π ∧
        eventMean (E.law π) {ω | 0 < treatedCount (fun i => E.T π i ω)}
          (fun ω => wATT (E.μhat π ω) (fun i => E.X i ω)
            (fun i => E.T π i ω) (E.observed π ω)) = E.A E.τ π / E.q π)) ∧
    (∀ π, (IsBest {π | Admissible π} E.expectedATO π ↔
       IsBest {π | Admissible π} (E.averageObjective E.μ1) π) ∧
      (IsBest {π | Admissible π} E.expectedATT π ↔
       IsBest {π | Admissible π} (E.averageObjective E.τ) π)) := by
  have : IsProbabilityMeasure E.PX := hS.px_probability
  have hpolicy : (∀ π, Admissible π →
      (E.law π {ω | treatedCount (fun i => E.T π i ω) = 0}).toReal =
        (1-E.q π)^n ∧
      E.expectedATO π = E.averageObjective E.μ1 π ∧
      E.expectedATT π = E.averageObjective E.τ π ∧
      E.averageObjective E.μ1 π =
        (if 0 < E.q π then (1-(1-E.q π)^n)*(E.A E.μ1 π/E.q π) else 0) ∧
      E.averageObjective E.τ π =
        (if 0 < E.q π then (1-(1-E.q π)^n)*(E.A E.τ π/E.q π) else 0) ∧
      (0 < E.q π →
        eventMean (E.law π) {ω | 0 < treatedCount (fun i => E.T π i ω)}
          (fun ω => wATO (fun i => E.T π i ω) (E.observed π ω)) =
            E.A E.μ1 π / E.q π ∧
        eventMean (E.law π) {ω | 0 < treatedCount (fun i => E.T π i ω)}
          (fun ω => wATT (E.μhat π ω) (fun i => E.X i ω)
            (fun i => E.T π i ω) (E.observed π ω)) = E.A E.τ π / E.q π)) := by
    intro π hp
    have : IsProbabilityMeasure (E.law π) := hS.law_probability π hp
    have ha := T2_actual_averages E hS hp (hU π hp)
    have hstats := T2_treatment_stats E hS hp
    refine And.intro ha.1 (And.intro ha.2.1 (And.intro ha.2.2
      (And.intro (T2_objective_formula E hp E.μ1)
        (And.intro (T2_objective_formula E hp E.τ) ?_))))
    intro hqpos
    constructor
    · apply T2_event_mean (E.law π) E.hn (E.T π)
        (fun i => (hS.measurable_units π hp i).2.2.2) (E.q π) (E.A E.μ1 π)
        hqpos hstats.2.1 ha.1
      · intro ω hω
        simp only [wATO, if_neg hω]
      · exact ha.2.1
    · apply T2_event_mean (E.law π) E.hn (E.T π)
        (fun i => (hS.measurable_units π hp i).2.2.2) (E.q π) (E.A E.τ π)
        hqpos hstats.2.1 ha.1
      · intro ω hω
        simp only [wATT, wATO, if_neg hω]
      · exact ha.2.2
  refine ⟨hpolicy, ?_⟩
  intro π
  exact ⟨T2_best_congr _ _ _ (fun p hp => (hpolicy p hp).2.1) π,
    T2_best_congr _ _ _ (fun p hp => (hpolicy p hp).2.2.1) π⟩

end
end AronowAudit.P006.Wave1
