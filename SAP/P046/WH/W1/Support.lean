import SAP.P046.Defs.WholeW1
import SAP.P046.Bridge
import AronowAudit.P046.Wave1.Gap.GLP046B2

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false

namespace SAP.P046.WH.W1

noncomputable section
open MeasureTheory ProbabilityTheory Filter Finset
open scoped BigOperators ENNReal

theorem measurable_X : Measurable X :=
  (measurable_of_countable bit).comp measurable_snd.fst

theorem measurable_Y0 : Measurable Y0 :=
  (measurable_of_countable bit).comp measurable_snd.snd.fst

theorem measurable_Y1 : Measurable Y1 :=
  (measurable_of_countable bit).comp measurable_snd.snd.snd

theorem measurable_Y : Measurable Y :=
  ((measurable_const.sub measurable_X).mul measurable_Y0).add (measurable_X.mul measurable_Y1)

theorem measurable_htUnit (M : Study) (hM : ValidStudy M) :
    Measurable (fun o => htTerm (M.pi (W o)) (X o) (Y o)) :=
  (measurable_X.mul measurable_Y).div (hM.measurable_pi.comp measurable_fst)

theorem measurable_ht (M : Study) (hM : ValidStudy M) (n : ℕ) :
    Measurable (ht M (n := n)) :=
  (Finset.measurable_sum univ (fun i _ =>
    (measurable_htUnit M hM).comp (measurable_pi_apply i))).div_const n

theorem measurable_xi (M : Study) (hM : ValidStudy M) (n : ℕ) :
    Measurable (xi M (n := n)) :=
  (Finset.measurable_sum univ (fun i _ =>
    ((hM.measurable_pi.comp measurable_fst).comp (measurable_pi_apply i)).inv.pow_const 2)).div_const n

theorem measurable_muW (M : Study) (hM : ValidStudy M) (n : ℕ) :
    Measurable (muW M (n := n)) :=
  (Finset.measurable_sum univ (fun i _ =>
    (hM.measurable_m.comp measurable_fst).comp (measurable_pi_apply i))).div_const n

theorem measurable_printed (M : Study) (hM : ValidStudy M) (n : ℕ) (alpha : ℝ) :
    Measurable (printedRadius M alpha (n := n)) :=
  (((measurable_xi M hM n).mul_const _).div_const _).sqrt

theorem measurable_corrected (M : Study) (hM : ValidStudy M) (n : ℕ) (alpha : ℝ) :
    Measurable (correctedRadius M alpha (n := n)) :=
  ((measurable_xi M hM n).sqrt.add_const 1).mul_const _

theorem iid_sample (M : Study) (hM : ValidStudy M) (n : ℕ) (f : Unit → ℝ)
    (hf : Measurable f) : WholeIID M n f := by
  letI := hM.probability
  refine ⟨iIndepFun_pi (fun _ => hf.aemeasurable), ?_⟩
  intro i
  have he := (measurePreserving_eval (fun _ : Fin n => M.law) i).map_eq
  calc
    _ = Measure.map f (Measure.map (fun a : Sample n => a i) (sampleLaw M n)) :=
      (Measure.map_map hf (measurable_pi_apply i)).symm
    _ = _ := congrArg (Measure.map f) he

theorem coverage_complement (M : Study) (hM : ValidStudy M) {n : ℕ}
    (est radius : Sample n → ℝ) (he : Measurable est) (hr : Measurable radius) :
    wholeCoverage M est radius =
      1 - (sampleLaw M n {a | radius a < |est a - mu M|}).toReal := by
  letI := hM.probability
  have hset : {a : Sample n | est a - radius a ≤ mu M ∧ mu M ≤ est a + radius a} =
      {a | radius a < |est a - mu M|}ᶜ := by
    ext a
    simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, not_lt, abs_le]
    constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
  have hs : MeasurableSet {a : Sample n | radius a < |est a - mu M|} :=
    measurableSet_lt hr (he.sub_const _).abs
  change (sampleLaw M n).real _ = _
  rw [hset, measureReal_compl hs, probReal_univ]
  rfl

theorem coverage_of_tail (M : Study) (hM : ValidStudy M) {n : ℕ}
    (est radius : Sample n → ℝ) (he : Measurable est) (hr : Measurable radius)
    (alpha : ℝ) (htail : tailProb M est radius ≤ alpha) :
    1 - alpha ≤ wholeCoverage M est radius := by
  letI := hM.probability
  rw [coverage_complement M hM est radius he hr]
  have hm : (sampleLaw M n {a | radius a < |est a - mu M|}).toReal ≤
      tailProb M est radius := by
    exact ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (fun a h => show radius a ≤ |est a - mu M| from h.le))
  linarith

theorem counts_feasible {n : ℕ} (a : Sample n) : wholeS a ≤ wholeK a ∧ wholeK a ≤ n := by
  classical
  constructor
  · apply card_le_card
    intro i hi
    simp only [mem_filter, mem_univ, true_and] at hi
    simp only [mem_filter, mem_univ, true_and]
    rw [hi]
    decide
  · exact (card_filter_le ..).trans_eq (by simp)

theorem count_law : WholeT1CountLaw := by
  classical
  have hc := AronowAudit.P046.Wave1.PropositionThree.n3_proof
  refine ⟨hc.1, hc.2, ?_⟩
  intro k s hs hk
  letI := Bridge.target1.1.probability
  have h := AronowAudit.P046.Wave1.PropositionThree.n4_proof IntervalExample.study.law
    wholeCat hc.1 (![39 / 100, 21 / 100, 40 / 100]) (by intro j; fin_cases j <;> norm_num)
      hc.2 100 k s hs hk
  change _ = ENNReal.ofReal _ at h
  change sampleLaw IntervalExample.study 100 _ = ENNReal.ofReal _ at h
  unfold wholeK wholeS
  rw [h]
  congr 1
  dsimp [wholeCountMass]
  simp only [div_pow]
  have hp : (100 : ℝ) ^ s * 100 ^ (k - s) * 100 ^ (100 - k) = 100 ^ 100 := by
    rw [← pow_add, ← pow_add]
    congr 1
    omega
  calc
    _ = (100 : ℕ).choose k * (k.choose s : ℝ) * 39 ^ s * 21 ^ (k - s) * 40 ^ (100 - k) /
        (100 ^ s * 100 ^ (k - s) * 100 ^ (100 - k)) := by ring
    _ = _ := by rw [hp]

theorem count_exclusion (k s : ℕ) (_hs : s ≤ k) (hk : k ≤ 100) :
    0 < IntervalExample.xiK k ∧
    (Real.sqrt (IntervalExample.xiK k * Real.log 20000000 / 200) <
        |(s : ℝ) / 65 - 3 / 5| ↔
      IntervalExample.xiK k * Real.log 20000000 / 200 < ((s : ℝ) - 39) ^ 2 / 65 ^ 2) ∧
    (IntervalExample.xiK k * Real.log 20000000 / 200 < ((s : ℝ) - 39) ^ 2 / 65 ^ 2 ↔
      Real.log 20000000 < wholeCountThreshold k s) := by
  have hkR : (k : ℝ) ≤ 100 := by exact_mod_cast hk
  have hx : 0 < IntervalExample.xiK k := by
    dsimp [IntervalExample.xiK]
    have hkn : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    linarith
  refine ⟨hx, ?_, ?_⟩
  · have hsq : ((s : ℝ) / 65 - 3 / 5) ^ 2 = ((s : ℝ) - 39) ^ 2 / 65 ^ 2 := by ring
    rw [← hsq, ← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_lt_sqrt_iff (by positivity)
  · dsimp [wholeCountThreshold]
    rw [lt_div_iff₀ (mul_pos (by norm_num) hx)]
    constructor <;> intro h <;> nlinarith

theorem whole_exp (n : ℕ) (hn : 0 < n) (alpha : ℝ) (ha : 0 < alpha ∧ alpha < 1) :
    2 * Real.exp (-2 * n * (wholeC n alpha) ^ 2) =
      2 * Real.exp (-Real.log (4 / alpha)) ∧
    2 * Real.exp (-Real.log (4 / alpha)) = alpha / 2 := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hlog : 0 < Real.log (4 / alpha) := Real.log_pos (by
    rw [lt_div_iff₀ ha.1]
    linarith [ha.2])
  constructor
  · congr 1
    unfold wholeC
    rw [Real.sq_sqrt (by positivity)]
    field_simp
  · rw [Real.exp_neg, Real.exp_log (div_pos (by norm_num) ha.1)]
    field_simp
    ring

theorem t3_sampling : WholeT3Sampling := by
  intro M hM
  refine ⟨fun n => iid_sample M hM n _ (hM.measurable_m.comp measurable_fst),
    hM.regression_range, AronowAudit.P046.regression_mean (Bridge.toStudy M) (Bridge.valid_to hM), ?_⟩
  intro n hn alpha ha
  exact ⟨AronowAudit.P046.covariate_hoeffding (Bridge.toStudy M) (Bridge.valid_to hM)
    n hn (wholeC n alpha) (Real.sqrt_nonneg _), whole_exp n hn alpha ha⟩

theorem t3_fixed (hs : WholeT3Structure) : WholeT3FixedTail := by
  intro M hM n hn t ht
  have hc := AronowAudit.P046.Wave1.conditional_hoeffding_proof
    (Bridge.toStudy M) (Bridge.valid_to hM) n hn t ht
  filter_upwards [hc, (hs M hM n hn).2] with a hc ha
  have hnR : (n : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr hn)
  have hd : -2 * t ^ 2 / wholeDenom M a = -2 * n * t ^ 2 / xi M a := by
    rw [ha.2.2.2.1]
    field_simp
  exact ⟨by rw [hd]; exact hc, congrArg (fun z : ℝ => 2 * Real.exp z) hd⟩

theorem t3_union (hr : WholeT3RandomTail) : WholeT3Union := by
  intro M hM n hn alpha ha
  letI := hM.probability
  have htri (a : Sample n) : |ht M a - mu M| ≤ |ht M a - muW M a| + |muW M a - mu M| := by
    convert abs_add_le (ht M a - muW M a) (muW M a - mu M) using 1; ring_nf
  have hset : {a : Sample n | correctedRadius M alpha a ≤ |ht M a - mu M|} ⊆
      wholeConditionalError M n alpha ∪ wholeCovariateError M n alpha := by
    intro a ha'
    change Real.sqrt (xi M a) * wholeC n alpha ≤ |ht M a - muW M a| ∨
      wholeC n alpha ≤ |muW M a - mu M|
    by_contra h
    simp only [not_or, not_le] at h
    have he : correctedRadius M alpha a = Real.sqrt (xi M a) * wholeC n alpha + wholeC n alpha := by
      unfold correctedRadius wholeC
      ring
    change correctedRadius M alpha a ≤ |ht M a - mu M| at ha'
    rw [he] at ha'
    linarith [htri a]
  have hu : tailProb M (ht M) (correctedRadius M alpha (n := n)) ≤
      (sampleLaw M n (wholeConditionalError M n alpha)).toReal +
      (sampleLaw M n (wholeCovariateError M n alpha)).toReal := by
    exact (measureReal_mono (μ := sampleLaw M n) hset).trans (measureReal_union_le ..)
  have hsum : (sampleLaw M n (wholeConditionalError M n alpha)).toReal +
      (sampleLaw M n (wholeCovariateError M n alpha)).toReal ≤ alpha := by
    have hc := (hr M hM n hn alpha ha).2
    have hm := t3_sampling M hM |>.2.2.2 n hn alpha ha
    rw [hm.2.1, hm.2.2] at hm
    linarith [hm.1]
  exact ⟨htri, hset, hu, hsum, coverage_of_tail M hM _ _ (measurable_ht M hM n)
    (measurable_corrected M hM n alpha) alpha (hu.trans hsum)⟩

theorem t3_known : WholeT3Known := by
  intro M hM b hb hbound
  letI := hM.probability
  have mf := measurable_htUnit M hM
  have hmean : (∫ o, htTerm (M.pi (W o)) (X o) (Y o) ∂M.law) = mu M :=
    (AronowAudit.P046.ht_unit_facts (Bridge.toStudy M) (Bridge.valid_to hM)).2
  have hrange : ∀ᵐ o ∂M.law, 0 ≤ htTerm (M.pi (W o)) (X o) (Y o) ∧
      htTerm (M.pi (W o)) (X o) (Y o) ≤ b⁻¹ := by
    filter_upwards [hbound] with o ho
    have hp : 0 < M.pi (W o) := hb.trans_le ho
    have hi : (M.pi (W o))⁻¹ ≤ b⁻¹ := (inv_le_inv₀ hp hb).2 ho
    have ht : 0 ≤ htTerm (M.pi (W o)) (X o) (Y o) ∧
        htTerm (M.pi (W o)) (X o) (Y o) ≤ (M.pi (W o))⁻¹ := by
      simp only [htTerm]
      rcases o with ⟨w, x, y0, y1⟩
      cases x <;> cases y1 <;> simp [Y, Y0, X, Y1, bit, one_div, (inv_pos.mpr hp).le]
    exact ⟨ht.1, ht.2.trans hi⟩
  refine ⟨fun n => iid_sample M hM n _ mf, hrange, hmean, ?_, ?_⟩
  · intro n hn t ht
    have h := AronowAudit.P046.iid_mean_hoeffding M.law _ mf b⁻¹ (inv_pos.mpr hb) hrange n hn t ht
    rw [hmean] at h
    exact h
  · intro n hn alpha ha
    have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
    have hlog : 0 < Real.log (2 / alpha) := Real.log_pos (by
      rw [lt_div_iff₀ ha.1]
      linarith [ha.2])
    have he : -2 * n * (b⁻¹ * Real.sqrt (Real.log (2 / alpha) / (2 * n))) ^ 2 / (b⁻¹) ^ 2 =
        -Real.log (2 / alpha) := by
      rw [mul_pow, Real.sq_sqrt (by positivity)]
      field_simp
    refine ⟨?_, coverage_of_tail M hM _ _ (measurable_ht M hM n) measurable_const alpha
      (AronowAudit.P046.proposition3_known_bound (Bridge.toStudy M) (Bridge.valid_to hM)
        b hb hbound n hn alpha ha)⟩
    rw [he, Real.exp_neg, Real.exp_log (div_pos (by norm_num) ha.1)]
    field_simp

theorem measurable_wholeA : Measurable wholeA := by
  have mg : Measurable (RegressionExample.prediction 0) :=
    ((RegressionExample.fits 0).measurable_g false).comp
      (measurable_const.prodMk measurable_id :
        Measurable (fun w : ℝ => (((fun i : Fin 0 => Fin.elim0 i) : Sample 0), w)))
  unfold wholeA adjustedTerm
  exact ((measurable_X.mul (measurable_Y.sub (mg.comp measurable_fst))).div
    (Bridge.target4.1.measurable_pi.comp measurable_fst)).add (mg.comp measurable_fst)

end
end SAP.P046.WH.W1
