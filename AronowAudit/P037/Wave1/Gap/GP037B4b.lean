import AronowAudit.P037.P037_Bootstrap
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.Probability.Independence.Basic
import Mathlib.Tactic.FinCases

namespace AronowAudit.P037.Wave1
set_option autoImplicit false
open MeasureTheory Set
open scoped BigOperators ENNReal

private def GP037B4b_cap (m : ℕ) (t : ℝ) : Set (Fin m → ℝ) :=
  {p | (∀ i, 0 < p i) ∧ ∑ i, p i < t}

private theorem GP037B4b_cap_measurable (m : ℕ) (t : ℝ) :
    MeasurableSet (GP037B4b_cap m t) := by
  have hp : MeasurableSet {p : Fin m → ℝ | ∀ i, 0 < p i} := by
    simp only [setOf_forall]
    exact MeasurableSet.iInter fun i => measurableSet_lt measurable_const (measurable_pi_apply i)
  exact hp.inter (measurableSet_lt
    (Finset.measurable_sum _ (fun i _ => measurable_pi_apply i)) measurable_const)

private theorem GP037B4b_cap_section (m : ℕ) (t x : ℝ) :
    (fun y : Fin m → ℝ => Fin.cons x y) ⁻¹' GP037B4b_cap (m+1) t =
      if 0 < x ∧ x < t then GP037B4b_cap m (t-x) else ∅ := by
  classical
  ext y
  simp only [Set.mem_preimage, GP037B4b_cap, Set.mem_setOf_eq,
    Fin.forall_fin_succ, Fin.cons_zero, Fin.cons_succ, Fin.sum_univ_succ]
  split_ifs with hx
  · simp only [Set.mem_setOf_eq]
    constructor
    · rintro ⟨⟨_,hy⟩,hs⟩; exact ⟨hy, by linarith⟩
    · rintro ⟨hy,hs⟩; exact ⟨⟨hx.1,hy⟩, by linarith⟩
  · simp only [Set.mem_empty_iff_false, iff_false, not_and]
    rintro ⟨hx0,hy⟩ hs
    have hsum : 0 ≤ ∑ i, y i := Finset.sum_nonneg fun i _ => (hy i).le
    exact hx ⟨hx0, by linarith⟩

private theorem GP037B4b_cap_slice (m : ℕ) (t : ℝ) :
    volume (GP037B4b_cap (m+1) t) =
      ∫⁻ x : ℝ in Ioo 0 t, volume (GP037B4b_cap m (t-x)) := by
  classical
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m+1) => ℝ) 0
  have he := (volume_preserving_piFinSuccAbove (fun _ : Fin (m+1) => ℝ) 0).symm
  rw [← he.measure_preimage_equiv (GP037B4b_cap (m+1) t)]
  change (volume.prod volume) (e.symm ⁻¹' GP037B4b_cap (m+1) t) = _
  rw [Measure.prod_apply ((GP037B4b_cap_measurable (m+1) t).preimage e.symm.measurable)]
  rw [← lintegral_indicator measurableSet_Ioo]
  apply lintegral_congr
  intro x
  have heq : (fun y : Fin m → ℝ => e.symm (x,y)) =
      (fun y => Fin.cons (α := fun _ : Fin (m+1) => ℝ) x y) := by
    funext y
    simp [e, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.consEquiv]
  change volume ((fun y : Fin m → ℝ => e.symm (x,y)) ⁻¹' GP037B4b_cap (m+1) t) = _
  rw [heq, GP037B4b_cap_section]
  by_cases hx : x ∈ Ioo 0 t <;> simp [← Set.mem_Ioo, hx, Set.indicator]

private theorem GP037B4b_power_integral (m : ℕ) (t : ℝ) (ht : 0 < t) :
    (∫⁻ x : ℝ in Ioo 0 t, ENNReal.ofReal ((t-x)^m / m.factorial)) =
      ENNReal.ofReal (t^(m+1) / (m+1).factorial) := by
  have hf : IntegrableOn (fun x : ℝ => (t-x)^m / (m.factorial : ℝ)) (Ioo 0 t) :=
    (Continuous.div_const ((continuous_const.sub continuous_id).pow m) _).integrableOn_Icc.mono_set
      Ioo_subset_Icc_self
  rw [← ofReal_integral_eq_lintegral_ofReal hf]
  · congr 1
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le ht.le,
      intervalIntegral.integral_div,
      intervalIntegral.integral_comp_sub_left (fun x : ℝ => x^m) t,
      sub_self, sub_zero, integral_pow]
    simp only [zero_pow (Nat.succ_ne_zero _), sub_zero, Nat.factorial_succ, Nat.cast_mul,
      Nat.cast_add, Nat.cast_one]
    rw [div_div]
  · exact ae_restrict_of_forall_mem measurableSet_Ioo fun x hx =>
      div_nonneg (pow_nonneg (by linarith [hx.2]) _) (Nat.cast_nonneg _)

/-- Integrating one positive coordinate at a time gives the simplex volume. -/
private theorem GP037B4b_cap_volume (m : ℕ) (t : ℝ) (ht : 0 < t) :
    volume (GP037B4b_cap m t) = ENNReal.ofReal (t^m / m.factorial) := by
  induction m generalizing t with
  | zero =>
    have hs : GP037B4b_cap 0 t = Set.univ := by
      ext p
      simp [GP037B4b_cap, ht]
    rw [hs]
    simp [volume_pi]
  | succ m ih =>
    rw [GP037B4b_cap_slice]
    calc
      (∫⁻ x : ℝ in Ioo 0 t, volume (GP037B4b_cap m (t-x))) =
          ∫⁻ x : ℝ in Ioo 0 t, ENNReal.ofReal ((t-x)^m / m.factorial) := by
        apply setLIntegral_congr_fun measurableSet_Ioo
        intro x hx
        exact ih (t-x) (by linarith [hx.2])
      _ = _ := GP037B4b_power_integral m t ht

private def GP037B4b_headCut (m : ℕ) : Set (Fin (m+1) → ℝ) :=
  GP037B4b_cap (m+1) 1 ∩ {p | p 0 < (1 - ∑ j : Fin m, p j.succ) / 4}

private theorem GP037B4b_headCut_measurable (m : ℕ) :
    MeasurableSet (GP037B4b_headCut m) := by
  exact (GP037B4b_cap_measurable _ _).inter
    (measurableSet_lt (measurable_pi_apply 0)
      ((measurable_const.sub (Finset.measurable_sum _
        (fun j _ => measurable_pi_apply j.succ))).div_const 4))

private theorem GP037B4b_head_sections (m : ℕ) (y : Fin m → ℝ) :
    (fun x : ℝ => Fin.cons x y) ⁻¹' GP037B4b_cap (m+1) 1 =
      if ∀ j, 0 < y j then Ioo 0 (1 - ∑ j, y j) else ∅ := by
  classical
  ext x
  simp only [Set.mem_preimage, GP037B4b_cap, Set.mem_setOf_eq, Fin.forall_fin_succ,
    Fin.cons_zero, Fin.cons_succ, Fin.sum_univ_succ]
  split_ifs with hy <;> simp only [Set.mem_Ioo, Set.mem_empty_iff_false]
  · constructor
    · rintro ⟨⟨hx,_⟩,hs⟩; exact ⟨hx,by linarith⟩
    · rintro ⟨hx,hs⟩; exact ⟨⟨hx,hy⟩,by linarith⟩
  · simp [hy]

private theorem GP037B4b_cut_sections (m : ℕ) (y : Fin m → ℝ) :
    (fun x : ℝ => Fin.cons x y) ⁻¹' GP037B4b_headCut m =
      if ∀ j, 0 < y j then Ioo 0 ((1 - ∑ j, y j) / 4) else ∅ := by
  classical
  ext x
  simp only [GP037B4b_headCut, Set.preimage_inter, GP037B4b_head_sections,
    Set.mem_inter_iff, Set.mem_preimage, Set.mem_setOf_eq, Fin.cons_zero, Fin.cons_succ]
  split_ifs with hy <;> simp only [Set.mem_Ioo, Set.mem_empty_iff_false, false_and]
  constructor
  · exact fun h => ⟨h.1.1,h.2⟩
  · rintro ⟨hx,hs⟩; exact ⟨⟨hx,by linarith⟩,hs⟩

/-- Every nonempty section in the first coordinate is shortened by a factor of four. -/
private theorem GP037B4b_headCut_volume (m : ℕ) :
    volume (GP037B4b_headCut m) = (ENNReal.ofReal (1/4:ℝ)) *
      volume (GP037B4b_cap (m+1) 1) := by
  classical
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m+1) => ℝ) 0
  have he := (volume_preserving_piFinSuccAbove (fun _ : Fin (m+1) => ℝ) 0).symm
  rw [← he.measure_preimage_equiv (GP037B4b_headCut m),
    ← he.measure_preimage_equiv (GP037B4b_cap (m+1) 1)]
  change (volume.prod volume) (e.symm ⁻¹' GP037B4b_headCut m) =
    _ * (volume.prod volume) (e.symm ⁻¹' GP037B4b_cap (m+1) 1)
  rw [Measure.prod_apply_symm ((GP037B4b_headCut_measurable m).preimage e.symm.measurable),
    Measure.prod_apply_symm ((GP037B4b_cap_measurable (m+1) 1).preimage e.symm.measurable),
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_congr
  intro y
  have heq : (fun x : ℝ => e.symm (x,y)) =
      (fun x => Fin.cons (α := fun _ : Fin (m+1) => ℝ) x y) := by
    funext x
    simp [e, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.consEquiv]
  change volume ((fun x : ℝ => e.symm (x,y)) ⁻¹' GP037B4b_headCut m) =
    _ * volume ((fun x : ℝ => e.symm (x,y)) ⁻¹' GP037B4b_cap (m+1) 1)
  rw [heq, GP037B4b_cut_sections, GP037B4b_head_sections]
  by_cases hy : ∀ j, 0 < y j
  · simp only [if_pos hy, Real.volume_Ioo, sub_zero]
    rw [div_eq_mul_inv, mul_comm, ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 4⁻¹)]
    norm_num
  · simp [hy]

/-- Swap one free coordinate with the unrecorded final simplex mass. -/
private noncomputable def GP037B4b_swapSlack (m : ℕ) (i : Fin (m+1))
    (p : Fin (m+1) → ℝ) : Fin (m+1) → ℝ :=
  Function.update p i (1 - ∑ j, p j)

private theorem GP037B4b_swapSlack_preserving (m : ℕ) (i : Fin (m+1)) :
    MeasurePreserving (GP037B4b_swapSlack m i) volume volume := by
  classical
  have he := volume_preserving_piFinSuccAbove (fun _ : Fin (m+1) => ℝ) i
  have hg : MeasurePreserving
      (fun q : (Fin m → ℝ) × ℝ => (q.1, 1 - (∑ j, q.1 j) - q.2))
      (volume.prod volume) (volume.prod volume) := by
    apply (MeasurePreserving.id (volume : Measure (Fin m → ℝ))).skew_product
      (g := fun y x => 1 - (∑ j, y j) - x)
    · exact (measurable_const.sub (Finset.measurable_sum _
        (fun j _ => (measurable_pi_apply j).comp measurable_fst))).sub measurable_snd
    · exact Filter.Eventually.of_forall fun y =>
        (Measure.measurePreserving_sub_left (volume : Measure ℝ) (1 - ∑ j, y j)).map_eq
  have h := he.symm.comp ((Measure.measurePreserving_swap.comp hg).comp
    (Measure.measurePreserving_swap.comp he))
  convert h using 1
  funext p
  change Function.update p i (1 - ∑ j, p j) =
    i.insertNth (1 - (∑ j, p (i.succAbove j)) - p i) (fun j => p (i.succAbove j))
  apply Fin.eq_insertNth_iff.mpr
  constructor
  · simp only [Function.update_self]
    rw [Fin.sum_univ_succAbove _ i]
    ring
  · funext j
    simp [Fin.removeNth, Fin.succAbove_ne]

private theorem GP037B4b_swapSlack_sum (m : ℕ) (i : Fin (m+1))
    (p : Fin (m+1) → ℝ) : ∑ j, GP037B4b_swapSlack m i p j = 1 - p i := by
  classical
  rw [Fin.sum_univ_succAbove _ i]
  simp only [GP037B4b_swapSlack, Function.update_self,
    Function.update_of_ne (Fin.succAbove_ne _ _)]
  rw [Fin.sum_univ_succAbove p i]
  ring

private theorem GP037B4b_swapSlack_cap (m : ℕ) (i : Fin (m+1)) :
    (GP037B4b_swapSlack m i) ⁻¹' GP037B4b_cap (m+1) 1 =
      GP037B4b_cap (m+1) 1 := by
  classical
  ext p
  change ((∀ j, 0 < GP037B4b_swapSlack m i p j) ∧
    ∑ j, GP037B4b_swapSlack m i p j < 1) ↔ ((∀ j, 0 < p j) ∧ ∑ j, p j < 1)
  rw [GP037B4b_swapSlack_sum]
  simp only [Fin.forall_iff_succAbove i, GP037B4b_swapSlack, Function.update_self,
    Function.update_of_ne (Fin.succAbove_ne _ _)]
  constructor
  · rintro ⟨⟨hs,hp⟩,hi⟩
    exact ⟨⟨by linarith,hp⟩,by linarith⟩
  · rintro ⟨⟨hi,hp⟩,hs⟩
    exact ⟨⟨by linarith,hp⟩,by linarith⟩

private theorem GP037B4b_completion_measurable (m : ℕ) : Measurable (completeSimplex m) := by
  apply measurable_pi_lambda
  intro i
  unfold completeSimplex
  split_ifs
  · exact measurable_pi_apply _
  · exact measurable_const.sub (Finset.measurable_sum _ (fun j _ => measurable_pi_apply j))

private theorem GP037B4b_event_measurable (n : ℕ) :
    MeasurableSet (bootstrapWitnessEvent n) := by
  exact measurableSet_lt ((measurable_pi_apply 0).div
    ((measurable_pi_apply 0).add (measurable_pi_apply 1))) measurable_const

/-- Swapping the second mass with the final mass turns the ratio event into `GP037B4b_headCut`.
With only two masses the event already has that form. -/
private theorem GP037B4b_simplex_event_set (n : ℕ) :
    volume ((completeSimplex (n+1)) ⁻¹' bootstrapWitnessEvent n ∩
      GP037B4b_cap (n+1) 1) = volume (GP037B4b_headCut n) := by
  classical
  cases n with
  | zero =>
    congr 1
    ext p
    have hcomp : completeSimplex 1 p = ![p 0, 1 - p 0] := by
      ext j
      fin_cases j <;> simp [completeSimplex]
    change (completeSimplex 1 p 0 / (completeSimplex 1 p 0 + completeSimplex 1 p 1) <
      (1:ℝ)/4 ∧ p ∈ GP037B4b_cap 1 1) ↔ p ∈ GP037B4b_headCut 0
    simp [hcomp, GP037B4b_headCut, and_comm]
  | succ k =>
    let i : Fin (k+2) := 1
    let A : Set (Fin (k+2) → ℝ) :=
      (completeSimplex (k+2)) ⁻¹' bootstrapWitnessEvent (k+1) ∩ GP037B4b_cap (k+2) 1
    have hA : MeasurableSet A :=
      ((GP037B4b_event_measurable _).preimage (GP037B4b_completion_measurable _)).inter
        (GP037B4b_cap_measurable _ _)
    have hs : (GP037B4b_swapSlack (k+1) i) ⁻¹' A = GP037B4b_headCut (k+1) := by
      rw [show A = _ by rfl, Set.preimage_inter, GP037B4b_swapSlack_cap]
      ext p
      by_cases hp : p ∈ GP037B4b_cap (k+2) 1
      · have hu : 0 < p 0 := hp.1 0
        have hv : 0 < 1 - ∑ j, p j := by linarith [hp.2]
        have hsum : p 0 + (1 - ∑ j, p j) = 1 - ∑ j : Fin (k+1), p j.succ := by
          rw [Fin.sum_univ_succ]
          ring
        change ((_ ∈ bootstrapWitnessEvent (k+1)) ∧ _) ↔ _
        simp only [GP037B4b_headCut, Set.mem_inter_iff, hp, and_true, true_and,
          Set.mem_setOf_eq]
        have h0 : completeSimplex (k+2) (GP037B4b_swapSlack (k+1) i p) 0 = p 0 := by
          simp [completeSimplex, GP037B4b_swapSlack, i]
        have h1 : completeSimplex (k+2) (GP037B4b_swapSlack (k+1) i p) 1 =
            1 - ∑ j, p j := by
          simp [completeSimplex, GP037B4b_swapSlack, i, show 1 < k+2 by omega,
            Nat.mod_eq_of_lt (show 1 < k+2+1 by omega)]
          have heq (h : 1 % (k+2+1) < k+2) :
              (⟨1 % (k+2+1), h⟩ : Fin (k+2)) = 1 := by
            apply Fin.ext
            change 1 % (k+2+1) = 1 % (k+2)
            rw [Nat.mod_eq_of_lt (show 1 < k+2+1 by omega),
              Nat.mod_eq_of_lt (show 1 < k+2 by omega)]
          rw [heq, Function.update_self]
        change _ / (_ + _) < (1:ℝ)/4 ↔ _
        rw [h0,h1, div_lt_iff₀ (add_pos hu hv), hsum]
        simp only [div_eq_mul_inv, one_mul, mul_comm]
      · simp [GP037B4b_headCut, hp]
    change volume A = _
    rw [← (GP037B4b_swapSlack_preserving (k+1) i).measure_preimage hA.nullMeasurableSet, hs]

private theorem GP037B4b_bayesian_probability (n : ℕ) :
    (bayesianBootstrapLaw (n+1) (bootstrapWitnessEvent n)).toReal = 1/4 := by
  have hpre : MeasurableSet ((completeSimplex (n+1)) ⁻¹' bootstrapWitnessEvent n) :=
    (GP037B4b_event_measurable n).preimage (GP037B4b_completion_measurable (n+1))
  rw [bayesianBootstrapLaw, Measure.map_apply (GP037B4b_completion_measurable _)
    (GP037B4b_event_measurable _), Measure.smul_apply, smul_eq_mul,
    Measure.restrict_apply hpre]
  change ((↑(n+1).factorial : ℝ≥0∞) * volume
    ((completeSimplex (n+1)) ⁻¹' bootstrapWitnessEvent n ∩ GP037B4b_cap (n+1) 1)).toReal = _
  rw [GP037B4b_simplex_event_set, GP037B4b_headCut_volume,
    GP037B4b_cap_volume (n+1) 1 zero_lt_one]
  have hf : (0:ℝ) < (n+1).factorial := Nat.cast_pos.mpr (Nat.factorial_pos _)
  simp only [one_pow, ENNReal.toReal_mul, ENNReal.toReal_natCast,
    ENNReal.toReal_ofReal (by norm_num : (0:ℝ) ≤ 1/4),
    ENNReal.toReal_ofReal (le_of_lt (one_div_pos.mpr hf))]
  field_simp

private theorem GP037B4b_normalize_measurable (m : ℕ) :
    Measurable (@normalizeWeights m) := by
  apply measurable_pi_lambda
  intro i
  exact (measurable_pi_apply i).div
    (Finset.measurable_sum _ (fun j _ => measurable_pi_apply j))

private theorem GP037B4b_uniform_probability : IsProbabilityMeasure unitUniformLaw := by
  constructor
  norm_num [unitUniformLaw, Real.volume_Ioo]

private theorem GP037B4b_uniform_positive : ∀ᵐ x : ℝ ∂unitUniformLaw, 0 < x := by
  have h := ae_restrict_mem (μ := (volume : Measure ℝ)) (s := Ioo 0 1) measurableSet_Ioo
  exact h.mono fun _ hx => hx.1

private theorem GP037B4b_uniform_pair (n : ℕ) :
    Measure.map (fun w : Fin (n+2) → ℝ => (w 0, w 1))
      (Measure.pi (fun _ => unitUniformLaw)) = unitUniformLaw.prod unitUniformLaw := by
  have GP037B4b_instUniform : IsProbabilityMeasure unitUniformLaw := GP037B4b_uniform_probability
  have hind := ProbabilityTheory.iIndepFun_pi
    (μ := fun _ : Fin (n+2) => unitUniformLaw) (X := fun _ => id)
    (fun _ => measurable_id.aemeasurable)
  have hp := (hind.indepFun (show (0 : Fin (n+2)) ≠ 1 by simp)).map_prod_eq_prod_map_map
    (measurable_pi_apply 0).aemeasurable (measurable_pi_apply 1).aemeasurable
  simpa only [(measurePreserving_eval (fun _ : Fin (n+2) => unitUniformLaw) 0).map_eq,
    (measurePreserving_eval (fun _ : Fin (n+2) => unitUniformLaw) 1).map_eq] using hp

private theorem GP037B4b_uniform_triangle :
    (unitUniformLaw.prod unitUniformLaw) {p : ℝ × ℝ | p.1 < p.2/3} =
      ENNReal.ofReal (1/6:ℝ) := by
  have GP037B4b_instUniform : IsProbabilityMeasure unitUniformLaw := GP037B4b_uniform_probability
  have hset : MeasurableSet {p : ℝ × ℝ | p.1 < p.2/3} :=
    measurableSet_lt measurable_fst (measurable_snd.div_const 3)
  rw [Measure.prod_apply_symm hset]
  change (∫⁻ v : ℝ in Ioo 0 1, unitUniformLaw {u : ℝ | u < v/3}) = _
  calc
    (∫⁻ v : ℝ in Ioo 0 1, unitUniformLaw {u : ℝ | u < v/3}) =
        ∫⁻ v : ℝ in Ioo 0 1, ENNReal.ofReal (v/3) := by
      apply setLIntegral_congr_fun measurableSet_Ioo
      intro v hv
      change unitUniformLaw {u : ℝ | u < v/3} = ENNReal.ofReal (v/3)
      rw [unitUniformLaw, Measure.restrict_apply
        (measurableSet_lt measurable_id' measurable_const)]
      have he : {u : ℝ | u < v/3} ∩ Ioo 0 1 = Ioo 0 (v/3) := by
        ext u
        simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_Ioo]
        constructor
        · exact fun h => ⟨h.2.1,h.1⟩
        · rintro ⟨hu0,huv⟩; exact ⟨huv,hu0,by linarith [hv.2]⟩
      rw [he, Real.volume_Ioo, sub_zero]
    _ = ENNReal.ofReal (1/6:ℝ) := by
      rw [← ofReal_integral_eq_lintegral_ofReal]
      · congr 1
        rw [← integral_Ioc_eq_integral_Ioo,
          ← intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1),
          intervalIntegral.integral_div, integral_id]
        norm_num
      · exact (continuous_id.div_const 3).integrableOn_Icc.mono_set Ioo_subset_Icc_self
      · exact ae_restrict_of_forall_mem measurableSet_Ioo fun v hv =>
          div_nonneg hv.1.le (by norm_num)

/-- Positive normalization cancels; the remaining coordinates marginalize to probability one. -/
private theorem GP037B4b_uniform_probability_event (n : ℕ) :
    (normalizedUniformLaw n (bootstrapWitnessEvent n)).toReal = 1/6 := by
  classical
  have GP037B4b_instUniform : IsProbabilityMeasure unitUniformLaw := GP037B4b_uniform_probability
  let μ : Measure (Fin (n+2) → ℝ) := Measure.pi (fun _ => unitUniformLaw)
  have hpos : ∀ᵐ w ∂μ, ∀ i, 0 < w i := by
    apply ae_all_iff.mpr
    intro i
    apply ae_of_ae_map (measurable_pi_apply i).aemeasurable
    rw [(measurePreserving_eval (fun _ : Fin (n+2) => unitUniformLaw) i).map_eq]
    exact GP037B4b_uniform_positive
  have he : normalizeWeights ⁻¹' bootstrapWitnessEvent n =ᵐ[μ]
      {w | w 0 < w 1 / 3} := by
    filter_upwards [hpos] with w hw
    have hs : 0 < ∑ i, w i :=
      Finset.sum_pos (fun i _ => hw i) Finset.univ_nonempty
    have h := bootstrap_ratio_cancellation (w 0) (w 1) (∑ i, w i) (hw 0) (hw 1) hs
    apply propext
    change (_ / (_ + _) < (1:ℝ)/4) ↔ _
    simp only [normalizeWeights]
    rw [h.1,h.2]
  rw [normalizedUniformLaw, Measure.map_apply (GP037B4b_normalize_measurable _)
    (GP037B4b_event_measurable _)]
  change (μ (normalizeWeights ⁻¹' bootstrapWitnessEvent n)).toReal = _
  rw [measure_congr he]
  have hm : Measurable (fun w : Fin (n+2) → ℝ => (w 0,w 1)) :=
    (measurable_pi_apply 0).prodMk (measurable_pi_apply 1)
  have hset : MeasurableSet {p : ℝ × ℝ | p.1 < p.2/3} :=
    measurableSet_lt measurable_fst (measurable_snd.div_const 3)
  have hmarg := congrArg (fun ν : Measure (ℝ × ℝ) => ν {p | p.1 < p.2/3})
    (GP037B4b_uniform_pair n)
  rw [Measure.map_apply hm hset, GP037B4b_uniform_triangle] at hmarg
  change μ {w | w 0 < w 1/3} = ENNReal.ofReal (1/6:ℝ) at hmarg
  rw [hmarg, ENNReal.toReal_ofReal (by norm_num : (0:ℝ) ≤ 1/6)]

/-- Direct uniforms and the Bayesian bootstrap assign different probabilities
to the ratio witness, for every number of schools at least two. -/
theorem uniform_weights_not_bayesian_bootstrap_proof (n : ℕ) :
    (normalizedUniformLaw n (bootstrapWitnessEvent n)).toReal = 1/6 ∧
    (bayesianBootstrapLaw (n+1) (bootstrapWitnessEvent n)).toReal = 1/4 ∧
    normalizedUniformLaw n ≠ bayesianBootstrapLaw (n+1) := by
  have hu := GP037B4b_uniform_probability_event n
  have hb := GP037B4b_bayesian_probability n
  refine ⟨hu,hb,?_⟩
  intro heq
  have hp := congrArg (fun μ : Measure (Fin (n+2) → ℝ) =>
    (μ (bootstrapWitnessEvent n)).toReal) heq
  rw [hu,hb] at hp
  norm_num at hp

end AronowAudit.P037.Wave1
