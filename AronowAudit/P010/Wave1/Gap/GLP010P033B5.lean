import AronowAudit.P010.P010_Population
import AronowAudit.P053.P053_NormalQuantiles
import Mathlib.Analysis.Real.Pi.Bounds

namespace AronowAudit.P010.Wave1

set_option maxRecDepth 4096
set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false
set_option linter.style.haveILetI false
set_option linter.unnecessarySeqFocus false

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Classical Topology

noncomputable section

lemma t9_gaussian_integrable (m : ℝ) : Integrable (fun x : ℝ => x) (gaussianReal m 1) :=
  (memLp_id_gaussianReal (μ := m) (v := 1) 1).integrable (by norm_num)

lemma t9_mixture_probability (w : ℝ) (hw : 0 ≤ w) (hw1 : w ≤ 1) :
    IsProbabilityMeasure (normalMixture w) := by
  constructor
  simp only [normalMixture, Measure.add_apply, Measure.smul_apply, measure_univ,
    smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add (sub_nonneg.mpr hw1) hw]
  norm_num

lemma t9_mixture_integrable (w : ℝ) : Integrable (fun x : ℝ => x) (normalMixture w) := by
  exact ((t9_gaussian_integrable 0).smul_measure ENNReal.ofReal_ne_top).add_measure
    ((t9_gaussian_integrable (-1)).smul_measure ENNReal.ofReal_ne_top)

lemma t9_mixture_mean (w : ℝ) (hw : 0 ≤ w) (hw1 : w ≤ 1) :
    (∫ x, x ∂normalMixture w) = -w := by
  rw [normalMixture, integral_add_measure
    ((t9_gaussian_integrable 0).smul_measure ENNReal.ofReal_ne_top)
    ((t9_gaussian_integrable (-1)).smul_measure ENNReal.ofReal_ne_top)]
  simp [integral_smul_measure, integral_id_gaussianReal,
    ENNReal.toReal_ofReal hw, ENNReal.toReal_ofReal (sub_nonneg.mpr hw1)]

lemma t9_gaussian_sq_integrable (m : ℝ) :
    Integrable (fun x : ℝ => x^2) (gaussianReal m 1) :=
  (memLp_id_gaussianReal (μ := m) (v := 1) 2).integrable_sq

lemma t9_gaussian_sq (m : ℝ) : (∫ x, x^2 ∂gaussianReal m 1) = 1+m^2 := by
  have h := variance_eq_sub (memLp_id_gaussianReal (μ := m) (v := 1) 2)
  simp only [variance_id_gaussianReal, NNReal.coe_one] at h
  change (1:ℝ) = (∫ x, x^2 ∂gaussianReal m 1) - (∫ x, x ∂gaussianReal m 1)^2 at h
  rw [integral_id_gaussianReal] at h
  linarith

lemma t9_gaussian_centered (m w : ℝ) :
    (∫ x, (x+w)^2 ∂gaussianReal m 1) = 1 + (m+w)^2 := by
  have he : (fun x : ℝ => (x+w)^2) = fun x => x^2 + (2*w)*x + w^2 := by
    funext x; ring
  rw [he]
  have hc : Integrable (fun _ : ℝ => w^2) (gaussianReal m 1) := integrable_const _
  have ha : Integrable (fun x : ℝ => x^2 + (2*w)*x) (gaussianReal m 1) :=
    (t9_gaussian_sq_integrable m).add ((t9_gaussian_integrable m).const_mul (2*w))
  rw [integral_add ha hc,
    integral_add (t9_gaussian_sq_integrable m) ((t9_gaussian_integrable m).const_mul (2*w)),
    integral_const_mul, t9_gaussian_sq, integral_id_gaussianReal]
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
  ring

lemma t9_mixture_centered (w : ℝ) (hw : 0 ≤ w) (hw1 : w ≤ 1) :
    (∫ x, (x+w)^2 ∂normalMixture w) = 1+w-w^2 := by
  have hi (m : ℝ) : Integrable (fun x : ℝ => (x+w)^2) (gaussianReal m 1) := by
    exact ((memLp_id_gaussianReal (μ := m) (v := 1) 2).add
      (memLp_const w)).integrable_sq
  rw [normalMixture, integral_add_measure
    ((hi 0).smul_measure ENNReal.ofReal_ne_top)
    ((hi (-1)).smul_measure ENNReal.ofReal_ne_top)]
  simp only [integral_smul_measure, smul_eq_mul, ENNReal.toReal_ofReal hw,
    ENNReal.toReal_ofReal (sub_nonneg.mpr hw1), t9_gaussian_centered]
  ring

lemma t9_mixture_null_singleton (w : ℝ) (x : ℝ) : normalMixture w {x} = 0 := by
  have h0 := nullSingletonClass_gaussianReal (μ := (0:ℝ)) (by norm_num : (1:NNReal) ≠ 0)
  have h1 := nullSingletonClass_gaussianReal (μ := (-1:ℝ)) (by norm_num : (1:NNReal) ≠ 0)
  letI := h0
  letI := h1
  simp [normalMixture, Measure.smul_apply]

lemma t9_mixture_cdf (w x : ℝ) (hw : 0 ≤ w) (hw1 : w ≤ 1) :
    cdf (normalMixture w) x =
      (1-w)*cdf (gaussianReal 0 1) x + w*cdf (gaussianReal 0 1) (x+1) := by
  letI := t9_mixture_probability w hw hw1
  have hm : gaussianReal (-1) 1 (Iic x) = gaussianReal 0 1 (Iic (x+1)) := by
    rw [← show (gaussianReal 0 1).map (fun y => y-1) = gaussianReal (-1) 1 by
      simpa using gaussianReal_map_sub_const (μ := (0:ℝ)) (v := 1) 1,
      Measure.map_apply (by fun_prop) measurableSet_Iic]
    congr 1
    ext y
    simp only [mem_preimage, mem_Iic]
    constructor <;> intro h <;> linarith
  rw [cdf_eq_real, measureReal_def, normalMixture, Measure.add_apply,
    Measure.smul_apply, Measure.smul_apply, smul_eq_mul, smul_eq_mul,
    ENNReal.toReal_add (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _))
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _))]
  rw [hm]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hw,
    ENNReal.toReal_ofReal (sub_nonneg.mpr hw1), cdf_eq_real, measureReal_def]

lemma t9_mixture_cdf_strict (w : ℝ) (hw : 0 ≤ w) (hw1 : w < 1) :
    StrictMono (cdf (normalMixture w)) := by
  intro x y hxy
  rw [t9_mixture_cdf w x hw hw1.le, t9_mixture_cdf w y hw hw1.le]
  exact add_lt_add_of_lt_of_le
    (mul_lt_mul_of_pos_left (AronowAudit.P053.NormalCompletion.strictMono_normal_cdf hxy)
      (sub_pos.mpr hw1))
    (mul_le_mul_of_nonneg_left
      (monotone_cdf (μ := gaussianReal 0 1) (by linarith : x+1 ≤ y+1)) hw)

lemma t9_fair_probability : IsProbabilityMeasure fairAssignment := by
  constructor
  simpa [fairAssignment, Measure.add_apply, Measure.smul_apply] using
    ENNReal.inv_two_add_inv_two

local instance t9_instFairProbability : IsProbabilityMeasure fairAssignment := t9_fair_probability

@[fun_prop] lemma t9_simulation_measurable (s t : Bool) :
    Measurable (simulationState s t 1) := by
  unfold simulationState
  fun_prop

noncomputable def t9_component (s t : Bool) : Measure (State 2 0) :=
  ((gaussianReal 0 1).prod fairAssignment).map (simulationState s t 1)

local instance t9_instComponentProbability (s t : Bool) :
    IsProbabilityMeasure (t9_component s t) :=
  (Measure.isProbabilityMeasure_map_iff (t9_simulation_measurable s t).aemeasurable).2
    inferInstance

noncomputable def t9_sum (a b c d : ℝ≥0∞) : Measure (State 2 0) :=
  a • t9_component false false + b • t9_component true false +
    c • t9_component false true + d • t9_component true true

lemma t9_sum_probability (a b c d : ℝ≥0∞) (h : a+b+c+d=1) :
    IsProbabilityMeasure (t9_sum a b c d) := by
  constructor
  simpa [t9_sum, Measure.add_apply, Measure.smul_apply] using h

lemma t9_design_one : simulationLaw (4/5) (4/5) (1/4) 1 1 =
    t9_sum (2/25) (3/25) (3/25) (17/25) := by
  have hs : Real.sqrt ((4/5:ℝ)*(1-4/5)*(4/5)*(1-4/5)) = 4/25 := by
    norm_num
  norm_num [simulationLaw, hs, t9_sum, t9_component, ENNReal.ofReal_div_of_pos]
  rfl

lemma t9_design_two : simulationLaw (4/5) (4/5) (1/2) 1 1 =
    t9_sum (3/25) (2/25) (2/25) (18/25) := by
  have hs : Real.sqrt ((4/5:ℝ)*(1-4/5)*(4/5)*(1-4/5)) = 4/25 := by
    norm_num
  norm_num [simulationLaw, hs, t9_sum, t9_component, ENNReal.ofReal_div_of_pos]
  rfl

lemma t9_component_event (s t : Bool) (E : Set (State 2 0)) (hE : MeasurableSet E) :
    t9_component s t E = ((gaussianReal 0 1).prod fairAssignment)
      ((simulationState s t 1) ⁻¹' E) :=
  Measure.map_apply (t9_simulation_measurable s t) hE

lemma t9_component_always (s t : Bool) :
    t9_component s t alwaysPass = if s && t then 1 else 0 := by
  rw [t9_component_event s t _ measurableSet_always]
  cases s <;> cases t <;>
    simp [alwaysPass, potentialS, simulationState, Fin.forall_fin_two]

lemma t9_component_potential (s t : Bool) (i : Fin 2) :
    t9_component s t (potentialPass i) = if (![s,t] : Fin 2 → Bool) i then 1 else 0 := by
  rw [t9_component_event s t _ (measurableSet_potentialPass i)]
  fin_cases i <;> cases s <;> cases t <;> simp [potentialPass, potentialS, simulationState]

lemma t9_component_arm (s t : Bool) (i : Fin 2) :
    t9_component s t (armEvent i) = 1/2 := by
  rw [t9_component_event s t _ (measurableSet_arm i)]
  have he : simulationState s t 1 ⁻¹' armEvent i = univ ×ˢ {i} := by
    ext ω; simp [simulationState, armEvent, assignment]
  rw [he]
  rw [Measure.prod_prod, measure_univ, one_mul]
  fin_cases i <;> norm_num [fairAssignment, Measure.smul_apply]

lemma t9_component_joint (s t : Bool) :
    t9_component s t (potentialPass 0 ∩ potentialPass 1) = if s && t then 1 else 0 := by
  rw [t9_component_event s t _
    ((measurableSet_potentialPass 0).inter (measurableSet_potentialPass 1))]
  cases s <;> cases t <;> simp [potentialPass, potentialS, simulationState]

lemma t9_component_pass_arm (s t : Bool) (i : Fin 2) :
    t9_component s t (passEvent ∩ armEvent i) =
      if (![s,t] : Fin 2 → Bool) i then 1/2 else 0 := by
  rw [pass_inter_arm, t9_component_event s t _
    ((measurableSet_potentialPass i).inter (measurableSet_arm i))]
  have he : (simulationState s t 1) ⁻¹' (potentialPass i ∩ armEvent i) =
      if (![s,t] : Fin 2 → Bool) i then univ ×ˢ {i} else ∅ := by
    ext ω
    fin_cases i <;> cases s <;> cases t <;>
      simp [potentialPass, potentialS, armEvent, assignment, simulationState]
  rw [he]
  split_ifs
  · rw [Measure.prod_prod, measure_univ, one_mul]
    fin_cases i <;> norm_num [fairAssignment, Measure.smul_apply]
  · exact measure_empty

lemma t9_sum_always (a b c d : ℝ≥0∞) : t9_sum a b c d alwaysPass = d := by
  simp [t9_sum, Measure.add_apply, Measure.smul_apply, t9_component_always]

lemma t9_sum_potential_zero (a b c d : ℝ≥0∞) :
    t9_sum a b c d (potentialPass 0) = b+d := by
  simp [t9_sum, Measure.add_apply, Measure.smul_apply, t9_component_potential]

lemma t9_sum_potential_one (a b c d : ℝ≥0∞) :
    t9_sum a b c d (potentialPass 1) = c+d := by
  simp [t9_sum, Measure.add_apply, Measure.smul_apply, t9_component_potential]

lemma t9_sum_joint (a b c d : ℝ≥0∞) :
    t9_sum a b c d (potentialPass 0 ∩ potentialPass 1) = d := by
  simp [t9_sum, Measure.add_apply, Measure.smul_apply, t9_component_joint]

lemma t9_sum_arm (a b c d : ℝ≥0∞) (i : Fin 2) :
    t9_sum a b c d (armEvent i) = (a+b+c+d)/2 := by
  simp only [t9_sum, Measure.add_apply, Measure.smul_apply, smul_eq_mul, t9_component_arm, div_eq_mul_inv]
  ring

lemma t9_sum_rate_zero (a b c d : ℝ≥0∞) (h : a+b+c+d=1) :
    passingRate (t9_sum a b c d) 0 = (b+d).toReal := by
  simp only [passingRate, t9_sum_arm, h]
  simp only [t9_sum, Measure.add_apply, Measure.smul_apply, smul_eq_mul, t9_component_pass_arm]
  norm_num
  rw [← add_mul, ENNReal.toReal_mul]
  norm_num

lemma t9_sum_rate_one (a b c d : ℝ≥0∞) (h : a+b+c+d=1) :
    passingRate (t9_sum a b c d) 1 = (c+d).toReal := by
  simp only [passingRate, t9_sum_arm, h]
  simp only [t9_sum, Measure.add_apply, Measure.smul_apply, smul_eq_mul, t9_component_pass_arm]
  norm_num
  rw [← add_mul, ENNReal.toReal_mul]
  norm_num

lemma t9_component_map {B : Type*} [MeasurableSpace B]
    (s t : Bool) (f : State 2 0 → B) (g : ℝ → B)
    (hf : Measurable f) (hg : Measurable g)
    (h : ∀ ω, f (simulationState s t 1 ω) = g ω.1) :
    (t9_component s t).map f = (gaussianReal 0 1).map g := by
  have he : f ∘ simulationState s t 1 = g ∘ Prod.fst := funext h
  rw [t9_component, Measure.map_map hf (t9_simulation_measurable s t), he,
    ← Measure.map_map hg measurable_fst, Measure.map_fst_prod, measure_univ, one_smul]

lemma t9_component_assignment_map (s t : Bool) :
    (t9_component s t).map assignment = fairAssignment := by
  rw [t9_component, Measure.map_map measurable_assignment (t9_simulation_measurable s t)]
  change ((gaussianReal 0 1).prod fairAssignment).map Prod.snd = fairAssignment
  simp

lemma t9_component_pair_map {B : Type*} [MeasurableSpace B]
    (s t : Bool) (f : State 2 0 → B) (g : ℝ → B)
    (hf : Measurable f) (hg : Measurable g)
    (h : ∀ ω, f (simulationState s t 1 ω) = g ω.1) :
    (t9_component s t).map (fun ω => (f ω, assignment ω)) =
      ((gaussianReal 0 1).map g).prod fairAssignment := by
  have he : (fun ω => (f ω, assignment ω)) ∘ simulationState s t 1 =
      Prod.map g id := by
    funext ω
    change (f (simulationState s t 1 ω), ω.2) = (g ω.1, ω.2)
    rw [h]
  rw [t9_component, Measure.map_map (hf.prodMk measurable_assignment)
    (t9_simulation_measurable s t), he, ← Measure.map_prod_map _ _ hg measurable_id]
  simp

lemma t9_sum_independent {B : Type*} [MeasurableSpace B]
    (a b c d : ℝ≥0∞) (hs : a+b+c+d=1)
    (f : State 2 0 → B) (g : Bool → Bool → ℝ → B)
    (hf : Measurable f) (hg : ∀ s t, Measurable (g s t))
    (he : ∀ s t ω, f (simulationState s t 1 ω) = g s t ω.1) :
    IndepFun f assignment (t9_sum a b c d) := by
  letI := t9_sum_probability a b c d hs
  have ha : (t9_sum a b c d).map assignment = fairAssignment := by
    simp only [t9_sum, Measure.map_add _ _ measurable_assignment,
      Measure.map_smul _ measurable_assignment.aemeasurable, t9_component_assignment_map]
    rw [← add_smul, ← add_smul, ← add_smul, hs, one_smul]
  rw [indepFun_iff_map_prod_eq_prod_map_map hf.aemeasurable
    measurable_assignment.aemeasurable, ha]
  simp only [t9_sum, Measure.map_add _ _ (hf.prodMk measurable_assignment),
    Measure.map_add _ _ hf, Measure.map_smul _ (hf.prodMk measurable_assignment).aemeasurable,
    Measure.map_smul _ hf.aemeasurable, t9_component_pair_map _ _ _ _ hf (hg _ _) (he _ _),
    t9_component_map _ _ _ _ hf (hg _ _) (he _ _), Measure.add_prod, Measure.prod_smul_left]

lemma t9_sum_ignorability (a b c d : ℝ≥0∞) (hs : a+b+c+d=1) :
    Ignorability (t9_sum a b c d) := by
  constructor
  · intro i
    apply t9_sum_independent a b c d hs _
      (fun s t x =>
        (((if t then (1:ℝ) else 0)-(if s then (1:ℝ) else 0)+x),
          (![s,t] : Fin 2 → Bool) i))
      ((measurable_potentialY i).prodMk (measurable_potentialS i))
    · intro s t; fun_prop
    · intro s t ω
      fin_cases i <;> simp [simulationState, potentialY, potentialS]
  · intro i
    rw [t9_sum_arm, hs]
    norm_num

lemma t9_sum_assumptions (a b c d : ℝ≥0∞) (hs : a+b+c+d=1)
    (h0 : 0 < (b+d).toReal) (h1 : 0 < (c+d).toReal) :
    Assumptions (t9_sum a b c d) := by
  refine ⟨t9_sum_probability a b c d hs, t9_sum_ignorability a b c d hs, ?_⟩
  intro i
  fin_cases i
  · change 0 < passingRate (t9_sum a b c d) 0
    rw [t9_sum_rate_zero _ _ _ _ hs]; exact h0
  · change 0 < passingRate (t9_sum a b c d) 1
    rw [t9_sum_rate_one _ _ _ _ hs]; exact h1

lemma t9_component_outcome (s t : Bool) (i : Fin 2) :
    (t9_component s t).map (potentialY i) =
      gaussianReal ((if t then (1:ℝ) else 0)-(if s then (1:ℝ) else 0)) 1 := by
  rw [t9_component_map s t _
    (fun x => (if t then (1:ℝ) else 0)-(if s then (1:ℝ) else 0)+x)
    (measurable_potentialY i) (by fun_prop) (by
      intro ω; fin_cases i <;> simp [potentialY, simulationState])]
  simpa using gaussianReal_map_const_add (μ := (0:ℝ)) (v := 1)
    ((if t then (1:ℝ) else 0)-(if s then (1:ℝ) else 0))

lemma t9_component_observed (s t : Bool) :
    (t9_component s t).map observedY =
      gaussianReal ((if t then (1:ℝ) else 0)-(if s then (1:ℝ) else 0)) 1 := by
  rw [t9_component_map s t _
    (fun x => (if t then (1:ℝ) else 0)-(if s then (1:ℝ) else 0)+x)
    measurable_observedY (by fun_prop) (by
      rintro ⟨x,i⟩; fin_cases i <;> simp [observedY, assignment, potentialY, simulationState])]
  simpa using gaussianReal_map_const_add (μ := (0:ℝ)) (v := 1)
    ((if t then (1:ℝ) else 0)-(if s then (1:ℝ) else 0))

lemma t9_sum_observed (a b c d : ℝ≥0∞) :
    (t9_sum a b c d).map observedY =
      a • gaussianReal 0 1 + b • gaussianReal (-1) 1 +
        c • gaussianReal 1 1 + d • gaussianReal 0 1 := by
  simp [t9_sum, Measure.map_add _ _ measurable_observedY,
    Measure.map_smul _ measurable_observedY.aemeasurable, t9_component_observed]

lemma t9_component_selected (s t : Bool) (i : Fin 2) :
    ((t9_component s t).restrict (potentialPass i)).map (potentialY i) =
      if (![s,t] : Fin 2 → Bool) i then
        gaussianReal ((if t then (1:ℝ) else 0)-(if s then (1:ℝ) else 0)) 1 else 0 := by
  ext E hE
  rw [Measure.map_apply (measurable_potentialY i) hE,
    Measure.restrict_apply ((measurable_potentialY i) hE)]
  have he : (simulationState s t 1) ⁻¹' (potentialY i ⁻¹' E ∩ potentialPass i) =
      if (![s,t] : Fin 2 → Bool) i then
        (simulationState s t 1) ⁻¹' (potentialY i ⁻¹' E) else ∅ := by
    ext ω
    fin_cases i <;> cases s <;> cases t <;>
      simp [potentialY, potentialPass, potentialS, simulationState]
  rw [t9_component_event s t _ (((measurable_potentialY i) hE).inter
    (measurableSet_potentialPass i)), he]
  by_cases hp : (![s,t] : Fin 2 → Bool) i = true
  · simp only [hp, if_true]
    rw [← t9_component_event s t _ ((measurable_potentialY i) hE),
      ← Measure.map_apply (measurable_potentialY i) hE, t9_component_outcome]
  · simp [hp]

lemma t9_sum_selected_zero (a b c d : ℝ≥0∞) :
    ((t9_sum a b c d).restrict (potentialPass 0)).map (potentialY 0) =
      b • gaussianReal (-1) 1 + d • gaussianReal 0 1 := by
  simp [t9_sum, Measure.restrict_add, Measure.restrict_smul,
    Measure.map_add _ _ (measurable_potentialY 0),
    Measure.map_smul _ (measurable_potentialY 0).aemeasurable, t9_component_selected]

lemma t9_sum_selected_one (a b c d : ℝ≥0∞) :
    ((t9_sum a b c d).restrict (potentialPass 1)).map (potentialY 1) =
      c • gaussianReal 1 1 + d • gaussianReal 0 1 := by
  simp [t9_sum, Measure.restrict_add, Measure.restrict_smul,
    Measure.map_add _ _ (measurable_potentialY 1),
    Measure.map_smul _ (measurable_potentialY 1).aemeasurable, t9_component_selected]

lemma t9_sum_passer_zero (a b c d : ℝ≥0∞) (h : Assumptions (t9_sum a b c d)) :
    passerLaw (t9_sum a b c d) 0 =
      (b+d)⁻¹ • (b • gaussianReal (-1) 1 + d • gaussianReal 0 1) := by
  rw [← conditional_law_consistency _ h 0, eventLaw, t9_sum_potential_zero,
    t9_sum_selected_zero]

lemma t9_sum_passer_one (a b c d : ℝ≥0∞) (h : Assumptions (t9_sum a b c d)) :
    passerLaw (t9_sum a b c d) 1 =
      (c+d)⁻¹ • (c • gaussianReal 1 1 + d • gaussianReal 0 1) := by
  rw [← conditional_law_consistency _ h 1, eventLaw, t9_sum_potential_one,
    t9_sum_selected_one]

lemma t9_sum_atomless (a b c d : ℝ≥0∞) : Atomless ((t9_sum a b c d).map observedY) := by
  intro x
  have hn (m : ℝ) : gaussianReal m 1 {x} = 0 := by
    letI := nullSingletonClass_gaussianReal (μ := m) (by norm_num : (1:NNReal) ≠ 0)
    exact measure_singleton x
  simp [t9_sum_observed, Measure.add_apply, Measure.smul_apply, hn]

lemma t9_gaussian_interval (m l u : ℝ) (hlu : l < u) : 0 < gaussianReal m 1 (Ioo l u) := by
  apply pos_iff_ne_zero.mpr
  intro h
  have hz := (gaussianReal_absolutelyContinuous' m (by norm_num : (1:NNReal) ≠ 0)) h
  rw [Real.volume_Ioo] at hz
  exact (ENNReal.ofReal_pos.mpr (sub_pos.mpr hlu)).ne' hz

lemma t9_sum_support (a b c d : ℝ≥0∞) (hd : 0 < d) :
    FullRealSupport (t9_sum a b c d) observedY := by
  intro l u hlu
  change 0 < t9_sum a b c d (observedY ⁻¹' Ioo l u)
  rw [← Measure.map_apply measurable_observedY measurableSet_Ioo, t9_sum_observed]
  simp only [Measure.add_apply, Measure.smul_apply, smul_eq_mul]
  have hp := ENNReal.mul_pos hd.ne' (t9_gaussian_interval 0 l u hlu).ne'
  exact hp.trans_le (le_add_left le_rfl)

lemma t9_design_one_assumptions : Assumptions (simulationLaw (4/5) (4/5) (1/4) 1 1) := by
  rw [t9_design_one]
  apply t9_sum_assumptions
  · apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
    simp (disch := finiteness) only [ENNReal.toReal_add, ENNReal.toReal_div, ENNReal.toReal_ofNat]
    norm_num
  · simp (disch := finiteness) only [ENNReal.toReal_add, ENNReal.toReal_div, ENNReal.toReal_ofNat]
    norm_num
  · simp (disch := finiteness) only [ENNReal.toReal_add, ENNReal.toReal_div, ENNReal.toReal_ofNat]
    norm_num

lemma t9_design_two_assumptions : Assumptions (simulationLaw (4/5) (4/5) (1/2) 1 1) := by
  rw [t9_design_two]
  apply t9_sum_assumptions
  · apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
    simp (disch := finiteness) only [ENNReal.toReal_add, ENNReal.toReal_div, ENNReal.toReal_ofNat]
    norm_num
  · simp (disch := finiteness) only [ENNReal.toReal_add, ENNReal.toReal_div, ENNReal.toReal_ofNat]
    norm_num
  · simp (disch := finiteness) only [ENNReal.toReal_add, ENNReal.toReal_div, ENNReal.toReal_ofNat]
    norm_num

lemma t9_quantile_eq_of_cdf (F : Measure ℝ) [IsProbabilityMeasure F]
    (hs : StrictMono (cdf F)) (p q : ℝ) (hp : 0 < p) (hp1 : p < 1)
    (hq : cdf F q = p) : quantile F p = (q : EReal) := by
  have he : {x : EReal | p ≤ (F {y : ℝ | (y : EReal) ≤ x}).toReal} = Ici (q:EReal) := by
    ext x
    induction x with
    | bot => simp [hp.not_ge]
    | coe x =>
      simp only [EReal.coe_le_coe_iff, mem_setOf_eq, mem_Ici]
      change p ≤ (F (Iic x)).toReal ↔ q ≤ x
      rw [← measureReal_def, ← cdf_eq_real, ← hq]
      exact hs.le_iff_le
    | top => simp [hp1.le]
  rw [quantile, he, csInf_Ici]

lemma t9_mixture_quantile (w p : ℝ) (hw : 0 ≤ w) (hw1 : w < 1)
    (hp : 0 < p) (hp1 : p < 1) :
    ∃ q : ℝ, quantile (normalMixture w) p = (q:EReal) ∧ cdf (normalMixture w) q = p := by
  letI := t9_mixture_probability w hw hw1.le
  letI : NullSingletonClass (normalMixture w) := ⟨t9_mixture_null_singleton w⟩
  obtain ⟨q,hq⟩ := AronowAudit.P053.NormalCompletion.exists_cdf_eq (normalMixture w) hp hp1
  exact ⟨q,t9_quantile_eq_of_cdf _ (t9_mixture_cdf_strict w hw hw1) p q hp hp1 hq,hq⟩

lemma t9_mixture_reflection (w : ℝ) :
    (normalMixture w).map (fun x => -x) =
      ENNReal.ofReal (1-w) • gaussianReal 0 1 + ENNReal.ofReal w • gaussianReal 1 1 := by
  simp [normalMixture, Measure.map_add _ _ measurable_neg,
    Measure.map_smul _ measurable_neg.aemeasurable, gaussianReal_map_neg]

lemma t9_design_one_rates :
    passingRate (simulationLaw (4/5) (4/5) (1/4) 1 1) 0 = 4/5 ∧
    passingRate (simulationLaw (4/5) (4/5) (1/4) 1 1) 1 = 4/5 := by
  have h := (nonzero_passing_corrected _ t9_design_one_assumptions.1
    t9_design_one_assumptions.2.1).1
  rw [h 0, h 1, t9_design_one, t9_sum_potential_zero, t9_sum_potential_one]
  simp (disch := finiteness) only [ENNReal.toReal_add, ENNReal.toReal_div, ENNReal.toReal_ofNat]
  norm_num

lemma t9_design_two_rates :
    passingRate (simulationLaw (4/5) (4/5) (1/2) 1 1) 0 = 4/5 ∧
    passingRate (simulationLaw (4/5) (4/5) (1/2) 1 1) 1 = 4/5 := by
  have h := (nonzero_passing_corrected _ t9_design_two_assumptions.1
    t9_design_two_assumptions.2.1).1
  rw [h 0, h 1, t9_design_two, t9_sum_potential_zero, t9_sum_potential_one]
  simp (disch := finiteness) only [ENNReal.toReal_add, ENNReal.toReal_div, ENNReal.toReal_ofNat]
  norm_num

lemma t9_trim_of_rates (μ : Measure (State 2 0))
    (h0 : passingRate μ 0 = 4/5) (h1 : passingRate μ 1 = 4/5) :
    trimRatio μ 0 = 1/4 ∧ trimRatio μ 1 = 1/4 := by
  norm_num [trimRatio, Fin.sum_univ_succ, h0, h1]

lemma t9_design_one_correlation :
    checkCorrelation (simulationLaw (4/5) (4/5) (1/4) 1 1) 0 1 = 1/4 := by
  simp only [checkCorrelation, t9_design_one, t9_sum_potential_zero,
    t9_sum_potential_one, t9_sum_joint]
  simp (disch := finiteness) only [ENNReal.toReal_add, ENNReal.toReal_div, ENNReal.toReal_ofNat]
  norm_num

lemma t9_design_two_correlation :
    checkCorrelation (simulationLaw (4/5) (4/5) (1/2) 1 1) 0 1 = 1/2 := by
  simp only [checkCorrelation, t9_design_two, t9_sum_potential_zero,
    t9_sum_potential_one, t9_sum_joint]
  simp (disch := finiteness) only [ENNReal.toReal_add, ENNReal.toReal_div, ENNReal.toReal_ofNat]
  norm_num

lemma t9_design_one_passer :
    passerLaw (simulationLaw (4/5) (4/5) (1/4) 1 1) 0 = normalMixture (3/20) ∧
    passerLaw (simulationLaw (4/5) (4/5) (1/4) 1 1) 1 =
      (normalMixture (3/20)).map (fun y => -y) := by
  have h := t9_design_one_assumptions
  rw [t9_design_one] at h ⊢
  rw [t9_sum_passer_zero _ _ _ _ h, t9_sum_passer_one _ _ _ _ h,
    t9_mixture_reflection, normalMixture]
  have hc0 : (3/25+17/25:ℝ≥0∞)⁻¹*(3/25) = ENNReal.ofReal (3/20) := by
    apply (ENNReal.toReal_eq_toReal_iff' (by
      apply ENNReal.mul_ne_top
      · exact ENNReal.inv_ne_top.mpr (by
        simp only [ne_eq, add_eq_zero, ENNReal.div_eq_zero_iff]
        norm_num)
      · finiteness) (by finiteness)).mp
    simp (disch := finiteness) only [ENNReal.toReal_add, ENNReal.toReal_mul,
      ENNReal.toReal_inv, ENNReal.toReal_div, ENNReal.toReal_ofNat,
      ENNReal.toReal_ofReal (by norm_num : (0:ℝ) ≤ 3/20)]
    norm_num
  have hc1 : (3/25+17/25:ℝ≥0∞)⁻¹*(17/25) = ENNReal.ofReal (1-3/20) := by
    apply (ENNReal.toReal_eq_toReal_iff' (by
      apply ENNReal.mul_ne_top
      · exact ENNReal.inv_ne_top.mpr (by
        simp only [ne_eq, add_eq_zero, ENNReal.div_eq_zero_iff]
        norm_num)
      · finiteness) (by finiteness)).mp
    simp (disch := finiteness) only [ENNReal.toReal_add, ENNReal.toReal_mul,
      ENNReal.toReal_inv, ENNReal.toReal_div, ENNReal.toReal_ofNat,
      ENNReal.toReal_ofReal (by norm_num : (0:ℝ) ≤ 1-3/20)]
    norm_num
  simp only [smul_add, smul_smul, hc0, hc1]
  exact ⟨add_comm _ _, add_comm _ _⟩

lemma t9_design_two_passer :
    passerLaw (simulationLaw (4/5) (4/5) (1/2) 1 1) 0 = normalMixture (1/10) ∧
    passerLaw (simulationLaw (4/5) (4/5) (1/2) 1 1) 1 =
      (normalMixture (1/10)).map (fun y => -y) := by
  have h := t9_design_two_assumptions
  rw [t9_design_two] at h ⊢
  rw [t9_sum_passer_zero _ _ _ _ h, t9_sum_passer_one _ _ _ _ h,
    t9_mixture_reflection, normalMixture]
  have hc0 : (2/25+18/25:ℝ≥0∞)⁻¹*(2/25) = ENNReal.ofReal (1/10) := by
    apply (ENNReal.toReal_eq_toReal_iff' (by
      apply ENNReal.mul_ne_top
      · exact ENNReal.inv_ne_top.mpr (by
        simp only [ne_eq, add_eq_zero, ENNReal.div_eq_zero_iff]
        norm_num)
      · finiteness) (by finiteness)).mp
    simp (disch := finiteness) only [ENNReal.toReal_add, ENNReal.toReal_mul,
      ENNReal.toReal_inv, ENNReal.toReal_div, ENNReal.toReal_ofNat,
      ENNReal.toReal_ofReal (by norm_num : (0:ℝ) ≤ 1/10)]
    norm_num
  have hc1 : (2/25+18/25:ℝ≥0∞)⁻¹*(18/25) = ENNReal.ofReal (1-1/10) := by
    apply (ENNReal.toReal_eq_toReal_iff' (by
      apply ENNReal.mul_ne_top
      · exact ENNReal.inv_ne_top.mpr (by
        simp only [ne_eq, add_eq_zero, ENNReal.div_eq_zero_iff]
        norm_num)
      · finiteness) (by finiteness)).mp
    simp (disch := finiteness) only [ENNReal.toReal_add, ENNReal.toReal_mul,
      ENNReal.toReal_inv, ENNReal.toReal_div, ENNReal.toReal_ofNat,
      ENNReal.toReal_ofReal (by norm_num : (0:ℝ) ≤ 1-1/10)]
    norm_num
  simp only [smul_add, smul_smul, hc0, hc1]
  exact ⟨add_comm _ _, add_comm _ _⟩

lemma t9_reflected_cdf (F : Measure ℝ) [IsProbabilityMeasure F]
    [NullSingletonClass F] (x : ℝ) :
    cdf (F.map (fun y => -y)) x = 1-cdf F (-x) := by
  rw [cdf_eq_real, cdf_eq_real, measureReal_def, measureReal_def,
    Measure.map_apply measurable_neg measurableSet_Iic]
  have he : (fun y : ℝ => -y) ⁻¹' Iic x = Ici (-x) := by
    ext y; simp
  rw [he, ← measure_congr (Ioi_ae_eq_Ici' (measure_singleton (-x)))]
  have h := measureReal_add_measureReal_compl (μ := F) (s := Iic (-x)) measurableSet_Iic
  simp only [compl_Iic, measureReal_def, measure_univ, ENNReal.toReal_one] at h
  linarith

lemma t9_eventMean_reflect (F : Measure ℝ) (E : Set ℝ) (hE : MeasurableSet E) :
    eventMean (F.map (fun x => -x)) id E =
      -eventMean F id ((fun x => -x) ⁻¹' E) := by
  unfold eventMean
  rw [← integral_indicator hE, integral_map measurable_neg.aemeasurable
    ((measurable_id.indicator hE).aestronglyMeasurable),
    Measure.map_apply measurable_neg hE]
  have he : (fun x : ℝ => E.indicator id (-x)) =
      fun x => -(((fun y : ℝ => -y) ⁻¹' E).indicator id x) := by
    funext x
    by_cases hx : -x ∈ E <;> simp [hx, indicator]
  rw [he, integral_neg, integral_indicator (measurable_neg hE), neg_div]

lemma t9_mixture_reflected_tails (w : ℝ) (hw : 0 ≤ w) (hw1 : w < 1) :
    eventMean ((normalMixture w).map (fun y => -y)) id
        {y | (y:EReal) ≤ quantile ((normalMixture w).map (fun y => -y)) (3/4)} =
      -mixtureUpper w ∧
    tailUpper ((normalMixture w).map (fun y => -y)) (1/4) = -mixtureLower w := by
  let F := normalMixture w
  letI := t9_mixture_probability w hw hw1.le
  letI : NullSingletonClass F := ⟨t9_mixture_null_singleton w⟩
  have hs : StrictMono (cdf F) := t9_mixture_cdf_strict w hw hw1
  have hr : StrictMono (cdf (F.map (fun y => -y))) := by
    intro x y hxy
    rw [t9_reflected_cdf, t9_reflected_cdf]
    linarith [hs (neg_lt_neg hxy)]
  obtain ⟨q1,hq1,hc1⟩ := t9_mixture_quantile w (1/4) hw hw1 (by norm_num) (by norm_num)
  obtain ⟨q3,hq3,hc3⟩ := t9_mixture_quantile w (3/4) hw hw1 (by norm_num) (by norm_num)
  have hr3 : quantile (F.map (fun y => -y)) (3/4) = ((-q1:ℝ):EReal) := by
    apply t9_quantile_eq_of_cdf _ hr _ _ (by norm_num) (by norm_num)
    rw [t9_reflected_cdf, neg_neg, hc1]
    norm_num
  have hr1 : quantile (F.map (fun y => -y)) (1/4) = ((-q3:ℝ):EReal) := by
    apply t9_quantile_eq_of_cdf _ hr _ _ (by norm_num) (by norm_num)
    rw [t9_reflected_cdf, neg_neg, hc3]
    norm_num
  change eventMean (F.map (fun y => -y)) id _ = -mixtureUpper w ∧
    tailUpper (F.map (fun y => -y)) (1/4) = -mixtureLower w
  rw [hr3, tailUpper, hr1]
  simp only [EReal.coe_le_coe_iff]
  rw [t9_eventMean_reflect _ _ (show MeasurableSet {y : ℝ | y ≤ -q1} from measurableSet_Iic),
    t9_eventMean_reflect _ _ (show MeasurableSet {y : ℝ | -q3 ≤ y} from measurableSet_Ici)]
  have he1 : (fun y : ℝ => -y) ⁻¹' {y | y ≤ -q1} = {y | q1 ≤ y} := by
    ext y; simp
  have he3 : (fun y : ℝ => -y) ⁻¹' {y | -q3 ≤ y} = {y | y ≤ q3} := by
    ext y; simp
  rw [he1, he3]
  simp only [mixtureUpper, mixtureLower, tailUpper, hq1, hq3, EReal.coe_le_coe_iff]
  exact ⟨rfl,rfl⟩

lemma t9_phi_deriv (x : ℝ) :
    HasDerivAt (gaussianPDFReal 0 1) (-x*gaussianPDFReal 0 1 x) x := by
  have h0 : HasDerivAt (fun y : ℝ => -y^2/2) (-x) x := by
    convert (((hasDerivAt_id' x).pow 2).neg.div_const 2) using 1 <;>
      norm_num [Pi.pow_apply, Pi.neg_apply] <;> ring
  have h := h0.exp.const_mul (Real.sqrt (2*Real.pi))⁻¹
  convert h using 1
  · funext y; simp [gaussianPDFReal]
  · simp only [gaussianPDFReal, NNReal.coe_one, sub_zero, mul_one]
    ring

lemma t9_phi_tendsto_bot : Tendsto (gaussianPDFReal 0 1) atBot (𝓝 0) := by
  have hp : Tendsto (fun x : ℝ => x^2) atBot atTop := by
    simpa only [Function.comp_def, neg_sq] using (tendsto_pow_atTop (α := ℝ) (by norm_num : (2:ℕ) ≠ 0)).comp tendsto_neg_atBot_atTop
  have he := Real.tendsto_exp_atBot.comp
    (hp.const_mul_atTop_of_neg (by norm_num : (-1/2:ℝ) < 0))
  have hc := he.const_mul (Real.sqrt (2*Real.pi))⁻¹
  have heq : (fun x : ℝ => (Real.sqrt (2*Real.pi))⁻¹ *
      Real.exp ((-1/2:ℝ)*x^2)) = gaussianPDFReal 0 1 := by
    funext x
    simp only [gaussianPDFReal, NNReal.coe_one, sub_zero, mul_one]
    congr 2 <;> ring
  simp only [Function.comp_apply] at hc
  rw [heq] at hc
  simpa only [mul_zero] using hc

lemma t9_phi_first_integrable :
    Integrable (fun x : ℝ => x*gaussianPDFReal 0 1 x) volume := by
  have hi := (integrable_mul_exp_neg_mul_sq (by norm_num : (0:ℝ) < 1/2)).const_mul
    (Real.sqrt (2*Real.pi))⁻¹
  convert hi using 1
  funext x
  simp only [gaussianPDFReal, NNReal.coe_one, sub_zero, mul_one]
  rw [show -(x^2)/2 = -(1/2:ℝ)*x^2 by ring]
  ring

lemma t9_normal_partial (x : ℝ) :
    (∫ y in Iic x, y ∂gaussianReal 0 1) = -gaussianPDFReal 0 1 x := by
  have h := integral_Iic_of_hasDerivAt_of_tendsto'
    (a := x) (f := fun y => -gaussianPDFReal 0 1 y)
    (f' := fun y => y*gaussianPDFReal 0 1 y)
    (fun y _ => by simpa only [Pi.neg_def, neg_mul, neg_neg] using (t9_phi_deriv y).neg)
    t9_phi_first_integrable.integrableOn t9_phi_tendsto_bot.neg
  rw [neg_zero, sub_zero] at h
  rw [← integral_indicator measurableSet_Iic,
    integral_gaussianReal_eq_integral_smul (by norm_num : (1:NNReal) ≠ 0)]
  have he : (fun y : ℝ => gaussianPDFReal 0 1 y • (Iic x).indicator (fun y => y) y) =
      (Iic x).indicator (fun y => y*gaussianPDFReal 0 1 y) := by
    funext y
    by_cases hy : y ≤ x <;> simp [indicator, hy, mul_comm]
  rw [he, integral_indicator measurableSet_Iic, h]

lemma t9_shifted_partial (x : ℝ) :
    (∫ y in Iic x, y ∂gaussianReal (-1) 1) =
      -gaussianPDFReal 0 1 (x+1) - cdf (gaussianReal 0 1) (x+1) := by
  have hm : (gaussianReal 0 1).map (fun y => y-1) = gaussianReal (-1) 1 := by
    simpa using gaussianReal_map_sub_const (μ := (0:ℝ)) (v := 1) 1
  rw [← hm, ← integral_indicator measurableSet_Iic,
    integral_map (by fun_prop) ((measurable_id'.indicator measurableSet_Iic).aestronglyMeasurable)]
  have he : (fun y : ℝ => (Iic x).indicator (fun y => y) (y-1)) =
      (Iic (x+1)).indicator (fun y => y-1) := by
    funext y
    by_cases hy : y ≤ x+1
    · have hy' : y-1 ≤ x := by linarith
      simp [hy, hy', indicator]
    · have hy' : ¬y-1 ≤ x := by linarith
      simp [hy, hy', indicator]
  rw [he, integral_indicator measurableSet_Iic,
    integral_sub (t9_gaussian_integrable 0).integrableOn (integrable_const 1),
    t9_normal_partial, setIntegral_const]
  simp only [smul_eq_mul, mul_one, cdf_eq_real]

noncomputable def t9_partial (w x : ℝ) : ℝ :=
  -(1-w)*gaussianPDFReal 0 1 x - w*cdf (gaussianReal 0 1) (x+1) -
    w*gaussianPDFReal 0 1 (x+1)

lemma t9_mixture_partial (w x : ℝ) (hw : 0 ≤ w) (hw1 : w ≤ 1) :
    (∫ y in Iic x, y ∂normalMixture w) = t9_partial w x := by
  rw [normalMixture, Measure.restrict_add, integral_add_measure
    (((t9_gaussian_integrable 0).smul_measure ENNReal.ofReal_ne_top).integrableOn)
    (((t9_gaussian_integrable (-1)).smul_measure ENNReal.ofReal_ne_top).integrableOn)]
  simp only [Measure.restrict_smul, integral_smul_measure, smul_eq_mul,
    ENNReal.toReal_ofReal hw, ENNReal.toReal_ofReal (sub_nonneg.mpr hw1),
    t9_normal_partial, t9_shifted_partial, t9_partial]
  ring

lemma t9_normal_cdf_integral (x : ℝ) :
    cdf (gaussianReal 0 1) x = 1/2 +
      (Real.sqrt (2*Real.pi))⁻¹ * ∫ y in (0:ℝ)..x, Real.exp (-y^2/2) := by
  have he (x : ℝ) : cdf (gaussianReal 0 1) x = ∫ y in Iic x, gaussianPDFReal 0 1 y := by
    rw [cdf_eq_real, measureReal_def,
      gaussianReal_apply_eq_integral 0 (by norm_num : (1:NNReal) ≠ 0)]
    exact ENNReal.toReal_ofReal (integral_nonneg (fun y => gaussianPDFReal_nonneg 0 1 y))
  have hi := integrable_gaussianPDFReal 0 1
  have hd := intervalIntegral.integral_Iic_sub_Iic
    (hi.integrableOn : IntegrableOn (gaussianPDFReal 0 1) (Iic (0:ℝ)) volume)
    (hi.integrableOn : IntegrableOn (gaussianPDFReal 0 1) (Iic x) volume)
  rw [← he x, ← he 0, AronowAudit.P053.NormalCompletion.normal_cdf_zero] at hd
  rw [show (gaussianPDFReal 0 1) = fun y =>
      (Real.sqrt (2*Real.pi))⁻¹ * Real.exp (-y^2/2) by
    funext y; simp [gaussianPDFReal], intervalIntegral.integral_const_mul] at hd
  linarith

/- The numerical engine uses Mathlib's exponential series remainder and its
   proved 20-place bounds for pi. All subsequent evaluations are rational. -/
noncomputable def t9_expPoly (z : ℝ) : ℝ :=
  ∑ n ∈ Finset.range 26, z^n / n.factorial

noncomputable def t9_cdfPoly (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.range 26, (-1/2:ℝ)^n * x^(2*n+1) / (n.factorial*(2*n+1))

lemma t9_exp_error (z : ℝ) (hz : |z| ≤ 2) :
    |Real.exp z - t9_expPoly z| ≤ 1/1000000000000000000 := by
  have hc : ‖(z:ℂ)‖ / (26+1:ℕ) ≤ (1/2:ℝ) := by
    simpa only [Complex.norm_real, Real.norm_eq_abs] using
      (show |z|/(26+1:ℕ) ≤ (1/2:ℝ) by norm_num; linarith)
  have h := Complex.exp_bound' (n := 26) hc
  have hr : |Real.exp z - t9_expPoly z| ≤ |z|^26 / (Nat.factorial 26:ℝ)*2 := by
    unfold t9_expPoly
    convert h using 1 <;> norm_cast
  calc
    _ ≤ |z|^26 / (Nat.factorial 26:ℝ)*2 := hr
    _ ≤ (2:ℝ)^26 / (Nat.factorial 26:ℝ)*2 := by gcongr
    _ ≤ _ := by norm_num

lemma t9_expPoly_integral (x : ℝ) :
    (∫ t in (0:ℝ)..x, t9_expPoly (-t^2/2)) = t9_cdfPoly x := by
  have he : (fun t : ℝ => t9_expPoly (-t^2/2)) = fun t =>
      ∑ n ∈ Finset.range 26, ((-1/2:ℝ)^n / n.factorial) * t^(2*n) := by
    funext t
    unfold t9_expPoly
    apply Finset.sum_congr rfl
    intro n hn
    rw [show -t^2/2 = (-1/2:ℝ)*t^2 by ring, mul_pow, ← pow_mul]
    ring
  rw [he, intervalIntegral.integral_finsetSum (fun n hn => by
    apply Continuous.intervalIntegrable; fun_prop)]
  simp only [intervalIntegral.integral_const_mul, integral_pow, zero_pow (by omega : 2*_+1 ≠ 0),
    sub_zero, t9_cdfPoly]
  apply Finset.sum_congr rfl
  intro n hn
  push_cast
  field_simp

lemma t9_cdf_error (x : ℝ) (hx : |x| ≤ 2) :
    |cdf (gaussianReal 0 1) x -
      (1/2 + (Real.sqrt (2*Real.pi))⁻¹*t9_cdfPoly x)| ≤
      (Real.sqrt (2*Real.pi))⁻¹*(2/1000000000000000000) := by
  have hi : IntervalIntegrable (fun t : ℝ => Real.exp (-t^2/2)) volume 0 x := by
    apply Continuous.intervalIntegrable; fun_prop
  have hp : IntervalIntegrable (fun t : ℝ => t9_expPoly (-t^2/2)) volume 0 x := by
    apply Continuous.intervalIntegrable
    unfold t9_expPoly
    fun_prop
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0:ℝ)) (b := x) (C := (1/1000000000000000000:ℝ))
    (f := fun t : ℝ => Real.exp (-t^2/2)-t9_expPoly (-t^2/2)) (by
      intro t ht
      have ht2 : |t| ≤ 2 := by
        rw [mem_uIoc] at ht
        rcases ht with ht | ht <;> rw [abs_le] at hx ⊢ <;> constructor <;> linarith
      have ht4 : t^2 ≤ 4 := by
        nlinarith [sq_abs t, (sq_le_sq₀ (abs_nonneg t) (by norm_num : (0:ℝ) ≤ 2)).2 ht2]
      have hz : |-t^2/2| ≤ 2 := by
        rw [abs_of_nonpos (by nlinarith [sq_nonneg t])]
        nlinarith
      simpa only [Real.norm_eq_abs] using t9_exp_error (-t^2/2) hz)
  rw [intervalIntegral.integral_sub hi hp, t9_expPoly_integral, Real.norm_eq_abs] at hb
  have hb' : |(∫ t in (0:ℝ)..x, Real.exp (-t^2/2)) - t9_cdfPoly x| ≤
      2/1000000000000000000 := by
    simp only [sub_zero] at hb
    linarith
  rw [t9_normal_cdf_integral, show
    (1/2+(Real.sqrt (2*Real.pi))⁻¹*(∫ t in (0:ℝ)..x, Real.exp (-t^2/2))) -
      (1/2+(Real.sqrt (2*Real.pi))⁻¹*t9_cdfPoly x) =
      (Real.sqrt (2*Real.pi))⁻¹*((∫ t in (0:ℝ)..x, Real.exp (-t^2/2))-t9_cdfPoly x) by ring,
    abs_mul, abs_of_nonneg (by positivity : 0 ≤ (Real.sqrt (2*Real.pi))⁻¹)]
  exact mul_le_mul_of_nonneg_left hb' (by positivity)

lemma t9_normalizer_bounds :
    (39894228040143267793/100000000000000000000:ℝ) ≤ (Real.sqrt (2*Real.pi))⁻¹ ∧
    (Real.sqrt (2*Real.pi))⁻¹ ≤ 39894228040143267795/100000000000000000000 := by
  have hs : 0 < Real.sqrt (2*Real.pi) := Real.sqrt_pos.2 (by positivity)
  have he : (Real.sqrt (2*Real.pi))^2 = 2*Real.pi := Real.sq_sqrt (by positivity)
  have hl : Real.sqrt (2*Real.pi) ≤ (100000000000000000000:ℝ)/39894228040143267793 := by
    nlinarith [Real.pi_lt_d20]
  have hu : (100000000000000000000:ℝ)/39894228040143267795 ≤ Real.sqrt (2*Real.pi) := by
    nlinarith [Real.pi_gt_d20]
  constructor
  · rw [inv_eq_one_div, le_div_iff₀ hs]
    nlinarith
  · rw [inv_eq_one_div, div_le_iff₀ hs]
    nlinarith

lemma t9_mixture_tail_values (w q1 q3 : ℝ) (hw : 0 ≤ w) (hw1 : w < 1)
    (h1 : cdf (normalMixture w) q1 = 1/4) (h3 : cdf (normalMixture w) q3 = 3/4) :
    mixtureLower w = t9_partial w q3/(3/4) ∧
    mixtureUpper w = (-w-t9_partial w q1)/(3/4) := by
  letI := t9_mixture_probability w hw hw1.le
  letI : NullSingletonClass (normalMixture w) := ⟨t9_mixture_null_singleton w⟩
  have hq1 := t9_quantile_eq_of_cdf _ (t9_mixture_cdf_strict w hw hw1)
    (1/4) q1 (by norm_num) (by norm_num) h1
  have hq3 := t9_quantile_eq_of_cdf _ (t9_mixture_cdf_strict w hw hw1)
    (3/4) q3 (by norm_num) (by norm_num) h3
  have hm1 : ((normalMixture w) (Ici q1)).toReal = 3/4 := by
    rw [← measure_congr (Ioi_ae_eq_Ici' (measure_singleton q1))]
    have hh := measureReal_add_measureReal_compl (μ := normalMixture w)
      (s := Iic q1) measurableSet_Iic
    rw [cdf_eq_real, measureReal_def] at h1
    simp only [compl_Iic, measureReal_def, measure_univ, ENNReal.toReal_one] at hh
    linarith
  have hi : (∫ y in Ici q1, y ∂normalMixture w) = -w-t9_partial w q1 := by
    have hh := integral_add_compl (s := Iic q1) measurableSet_Iic (t9_mixture_integrable w)
    rw [compl_Iic, t9_mixture_mean w hw hw1.le, t9_mixture_partial w q1 hw hw1.le] at hh
    rw [setIntegral_congr_set (Ioi_ae_eq_Ici' (measure_singleton q1))] at hh
    linarith
  constructor
  · rw [mixtureLower, hq3]
    simp only [EReal.coe_le_coe_iff]
    change (∫ y in Iic q3, y ∂normalMixture w)/((normalMixture w) (Iic q3)).toReal = _
    rw [t9_mixture_partial w q3 hw hw1.le]
    rw [cdf_eq_real, measureReal_def] at h3
    rw [h3]
  · rw [mixtureUpper, tailUpper, hq1]
    simp only [EReal.coe_le_coe_iff]
    change (∫ y in Ici q1, y ∂normalMixture w)/((normalMixture w) (Ici q1)).toReal = _
    rw [hi, hm1]

lemma t9_width_of_passer (μ : Measure (State 2 0)) (h : Assumptions μ)
    (w : ℝ) (hw : 0 ≤ w) (hw1 : w < 1)
    (hp0 : passerLaw μ 0 = normalMixture w)
    (hp1 : passerLaw μ 1 = (normalMixture w).map (fun y => -y))
    (hr0 : trimRatio μ 0 = 1/4) (hr1 : trimRatio μ 1 = 1/4) :
    effectBoundWidth μ = 2*(mixtureUpper w-mixtureLower w) := by
  have hb0 := passer_tail_mean_formula μ h 0
  have hb1 := passer_tail_mean_formula μ h 1
  rw [hr0, hp0] at hb0
  rw [hr1, hp1] at hb1
  norm_num only [show (1-(1/4:ℝ)) = 3/4 by norm_num] at hb0 hb1
  have hrefl := t9_mixture_reflected_tails w hw hw1
  rw [hrefl.1, hrefl.2] at hb1
  change lowerBound μ 0 = mixtureLower w ∧ upperBound μ 0 = mixtureUpper w at hb0
  rw [effectBoundWidth, hb0.1, hb0.2, hb1.1, hb1.2]
  ring

lemma t9_cdf_certificate (x l u : ℝ) (hx : |x| ≤ 2)
    (hp : 0 ≤ t9_cdfPoly x)
    (hl : l ≤ 1/2 + (39894228040143267793/100000000000000000000)*t9_cdfPoly x -
      (39894228040143267795/100000000000000000000)*(2/1000000000000000000))
    (hu : 1/2 + (39894228040143267795/100000000000000000000)*t9_cdfPoly x +
      (39894228040143267795/100000000000000000000)*(2/1000000000000000000) ≤ u) :
    l ≤ cdf (gaussianReal 0 1) x ∧ cdf (gaussianReal 0 1) x ≤ u := by
  have he := (abs_le.mp (t9_cdf_error x hx))
  have hc := t9_normalizer_bounds
  have hlo := mul_le_mul_of_nonneg_right hc.1 hp
  have hhi := mul_le_mul_of_nonneg_right hc.2 hp
  have herr := mul_le_mul_of_nonneg_right hc.2 (by norm_num : (0:ℝ) ≤ 2/1000000000000000000)
  constructor <;> linarith

lemma t9_pdf_certificate (x l u : ℝ) (hx : |x| ≤ 2)
    (hp : 0 ≤ t9_expPoly (-x^2/2)-1/1000000000000000000)
    (hl : l ≤ (39894228040143267793/100000000000000000000)*
      (t9_expPoly (-x^2/2)-1/1000000000000000000))
    (hu : (39894228040143267795/100000000000000000000)*
      (t9_expPoly (-x^2/2)+1/1000000000000000000) ≤ u) :
    l ≤ gaussianPDFReal 0 1 x ∧ gaussianPDFReal 0 1 x ≤ u := by
  have hx4 : x^2 ≤ 4 := by
    nlinarith [sq_abs x, (sq_le_sq₀ (abs_nonneg x) (by norm_num : (0:ℝ) ≤ 2)).2 hx]
  have hz : |-x^2/2| ≤ 2 := by
    rw [abs_of_nonpos (by nlinarith [sq_nonneg x])]
    nlinarith
  have he := abs_le.mp (t9_exp_error (-x^2/2) hz)
  have hc := t9_normalizer_bounds
  have hp' : 0 ≤ (Real.sqrt (2*Real.pi))⁻¹ := by positivity
  simp only [gaussianPDFReal, NNReal.coe_one, sub_zero, mul_one]
  constructor
  · calc
      _ ≤ (39894228040143267793/100000000000000000000)*
        (t9_expPoly (-x^2/2)-1/1000000000000000000) := hl
      _ ≤ (Real.sqrt (2*Real.pi))⁻¹*Real.exp (-x^2/2) := by
        apply mul_le_mul hc.1 (by linarith) hp hp'
  · calc
      _ ≤ (39894228040143267795/100000000000000000000)*
        (t9_expPoly (-x^2/2)+1/1000000000000000000) := by
        apply mul_le_mul hc.2 (by linarith) (Real.exp_nonneg _)
        norm_num
      _ ≤ _ := hu

lemma t9_phi_even (x : ℝ) : gaussianPDFReal 0 1 (-x) = gaussianPDFReal 0 1 x := by
  simp [gaussianPDFReal]

lemma t9_phi_antitone {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    gaussianPDFReal 0 1 y ≤ gaussianPDFReal 0 1 x := by
  simp only [gaussianPDFReal, NNReal.coe_one, sub_zero, mul_one]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.exp_le_exp.mpr
  have hs := (sq_le_sq₀ hx (hx.trans hxy)).2 hxy
  linarith

lemma t9_phi_monotone_neg {x y : ℝ} (hy : y ≤ 0) (hxy : x ≤ y) :
    gaussianPDFReal 0 1 x ≤ gaussianPDFReal 0 1 y := by
  rw [← t9_phi_even x, ← t9_phi_even y]
  exact t9_phi_antitone (by linarith) (by linarith)

lemma t9_partial_enclosure (w x pl pu cl cu gl gu : ℝ) (hw : 0 ≤ w) (hw1 : w ≤ 1)
    (hp : pl ≤ gaussianPDFReal 0 1 x ∧ gaussianPDFReal 0 1 x ≤ pu)
    (hc : cl ≤ cdf (gaussianReal 0 1) (x+1) ∧ cdf (gaussianReal 0 1) (x+1) ≤ cu)
    (hg : gl ≤ gaussianPDFReal 0 1 (x+1) ∧ gaussianPDFReal 0 1 (x+1) ≤ gu) :
    -(1-w)*pu-w*cu-w*gu ≤ t9_partial w x ∧
      t9_partial w x ≤ -(1-w)*pl-w*cl-w*gl := by
  have hp0 := mul_le_mul_of_nonneg_left hp.1 (sub_nonneg.mpr hw1)
  have hp1 := mul_le_mul_of_nonneg_left hp.2 (sub_nonneg.mpr hw1)
  have hc0 := mul_le_mul_of_nonneg_left hc.1 hw
  have hc1 := mul_le_mul_of_nonneg_left hc.2 hw
  have hg0 := mul_le_mul_of_nonneg_left hg.1 hw
  have hg1 := mul_le_mul_of_nonneg_left hg.2 hw
  unfold t9_partial
  constructor <;> linarith

-- Exact rational normal-CDF and density evaluations for the quantile brackets.

lemma t9_eval_w15q1a :
    ((1958236224212559/10000000000000000:ℝ) ≤ cdf (gaussianReal 0 1) (-856633899321/1000000000000:ℝ) ∧
      cdf (gaussianReal 0 1) (-856633899321/1000000000000:ℝ) ≤ (24477952802657/125000000000000:ℝ)) ∧
    ((2764157096821629/10000000000000000:ℝ) ≤ gaussianPDFReal 0 1 (-856633899321/1000000000000:ℝ) ∧
      gaussianPDFReal 0 1 (-856633899321/1000000000000:ℝ) ≤ (276415709682163/1000000000000000:ℝ)) := by
  constructor
  · have h : (100522047197343/125000000000000:ℝ) ≤ cdf (gaussianReal 0 1) (856633899321/1000000000000:ℝ) ∧
        cdf (gaussianReal 0 1) (856633899321/1000000000000:ℝ) ≤ (8041763775787441/10000000000000000:ℝ) := by
      apply t9_cdf_certificate <;> norm_num [t9_cdfPoly, Finset.sum_range_succ]
    have he : cdf (gaussianReal 0 1) (-856633899321/1000000000000:ℝ) =
        1-cdf (gaussianReal 0 1) (856633899321/1000000000000:ℝ) := by
      convert AronowAudit.P053.NormalCompletion.normal_cdf_neg (856633899321/1000000000000:ℝ) using 1 <;> norm_num
    rw [he]
    constructor <;> linarith [h.1, h.2]
  · apply t9_pdf_certificate <;>
      norm_num [t9_expPoly, Finset.sum_range_succ]

lemma t9_eval_w15q1b :
    ((1958236224215323/10000000000000000:ℝ) ≤ cdf (gaussianReal 0 1) (-21415847483/25000000000:ℝ) ∧
      cdf (gaussianReal 0 1) (-21415847483/25000000000:ℝ) ≤ (489559056053831/2500000000000000:ℝ)) ∧
    ((2764157096823997/10000000000000000:ℝ) ≤ gaussianPDFReal 0 1 (-21415847483/25000000000:ℝ) ∧
      gaussianPDFReal 0 1 (-21415847483/25000000000:ℝ) ≤ (1382078548411999/5000000000000000:ℝ)) := by
  constructor
  · have h : (2010440943946169/2500000000000000:ℝ) ≤ cdf (gaussianReal 0 1) (21415847483/25000000000:ℝ) ∧
        cdf (gaussianReal 0 1) (21415847483/25000000000:ℝ) ≤ (8041763775784677/10000000000000000:ℝ) := by
      apply t9_cdf_certificate <;> norm_num [t9_cdfPoly, Finset.sum_range_succ]
    have he : cdf (gaussianReal 0 1) (-21415847483/25000000000:ℝ) =
        1-cdf (gaussianReal 0 1) (21415847483/25000000000:ℝ) := by
      convert AronowAudit.P053.NormalCompletion.normal_cdf_neg (21415847483/25000000000:ℝ) using 1 <;> norm_num
    rw [he]
    constructor <;> linarith [h.1, h.2]
  · apply t9_pdf_certificate <;>
      norm_num [t9_expPoly, Finset.sum_range_succ]

lemma t9_eval_w15q1ap :
    ((2784997364723989/5000000000000000:ℝ) ≤ cdf (gaussianReal 0 1) (143366100679/1000000000000:ℝ) ∧
      cdf (gaussianReal 0 1) (143366100679/1000000000000:ℝ) ≤ (5569994729447979/10000000000000000:ℝ)) ∧
    ((3948633779112199/10000000000000000:ℝ) ≤ gaussianPDFReal 0 1 (143366100679/1000000000000:ℝ) ∧
      gaussianPDFReal 0 1 (143366100679/1000000000000:ℝ) ≤ (19743168895561/50000000000000:ℝ)) := by
  constructor
  · apply t9_cdf_certificate <;>
      norm_num [t9_cdfPoly, Finset.sum_range_succ]
  · apply t9_pdf_certificate <;>
      norm_num [t9_expPoly, Finset.sum_range_succ]

lemma t9_eval_w15q1bp :
    ((5569994729451927/10000000000000000:ℝ) ≤ cdf (gaussianReal 0 1) (3584152517/25000000000:ℝ) ∧
      cdf (gaussianReal 0 1) (3584152517/25000000000:ℝ) ≤ (696249341181491/1250000000000000:ℝ)) ∧
    ((3948633779111633/10000000000000000:ℝ) ≤ gaussianPDFReal 0 1 (3584152517/25000000000:ℝ) ∧
      gaussianPDFReal 0 1 (3584152517/25000000000:ℝ) ≤ (1974316889555817/5000000000000000:ℝ)) := by
  constructor
  · apply t9_cdf_certificate <;>
      norm_num [t9_cdfPoly, Finset.sum_range_succ]
  · apply t9_pdf_certificate <;>
      norm_num [t9_expPoly, Finset.sum_range_succ]

lemma t9_eval_w15q3a :
    ((7161261471710229/10000000000000000:ℝ) ≤ cdf (gaussianReal 0 1) (571371703981/1000000000000:ℝ) ∧
      cdf (gaussianReal 0 1) (571371703981/1000000000000:ℝ) ≤ (716126147171023/1000000000000000:ℝ)) ∧
    ((3388589464833319/10000000000000000:ℝ) ≤ gaussianPDFReal 0 1 (571371703981/1000000000000:ℝ) ∧
      gaussianPDFReal 0 1 (571371703981/1000000000000:ℝ) ≤ (84714736620833/250000000000000:ℝ)) := by
  constructor
  · apply t9_cdf_certificate <;>
      norm_num [t9_cdfPoly, Finset.sum_range_succ]
  · apply t9_pdf_certificate <;>
      norm_num [t9_expPoly, Finset.sum_range_succ]

lemma t9_eval_w15q3b :
    ((7161261471713617/10000000000000000:ℝ) ≤ cdf (gaussianReal 0 1) (285685851991/500000000000:ℝ) ∧
      cdf (gaussianReal 0 1) (285685851991/500000000000:ℝ) ≤ (3580630735856809/5000000000000000:ℝ)) ∧
    ((3388589464831383/10000000000000000:ℝ) ≤ gaussianPDFReal 0 1 (285685851991/500000000000:ℝ) ∧
      gaussianPDFReal 0 1 (285685851991/500000000000:ℝ) ≤ (423573683103923/1250000000000000:ℝ)) := by
  constructor
  · apply t9_cdf_certificate <;>
      norm_num [t9_cdfPoly, Finset.sum_range_succ]
  · apply t9_pdf_certificate <;>
      norm_num [t9_expPoly, Finset.sum_range_succ]

lemma t9_eval_w15q3ap :
    ((9419518326970377/10000000000000000:ℝ) ≤ cdf (gaussianReal 0 1) (1571371703981/1000000000000:ℝ) ∧
      cdf (gaussianReal 0 1) (1571371703981/1000000000000:ℝ) ≤ (4709759163485189/5000000000000000:ℝ)) ∧
    ((290180447320941/2500000000000000:ℝ) ≤ gaussianPDFReal 0 1 (1571371703981/1000000000000:ℝ) ∧
      gaussianPDFReal 0 1 (1571371703981/1000000000000:ℝ) ≤ (232144357856753/2000000000000000:ℝ)) := by
  constructor
  · apply t9_cdf_certificate <;>
      norm_num [t9_cdfPoly, Finset.sum_range_succ]
  · apply t9_pdf_certificate <;>
      norm_num [t9_expPoly, Finset.sum_range_succ]

lemma t9_eval_w15q3bp :
    ((4709759163485769/5000000000000000:ℝ) ≤ cdf (gaussianReal 0 1) (785685851991/500000000000:ℝ) ∧
      cdf (gaussianReal 0 1) (785685851991/500000000000:ℝ) ≤ (9419518326971539/10000000000000000:ℝ)) ∧
    ((58036089464097/500000000000000:ℝ) ≤ gaussianPDFReal 0 1 (785685851991/500000000000:ℝ) ∧
      gaussianPDFReal 0 1 (785685851991/500000000000:ℝ) ≤ (1160721789281941/10000000000000000:ℝ)) := by
  constructor
  · apply t9_cdf_certificate <;>
      norm_num [t9_cdfPoly, Finset.sum_range_succ]
  · apply t9_pdf_certificate <;>
      norm_num [t9_expPoly, Finset.sum_range_succ]

lemma t9_eval_w10q1a :
    ((1066062584173611/5000000000000000:ℝ) ≤ cdf (gaussianReal 0 1) (-159064807773/200000000000:ℝ) ∧
      cdf (gaussianReal 0 1) (-159064807773/200000000000:ℝ) ≤ (2132125168347223/10000000000000000:ℝ)) ∧
    ((2907740724740359/10000000000000000:ℝ) ≤ gaussianPDFReal 0 1 (-159064807773/200000000000:ℝ) ∧
      gaussianPDFReal 0 1 (-159064807773/200000000000:ℝ) ≤ (72693518118509/250000000000000:ℝ)) := by
  constructor
  · have h : (7867874831652777/10000000000000000:ℝ) ≤ cdf (gaussianReal 0 1) (159064807773/200000000000:ℝ) ∧
        cdf (gaussianReal 0 1) (159064807773/200000000000:ℝ) ≤ (3933937415826389/5000000000000000:ℝ) := by
      apply t9_cdf_certificate <;> norm_num [t9_cdfPoly, Finset.sum_range_succ]
    have he : cdf (gaussianReal 0 1) (-159064807773/200000000000:ℝ) =
        1-cdf (gaussianReal 0 1) (159064807773/200000000000:ℝ) := by
      convert AronowAudit.P053.NormalCompletion.normal_cdf_neg (159064807773/200000000000:ℝ) using 1 <;> norm_num
    rw [he]
    constructor <;> linarith [h.1, h.2]
  · apply t9_pdf_certificate <;>
      norm_num [t9_expPoly, Finset.sum_range_succ]

lemma t9_eval_w10q1b :
    ((213212516835013/1000000000000000:ℝ) ≤ cdf (gaussianReal 0 1) (-49707752429/62500000000:ℝ) ∧
      cdf (gaussianReal 0 1) (-49707752429/62500000000:ℝ) ≤ (2132125168350131/10000000000000000:ℝ)) ∧
    ((181733795296417/625000000000000:ℝ) ≤ gaussianPDFReal 0 1 (-49707752429/62500000000:ℝ) ∧
      gaussianPDFReal 0 1 (-49707752429/62500000000:ℝ) ≤ (2907740724742673/10000000000000000:ℝ)) := by
  constructor
  · have h : (7867874831649869/10000000000000000:ℝ) ≤ cdf (gaussianReal 0 1) (49707752429/62500000000:ℝ) ∧
        cdf (gaussianReal 0 1) (49707752429/62500000000:ℝ) ≤ (786787483164987/1000000000000000:ℝ) := by
      apply t9_cdf_certificate <;> norm_num [t9_cdfPoly, Finset.sum_range_succ]
    have he : cdf (gaussianReal 0 1) (-49707752429/62500000000:ℝ) =
        1-cdf (gaussianReal 0 1) (49707752429/62500000000:ℝ) := by
      convert AronowAudit.P053.NormalCompletion.normal_cdf_neg (49707752429/62500000000:ℝ) using 1 <;> norm_num
    rw [he]
    constructor <;> linarith [h.1, h.2]
  · apply t9_pdf_certificate <;>
      norm_num [t9_expPoly, Finset.sum_range_succ]

lemma t9_eval_w10q1ap :
    ((2905436742432389/5000000000000000:ℝ) ≤ cdf (gaussianReal 0 1) (40935192227/200000000000:ℝ) ∧
      cdf (gaussianReal 0 1) (40935192227/200000000000:ℝ) ≤ (5810873484864779/10000000000000000:ℝ)) ∧
    ((3906728938551991/10000000000000000:ℝ) ≤ gaussianPDFReal 0 1 (40935192227/200000000000:ℝ) ∧
      gaussianPDFReal 0 1 (40935192227/200000000000:ℝ) ≤ (488341117318999/1250000000000000:ℝ)) := by
  constructor
  · apply t9_cdf_certificate <;>
      norm_num [t9_cdfPoly, Finset.sum_range_succ]
  · apply t9_pdf_certificate <;>
      norm_num [t9_expPoly, Finset.sum_range_succ]

lemma t9_eval_w10q1bp :
    ((1162174696973737/2000000000000000:ℝ) ≤ cdf (gaussianReal 0 1) (12792247571/62500000000:ℝ) ∧
      cdf (gaussianReal 0 1) (12792247571/62500000000:ℝ) ≤ (2905436742434343/5000000000000000:ℝ)) ∧
    ((488341117318899/1250000000000000:ℝ) ≤ gaussianPDFReal 0 1 (12792247571/62500000000:ℝ) ∧
      gaussianPDFReal 0 1 (12792247571/62500000000:ℝ) ≤ (3906728938551193/10000000000000000:ℝ)) := by
  constructor
  · apply t9_cdf_certificate <;>
      norm_num [t9_cdfPoly, Finset.sum_range_succ]
  · apply t9_pdf_certificate <;>
      norm_num [t9_expPoly, Finset.sum_range_succ]

lemma t9_eval_w10q3a :
    ((7282199050645219/10000000000000000:ℝ) ≤ cdf (gaussianReal 0 1) (607438130699/1000000000000:ℝ) ∧
      cdf (gaussianReal 0 1) (607438130699/1000000000000:ℝ) ≤ (364109952532261/500000000000000:ℝ)) ∧
    ((3317315987530699/10000000000000000:ℝ) ≤ gaussianPDFReal 0 1 (607438130699/1000000000000:ℝ) ∧
      gaussianPDFReal 0 1 (607438130699/1000000000000:ℝ) ≤ (33173159875307/100000000000000:ℝ)) := by
  constructor
  · apply t9_cdf_certificate <;>
      norm_num [t9_cdfPoly, Finset.sum_range_succ]
  · apply t9_pdf_certificate <;>
      norm_num [t9_expPoly, Finset.sum_range_succ]

lemma t9_eval_w10q3b :
    ((910274881331067/1250000000000000:ℝ) ≤ cdf (gaussianReal 0 1) (6074381307/10000000000:ℝ) ∧
      cdf (gaussianReal 0 1) (6074381307/10000000000:ℝ) ≤ (7282199050648537/10000000000000000:ℝ)) ∧
    ((829328996882171/2500000000000000:ℝ) ≤ gaussianPDFReal 0 1 (6074381307/10000000000:ℝ) ∧
      gaussianPDFReal 0 1 (6074381307/10000000000:ℝ) ≤ (663463197505737/2000000000000000:ℝ)) := by
  constructor
  · apply t9_cdf_certificate <;>
      norm_num [t9_cdfPoly, Finset.sum_range_succ]
  · apply t9_pdf_certificate <;>
      norm_num [t9_expPoly, Finset.sum_range_succ]

lemma t9_eval_w10q3ap :
    ((9460208544177833/10000000000000000:ℝ) ≤ cdf (gaussianReal 0 1) (1607438130699/1000000000000:ℝ) ∧
      cdf (gaussianReal 0 1) (1607438130699/1000000000000:ℝ) ≤ (4730104272088917/5000000000000000:ℝ)) ∧
    ((274013891946927/2500000000000000:ℝ) ≤ gaussianPDFReal 0 1 (1607438130699/1000000000000:ℝ) ∧
      gaussianPDFReal 0 1 (1607438130699/1000000000000:ℝ) ≤ (1096055567787709/10000000000000000:ℝ)) := by
  constructor
  · apply t9_cdf_certificate <;>
      norm_num [t9_cdfPoly, Finset.sum_range_succ]
  · apply t9_pdf_certificate <;>
      norm_num [t9_expPoly, Finset.sum_range_succ]

lemma t9_eval_w10q3bp :
    ((9460208544178929/10000000000000000:ℝ) ≤ cdf (gaussianReal 0 1) (16074381307/10000000000:ℝ) ∧
      cdf (gaussianReal 0 1) (16074381307/10000000000:ℝ) ≤ (946020854417893/1000000000000000:ℝ)) ∧
    ((548027783892973/5000000000000000:ℝ) ≤ gaussianPDFReal 0 1 (16074381307/10000000000:ℝ) ∧
      gaussianPDFReal 0 1 (16074381307/10000000000:ℝ) ≤ (1096055567785947/10000000000000000:ℝ)) := by
  constructor
  · apply t9_cdf_certificate <;>
      norm_num [t9_cdfPoly, Finset.sum_range_succ]
  · apply t9_pdf_certificate <;>
      norm_num [t9_expPoly, Finset.sum_range_succ]

-- Quantile brackets and propagated lower partial moment bounds.

lemma t9_quantile_w15q1 : ∃ q : ℝ,
    quantile (normalMixture (3/20:ℝ)) (1/4:ℝ) = (q:EReal) ∧
    cdf (normalMixture (3/20:ℝ)) q = (1/4:ℝ) ∧
    t9_partial (3/20:ℝ) q ∈ Icc (-1510931123434007/4000000000000000:ℝ) (-37773278085823263/100000000000000000:ℝ) := by
  obtain ⟨q,hq,hcdf⟩ := t9_mixture_quantile (3/20:ℝ) (1/4:ℝ)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hfa : cdf (normalMixture (3/20:ℝ)) (-856633899321/1000000000000:ℝ) < (1/4:ℝ) := by
    rw [t9_mixture_cdf _ _ (by norm_num) (by norm_num)]
    have h0 := t9_eval_w15q1a.1.2
    have h1 := t9_eval_w15q1ap.1.2
    norm_num only [show (-856633899321/1000000000000:ℝ)+1 = (143366100679/1000000000000:ℝ) by norm_num]
    linarith
  have hfb : (1/4:ℝ) < cdf (normalMixture (3/20:ℝ)) (-21415847483/25000000000:ℝ) := by
    rw [t9_mixture_cdf _ _ (by norm_num) (by norm_num)]
    have h0 := t9_eval_w15q1b.1.1
    have h1 := t9_eval_w15q1bp.1.1
    norm_num only [show (-21415847483/25000000000:ℝ)+1 = (3584152517/25000000000:ℝ) by norm_num]
    linarith
  have hqa : (-856633899321/1000000000000:ℝ) ≤ q := le_of_lt
    ((t9_mixture_cdf_strict (3/20:ℝ) (by norm_num) (by norm_num)).lt_iff_lt.mp (by
      rw [hcdf]; exact hfa))
  have hqb : q ≤ (-21415847483/25000000000:ℝ) := le_of_lt
    ((t9_mixture_cdf_strict (3/20:ℝ) (by norm_num) (by norm_num)).lt_iff_lt.mp (by
      rw [hcdf]; exact hfb))
  have hp : (2764157096821629/10000000000000000:ℝ) ≤ gaussianPDFReal 0 1 q ∧
      gaussianPDFReal 0 1 q ≤ (1382078548411999/5000000000000000:ℝ) := by
    exact ⟨t9_eval_w15q1a.2.1.trans (t9_phi_monotone_neg (by linarith) hqa),
      (t9_phi_monotone_neg (by norm_num) hqb).trans t9_eval_w15q1b.2.2⟩
  have hc : (2784997364723989/5000000000000000:ℝ) ≤ cdf (gaussianReal 0 1) (q+1) ∧
      cdf (gaussianReal 0 1) (q+1) ≤ (696249341181491/1250000000000000:ℝ) := by
    exact ⟨t9_eval_w15q1ap.1.1.trans (monotone_cdf _ (by linarith)),
      (monotone_cdf _ (by linarith)).trans t9_eval_w15q1bp.1.2⟩
  have hg : (3948633779111633/10000000000000000:ℝ) ≤ gaussianPDFReal 0 1 (q+1) ∧
      gaussianPDFReal 0 1 (q+1) ≤ (19743168895561/50000000000000:ℝ) := by
    exact ⟨t9_eval_w15q1bp.2.1.trans (t9_phi_antitone (by linarith) (by linarith)),
      (t9_phi_antitone (by norm_num) (by linarith)).trans t9_eval_w15q1ap.2.2⟩
  have hm := t9_partial_enclosure (3/20:ℝ) q _ _ _ _ _ _
    (by norm_num) (by norm_num) hp hc hg
  refine ⟨q,hq,hcdf,?_,?_⟩ <;> linarith [hm.1,hm.2]

lemma t9_quantile_w15q3 : ∃ q : ℝ,
    quantile (normalMixture (3/20:ℝ)) (3/4:ℝ) = (q:EReal) ∧
    cdf (normalMixture (3/20:ℝ)) q = (3/4:ℝ) ∧
    t9_partial (3/20:ℝ) q ∈ Icc (-698021416022909/1562500000000000:ℝ) (-44673370625445231/100000000000000000:ℝ) := by
  obtain ⟨q,hq,hcdf⟩ := t9_mixture_quantile (3/20:ℝ) (3/4:ℝ)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hfa : cdf (normalMixture (3/20:ℝ)) (571371703981/1000000000000:ℝ) < (3/4:ℝ) := by
    rw [t9_mixture_cdf _ _ (by norm_num) (by norm_num)]
    have h0 := t9_eval_w15q3a.1.2
    have h1 := t9_eval_w15q3ap.1.2
    norm_num only [show (571371703981/1000000000000:ℝ)+1 = (1571371703981/1000000000000:ℝ) by norm_num]
    linarith
  have hfb : (3/4:ℝ) < cdf (normalMixture (3/20:ℝ)) (285685851991/500000000000:ℝ) := by
    rw [t9_mixture_cdf _ _ (by norm_num) (by norm_num)]
    have h0 := t9_eval_w15q3b.1.1
    have h1 := t9_eval_w15q3bp.1.1
    norm_num only [show (285685851991/500000000000:ℝ)+1 = (785685851991/500000000000:ℝ) by norm_num]
    linarith
  have hqa : (571371703981/1000000000000:ℝ) ≤ q := le_of_lt
    ((t9_mixture_cdf_strict (3/20:ℝ) (by norm_num) (by norm_num)).lt_iff_lt.mp (by
      rw [hcdf]; exact hfa))
  have hqb : q ≤ (285685851991/500000000000:ℝ) := le_of_lt
    ((t9_mixture_cdf_strict (3/20:ℝ) (by norm_num) (by norm_num)).lt_iff_lt.mp (by
      rw [hcdf]; exact hfb))
  have hp : (3388589464831383/10000000000000000:ℝ) ≤ gaussianPDFReal 0 1 q ∧
      gaussianPDFReal 0 1 q ≤ (84714736620833/250000000000000:ℝ) := by
    exact ⟨t9_eval_w15q3b.2.1.trans (t9_phi_antitone (by linarith) hqb),
      (t9_phi_antitone (by norm_num) hqa).trans t9_eval_w15q3a.2.2⟩
  have hc : (9419518326970377/10000000000000000:ℝ) ≤ cdf (gaussianReal 0 1) (q+1) ∧
      cdf (gaussianReal 0 1) (q+1) ≤ (9419518326971539/10000000000000000:ℝ) := by
    exact ⟨t9_eval_w15q3ap.1.1.trans (monotone_cdf _ (by linarith)),
      (monotone_cdf _ (by linarith)).trans t9_eval_w15q3bp.1.2⟩
  have hg : (58036089464097/500000000000000:ℝ) ≤ gaussianPDFReal 0 1 (q+1) ∧
      gaussianPDFReal 0 1 (q+1) ≤ (232144357856753/2000000000000000:ℝ) := by
    exact ⟨t9_eval_w15q3bp.2.1.trans (t9_phi_antitone (by linarith) (by linarith)),
      (t9_phi_antitone (by norm_num) (by linarith)).trans t9_eval_w15q3ap.2.2⟩
  have hm := t9_partial_enclosure (3/20:ℝ) q _ _ _ _ _ _
    (by norm_num) (by norm_num) hp hc hg
  refine ⟨q,hq,hcdf,?_,?_⟩ <;> linarith [hm.1,hm.2]

lemma t9_quantile_w10q1 : ∃ q : ℝ,
    quantile (normalMixture (1/10:ℝ)) (1/4:ℝ) = (q:EReal) ∧
    cdf (normalMixture (1/10:ℝ)) q = (1/4:ℝ) ∧
    t9_partial (1/10:ℝ) q ∈ Icc (-7177453789220947/20000000000000000:ℝ) (-35887268946079201/100000000000000000:ℝ) := by
  obtain ⟨q,hq,hcdf⟩ := t9_mixture_quantile (1/10:ℝ) (1/4:ℝ)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hfa : cdf (normalMixture (1/10:ℝ)) (-159064807773/200000000000:ℝ) < (1/4:ℝ) := by
    rw [t9_mixture_cdf _ _ (by norm_num) (by norm_num)]
    have h0 := t9_eval_w10q1a.1.2
    have h1 := t9_eval_w10q1ap.1.2
    norm_num only [show (-159064807773/200000000000:ℝ)+1 = (40935192227/200000000000:ℝ) by norm_num]
    linarith
  have hfb : (1/4:ℝ) < cdf (normalMixture (1/10:ℝ)) (-49707752429/62500000000:ℝ) := by
    rw [t9_mixture_cdf _ _ (by norm_num) (by norm_num)]
    have h0 := t9_eval_w10q1b.1.1
    have h1 := t9_eval_w10q1bp.1.1
    norm_num only [show (-49707752429/62500000000:ℝ)+1 = (12792247571/62500000000:ℝ) by norm_num]
    linarith
  have hqa : (-159064807773/200000000000:ℝ) ≤ q := le_of_lt
    ((t9_mixture_cdf_strict (1/10:ℝ) (by norm_num) (by norm_num)).lt_iff_lt.mp (by
      rw [hcdf]; exact hfa))
  have hqb : q ≤ (-49707752429/62500000000:ℝ) := le_of_lt
    ((t9_mixture_cdf_strict (1/10:ℝ) (by norm_num) (by norm_num)).lt_iff_lt.mp (by
      rw [hcdf]; exact hfb))
  have hp : (2907740724740359/10000000000000000:ℝ) ≤ gaussianPDFReal 0 1 q ∧
      gaussianPDFReal 0 1 q ≤ (2907740724742673/10000000000000000:ℝ) := by
    exact ⟨t9_eval_w10q1a.2.1.trans (t9_phi_monotone_neg (by linarith) hqa),
      (t9_phi_monotone_neg (by norm_num) hqb).trans t9_eval_w10q1b.2.2⟩
  have hc : (2905436742432389/5000000000000000:ℝ) ≤ cdf (gaussianReal 0 1) (q+1) ∧
      cdf (gaussianReal 0 1) (q+1) ≤ (2905436742434343/5000000000000000:ℝ) := by
    exact ⟨t9_eval_w10q1ap.1.1.trans (monotone_cdf _ (by linarith)),
      (monotone_cdf _ (by linarith)).trans t9_eval_w10q1bp.1.2⟩
  have hg : (488341117318899/1250000000000000:ℝ) ≤ gaussianPDFReal 0 1 (q+1) ∧
      gaussianPDFReal 0 1 (q+1) ≤ (488341117318999/1250000000000000:ℝ) := by
    exact ⟨t9_eval_w10q1bp.2.1.trans (t9_phi_antitone (by linarith) (by linarith)),
      (t9_phi_antitone (by norm_num) (by linarith)).trans t9_eval_w10q1ap.2.2⟩
  have hm := t9_partial_enclosure (1/10:ℝ) q _ _ _ _ _ _
    (by norm_num) (by norm_num) hp hc hg
  refine ⟨q,hq,hcdf,?_,?_⟩ <;> linarith [hm.1,hm.2]

lemma t9_quantile_w10q3 : ∃ q : ℝ,
    quantile (normalMixture (1/10:ℝ)) (3/4:ℝ) = (q:EReal) ∧
    cdf (normalMixture (1/10:ℝ)) q = (3/4:ℝ) ∧
    t9_partial (1/10:ℝ) q ∈ Icc (-40412107999742939/100000000000000000:ℝ) (-8082421599944387/20000000000000000:ℝ) := by
  obtain ⟨q,hq,hcdf⟩ := t9_mixture_quantile (1/10:ℝ) (3/4:ℝ)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hfa : cdf (normalMixture (1/10:ℝ)) (607438130699/1000000000000:ℝ) < (3/4:ℝ) := by
    rw [t9_mixture_cdf _ _ (by norm_num) (by norm_num)]
    have h0 := t9_eval_w10q3a.1.2
    have h1 := t9_eval_w10q3ap.1.2
    norm_num only [show (607438130699/1000000000000:ℝ)+1 = (1607438130699/1000000000000:ℝ) by norm_num]
    linarith
  have hfb : (3/4:ℝ) < cdf (normalMixture (1/10:ℝ)) (6074381307/10000000000:ℝ) := by
    rw [t9_mixture_cdf _ _ (by norm_num) (by norm_num)]
    have h0 := t9_eval_w10q3b.1.1
    have h1 := t9_eval_w10q3bp.1.1
    norm_num only [show (6074381307/10000000000:ℝ)+1 = (16074381307/10000000000:ℝ) by norm_num]
    linarith
  have hqa : (607438130699/1000000000000:ℝ) ≤ q := le_of_lt
    ((t9_mixture_cdf_strict (1/10:ℝ) (by norm_num) (by norm_num)).lt_iff_lt.mp (by
      rw [hcdf]; exact hfa))
  have hqb : q ≤ (6074381307/10000000000:ℝ) := le_of_lt
    ((t9_mixture_cdf_strict (1/10:ℝ) (by norm_num) (by norm_num)).lt_iff_lt.mp (by
      rw [hcdf]; exact hfb))
  have hp : (829328996882171/2500000000000000:ℝ) ≤ gaussianPDFReal 0 1 q ∧
      gaussianPDFReal 0 1 q ≤ (33173159875307/100000000000000:ℝ) := by
    exact ⟨t9_eval_w10q3b.2.1.trans (t9_phi_antitone (by linarith) hqb),
      (t9_phi_antitone (by norm_num) hqa).trans t9_eval_w10q3a.2.2⟩
  have hc : (9460208544177833/10000000000000000:ℝ) ≤ cdf (gaussianReal 0 1) (q+1) ∧
      cdf (gaussianReal 0 1) (q+1) ≤ (946020854417893/1000000000000000:ℝ) := by
    exact ⟨t9_eval_w10q3ap.1.1.trans (monotone_cdf _ (by linarith)),
      (monotone_cdf _ (by linarith)).trans t9_eval_w10q3bp.1.2⟩
  have hg : (548027783892973/5000000000000000:ℝ) ≤ gaussianPDFReal 0 1 (q+1) ∧
      gaussianPDFReal 0 1 (q+1) ≤ (1096055567787709/10000000000000000:ℝ) := by
    exact ⟨t9_eval_w10q3bp.2.1.trans (t9_phi_antitone (by linarith) (by linarith)),
      (t9_phi_antitone (by norm_num) (by linarith)).trans t9_eval_w10q3ap.2.2⟩
  have hm := t9_partial_enclosure (1/10:ℝ) q _ _ _ _ _ _
    (by norm_num) (by norm_num) hp hc hg
  refine ⟨q,hq,hcdf,?_,?_⟩ <;> linarith [hm.1,hm.2]

lemma t9_mixture_width_15 :
    2*(mixtureUpper (3/20:ℝ)-mixtureLower (3/20:ℝ)) ∈ Icc (22482216237/12500000000:ℝ) (89928864949/50000000000:ℝ) := by
  obtain ⟨q1,hq1,hc1,hm1⟩ := t9_quantile_w15q1
  obtain ⟨q3,hq3,hc3,hm3⟩ := t9_quantile_w15q3
  have ht := t9_mixture_tail_values (3/20:ℝ) q1 q3 (by norm_num) (by norm_num) hc1 hc3
  rw [ht.1,ht.2]
  constructor <;> linarith [hm1.1,hm1.2,hm3.1,hm3.2]

lemma t9_mixture_width_10 :
    2*(mixtureUpper (1/10:ℝ)-mixtureLower (1/10:ℝ)) ∈ Icc (176798338521/100000000000:ℝ) (176798338523/100000000000:ℝ) := by
  obtain ⟨q1,hq1,hc1,hm1⟩ := t9_quantile_w10q1
  obtain ⟨q3,hq3,hc3,hm3⟩ := t9_quantile_w10q3
  have ht := t9_mixture_tail_values (1/10:ℝ) q1 q3 (by norm_num) (by norm_num) hc1 hc3
  rw [ht.1,ht.2]
  constructor <;> linarith [hm1.1,hm1.2,hm3.1,hm3.2]

lemma t9_design_one_width :
    effectBoundWidth (simulationLaw (4/5) (4/5) (1/4) 1 1) =
      2*(mixtureUpper (3/20)-mixtureLower (3/20)) := by
  have ht := t9_trim_of_rates _ t9_design_one_rates.1 t9_design_one_rates.2
  exact t9_width_of_passer _ t9_design_one_assumptions (3/20) (by norm_num) (by norm_num)
    t9_design_one_passer.1 t9_design_one_passer.2 ht.1 ht.2

lemma t9_design_two_width :
    effectBoundWidth (simulationLaw (4/5) (4/5) (1/2) 1 1) =
      2*(mixtureUpper (1/10)-mixtureLower (1/10)) := by
  have ht := t9_trim_of_rates _ t9_design_two_rates.1 t9_design_two_rates.2
  exact t9_width_of_passer _ t9_design_two_assumptions (1/10) (by norm_num) (by norm_num)
    t9_design_two_passer.1 t9_design_two_passer.2 ht.1 ht.2

lemma t9_simulation_parameters :
    ∀ ρ ∈ ({(1/4 : ℝ), 1/2} : Set ℝ), let μ := simulationLaw (4/5) (4/5) ρ 1 1
      Assumptions μ ∧ 0 < μ alwaysPass ∧ Atomless (μ.map observedY) ∧
      FullRealSupport μ observedY ∧ checkCorrelation μ 0 1 = ρ ∧
      passingRate μ 0 = 4/5 ∧ passingRate μ 1 = 4/5 ∧ trimRatio μ 0 = 1/4 ∧ trimRatio μ 1 = 1/4 := by
  intro ρ hρ
  simp only [mem_insert_iff, mem_singleton_iff] at hρ
  rcases hρ with rfl | rfl
  · have ht := t9_trim_of_rates _ t9_design_one_rates.1 t9_design_one_rates.2
    refine ⟨t9_design_one_assumptions, ?_, ?_, ?_, t9_design_one_correlation,
      t9_design_one_rates.1, t9_design_one_rates.2, ht.1, ht.2⟩
    · rw [t9_design_one, t9_sum_always]
      norm_num [ENNReal.div_pos_iff]
    · rw [t9_design_one]
      exact t9_sum_atomless _ _ _ _
    · rw [t9_design_one]
      apply t9_sum_support
      norm_num [ENNReal.div_pos_iff]
  · have ht := t9_trim_of_rates _ t9_design_two_rates.1 t9_design_two_rates.2
    refine ⟨t9_design_two_assumptions, ?_, ?_, ?_, t9_design_two_correlation,
      t9_design_two_rates.1, t9_design_two_rates.2, ht.1, ht.2⟩
    · rw [t9_design_two, t9_sum_always]
      norm_num [ENNReal.div_pos_iff]
    · rw [t9_design_two]
      exact t9_sum_atomless _ _ _ _
    · rw [t9_design_two]
      apply t9_sum_support
      norm_num [ENNReal.div_pos_iff]

/-- The exact T9 statement, proved from the simulation laws and rational certificates above. -/
theorem simulation_width_counterexample_proof :
    (∀ ρ ∈ ({(1/4 : ℝ), 1/2} : Set ℝ), let μ := simulationLaw (4/5) (4/5) ρ 1 1
      Assumptions μ ∧ 0 < μ alwaysPass ∧ Atomless (μ.map observedY) ∧
      FullRealSupport μ observedY ∧ checkCorrelation μ 0 1 = ρ ∧
      passingRate μ 0 = 4/5 ∧ passingRate μ 1 = 4/5 ∧ trimRatio μ 0 = 1/4 ∧ trimRatio μ 1 = 1/4) ∧
    (simulationLaw (4/5) (4/5) (1/4) 1 1) alwaysPass = 17/25 ∧
    (simulationLaw (4/5) (4/5) (1/2) 1 1) alwaysPass = 18/25 ∧
    passerLaw (simulationLaw (4/5) (4/5) (1/4) 1 1) 0 = normalMixture (3/20) ∧
    passerLaw (simulationLaw (4/5) (4/5) (1/2) 1 1) 0 = normalMixture (1/10) ∧
    passerLaw (simulationLaw (4/5) (4/5) (1/4) 1 1) 1 = (normalMixture (3/20)).map (fun y => -y) ∧
    passerLaw (simulationLaw (4/5) (4/5) (1/2) 1 1) 1 = (normalMixture (1/10)).map (fun y => -y) ∧
    (∫ y, y ∂normalMixture (3/20)) = -3/20 ∧
    (∫ y, y ∂normalMixture (1/10)) = -1/10 ∧
    (∫ y, (y+3/20)^2 ∂normalMixture (3/20)) = 451/400 ∧
    (∫ y, (y+1/10)^2 ∂normalMixture (1/10)) = 109/100 ∧
    effectBoundWidth (simulationLaw (4/5) (4/5) (1/4) 1 1) =
      2*(mixtureUpper (3/20)-mixtureLower (3/20)) ∧
    effectBoundWidth (simulationLaw (4/5) (4/5) (1/2) 1 1) =
      2*(mixtureUpper (1/10)-mixtureLower (1/10)) ∧
    effectBoundWidth (simulationLaw (4/5) (4/5) (1/4) 1 1) ∈
      Icc (1798577298898/1000000000000) (1798577299027/1000000000000) ∧
    effectBoundWidth (simulationLaw (4/5) (4/5) (1/2) 1 1) ∈
      Icc (1767983385194/1000000000000) (1767983385319/1000000000000) ∧
    30593913580/1000000000000 <
      effectBoundWidth (simulationLaw (4/5) (4/5) (1/4) 1 1) -
      effectBoundWidth (simulationLaw (4/5) (4/5) (1/2) 1 1) := by
  have hw15 : effectBoundWidth (simulationLaw (4/5) (4/5) (1/4) 1 1) ∈
      Icc (179857729896/100000000000) (179857729898/100000000000) := by
    rw [t9_design_one_width]
    convert t9_mixture_width_15 using 1 <;> norm_num
  have hw10 : effectBoundWidth (simulationLaw (4/5) (4/5) (1/2) 1 1) ∈
      Icc (176798338521/100000000000) (176798338523/100000000000) := by
    rw [t9_design_two_width]
    convert t9_mixture_width_10 using 1 <;> norm_num
  refine ⟨t9_simulation_parameters, ?_, ?_, t9_design_one_passer.1, t9_design_two_passer.1,
    t9_design_one_passer.2, t9_design_two_passer.2, ?_, ?_, ?_, ?_,
    t9_design_one_width, t9_design_two_width, ?_, ?_, ?_⟩
  · rw [t9_design_one, t9_sum_always]
  · rw [t9_design_two, t9_sum_always]
  · convert t9_mixture_mean (3/20) (by norm_num) (by norm_num) using 1 <;> norm_num
  · convert t9_mixture_mean (1/10) (by norm_num) (by norm_num) using 1 <;> norm_num
  · convert t9_mixture_centered (3/20) (by norm_num) (by norm_num) using 1 <;> norm_num
  · convert t9_mixture_centered (1/10) (by norm_num) (by norm_num) using 1 <;> norm_num
  · constructor <;> linarith [hw15.1, hw15.2]
  · constructor <;> linarith [hw10.1, hw10.2]
  · linarith [hw15.1, hw10.2]

end
end AronowAudit.P010.Wave1
