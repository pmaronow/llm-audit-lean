import SAP.P029a.WH.W1.Leaves
import Mathlib.Probability.Independence.Integration
import Mathlib.MeasureTheory.Integral.Bochner.Set

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 900000

namespace SAP.P029a.WH.W1.P.T4_L2

open SAP.P029a MeasureTheory ProbabilityTheory Set
open scoped BigOperators Classical

noncomputable section

theorem profile_mul_integrable {Ω X : Type*}
    [MeasurableSpace Ω] [Fintype X] [MeasurableSpace X]
    [MeasurableSingletonClass X] {μ : Measure Ω} {T : Ω → X}
    (hT : Measurable T) {v : Ω → ℝ} (hv : Integrable v μ) (w : X → ℝ) :
    Integrable (fun ω => w (T ω) * v ω) μ := by
  have hcell (x : X) : MeasurableSet {ω | T ω = x} :=
    hT (measurableSet_singleton x)
  have hid : (fun ω => w (T ω) * v ω) =
      fun ω => ∑ x : X, ({ω | T ω = x}.indicator (fun ω => w x * v ω)) ω := by
    funext ω
    simp [Set.indicator, Finset.sum_ite_eq']
  rw [hid]
  exact integrable_finsetSum _ (fun x _ => (hv.const_mul (w x)).indicator (hcell x))

theorem profile_integral {Ω X : Type*}
    [MeasurableSpace Ω] [Fintype X] [MeasurableSpace X]
    [MeasurableSingletonClass X] {μ : Measure Ω} {T : Ω → X}
    (hT : Measurable T) {v : Ω → ℝ} (hv : Integrable v μ) (w : X → ℝ) :
    (∫ ω, w (T ω) * v ω ∂μ) =
      ∑ x : X, w x * (∫ ω in {ω | T ω = x}, v ω ∂μ) := by
  have hcell (x : X) : MeasurableSet {ω | T ω = x} :=
    hT (measurableSet_singleton x)
  calc
    _ = ∫ ω, ∑ x : X, ({ω | T ω = x}.indicator (fun ω => w x * v ω)) ω ∂μ := by
      congr 1
      funext ω
      simp [Set.indicator, Finset.sum_ite_eq']
    _ = ∑ x : X, ∫ ω, ({ω | T ω = x}.indicator (fun ω => w x * v ω)) ω ∂μ :=
      integral_finsetSum _ (fun x _ => (hv.const_mul (w x)).indicator (hcell x))
    _ = _ := by
      apply Finset.sum_congr rfl
      intro x _
      rw [integral_indicator (hcell x), integral_const_mul]

theorem independent_event_integral {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {v : Ω → ℝ} {Z : Ω → Bool}
    (hv : Integrable v μ) (hZ : Measurable Z) (hi : IndepFun Z v μ) (z : Bool) :
    (∫ ω in {ω | Z ω = z}, v ω ∂μ) =
      (∫ ω, v ω ∂μ) * eventProbability μ {ω | Z ω = z} := by
  let g : Bool → ℝ := fun b => if b = z then 1 else 0
  have hg : Measurable g := measurable_of_finite g
  have hi' : IndepFun v (fun ω => g (Z ω)) μ :=
    hi.symm.comp measurable_id hg
  have h := hi'.integral_fun_mul_eq_mul_integral
    hv.aestronglyMeasurable (hg.comp hZ).aestronglyMeasurable
  have hA : MeasurableSet {ω | Z ω = z} := hZ (measurableSet_singleton z)
  have hprod : (fun ω => v ω * g (Z ω)) = {ω | Z ω = z}.indicator v := by
    funext ω
    simp [g, Set.indicator]
  have hone : (fun ω => g (Z ω)) =
      {ω | Z ω = z}.indicator (fun _ => (1 : ℝ)) := by
    funext ω
    simp [g, Set.indicator]
  calc
    _ = ∫ ω, v ω * g (Z ω) ∂μ := by
      rw [hprod, integral_indicator hA]
    _ = (∫ ω, v ω ∂μ) * ∫ ω, g (Z ω) ∂μ := h
    _ = _ := by
      rw [hone, integral_indicator hA, setIntegral_const]
      simp [eventProbability, measureReal_def]

theorem received_measurable {Ω X : Type*} [MeasurableSpace Ω]
    [MeasurableSpace X] {U : Ω → PotentialResponse X} {Z : Ω → Bool}
    (hd0 : Measurable (fun ω => (U ω).d0)) (hd1 : Measurable (fun ω => (U ω).d1))
    (hZ : Measurable Z) : Measurable (fun ω => (U ω).receivedTreatment (Z ω)) := by
  change Measurable (fun ω => if Z ω ∈ ({true} : Set Bool)
    then (U ω).d1 else (U ω).d0)
  exact Measurable.ite (hZ (measurableSet_singleton true)) hd1 hd0

theorem observed_integrable {Ω X : Type*} [MeasurableSpace Ω]
    [MeasurableSpace X] {μ : Measure Ω} {U : Ω → PotentialResponse X} {Z : Ω → Bool}
    (hy0 : Integrable (fun ω => (U ω).y0) μ)
    (hy1 : Integrable (fun ω => (U ω).y1) μ)
    (hd0 : Measurable (fun ω => (U ω).d0)) (hd1 : Measurable (fun ω => (U ω).d1))
    (hZ : Measurable Z) : Integrable (fun ω => (U ω).observedOutcome (Z ω)) μ := by
  have hr := received_measurable hd0 hd1 hZ
  have hA : MeasurableSet {ω | (U ω).receivedTreatment (Z ω) = true} :=
    hr (measurableSet_singleton true)
  have hid : (fun ω => (U ω).observedOutcome (Z ω)) =
      (fun ω => ({ω | (U ω).receivedTreatment (Z ω) = true}.indicator
        (fun ω => (U ω).y1)) ω +
        ({ω | (U ω).receivedTreatment (Z ω) = true}ᶜ.indicator
          (fun ω => (U ω).y0)) ω) := by
    funext ω
    cases h : (U ω).receivedTreatment (Z ω) <;>
      simp [PotentialResponse.observedOutcome, h, Set.indicator]
  rw [hid]
  exact (hy1.indicator hA).add (hy0.indicator hA.compl)

theorem receipt_indicator_integrable {Ω X : Type*} [MeasurableSpace Ω]
    [MeasurableSpace X] {μ : Measure Ω} {U : Ω → PotentialResponse X}
    (hd0 : Measurable (fun ω => (U ω).d0)) (hd1 : Measurable (fun ω => (U ω).d1))
    (z : Bool) [IsFiniteMeasure μ] :
    Integrable (fun ω => indicatorValue ((U ω).receivedTreatment z)) μ := by
  have hd : Measurable (fun ω => (U ω).receivedTreatment z) := by
    cases z
    · simpa [PotentialResponse.receivedTreatment] using hd0
    · simpa [PotentialResponse.receivedTreatment] using hd1
  have hA : MeasurableSet {ω | (U ω).receivedTreatment z = true} :=
    hd (measurableSet_singleton true)
  convert (integrable_const (μ := μ) (1 : ℝ)).indicator hA using 1
  funext ω
  cases hh : (U ω).receivedTreatment z <;>
    simp [indicatorValue, Set.indicator, hh]

theorem whole_observation_integrable {Ω X : Type*} [MeasurableSpace Ω]
    [MeasurableSpace X] {μ : Measure Ω} {U : Ω → PotentialResponse X} {Z : Ω → Bool}
    [IsFiniteMeasure μ]
    (hy0 : Integrable (fun ω => (U ω).y0) μ)
    (hy1 : Integrable (fun ω => (U ω).y1) μ)
    (hd0 : Measurable (fun ω => (U ω).d0)) (hd1 : Measurable (fun ω => (U ω).d1))
    (hZ : Measurable Z) (k : Fin 3) :
    Integrable (fun ω => wholeObservation (U ω) (Z ω) k) μ := by
  fin_cases k
  · simp [wholeObservation]
  · simp [wholeObservation]
    exact observed_integrable hy0 hy1 hd0 hd1 hZ
  · simp [wholeObservation]
    have hr := received_measurable hd0 hd1 hZ
    have hA : MeasurableSet {ω | (U ω).receivedTreatment (Z ω) = true} :=
      hr (measurableSet_singleton true)
    convert (integrable_const (μ := μ) (1 : ℝ)).indicator hA using 1
    funext ω
    cases hh : (U ω).receivedTreatment (Z ω) <;>
      simp [indicatorValue, Set.indicator, hh]

theorem whole_cell_arm_integral {Ω X : Type*} [MeasurableSpace Ω]
    [Fintype X] [MeasurableSpace X] [MeasurableSingletonClass X]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {U : Ω → PotentialResponse X}
    {Z : Ω → Bool} (hX : Measurable (fun ω => (U ω).x)) (hZ : Measurable Z)
    (hy0 : Integrable (fun ω => (U ω).y0) μ)
    (hy1 : Integrable (fun ω => (U ω).y1) μ)
    (hd0 : Measurable (fun ω => (U ω).d0)) (hd1 : Measurable (fun ω => (U ω).d1))
    (w : X → ℝ) (z : Bool) (k : Fin 3) :
    wholeCellArm (wholePopulationCells μ U Z) w z k =
      ∫ ω in {ω | Z ω = z}, w (U ω).x * wholeObservation (U ω) (Z ω) k ∂μ := by
  let v : Ω → ℝ := fun ω => wholeObservation (U ω) (Z ω) k
  have hv : Integrable v μ := whole_observation_integrable hy0 hy1 hd0 hd1 hZ k
  have hcell (x : X) : MeasurableSet {ω | (U ω).x = x ∧ Z ω = z} :=
    (hX (measurableSet_singleton x)).inter (hZ (measurableSet_singleton z))
  have hA : MeasurableSet {ω | Z ω = z} := hZ (measurableSet_singleton z)
  have hpoint : (fun ω => {ω | Z ω = z}.indicator
        (fun ω => w (U ω).x * v ω) ω) =
      fun ω => ∑ x : X,
        ({ω | (U ω).x = x ∧ Z ω = z}.indicator (fun ω => w x * v ω)) ω := by
    funext ω
    by_cases hz : Z ω = z
    · simp [Set.indicator, hz, v, Finset.sum_ite_eq', eq_comm]
    · simp [Set.indicator, hz]
  calc
    _ = ∑ x : X, w x *
        (∫ ω in {ω | (U ω).x = x ∧ Z ω = z}, v ω ∂μ) := by
      rfl
    _ = ∑ x : X, ∫ ω,
        ({ω | (U ω).x = x ∧ Z ω = z}.indicator (fun ω => w x * v ω)) ω ∂μ := by
      apply Finset.sum_congr rfl
      intro x _
      rw [integral_indicator (hcell x), integral_const_mul]
    _ = ∫ ω, ∑ x : X,
        ({ω | (U ω).x = x ∧ Z ω = z}.indicator (fun ω => w x * v ω)) ω ∂μ := by
      symm
      exact integral_finsetSum _ (fun x _ =>
        (hv.const_mul (w x)).indicator (hcell x))
    _ = ∫ ω in {ω | Z ω = z}, w (U ω).x * v ω ∂μ := by
      rw [← integral_indicator hA]
      congr 1
      exact hpoint.symm

theorem weighted_arm_mean_eq_integral_ratio {Ω : Type*}
    [MeasurableSpace Ω] {μ : Measure Ω} {Z : Ω → Bool}
    (w v : Ω → ℝ) (z : Bool)
    (hp : eventProbability μ {ω | Z ω = z} ≠ 0)
    (hw : (∫ ω in {ω | Z ω = z}, w ω ∂μ) ≠ 0) :
    weightedArmMean μ Z w v z =
      (∫ ω in {ω | Z ω = z}, w ω * v ω ∂μ) /
        (∫ ω in {ω | Z ω = z}, w ω ∂μ) := by
  unfold weightedArmMean eventMean
  field_simp [hp, hw] <;> ring

theorem arm_probability_false_pos {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {Z : Ω → Bool}
    (hZ : Measurable Z) (hpos : 0 < eventProbability μ {ω | Z ω = true})
    (hlt : eventProbability μ {ω | Z ω = true} < 1) :
    0 < eventProbability μ {ω | Z ω = false} := by
  have hsum := measureReal_add_measureReal_compl (μ := μ)
    (hZ (measurableSet_singleton true))
  have hcomp : {ω | Z ω = false} = {ω | Z ω = true}ᶜ := by
    ext ω
    cases Z ω <;> simp
  rw [hcomp]
  change 0 < μ.real {ω | Z ω = true}ᶜ
  change 0 < μ.real {ω | Z ω = true} at hpos
  change μ.real {ω | Z ω = true} < 1 at hlt
  rw [probReal_univ] at hsum
  change μ.real {ω | Z ω = true} + μ.real {ω | Z ω = true}ᶜ = 1 at hsum
  linarith

theorem profile_probability_sum {Ω X : Type*} [MeasurableSpace Ω]
    [Fintype X] [MeasurableSpace X] [MeasurableSingletonClass X]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {T : Ω → X}
    (hT : Measurable T) :
    (∑ x : X, eventProbability μ {ω | T ω = x}) = 1 := by
  have h := profile_integral hT (integrable_const (μ := μ) (1 : ℝ)) (fun _ => 1)
  have h' : (∫ ω, (1 : ℝ) ∂μ) =
      ∑ x : X, eventProbability μ {ω | T ω = x} := by
    simpa [eventProbability, setIntegral_const, measureReal_def] using h
  simpa using h'.symm

theorem positive_profile_exists {X : Type*} [Fintype X]
    (f : X → ℝ) (hsum : (∑ x, f x) = 1) (hf : ∀ x, 0 < f x) :
    ∃ x, 0 < f x := by
  classical
  by_contra h
  have hzero : ∀ x, f x = 0 := by
    intro x
    have hn : ¬ 0 < f x := fun hp => h ⟨x, hp⟩
    exact le_antisymm (le_of_not_gt hn) (le_of_lt (hf x))
  have hz : (∑ x, f x) = 0 := by simp [hzero]
  rw [hz] at hsum
  norm_num at hsum

theorem positive_profile_mean {Ω X : Type*} [MeasurableSpace Ω]
    [Fintype X] [MeasurableSpace X] [MeasurableSingletonClass X]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {T : Ω → X}
    (hT : Measurable T) (w : X → ℝ)
    (hm : ∀ x, 0 < eventProbability μ {ω | T ω = x})
    (hw : ∀ x, 0 < w x) :
    0 < ∫ ω, w (T ω) ∂μ := by
  let f : X → ℝ := fun x => eventProbability μ {ω | T ω = x}
  have hsum : (∑ x, f x) = 1 := profile_probability_sum hT
  have hfp : ∀ x, 0 < f x := by intro x; exact hm x
  obtain ⟨x0, hx0⟩ := positive_profile_exists f hsum hfp
  have hformula : (∫ ω, w (T ω) ∂μ) = ∑ x, f x * w x := by
    have h := profile_integral hT (integrable_const (μ := μ) (1 : ℝ)) w
    simpa [f, eventProbability, setIntegral_const, measureReal_def, mul_comm] using h
  rw [hformula]
  apply Finset.sum_pos'
  · intro x _
    exact (mul_pos (hfp x) (hw x)).le
  · exact ⟨x0, Finset.mem_univ x0, mul_pos hx0 (hw x0)⟩

theorem positive_weighted_complier_mass {Ω X : Type*}
    [MeasurableSpace Ω] [Fintype X] [MeasurableSpace X]
    [MeasurableSingletonClass X] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {U : Ω → PotentialResponse X} (hX : Measurable (fun ω => (U ω).x))
    (hd0 : Measurable (fun ω => (U ω).d0)) (hd1 : Measurable (fun ω => (U ω).d1))
    (w : X → ℝ) (hw : ∀ x, 0 < w x)
    (hs : ∀ x, 0 < complianceProbability μ U x)
    (hm : ∀ x, 0 < eventProbability μ {ω | (U ω).x = x}) :
    0 < ∫ ω, w (U ω).x * (if (U ω).isComplier then (1 : ℝ) else 0) ∂μ := by
  let f : X → ℝ := fun x => eventProbability μ {ω | (U ω).x = x}
  have hsum : (∑ x, f x) = 1 := profile_probability_sum hX
  have hfp : ∀ x, 0 < f x := by intro x; exact hm x
  obtain ⟨x0, hx0⟩ := positive_profile_exists f hsum hfp
  have hcomp (x : X) :
      f x * complianceProbability μ U x =
        eventProbability μ {ω | (U ω).isComplier ∧ (U ω).x = x} := by
    unfold f complianceProbability
    have hden := ne_of_gt (hm x)
    field_simp [hden]
  have hcell (x : X) :
      (∫ ω in {ω | (U ω).x = x}, (if (U ω).isComplier then (1 : ℝ) else 0) ∂μ) =
        eventProbability μ {ω | (U ω).isComplier ∧ (U ω).x = x} := by
    have hC : MeasurableSet {ω | (U ω).isComplier} :=
      (hd0 (measurableSet_singleton false)).inter (hd1 (measurableSet_singleton true))
    have hprofile : MeasurableSet {ω | (U ω).x = x} := hX (measurableSet_singleton x)
    calc
      _ = ∫ ω, ({ω | (U ω).x = x}.indicator
          (fun ω => if (U ω).isComplier then (1 : ℝ) else 0)) ω ∂μ := by
        rw [integral_indicator hprofile]
      _ = ∫ ω, ({ω | (U ω).isComplier ∧ (U ω).x = x}.indicator
          (fun _ => (1 : ℝ))) ω ∂μ := by
        congr 1
        funext ω
        by_cases hp : (U ω).x = x
        · by_cases hc : (U ω).isComplier <;>
            simp [Set.indicator, hp, hc]
        · simp [Set.indicator, hp]
      _ = eventProbability μ {ω | (U ω).isComplier ∧ (U ω).x = x} := by
        have hset : {ω | (U ω).isComplier ∧ (U ω).x = x} =
            {ω | (U ω).isComplier} ∩ {ω | (U ω).x = x} := rfl
        rw [hset]
        change (∫ ω, ({ω | (U ω).isComplier} ∩ {ω | (U ω).x = x}).indicator
          1 ω ∂μ) = eventProbability μ
            ({ω | (U ω).isComplier} ∩ {ω | (U ω).x = x})
        simpa [eventProbability, measureReal_def] using
          (integral_indicator_one (s :=
            {ω | (U ω).isComplier} ∩ {ω | (U ω).x = x}) (hC.inter hprofile))
  have hformula :
      (∫ ω, w (U ω).x * (if (U ω).isComplier then (1 : ℝ) else 0) ∂μ) =
        ∑ x, f x * w x * complianceProbability μ U x := by
    have hC : MeasurableSet {ω | (U ω).isComplier} :=
      (hd0 (measurableSet_singleton false)).inter (hd1 (measurableSet_singleton true))
    have hCi : Integrable (fun ω => if (U ω).isComplier then (1 : ℝ) else 0) μ := by
      convert (integrable_const (μ := μ) (1 : ℝ)).indicator hC using 1
      funext ω
      simp [Set.indicator, PotentialResponse.isComplier]
    calc
      _ = ∑ x, w x * eventProbability μ
          {ω | (U ω).isComplier ∧ (U ω).x = x} := by
        rw [profile_integral hX hCi w]
        apply Finset.sum_congr rfl
        intro x _
        rw [hcell x]
      _ = ∑ x, f x * w x * complianceProbability μ U x := by
        apply Finset.sum_congr rfl
        intro x _
        rw [← hcomp x]
        ring
  rw [hformula]
  apply Finset.sum_pos'
  · intro x _
    exact (mul_pos (mul_pos (hfp x) (hw x)) (hs x)).le
  · exact ⟨x0, Finset.mem_univ x0, mul_pos (mul_pos hx0 (hw x0)) (hs x0)⟩

end

end SAP.P029a.WH.W1.P.T4_L2

namespace SAP.P029a.WH.W1

open SAP.P029a.WH.W1.P.T4_L2
open SAP.P029a MeasureTheory ProbabilityTheory Set
open scoped BigOperators Classical

noncomputable section

theorem T4_L2_proof : _root_.SAP.P029a.WH.W1.T4_L2 := by
  intro Ω X _ _ _ _ μ _ U Z hmodel hiv w hw
  rcases hiv with ⟨hX, hd0, hd1, hy0, hy1, hZ, iy0, iy1, hind,
    hassign, hassignlt, hrel⟩
  have hfalse : 0 < eventProbability μ {ω | Z ω = false} :=
    arm_probability_false_pos hZ hassign hassignlt
  have hWmeas : Measurable w := measurable_of_finite w
  let W : Ω → ℝ := fun ω => w (U ω).x
  have hWi : Integrable W μ := by
    simpa [W] using
      (profile_mul_integrable hX (integrable_const (μ := μ) (1 : ℝ)) w)
  have hWpos : 0 < ∫ ω, W ω ∂μ := by
    exact positive_profile_mean hX w hmodel.profile_mass hw
  have hWne : (∫ ω, W ω ∂μ) ≠ 0 := ne_of_gt hWpos
  have hWind : IndepFun Z W μ := by
    exact hind.comp measurable_id (hWmeas.comp measurable_fst)
  have hpz (z : Bool) : 0 < eventProbability μ {ω | Z ω = z} := by
    cases z
    · exact hfalse
    · exact hassign
  have hpzne (z : Bool) : eventProbability μ {ω | Z ω = z} ≠ 0 :=
    ne_of_gt (hpz z)
  have hWarm (z : Bool) :
      (∫ ω in {ω | Z ω = z}, W ω ∂μ) =
        (∫ ω, W ω ∂μ) * eventProbability μ {ω | Z ω = z} :=
    independent_event_integral hWi hZ hWind z
  have hWarm_pos (z : Bool) : 0 < ∫ ω in {ω | Z ω = z}, W ω ∂μ := by
    rw [hWarm z]
    exact mul_pos hWpos (hpz z)
  have hcell0 (z : Bool) :
      wholeCellArm (wholePopulationCells μ U Z) w z 0 =
        ∫ ω in {ω | Z ω = z}, W ω ∂μ := by
    simpa [W, wholeObservation] using
      (whole_cell_arm_integral hX hZ iy0 iy1 hd0 hd1 w z (0 : Fin 3))
  have hcellY (z : Bool) :
      wholeCellArm (wholePopulationCells μ U Z) w z 1 =
        ∫ ω in {ω | Z ω = z}, W ω * (U ω).observedOutcome (Z ω) ∂μ := by
    simpa [W, wholeObservation] using
      (whole_cell_arm_integral hX hZ iy0 iy1 hd0 hd1 w z (1 : Fin 3))
  have hcellD (z : Bool) :
      wholeCellArm (wholePopulationCells μ U Z) w z 2 =
        ∫ ω in {ω | Z ω = z}, W ω *
          indicatorValue ((U ω).receivedTreatment (Z ω)) ∂μ := by
    simpa [W, wholeObservation] using
      (whole_cell_arm_integral hX hZ iy0 iy1 hd0 hd1 w z (2 : Fin 3))
  have hcell0pos (z : Bool) :
      0 < wholeCellArm (wholePopulationCells μ U Z) w z 0 := by
    rw [hcell0 z]
    exact hWarm_pos z
  have hcell0ne (z : Bool) :
      wholeCellArm (wholePopulationCells μ U Z) w z 0 ≠ 0 :=
    ne_of_gt (hcell0pos z)
  have hmeanY (z : Bool) :
      weightedArmMean μ Z W (fun ω => (U ω).observedOutcome (Z ω)) z =
        wholeCellArm (wholePopulationCells μ U Z) w z 1 /
          wholeCellArm (wholePopulationCells μ U Z) w z 0 := by
    rw [weighted_arm_mean_eq_integral_ratio W
      (fun ω => (U ω).observedOutcome (Z ω)) z (hpzne z)
      (ne_of_gt (hWarm_pos z))]
    rw [← hcellY z, ← hcell0 z]
  have hmeanD (z : Bool) :
      weightedArmMean μ Z W
        (fun ω => indicatorValue ((U ω).receivedTreatment (Z ω))) z =
        wholeCellArm (wholePopulationCells μ U Z) w z 2 /
          wholeCellArm (wholePopulationCells μ U Z) w z 0 := by
    rw [weighted_arm_mean_eq_integral_ratio W
      (fun ω => indicatorValue ((U ω).receivedTreatment (Z ω))) z
      (hpzne z) (ne_of_gt (hWarm_pos z))]
    rw [← hcellD z, ← hcell0 z]
  have hcell_eq_population :
      wholeCellWald (wholePopulationCells μ U Z) w = populationWald μ U Z W := by
    simp only [wholeCellWald, populationWald]
    rw [hmeanY true, hmeanY false, hmeanD true, hmeanD false]
  have hDfixI (z : Bool) :
      Integrable (fun ω => W ω * indicatorValue ((U ω).receivedTreatment z)) μ := by
    exact profile_mul_integrable hX
      (receipt_indicator_integrable hd0 hd1 z) w
  have hDfixInd (z : Bool) :
      IndepFun Z (fun ω => W ω * indicatorValue ((U ω).receivedTreatment z)) μ := by
    let g : X × Bool × Bool × ℝ × ℝ → ℝ := fun t =>
      w t.1 * indicatorValue (if z then t.2.2.1 else t.2.1)
    have hg : Measurable g := by
      dsimp [g]
      have hW : Measurable (fun t : X × Bool × Bool × ℝ × ℝ => w t.1) :=
        hWmeas.comp measurable_fst
      have hR : Measurable (fun t : X × Bool × Bool × ℝ × ℝ =>
          indicatorValue (if z then t.2.2.1 else t.2.1)) := by
        cases z <;> fun_prop
      exact hW.mul hR
    have h := hind.comp measurable_id hg
    simpa [Function.comp_def, W, g, PotentialResponse.receivedTreatment] using h
  have hDarm (z : Bool) :
      (∫ ω in {ω | Z ω = z},
        W ω * indicatorValue ((U ω).receivedTreatment (Z ω)) ∂μ) =
        (∫ ω, W ω * indicatorValue ((U ω).receivedTreatment z) ∂μ) *
          eventProbability μ {ω | Z ω = z} := by
    calc
      _ = ∫ ω in {ω | Z ω = z},
          W ω * indicatorValue ((U ω).receivedTreatment z) ∂μ := by
        apply setIntegral_congr_fun (hZ (measurableSet_singleton z))
        intro ω hω
        have hz : Z ω = z := by simpa using hω
        exact congrArg (fun b : Bool =>
          W ω * indicatorValue ((U ω).receivedTreatment b)) hz
      _ = _ := independent_event_integral (hDfixI z) hZ (hDfixInd z) z
  have hCellDRatio (z : Bool) :
      wholeCellArm (wholePopulationCells μ U Z) w z 2 /
        wholeCellArm (wholePopulationCells μ U Z) w z 0 =
      (∫ ω, W ω * indicatorValue ((U ω).receivedTreatment z) ∂μ) /
        (∫ ω, W ω ∂μ) := by
    rw [hcellD z, hcell0 z, hDarm z, hWarm z]
    field_simp [hpzne z, hWne] <;> ring
  have hCpos :
      0 < ∫ ω, W ω * (if (U ω).isComplier then (1 : ℝ) else 0) ∂μ :=
    positive_weighted_complier_mass hX hd0 hd1 w hw hmodel.score_pos
      hmodel.profile_mass
  have hnd : ∀ᵐ ω ∂μ, ¬ (U ω).isDefier := by
    simpa only [ae_iff, not_not] using hmodel.no_defiers
  have hDdiff :
      (∫ ω, W ω * indicatorValue ((U ω).receivedTreatment true) ∂μ) -
        (∫ ω, W ω * indicatorValue ((U ω).receivedTreatment false) ∂μ) =
      ∫ ω, W ω * (if (U ω).isComplier then (1 : ℝ) else 0) ∂μ := by
    have i1 : Integrable (fun ω => W ω *
        indicatorValue ((U ω).receivedTreatment true)) μ := hDfixI true
    have i0 : Integrable (fun ω => W ω *
        indicatorValue ((U ω).receivedTreatment false)) μ := hDfixI false
    have iCbase : Integrable (fun ω =>
        if (U ω).isComplier then (1 : ℝ) else 0) μ := by
      have hC : MeasurableSet {ω | (U ω).isComplier} :=
        (hd0 (measurableSet_singleton false)).inter
          (hd1 (measurableSet_singleton true))
      convert (integrable_const (μ := μ) (1 : ℝ)).indicator hC using 1
      funext ω
      simp [Set.indicator, PotentialResponse.isComplier]
    have iC : Integrable (fun ω => W ω *
        (if (U ω).isComplier then (1 : ℝ) else 0)) μ := by
      exact profile_mul_integrable hX iCbase w
    rw [← integral_sub i1 i0]
    apply integral_congr_ae
    filter_upwards [hnd] with ω hn
    cases h0 : (U ω).d0 <;> cases h1 : (U ω).d1
    · simp [PotentialResponse.receivedTreatment, PotentialResponse.isComplier,
        indicatorValue, h0, h1]
    · simp [PotentialResponse.receivedTreatment, PotentialResponse.isComplier,
        indicatorValue, h0, h1]
    · have hc : (U ω).isDefier := by
        simp [PotentialResponse.isDefier, h0, h1]
      exact (hn hc).elim
    · simp [PotentialResponse.receivedTreatment, PotentialResponse.isComplier,
        indicatorValue, h0, h1]
  have hthird :
      wholeCellArm (wholePopulationCells μ U Z) w true 2 /
        wholeCellArm (wholePopulationCells μ U Z) w true 0 -
      (wholeCellArm (wholePopulationCells μ U Z) w false 2 /
        wholeCellArm (wholePopulationCells μ U Z) w false 0) =
      (∫ ω, W ω * (if (U ω).isComplier then (1 : ℝ) else 0) ∂μ) /
        (∫ ω, W ω ∂μ) := by
    rw [hCellDRatio true, hCellDRatio false, ← sub_div, hDdiff]
  have hdomain : WholeWaldDomain (wholePopulationCells μ U Z) w := by
    refine ⟨hcell0ne true, hcell0ne false, ?_⟩
    rw [hthird]
    exact ne_of_gt (div_pos hCpos hWpos)
  exact ⟨hdomain, hcell_eq_population⟩

end

end SAP.P029a.WH.W1
