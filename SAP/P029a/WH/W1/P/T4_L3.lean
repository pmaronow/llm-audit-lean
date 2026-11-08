import SAP.P029a.WH.W1.Leaves
import Mathlib.Probability.StrongLaw
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P029a.WH.W1.P.T4_L3

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Classical Topology Function

noncomputable section

/-- Decode a joint potential-response and assignment tuple into one cell moment. -/
def jointCellValue {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]
    (c : WholeCellIndex X) : (X × Bool × Bool × ℝ × ℝ × Bool) → ℝ := fun t =>
  if t.1 = c.1 ∧ t.2.2.2.2.2 = c.2.1 then
    wholeObservation
      ⟨t.1, t.2.1, t.2.2.1, t.2.2.2.1, t.2.2.2.2.1⟩
      t.2.2.2.2.2 c.2.2
  else 0

lemma measurable_jointCellValue {X : Type*} [MeasurableSpace X]
    [MeasurableSingletonClass X] (c : WholeCellIndex X) :
    Measurable (jointCellValue c) := by
  unfold jointCellValue
  have hx : Measurable (fun t : X × Bool × Bool × ℝ × ℝ × Bool => t.1) := measurable_fst
  have hz : Measurable (fun t : X × Bool × Bool × ℝ × ℝ × Bool => t.2.2.2.2.2) := by
    fun_prop
  have hset : MeasurableSet {t : X × Bool × Bool × ℝ × ℝ × Bool |
      t.1 = c.1 ∧ t.2.2.2.2.2 = c.2.1} :=
    MeasurableSet.inter
      (MeasurableSet.preimage (measurableSet_singleton c.1) hx)
      (MeasurableSet.preimage (measurableSet_singleton c.2.1) hz)
  let d0 : X × Bool × Bool × ℝ × ℝ × Bool → Bool := fun t => t.2.1
  let d1 : X × Bool × Bool × ℝ × ℝ × Bool → Bool := fun t => t.2.2.1
  let y0 : X × Bool × Bool × ℝ × ℝ × Bool → ℝ := fun t => t.2.2.2.1
  let y1 : X × Bool × Bool × ℝ × ℝ × Bool → ℝ := fun t => t.2.2.2.2.1
  let z : X × Bool × Bool × ℝ × ℝ × Bool → Bool := fun t => t.2.2.2.2.2
  have hd0 : Measurable d0 := by fun_prop
  have hd1 : Measurable d1 := by fun_prop
  have hy0 : Measurable y0 := by fun_prop
  have hy1 : Measurable y1 := by fun_prop
  have hz' : Measurable z := by fun_prop
  have hr : Measurable (fun t => if z t then d1 t else d0 t) :=
    Measurable.ite (hz' (measurableSet_singleton true)) hd1 hd0
  have hout : Measurable (fun t => if (if z t then d1 t else d0 t) then y1 t else y0 t) :=
    Measurable.ite (hr (measurableSet_singleton true)) hy1 hy0
  have hD : Measurable (fun t => if (if z t then d1 t else d0 t) then (1 : ℝ) else 0) :=
    Measurable.ite (hr (measurableSet_singleton true)) measurable_const measurable_const
  have hk0 : MeasurableSet {t : X × Bool × Bool × ℝ × ℝ × Bool | c.2.2 = 0} := by
    by_cases h : c.2.2 = 0 <;> simp [h]
  have hk1 : MeasurableSet {t : X × Bool × Bool × ℝ × ℝ × Bool | c.2.2 = 1} := by
    by_cases h : c.2.2 = 1 <;> simp [h]
  have hobs : Measurable (fun t : X × Bool × Bool × ℝ × ℝ × Bool =>
      wholeObservation ⟨t.1, d0 t, d1 t, y0 t, y1 t⟩ (z t) c.2.2) := by
    unfold wholeObservation
    exact Measurable.ite hk0 measurable_const (Measurable.ite hk1 hout hD)
  convert Measurable.ite hset hobs measurable_const using 1

lemma measurable_finite_sum {α ι : Type*} [MeasurableSpace α] [Fintype ι]
    (f : ι → α → ℝ) (hf : ∀ i, Measurable (f i)) :
    Measurable (fun x => ∑ i, f i x) := by
  classical
  have hs : ∀ s : Finset ι, Measurable (fun x => ∑ i ∈ s, f i x) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih =>
      simp only [Finset.sum_insert ha]
      exact (hf a).add ih
  simpa using hs Finset.univ

end
end SAP.P029a.WH.W1.P.T4_L3

open SAP.P029a.WH.W1.P.T4_L3
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Classical Topology Function

/-- The three raw empirical cell moments converge under iid sampling with finite first moments. -/
theorem SAP.P029a.WH.W1.T4_L3_proof : SAP.P029a.WH.W1.T4_L3 := by
  classical
  intro Ω X _ _ _ _ μ hμ U Z hmodel hiid c
  let g : (X × Bool × Bool × ℝ × ℝ × Bool) → ℝ := jointCellValue c
  have hg : Measurable g := measurable_jointCellValue c
  have hset : MeasurableSet {ω : Ω | (U 0 ω).x = c.1 ∧ Z 0 ω = c.2.1} := by
    refine MeasurableSet.inter ?_ ?_
    · exact hmodel.covariate_measurable (measurableSet_singleton c.1)
    · exact hmodel.assignment_measurable (measurableSet_singleton c.2.1)
  have hobs : Integrable
      (fun ω => wholeObservation (U 0 ω) (Z 0 ω) c.2.2) μ := by
    have hR : Measurable (fun ω => (U 0 ω).receivedTreatment (Z 0 ω)) := by
      unfold PotentialResponse.receivedTreatment
      exact Measurable.ite
        (hmodel.assignment_measurable (measurableSet_singleton true))
        hmodel.d1_measurable hmodel.d0_measurable
    have hY : Measurable (fun ω => (U 0 ω).observedOutcome (Z 0 ω)) := by
      unfold PotentialResponse.observedOutcome
      exact Measurable.ite (hR (measurableSet_singleton true))
        hmodel.y1_measurable hmodel.y0_measurable
    have hD : Measurable (fun ω => indicatorValue ((U 0 ω).receivedTreatment (Z 0 ω))) := by
      unfold indicatorValue
      exact Measurable.ite (hR (measurableSet_singleton true)) measurable_const measurable_const
    have hwhole : Measurable (fun ω => wholeObservation (U 0 ω) (Z 0 ω) c.2.2) := by
      unfold wholeObservation
      have hk0 : MeasurableSet {ω : Ω | c.2.2 = 0} := by
        by_cases h : c.2.2 = 0 <;> simp [h]
      have hk1 : MeasurableSet {ω : Ω | c.2.2 = 1} := by
        by_cases h : c.2.2 = 1 <;> simp [h]
      exact Measurable.ite hk0 measurable_const (Measurable.ite hk1 hY hD)
    refine (integrable_const (1 : ℝ)).add
        (hmodel.y0_integrable.norm.add hmodel.y1_integrable.norm) |>.mono'
          hwhole.aestronglyMeasurable ?_
    filter_upwards [] with ω
    simp only [Real.norm_eq_abs, wholeObservation, PotentialResponse.observedOutcome,
      PotentialResponse.receivedTreatment, indicatorValue]
    split_ifs <;> norm_num <;>
      linarith [abs_nonneg ((U 0 ω).y0), abs_nonneg ((U 0 ω).y1)]
  have hbase : Integrable (fun ω => g (wholeJoint (U 0) (Z 0) ω)) μ := by
    convert hobs.indicator hset using 1 <;>
      funext ω <;>
      simp [g, jointCellValue, wholeJoint, wholeObservation, Set.indicator]
  have hind : Pairwise
      ((· ⟂ᵢ[μ] ·) on fun i ω => g (wholeJoint (U i) (Z i) ω)) := by
    intro i j hij
    exact (hiid.independent.indepFun hij).comp hg hg
  have hident : ∀ i, IdentDistrib
      (fun ω => g (wholeJoint (U i) (Z i) ω))
      (fun ω => g (wholeJoint (U 0) (Z 0) ω)) μ μ := by
    intro i
    exact (hiid.identical i).comp hg
  have hstrong := ProbabilityTheory.strong_law_ae_real
    (fun i ω => g (wholeJoint (U i) (Z i) ω)) hbase hind hident
  have hpop : (∫ ω, g (wholeJoint (U 0) (Z 0) ω) ∂μ) =
      wholePopulationCells μ (U 0) (Z 0) c := by
    calc
      (∫ ω, g (wholeJoint (U 0) (Z 0) ω) ∂μ) =
          ∫ ω, Set.indicator {ω : Ω | (U 0 ω).x = c.1 ∧ Z 0 ω = c.2.1}
            (fun ω => wholeObservation (U 0 ω) (Z 0 ω) c.2.2) ω ∂μ := by
          congr 1
          funext ω
          simp [g, jointCellValue, wholeJoint, wholeObservation, Set.indicator]
      _ = wholePopulationCells μ (U 0) (Z 0) c := by
          rw [integral_indicator hset]
          rfl
  rw [hpop] at hstrong
  have hsucc : Tendsto (fun n : ℕ => n + 1) atTop atTop := by
    apply Filter.tendsto_atTop.2
    intro b
    filter_upwards [Filter.eventually_ge_atTop b] with n hn
    omega
  have hshift : ∀ᵐ ω ∂μ, Tendsto
      (fun n : ℕ =>
        (∑ i ∈ Finset.range (n + 1), g (wholeJoint (U i) (Z i) ω)) /
          ((n + 1 : ℕ) : ℝ))
      atTop (nhds (wholePopulationCells μ (U 0) (Z 0) c)) := by
    filter_upwards [hstrong] with ω hω
    exact hω.comp hsucc
  have hconv : ∀ᵐ ω ∂μ, Tendsto
      (fun n => wholeEmpiricalCells U Z n ω c) atTop
      (nhds (wholePopulationCells μ (U 0) (Z 0) c)) := by
    filter_upwards [hshift] with ω hω
    simpa only [wholeEmpiricalCells, g, jointCellValue, wholeJoint, wholeObservation,
      ← Fin.sum_univ_eq_sum_range] using hω
  have hmeas : ∀ n, Measurable (fun ω => wholeEmpiricalCells U Z n ω c) := by
    intro n
    unfold wholeEmpiricalCells
    apply Measurable.div_const
    apply SAP.P029a.WH.W1.P.T4_L3.measurable_finite_sum
    intro i
    exact hg.comp (hiid.measurable i.val)
  apply MeasureTheory.tendstoInMeasure_of_tendsto_ae
    (fun n => (hmeas n).aestronglyMeasurable) hconv
