import AronowAudit.P047.Wave1.ImpossibilityBlueprint
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Algebra.BigOperators.Ring.Finset

set_option autoImplicit false

universe u

namespace AronowAudit.P047.Wave1.Impossibility

open AronowAudit.P047 MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

noncomputable section

private theorem measurable_record_fixed (k : Fin 3) : Measurable (fun w => record w k) :=
  measurable_id.prodMk (measurable_const.prodMk measurable_const)

/-- Multiplying by the indicator of a measurable inverse image preserves integrability. -/
private theorem integrable_record_indicator {X Y : Type*} [MeasurableSpace X]
    [MeasurableSpace Y] {μ : Measure X} {f : X → ℝ} (hf : Integrable f μ)
    {r : X → Y} (hr : Measurable r) {B : Set Y} (hB : MeasurableSet B) :
    Integrable (fun x => f x * B.indicator (fun _ => (1 : ℝ)) (r x)) μ := by
  apply (hf.indicator (hr hB)).congr
  apply ae_of_all
  intro x
  by_cases hx : r x ∈ B <;> simp [Set.indicator, hx]

private theorem finite_density_of_integrable {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f : X → ℝ) (hf : Integrable f μ) (h0 : ∀ x, 0 ≤ f x) :
    IsFiniteMeasure (μ.withDensity (fun x => ENNReal.ofReal (f x))) := by
  apply isFiniteMeasure_withDensity
  rw [← ofReal_integral_eq_lintegral_ofReal hf (ae_of_all _ h0)]
  exact ENNReal.ofReal_ne_top

/-- A real-valued density evaluated on a measurable set, written as an indicator integral. -/
private theorem density_real_apply {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f : X → ℝ) (hfm : Measurable f) (h0 : ∀ x, 0 ≤ f x)
    (B : Set X) (hB : MeasurableSet B) :
    (μ.withDensity (fun x => ENNReal.ofReal (f x))).real B =
      ∫ x, f x * B.indicator (fun _ => (1 : ℝ)) x ∂μ := by
  rw [← integral_indicator_one hB,
    integral_withDensity_eq_integral_toReal_smul hfm.ennreal_ofReal
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top) _]
  have hreal (x : X) : (ENNReal.ofReal (f x)).toReal = f x :=
    ENNReal.toReal_ofReal (h0 x)
  simp only [hreal, smul_eq_mul]
  rfl

private theorem indicator_one_pi {ι X : Type*} [Fintype ι]
    (B : ι → Set X) (x : ι → X) :
    (Set.univ.pi B).indicator (fun _ => (1 : ℝ)) x =
      ∏ i, (B i).indicator (fun _ => (1 : ℝ)) (x i) := by
  classical
  by_cases hx : ∀ i, x i ∈ B i
  · have hx' : x ∈ Set.univ.pi B := by simpa using hx
    rw [Set.indicator_of_mem hx']
    symm
    exact Finset.prod_eq_one fun i _ => Set.indicator_of_mem (hx i) _
  · have hx' : x ∉ Set.univ.pi B := by simpa using hx
    obtain ⟨i, hi⟩ := not_forall.mp hx
    rw [Set.indicator_of_notMem hx']
    symm
    exact Finset.prod_eq_zero (Finset.mem_univ i) (Set.indicator_of_notMem hi _)

/-- Construct a finite sum of genuine measures indexed by the record vector, identify it
on measurable boxes with the product law, and then evaluate it on an arbitrary event.

The hypothesis does not explicitly assume integrable weights. Its `B = univ` case has
integral one, which proves integrability of the nonnegative sum and hence of each weight. -/
theorem n7_proof : N7 := by
  classical
  intro ν _ q hqm hq0 hformula n E hE
  have htotal : (∫ w, ∑ k, q w k ∂uniform01) = 1 := by
    simpa using (hformula Set.univ MeasurableSet.univ).symm
  have htotal_int : Integrable (fun w => ∑ k, q w k) uniform01 :=
    integrable_of_integral_eq_one htotal
  have hqint (k : Fin 3) : Integrable (fun w => q w k) uniform01 := by
    apply htotal_int.mono' (hqm k).aestronglyMeasurable
    apply ae_of_all
    intro w
    rw [Real.norm_eq_abs, abs_of_nonneg (hq0 w k)]
    exact Finset.single_le_sum (fun j _ => hq0 w j) (Finset.mem_univ k)
  have hone (B : Set ObservedUnit) (hB : MeasurableSet B) :
      (∑ k, ∫ w, q w k * B.indicator (fun _ => (1 : ℝ)) (record w k) ∂uniform01) =
        ν.real B := by
    rw [hformula B hB, integral_finsetSum Finset.univ
      (fun k _ => integrable_record_indicator (hqint k) (measurable_record_fixed k) hB)]
  let W : Measure (Fin n → ℝ) := Measure.pi (fun _ : Fin n => uniform01)
  let p : (Fin n → Fin 3) → (Fin n → ℝ) → ℝ := fun k w => ∏ i, q (w i) (k i)
  let r : (Fin n → Fin 3) → (Fin n → ℝ) → (Fin n → ObservedUnit) :=
    fun k w i => record (w i) (k i)
  have hpm (k : Fin n → Fin 3) : Measurable (p k) :=
    Finset.measurable_fun_prod Finset.univ fun i _ =>
      (hqm (k i)).comp (measurable_pi_apply i)
  have hp0 (k : Fin n → Fin 3) (w : Fin n → ℝ) : 0 ≤ p k w :=
    Finset.prod_nonneg fun i _ => hq0 (w i) (k i)
  have hpint (k : Fin n → Fin 3) : Integrable (p k) W :=
    Integrable.fintype_prod (fun i : Fin n => hqint (k i))
  have hrm (k : Fin n → Fin 3) : Measurable (r k) :=
    measurable_pi_lambda fun i => (measurable_record_fixed (k i)).comp (measurable_pi_apply i)
  let ρ : (Fin n → Fin 3) → Measure (Fin n → ObservedUnit) :=
    fun k => (W.withDensity (fun w => ENNReal.ofReal (p k w))).map (r k)
  have hfinite (k : Fin n → Fin 3) :
      IsFiniteMeasure (W.withDensity (fun w => ENNReal.ofReal (p k w))) :=
    finite_density_of_integrable W (p k) (hpint k) (hp0 k)
  letI : ∀ k, IsFiniteMeasure (ρ k) := fun k => by
    letI := hfinite k
    dsimp only [ρ]
    infer_instance
  let νsum : Measure (Fin n → ObservedUnit) := ∑ k, ρ k
  letI : IsFiniteMeasure νsum := by
    dsimp only [νsum]
    infer_instance
  have hρ (k : Fin n → Fin 3) (B : Set (Fin n → ObservedUnit)) (hB : MeasurableSet B) :
      (ρ k).real B =
        ∫ w, p k w * B.indicator (fun _ => (1 : ℝ)) (r k w) ∂W := by
    dsimp only [ρ]
    rw [map_measureReal_apply (hrm k) hB]
    exact density_real_apply W (p k) (hpm k) (hp0 k) _ ((hrm k) hB)
  have hsum_formula (B : Set (Fin n → ObservedUnit)) (hB : MeasurableSet B) :
      νsum.real B =
        ∫ w, ∑ k, p k w * B.indicator (fun _ => (1 : ℝ)) (r k w) ∂W := by
    have hsum : νsum.real B = ∑ k, (ρ k).real B := by
      change ((∑ k, ρ k) B).toReal = ∑ k, (ρ k B).toReal
      rw [Measure.finsetSum_apply, ENNReal.toReal_sum (fun k _ => measure_ne_top (ρ k) B)]
    rw [hsum]
    simp_rw [hρ _ B hB]
    exact (integral_finsetSum Finset.univ
      (fun k _ => integrable_record_indicator (hpint k) (hrm k) hB)).symm
  have hboxes (B : Fin n → Set ObservedUnit) (hB : ∀ i, MeasurableSet (B i)) :
      νsum.real (Set.univ.pi B) = ∏ i, ν.real (B i) := by
    have hbox : MeasurableSet (Set.univ.pi B) := MeasurableSet.univ_pi hB
    have hfactor (k : Fin n → Fin 3) :
        (∫ w, p k w * (Set.univ.pi B).indicator (fun _ => (1 : ℝ)) (r k w) ∂W) =
          ∏ i, ∫ w, q w (k i) * (B i).indicator (fun _ => (1 : ℝ)) (record w (k i))
            ∂uniform01 := by
      have hfun : (fun w => p k w *
          (Set.univ.pi B).indicator (fun _ => (1 : ℝ)) (r k w)) =
          (fun w : Fin n → ℝ => ∏ i,
            q (w i) (k i) * (B i).indicator (fun _ => (1 : ℝ)) (record (w i) (k i))) := by
        funext w
        rw [indicator_one_pi]
        exact (Finset.prod_mul_distrib :
          (∏ i, q (w i) (k i) * (B i).indicator (fun _ => (1 : ℝ)) (record (w i) (k i))) =
            (∏ i, q (w i) (k i)) *
              ∏ i, (B i).indicator (fun _ => (1 : ℝ)) (record (w i) (k i))).symm
      rw [hfun]
      exact integral_fintype_prod_eq_prod (μ := fun _ : Fin n => uniform01)
        (fun i (x : ℝ) => q x (k i) * (B i).indicator (fun _ => (1 : ℝ)) (record x (k i)))
    rw [hsum_formula _ hbox, integral_finsetSum Finset.univ
      (fun k _ => integrable_record_indicator (hpint k) (hrm k) hbox)]
    simp_rw [hfactor]
    rw [← Fintype.prod_sum (fun i (j : Fin 3) =>
      ∫ w, q w j * (B i).indicator (fun _ => (1 : ℝ)) (record w j) ∂uniform01)]
    apply Finset.prod_congr rfl
    intro i _
    exact hone (B i) (hB i)
  have hmeasure : (Measure.pi fun _ : Fin n => ν) = νsum := by
    apply Measure.pi_eq
    intro B hB
    calc
      νsum (Set.univ.pi B) = ENNReal.ofReal (νsum.real (Set.univ.pi B)) :=
        (ofReal_measureReal (measure_ne_top νsum _)).symm
      _ = ENNReal.ofReal (∏ i, ν.real (B i)) := congrArg ENNReal.ofReal (hboxes B hB)
      _ = ∏ i, ENNReal.ofReal (ν.real (B i)) :=
        ENNReal.ofReal_prod_of_nonneg (fun _ _ => measureReal_nonneg)
      _ = ∏ i, ν (B i) :=
        Finset.prod_congr rfl fun i _ => ofReal_measureReal (measure_ne_top ν _)
  rw [hmeasure]
  exact hsum_formula E hE

end

end AronowAudit.P047.Wave1.Impossibility
