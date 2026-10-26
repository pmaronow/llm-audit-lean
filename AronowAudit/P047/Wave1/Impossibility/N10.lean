import AronowAudit.P047.Wave1.ImpossibilityBlueprint
import Mathlib.Probability.Independence.Integration
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

set_option autoImplicit false

universe u

namespace AronowAudit.P047.Wave1.Impossibility

open AronowAudit.P047 MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

noncomputable section

/-- The finite prior's point masses, with all unused coordinates retained. -/
private theorem typePrior_real_singleton (M : ℕ) (σ : Fin M → Bool) :
    (typePrior M).real {σ} = (1 / 2 : ℝ) ^ M := by
  have hb (b : Bool) : fairBool.real {b} = (1 / 2 : ℝ) := by
    rw [← integral_indicator_one (measurableSet_singleton b)]
    cases b <;> norm_num [fairBool, integral_bernoulliMeasure, Set.indicator]
  rw [measureReal_def, typePrior, Measure.pi_singleton, ENNReal.toReal_prod]
  simp_rw [← measureReal_def, hb]
  simp

/-- Use independence of the *distinct* selected type coordinates. -/
theorem n10_proof : N10 := by
  classical
  intro M family n c hc k
  have hind0 : iIndepFun (fun j : Fin (M + 1) =>
      fun σ : Fin (M + 1) → Bool => σ j) (typePrior (M + 1)) :=
    iIndepFun_pi (μ := fun _ : Fin (M + 1) => fairBool)
      (X := fun _ : Fin (M + 1) => id) (fun _ => measurable_id.aemeasurable)
  have hind : iIndepFun (fun i : Fin n =>
      fun σ : Fin (M + 1) → Bool => σ (c i)) (typePrior (M + 1)) :=
    hind0.precomp hc
  have hmean (i : Fin n) :
      (∫ σ, cellObservable family (σ (c i)) (k i) ∂typePrior (M + 1)) = baseObs (k i) := by
    have hf : Measurable (fun b : Bool => cellObservable family b (k i)) :=
      measurable_of_countable _
    rw [typePrior, integral_comp_eval (μ := fun _ : Fin (M + 1) => fairBool)
      (i := c i) (f := fun b => cellObservable family b (k i)) hf.aestronglyMeasurable]
    have h := single_cell_observable_agreement family (k i)
    simp only [fairBool, integral_bernoulliMeasure, smul_eq_mul]
    change (1 / 2 : ℝ) * cellObservable family true (k i) +
      (1 - 1 / 2 : ℝ) * cellObservable family false (k i) = baseObs (k i)
    change (cellObservable family true (k i) + cellObservable family false (k i)) / 2 =
      baseObs (k i) at h
    linarith
  have hfactor :
      (∫ σ, ∏ i, cellObservable family (σ (c i)) (k i) ∂typePrior (M + 1)) =
        ∏ i, baseObs (k i) := by
    rw [hind.integral_fun_prod_comp
      (fun i => (measurable_pi_apply (c i)).aemeasurable)
      (fun i => (measurable_of_countable
        (fun b : Bool => cellObservable family b (k i))).aestronglyMeasurable)]
    simp_rw [hmean]
  rw [integral_fintype (Integrable.of_finite : Integrable
    (fun σ : Fin (M + 1) → Bool => ∏ i, cellObservable family (σ (c i)) (k i))
    (typePrior (M + 1)))] at hfactor
  simpa only [typePrior_real_singleton, smul_eq_mul] using hfactor

end

end AronowAudit.P047.Wave1.Impossibility
