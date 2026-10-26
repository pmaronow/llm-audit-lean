import AronowAudit.P017.Wave1.PropositionOneBlueprint
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.Prod

set_option autoImplicit false

namespace AronowAudit.P017.Wave1.PropositionOne

open AronowAudit.P017 MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal

noncomputable section


theorem effect_eq_fst : ipwEffect = (Prod.fst : ℝ × (ℝ × ℝ) → ℝ) := by
  funext ω
  simp [ipwEffect, ipwY1, ipwY0]

theorem fst_law : ipwPopulation.map Prod.fst = uniform01 := by
  simp only [ipwPopulation, Measure.map_fst_prod, measure_univ, one_smul]

theorem uniform_mem : ∀ᵐ u ∂uniform01, u ∈ Ioo (0 : ℝ) 1 :=
  ae_restrict_mem measurableSet_Ioo

theorem uniform_id_integrable : Integrable (fun u : ℝ => u) uniform01 := by
  apply Integrable.of_bound measurable_id.aestronglyMeasurable 1
  filter_upwards [uniform_mem] with u hu
  show ‖u‖ ≤ 1
  rw [Real.norm_eq_abs, abs_of_pos hu.1]
  exact hu.2.le

theorem uniform_first_moment : (∫ u : ℝ, u ∂uniform01) = 1 / 2 := by
  change (∫ u in Ioo (0 : ℝ) 1, u) = 1 / 2
  rw [← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    _root_.integral_id]
  norm_num

theorem uniform_second_moment : (∫ u : ℝ, u ^ 2 ∂uniform01) = 1 / 3 := by
  change (∫ u in Ioo (0 : ℝ) 1, u ^ 2) = 1 / 3
  rw [← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    _root_.integral_pow]
  norm_num

theorem n1_proof : N1 := by
  have hi_map : Integrable (fun u : ℝ => u) (ipwPopulation.map Prod.fst) := by
    rw [fst_law]
    exact uniform_id_integrable
  have hi : Integrable (Prod.fst : ℝ × (ℝ × ℝ) → ℝ) ipwPopulation :=
    hi_map.comp_measurable measurable_fst
  change Measurable ipwEffect ∧ Integrable ipwEffect ipwPopulation ∧
    populationMean ipwPopulation ipwEffect = 1 / 2
  rw [effect_eq_fst]
  refine ⟨measurable_fst, hi, ?_⟩
  unfold populationMean ipwPopulation
  rw [integral_fun_fst (fun u : ℝ => u)]
  simpa only [probReal_univ, one_smul] using uniform_first_moment

end

end AronowAudit.P017.Wave1.PropositionOne
