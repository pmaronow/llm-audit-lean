import AronowAudit.P046.Wave1.PropositionThreeBlueprint

set_option autoImplicit false

namespace AronowAudit.P046.Wave1.PropositionThree

open AronowAudit.P046 AronowAudit.P046.IntervalExample MeasureTheory ProbabilityTheory Filter Finset
open scoped BigOperators ENNReal

noncomputable section

theorem n3_proof : N3 := by
  classical
  have mlow : MeasurableSet {o : AronowAudit.P046.Unit | o.1 ≤ (3 / 5 : ℝ)} :=
    measurableSet_le measurable_fst measurable_const
  have mx : MeasurableSet {o : AronowAudit.P046.Unit | o.2.1 = true} :=
    measurableSet_eq_fun measurable_snd.fst measurable_const
  have mc : Measurable cat :=
    (measurable_const.ite mx measurable_const).ite mlow measurable_const
  refine ⟨mc, ?_⟩
  intro j
  change (Measure.map IntervalExample.generate (unitUniform.prod unitUniform))
    {o | cat o = j} = ENNReal.ofReal (catProb j)
  rw [Measure.map_apply IntervalExample.measurable_generate
    (measurableSet_eq_fun mc measurable_const)]
  have hu : unitUniform (Set.Iic (3 / 5 : ℝ)) = ENNReal.ofReal (3 / 5) :=
    unitUniform_Iic _ (by norm_num) (by norm_num)
  have hv : unitUniform (Set.Iic (13 / 20 : ℝ)) = ENNReal.ofReal (13 / 20) :=
    unitUniform_Iic _ (by norm_num) (by norm_num)
  have h0 : IntervalExample.generate ⁻¹' {o | cat o = (0 : Fin 3)} =
      Set.Iic (3 / 5 : ℝ) ×ˢ Set.Iic (13 / 20 : ℝ) := by
    ext z
    simp only [Set.mem_preimage, Set.mem_setOf_eq, Set.mem_prod, Set.mem_Iic, cat,
      IntervalExample.generate, score]
    by_cases hw : z.1 ≤ (3 / 5 : ℝ) <;> by_cases hx : z.2 ≤ (13 / 20 : ℝ) <;>
      simp [hw, hx]
  have h1 : IntervalExample.generate ⁻¹' {o | cat o = (1 : Fin 3)} =
      Set.Iic (3 / 5 : ℝ) ×ˢ (Set.Iic (13 / 20 : ℝ))ᶜ := by
    ext z
    simp only [Set.mem_preimage, Set.mem_setOf_eq, Set.mem_prod, Set.mem_Iic,
      Set.mem_compl_iff, cat, IntervalExample.generate, score]
    by_cases hw : z.1 ≤ (3 / 5 : ℝ) <;> by_cases hx : z.2 ≤ (13 / 20 : ℝ) <;>
      simp [hw, hx]
  have h2 : IntervalExample.generate ⁻¹' {o | cat o = (2 : Fin 3)} =
      (Set.Iic (3 / 5 : ℝ))ᶜ ×ˢ (Set.univ : Set ℝ) := by
    ext z
    simp only [Set.mem_preimage, Set.mem_setOf_eq, Set.mem_prod, Set.mem_Iic,
      Set.mem_compl_iff, Set.mem_univ, cat, IntervalExample.generate, score]
    by_cases hw : z.1 ≤ (3 / 5 : ℝ)
    · by_cases hx : z.2 ≤ (13 / 20 : ℝ) <;> simp [hw, hx]
    · simp [hw]
  fin_cases j
  · change (unitUniform.prod unitUniform) (IntervalExample.generate ⁻¹' {o | cat o = 0}) =
      ENNReal.ofReal (catProb 0)
    rw [h0, Measure.prod_prod, hu, hv, ← ENNReal.ofReal_mul (by norm_num)]
    norm_num [catProb]
  · change (unitUniform.prod unitUniform) (IntervalExample.generate ⁻¹' {o | cat o = 1}) =
      ENNReal.ofReal (catProb 1)
    rw [h1, Measure.prod_prod, measure_compl measurableSet_Iic (measure_ne_top _ _), hu, hv,
      measure_univ, ← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ (by norm_num),
      ← ENNReal.ofReal_mul (by norm_num)]
    norm_num [catProb]
  · change (unitUniform.prod unitUniform) (IntervalExample.generate ⁻¹' {o | cat o = 2}) =
      ENNReal.ofReal (catProb 2)
    rw [h2, Measure.prod_prod, measure_compl measurableSet_Iic (measure_ne_top _ _), hu,
      measure_univ, mul_one, ← ENNReal.ofReal_one,
      ← ENNReal.ofReal_sub _ (by norm_num)]
    norm_num [catProb]

end

end AronowAudit.P046.Wave1.PropositionThree
