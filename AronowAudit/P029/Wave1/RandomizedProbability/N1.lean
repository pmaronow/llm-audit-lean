import AronowAudit.P029.Wave1.RandomizedProbabilityBlueprint

namespace AronowAudit.P029.Wave1.RandomizedProbability

open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical
open AronowAudit.P029

noncomputable section

theorem n1_proof : N1 := by
  intro e he0 he1
  refine ⟨bernoulli_measure_probability e he0.le he1.le, ?_, ?_⟩
  · simp [bernoulliMeasure, Measure.add_apply, Measure.smul_apply,
      Measure.dirac_apply' true (measurableSet_singleton true),
      Measure.dirac_apply' false (measurableSet_singleton true)]
  · simp [bernoulliMeasure, Measure.add_apply, Measure.smul_apply,
      Measure.dirac_apply' true (measurableSet_singleton false),
      Measure.dirac_apply' false (measurableSet_singleton false)]

end

end AronowAudit.P029.Wave1.RandomizedProbability
