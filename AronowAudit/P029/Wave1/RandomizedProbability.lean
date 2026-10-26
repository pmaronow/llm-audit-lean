import AronowAudit.P029.Wave1.RandomizedProbabilityBlueprint
import AronowAudit.P029.Wave1.RandomizedProbability.N1
import AronowAudit.P029.Wave1.RandomizedProbability.N2

namespace AronowAudit.P029.Wave1

open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical
open AronowAudit.P029

universe u v

noncomputable section

theorem randomized_probability_independent {Ω : Type u} {A : Type v}
    [MeasurableSpace Ω] [MeasurableSpace A]
    (ν : Measure Ω) [IsProbabilityMeasure ν] (e : ℝ) (he0 : 0 < e) (he1 : e < 1)
    (v : Ω → A) (hv : Measurable v) :
    IsProbabilityMeasure (ν.prod (bernoulliMeasure e)) ∧
    IndepFun (fun i : Ω × Bool => v i.1) Prod.snd (ν.prod (bernoulliMeasure e)) ∧
    mP (ν.prod (bernoulliMeasure e)) {i | i.2 = true} = e ∧
    mP (ν.prod (bernoulliMeasure e)) {i | i.2 = false} = 1 - e := by
  exact RandomizedProbability.assemble RandomizedProbability.n1_proof
    RandomizedProbability.n2_proof ν e he0 he1 v hv

end

end AronowAudit.P029.Wave1
