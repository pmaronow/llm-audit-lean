import SAP.P009a.WH.W1.Support

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 8000
set_option backward.isDefEq.respectTransparency false

namespace SAP.P009a.WH.W1

open Filter MeasureTheory Bridge
open scoped BigOperators Topology Classical

noncomputable section

/-- Independent finite enumeration checks the signed example's entire new table. -/
theorem signed_table : W1SignedTable signedWitness := by
  norm_num [W1SignedTable, signedWitness, fromProjectExperiment,
    fromProjectDistribution, AronowAudit.P009.signedExperiment, AronowAudit.P009.unequalLaw,
    estimatedArmMean, armProbability, probability, expectation, armResponse,
    covariance, variance, twoUnitProduct, treatmentValue, AronowAudit.P009.bit,
    Fin.forall_fin_succ_pi, Fin.forall_fin_zero_pi, Bool.forall_bool, Fin.forall_fin_succ,
    Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.cons_zero, Fin.cons_succ,
    AronowAudit.P009.sum_cube_succ, AronowAudit.P009.sum_cube_zero, Fintype.sum_bool]

/-- Independent enumeration checks the almost-sure count support and both atoms. -/
theorem count_table : W1CountTable countWitness := by
  norm_num [W1CountTable, countWitness, fromProjectExperiment,
    fromProjectDistribution, AronowAudit.P009.countExperiment, AronowAudit.P009.anticorrelatedLaw,
    estimatedArmSize, armProbability, probability, expectation,
    covariance, variance, treatmentValue,
    Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.cons_zero, Fin.cons_succ,
    AronowAudit.P009.sum_cube_succ, AronowAudit.P009.sum_cube_zero, Fintype.sum_bool]

/-- Independent enumeration checks the squared-outcome example's law and both raw moments. -/
theorem square_table : W1SquareTable squareWitness := by
  norm_num [W1SquareTable, squareWitness, fromProjectExperiment,
    fromProjectDistribution, AronowAudit.P009.squareExperiment, AronowAudit.P009.unequalLaw,
    squareWeightedSum, armProbability, probability, expectation, armResponse,
    covariance, variance, treatmentValue, AronowAudit.P009.bit,
    Fin.forall_fin_succ_pi, Fin.forall_fin_zero_pi, Bool.forall_bool,
    Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.cons_zero, Fin.cons_succ,
    AronowAudit.P009.sum_cube_succ, AronowAudit.P009.sum_cube_zero, Fintype.sum_bool]


theorem whole_hypergeom_count (z : TreatmentVector 4) :
    treatedIncomingCount hypergeomWitness 0 z = if z 1 then 1 else 0 := by
  have hA (j : Fin 4) : Affects hypergeomWitness j 0 ↔ j = 0 ∨ j = 1 :=
    AronowAudit.P009.hypergeom_interferes_zero j
  have hPred (j : Fin 4) :
      (j ≠ 0 ∧ Affects hypergeomWitness j 0 ∧ z j = true) ↔ (j = 1 ∧ z 1 = true) := by
    by_cases hj1 : j = 1
    · subst j
      norm_num [hA]
    · by_cases hj0 : j = 0
      · subst j
        simp
      · simp [hA, hj0, hj1]
  unfold treatedIncomingCount
  simp_rw [hPred]
  by_cases hz : z 1 = true <;> simp [hz]

theorem whole_hypergeom_marginal (i : Fin 4) (b : Bool) :
    armProbability hypergeomWitness i b = 1/2 := by
  fin_cases i <;> cases b <;>
    simp only [armProbability, probability, expectation, hypergeomWitness,
      fromProjectExperiment, fromProjectDistribution, AronowAudit.P009.hypergeomExperiment,
      AronowAudit.P009.completeFourLaw, AronowAudit.P009.sum_cube_succ,
      AronowAudit.P009.sum_cube_zero, Fintype.sum_bool, Fin.sum_univ_succ,
      Fin.sum_univ_zero, Fin.cons_zero, Fin.cons_succ] <;>
    norm_num [Fin.cons_zero, Fin.cons_succ, AronowAudit.P009.cons_at_two,
      AronowAudit.P009.cons_at_three]

/-- All six table columns are checked at each of their three permitted arguments. -/
theorem hypergeom_first_facts :
    (∀ i b, armProbability hypergeomWitness i b = 1/2) ∧
    (∀ z, treatedIncomingCount hypergeomWitness 0 z = if z 1 then 1 else 0) ∧
    W1HypergeomTables hypergeomWitness := by
  refine ⟨whole_hypergeom_marginal, whole_hypergeom_count, ?_⟩
  intro t
  unfold incomingMass incomingConditionalMass conditionalMean
  simp_rw [whole_hypergeom_count]
  fin_cases t <;>
    simp only [probability, expectation,
      hypergeomWitness, fromProjectExperiment, fromProjectDistribution,
      AronowAudit.P009.hypergeomExperiment, AronowAudit.P009.completeFourLaw,
      AronowAudit.P009.sum_cube_succ, AronowAudit.P009.sum_cube_zero, Fintype.sum_bool,
      Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.cons_zero, Fin.cons_succ] <;>
    norm_num [printedHypergeomMass, Nat.choose, Fin.cons_zero, Fin.cons_succ,
      AronowAudit.P009.cons_at_two, AronowAudit.P009.cons_at_three]

/-- The second witness independently checks all denominators and the empty other-incoming set. -/
theorem hypergeom_second : W1HypergeomSecond hypergeomSecondWitness := by
  have hNo : NoSpillovers hypergeomSecondWitness := by
    intro i z w h
    exact congrArg treatmentValue h
  have hA (i j : Fin 4) : Affects hypergeomSecondWitness j i ↔ j = i :=
    AronowAudit.P009.SparseCompletion.noI_interferes
      (toProjectExperiment hypergeomSecondWitness) hNo j i
  have hT (i : Fin 4) (z : TreatmentVector 4) :
      treatedIncomingCount hypergeomSecondWitness i z = 0 := by
    unfold treatedIncomingCount
    apply Finset.sum_eq_zero
    intro j _
    have hh : ¬ (j ≠ i ∧ Affects hypergeomSecondWitness j i ∧ z j = true) := by
      rw [hA i j]
      tauto
    simp only [hh, ite_false]
  have hM (i : Fin 4) (b : Bool) : armProbability hypergeomSecondWitness i b = 1/2 :=
    whole_hypergeom_marginal i b
  have hReg : Regularity hypergeomSecondWitness 2 4 1 := by
    apply bounded_regularity _ 2 4 1 (by norm_num) (by norm_num) (by norm_num)
    · intro i
      rw [hM i true]
      norm_num
    · intro i z
      change |treatmentValue (z i)| ≤ 2
      cases z i <;> norm_num [treatmentValue]
  refine ⟨(fun _ => rfl), (fun _ _ => rfl),
    (AronowAudit.P009.hypergeometric_draw_counterexample).1, hReg, hNo, hM, hA, ?_, ?_, by norm_num⟩
  · intro i
    refine ⟨?_, hT i, ?_⟩
    · have he : Finset.univ.filter (fun j => Affects hypergeomSecondWitness j i) =
          ({i} : Finset (Fin 4)) := by
        ext j
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, hA, Finset.mem_singleton]
      rw [incomingCount, he, Finset.card_singleton]
    · simp only [incomingMass, probability, hT, ite_true]
      exact AronowAudit.P009.mean_const (toProjectDistribution hypergeomSecondWitness.design) 1
  · norm_num [printedHypergeomMass, Nat.choose]


end
end SAP.P009a.WH.W1
