import AronowAudit.P029.Wave1.IgnorabilityAllProfilesBlueprint

namespace AronowAudit.P029.Wave1.IgnorabilityAllProfiles

open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical
open AronowAudit.P029 AronowAudit.P029.Wave1.FiniteMeasure

noncomputable section

/-- Compare singleton masses of the constant-kernel and atomic population laws. -/
theorem n1_proof : N1 := by
  classical
  have hatom : ∀ {L : Type} [Fintype L] [MeasurableSpace L] [MeasurableSingletonClass L]
      (p : L → ℝ) (a : L), atomicMeasure p {a} = ENNReal.ofReal (p a) := by
    intro L _ _ _ p a
    simp [atomicMeasure, Measure.finsetSum_apply, Measure.smul_apply,
      Measure.dirac_apply, Set.indicator_apply, smul_eq_mul, mul_ite]
  have hnonneg : ∀ i : Fin 3, 0 ≤ typeMass i := by
    intro i
    unfold typeMass
    split <;> norm_num
  haveI : IsProbabilityMeasure nu := by
    constructor
    norm_num [nu, atomicMeasure, Measure.finsetSum_apply, Measure.smul_apply,
      smul_eq_mul, typeMass, Fin.sum_univ_succ]
    rw [← ENNReal.ofReal_add (by norm_num : (0 : ℝ) ≤ 1 / 4)
        (by norm_num : (0 : ℝ) ≤ 1 / 4),
      ← ENNReal.ofReal_add (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (0 : ℝ) ≤ 1 / 4 + 1 / 4)]
    norm_num
  haveI : IsProbabilityMeasure (bernoulliMeasure (1 / 2)) :=
    bernoulli_measure_probability (1 / 2) (by norm_num) (by norm_num)
  have hnu : ∀ i : Fin 3, nu {i} = ENNReal.ofReal (typeMass i) := by
    intro i
    exact hatom typeMass i
  have hbeta : ∀ z : Bool,
      bernoulliMeasure (1 / 2) {z} = ENNReal.ofReal (1 / 2 : ℝ) := by
    intro z
    cases z <;> norm_num [bernoulliMeasure, Measure.add_apply, Measure.smul_apply,
      smul_eq_mul, Measure.dirac_apply, Set.indicator_apply]
  constructor
  · change ((Measure.dirac ()).compProd (Kernel.const Unit nu)).prod
        (bernoulliMeasure (1 / 2)) = _
    rw [Measure.compProd_const]
    apply Measure.ext_of_singleton
    rintro ⟨⟨x, i⟩, z⟩
    cases x
    calc
      ((Measure.dirac ()).prod nu).prod (bernoulliMeasure (1 / 2)) {(((), i), z)} =
          ((Measure.dirac ()).prod nu) {((), i)} * bernoulliMeasure (1 / 2) {z} := by
        rw [← Set.singleton_prod_singleton, Measure.prod_prod]
      _ = ENNReal.ofReal (typeMass i) * ENNReal.ofReal (1 / 2 : ℝ) := by
        rw [← Set.singleton_prod_singleton, Measure.prod_prod]
        rw [Measure.dirac_apply_of_mem (Set.mem_singleton ()), hnu i, hbeta z, one_mul]
      _ = ENNReal.ofReal
          (randomized (fun l : Unit × Fin 3 => typeMass l.2) (1 / 2) (((), i), z)) := by
        cases z <;> norm_num [randomized, ENNReal.ofReal_mul (hnonneg i)]
      _ = atomicMeasure (randomized (fun l : Unit × Fin 3 => typeMass l.2) (1 / 2))
          {(((), i), z)} :=
        (hatom (randomized (fun l : Unit × Fin 3 => typeMass l.2) (1 / 2)) (((), i), z)).symm
  · change nu.prod (bernoulliMeasure (1 / 2)) = atomicMeasure sixMass
    apply Measure.ext_of_singleton
    rintro ⟨i, z⟩
    calc
      nu.prod (bernoulliMeasure (1 / 2)) {(i, z)} =
          nu {i} * bernoulliMeasure (1 / 2) {z} := by
        rw [← Set.singleton_prod_singleton, Measure.prod_prod]
      _ = ENNReal.ofReal (typeMass i) * ENNReal.ofReal (1 / 2 : ℝ) := by
        rw [hnu i, hbeta z]
      _ = ENNReal.ofReal (sixMass (i, z)) := by
        cases z <;> norm_num [sixMass, randomized, ENNReal.ofReal_mul (hnonneg i)]
      _ = atomicMeasure sixMass {(i, z)} := (hatom sixMass (i, z)).symm

end

end AronowAudit.P029.Wave1.IgnorabilityAllProfiles
