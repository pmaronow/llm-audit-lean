import SAP.P004a.WH.W2.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P004a.WH.W2.P.T14_L1

open MeasureTheory Set
open scoped BigOperators ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable

theorem atom_injective : Function.Injective oneShellAtom := by
  intro x y h
  have h0 := congrArg (fun p : EuclideanSpace ℝ (Fin 2) => p 0) h
  have h1 := congrArg (fun p : EuclideanSpace ℝ (Fin 2) => p 1) h
  fin_cases x <;> fin_cases y <;>
    norm_num [oneShellAtom, planePoint] at *

theorem atom_distance (x : Fin 3) :
    nodeDistance (oneShellPopulation {1}) 0 (oneShellAtom x) =
      if x = 0 then 1 else 2 := by
  simp only [nodeDistance, oneShellPopulation, Metric.infDist_singleton]
  rw [dist_eq_norm]
  fin_cases x <;>
    norm_num [oneShellAtom, planePoint, EuclideanSpace.norm_eq, Fin.sum_univ_succ]

theorem atom_distance_for (D : Set ℝ) (x : Fin 3) :
    nodeDistance (oneShellPopulation D) 0 (oneShellAtom x) =
      if x = 0 then 1 else 2 := by
  simpa only [nodeDistance, oneShellPopulation, Metric.infDist_singleton] using
    (atom_distance x)

theorem outcome_at_atom (D : Set ℝ) (z : Assignment 1) (x : Fin 3) :
    (oneShellPopulation D).outcome (oneShellAtom x) z =
      if x = 0 then 0 else bit (z 0) := by
  fin_cases x
  · have h1 : oneShellAtom 0 ≠ oneShellAtom 1 := by
      intro h
      have h' := atom_injective h
      norm_num at h'
    have h2 : oneShellAtom 0 ≠ oneShellAtom 2 := by
      intro h
      have h' := atom_injective h
      norm_num at h'
    simp [oneShellPopulation, h1, h2]
  · simp [oneShellPopulation]
  · simp [oneShellPopulation]

theorem region_measurable (D : Set ℝ) (hD : MeasurableSet D) :
    MeasurableSet (region (oneShellPopulation D) 0 0) := by
  simp only [region, nodeDistance, oneShellPopulation, Metric.infDist_singleton]
  exact hD.preimage (measurable_id.dist measurable_const)

theorem mass_count (D : Set ℝ) :
    (oneShellPopulation D).zeta (region (oneShellPopulation D) 0 0) =
      ∑ x : Fin 3, if (if x = 0 then 1 else 2) ∈ D then (1 : ENNReal) else 0 := by
  classical
  change (∑ x : Fin 3, Measure.dirac (oneShellAtom x))
    (region (oneShellPopulation D) 0 0) = _
  rw [Measure.finsetSum_apply]
  apply Finset.sum_congr rfl
  intro x hx
  rw [Measure.dirac_apply]
  have hmem : oneShellAtom x ∈ region (oneShellPopulation D) 0 0 ↔
      (if x = 0 then 1 else 2) ∈ D := by
    change nodeDistance (oneShellPopulation D) 0 (oneShellAtom x) ∈ D ↔ _
    rw [atom_distance_for]
  simp only [Set.indicator_apply]
  simp [hmem]

theorem numerator_count (D : Set ℝ) (z : Assignment 1) :
    (∫ y in region (oneShellPopulation D) 0 0,
      (oneShellPopulation D).outcome y z ∂(oneShellPopulation D).zeta) =
      ∑ x : Fin 3, if (if x = 0 then 1 else 2) ∈ D then
        (if x = 0 then 0 else bit (z 0)) else 0 := by
  classical
  let R := region (oneShellPopulation D) 0 0
  have hi : ∀ x : Fin 3, Integrable
      (fun y => (oneShellPopulation D).outcome y z)
      ((Measure.dirac (oneShellAtom x)).restrict R) := by
    intro x
    exact (integrable_dirac (by simp)).restrict
  have hr : ((∑ x : Fin 3, Measure.dirac (oneShellAtom x)).restrict R) =
      ∑ x : Fin 3, (Measure.dirac (oneShellAtom x)).restrict R := by
    simpa only [Measure.restrictₗ_apply] using
      map_sum (Measure.restrictₗ R) (fun x : Fin 3 => Measure.dirac (oneShellAtom x))
        Finset.univ
  change (∫ y, (oneShellPopulation D).outcome y z
      ∂((∑ x : Fin 3, Measure.dirac (oneShellAtom x)).restrict R)) = _
  rw [hr, integral_finsetSum_measure (fun x _ => hi x)]
  simp_rw [setIntegral_dirac]
  apply Finset.sum_congr rfl
  intro x hx
  rw [outcome_at_atom]
  have hmem : oneShellAtom x ∈ R ↔ (if x = 0 then 1 else 2) ∈ D := by
    change nodeDistance (oneShellPopulation D) 0 (oneShellAtom x) ∈ D ↔ _
    rw [atom_distance_for]
  simp [hmem]

theorem mass_one : (oneShellPopulation ({1} : Set ℝ)).zeta
    (region (oneShellPopulation {1}) 0 0) = 1 := by
  rw [mass_count]
  norm_num [Fin.sum_univ_succ]

theorem mass_two : (oneShellPopulation ({2} : Set ℝ)).zeta
    (region (oneShellPopulation {2}) 0 0) = 2 := by
  rw [mass_count]
  norm_num [Fin.sum_univ_succ]

theorem mass_02 : (oneShellPopulation (Icc 0 2)).zeta
    (region (oneShellPopulation (Icc 0 2)) 0 0) = 3 := by
  rw [mass_count]
  simp only [Fin.sum_univ_succ]
  norm_num [Set.mem_Icc]

theorem mass_12 : (oneShellPopulation (Icc 1 2)).zeta
    (region (oneShellPopulation (Icc 1 2)) 0 0) = 3 := by
  rw [mass_count]
  simp only [Fin.sum_univ_succ]
  norm_num [Set.mem_Icc]

theorem well_defined_named : ∀ D ∈ ({({1} : Set ℝ), {2}, Icc 0 2, Icc 1 2} : Set (Set ℝ)),
    WellDefined (oneShellPopulation D) 0 := by
  classical
  intro D hD
  have hcases : D = ({1} : Set ℝ) ∨ D = ({2} : Set ℝ) ∨ D = Icc 0 2 ∨ D = Icc 1 2 := by
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_insert_iff,
      Set.mem_singleton_iff] using hD
  have hmeas : MeasurableSet (region (oneShellPopulation D) 0 0) := by
    apply region_measurable
    rcases hcases with h | h | h | h <;> subst D
    · exact measurableSet_singleton 1
    · exact measurableSet_singleton 2
    · exact measurableSet_Icc
    · exact measurableSet_Icc
  intro i
  refine ⟨?_, ?_, ?_, ?_⟩
  · fin_cases i
    exact hmeas
  · fin_cases i
    rcases hcases with h | h | h | h <;> subst D
    · have h : 0 < (oneShellPopulation ({1} : Set ℝ)).zeta
          (region (oneShellPopulation {1}) 0 0) := by rw [mass_one]; norm_num
      simpa using h
    · have h : 0 < (oneShellPopulation ({2} : Set ℝ)).zeta
          (region (oneShellPopulation {2}) 0 0) := by rw [mass_two]; norm_num
      simpa using h
    · have h : 0 < (oneShellPopulation (Icc 0 2)).zeta
          (region (oneShellPopulation (Icc 0 2)) 0 0) := by rw [mass_02]; norm_num
      simpa using h
    · have h : 0 < (oneShellPopulation (Icc 1 2)).zeta
          (region (oneShellPopulation (Icc 1 2)) 0 0) := by rw [mass_12]; norm_num
      simpa using h
  · fin_cases i
    rcases hcases with h | h | h | h <;> subst D
    · have h : (oneShellPopulation ({1} : Set ℝ)).zeta
          (region (oneShellPopulation {1}) 0 0) < ⊤ := by rw [mass_one]; norm_num
      simpa using h
    · have h : (oneShellPopulation ({2} : Set ℝ)).zeta
          (region (oneShellPopulation {2}) 0 0) < ⊤ := by rw [mass_two]; norm_num
      simpa using h
    · have h : (oneShellPopulation (Icc 0 2)).zeta
          (region (oneShellPopulation (Icc 0 2)) 0 0) < ⊤ := by rw [mass_02]; norm_num
      simpa using h
    · have h : (oneShellPopulation (Icc 1 2)).zeta
          (region (oneShellPopulation (Icc 1 2)) 0 0) < ⊤ := by rw [mass_12]; norm_num
      simpa using h
  · intro z
    have hi : Integrable (fun y => (oneShellPopulation D).outcome y z)
        (oneShellPopulation D).zeta := by
      change Integrable (fun y => (oneShellPopulation D).outcome y z)
        (∑ x : Fin 3, Measure.dirac (oneShellAtom x))
      rw [integrable_finsetSum_measure]
      intro x hx
      exact integrable_dirac (by simp)
    exact hi.integrableOn

theorem circle_1 (z : Assignment 1) :
    circleAverage (oneShellPopulation {1}) 0 0 z = 0 := by
  rw [circleAverage, numerator_count, mass_one]
  norm_num [Fin.sum_univ_succ]

theorem circle_2 (z : Assignment 1) :
    circleAverage (oneShellPopulation {2}) 0 0 z = bit (z 0) := by
  rw [circleAverage, numerator_count, mass_two]
  cases hz : z 0 <;> simp [hz, bit, Fin.sum_univ_succ]

theorem circle_02 (z : Assignment 1) :
    circleAverage (oneShellPopulation (Icc 0 2)) 0 0 z = 2 * bit (z 0) / 3 := by
  rw [circleAverage, numerator_count, mass_02]
  cases hz : z 0 <;> simp [hz, bit, Fin.sum_univ_succ] <;> ring

theorem circle_12 (z : Assignment 1) :
    circleAverage (oneShellPopulation (Icc 1 2)) 0 0 z = 2 * bit (z 0) / 3 := by
  rw [circleAverage, numerator_count, mass_12]
  cases hz : z 0 <;> simp [hz, bit, Fin.sum_univ_succ] <;> ring

theorem bounded_outcome (x : EuclideanSpace ℝ (Fin 2)) (z : Assignment 1) :
    |(oneShellPopulation {1}).outcome x z| < 2 := by
  change |(if x = oneShellAtom 1 ∨ x = oneShellAtom 2 then bit (z 0) else 0)| < 2
  by_cases hx : x = oneShellAtom 1 ∨ x = oneShellAtom 2
  · by_cases hz : z 0 <;> simp [hx, hz, bit] <;> norm_num
  · simp [hx]

end
end SAP.P004a.WH.W2.P.T14_L1

open SAP.P004a.WH.W2.P.T14_L1
open Set

theorem SAP.P004a.WH.W2.T14_L1_proof : SAP.P004a.WH.W2.T14_L1 := by
  refine ⟨well_defined_named, bounded_outcome, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact atom_distance
  · intro z
    exact ⟨circle_1 z, circle_2 z, circle_02 z, circle_12 z⟩
  · change ((oneShellPopulation {1}).zeta
      (region (oneShellPopulation {1}) 0 0)).toReal = 1
    rw [mass_one]
    norm_num
  · change ((oneShellPopulation {2}).zeta
      (region (oneShellPopulation {2}) 0 0)).toReal = 2
    rw [mass_two]
    norm_num
  · change ((oneShellPopulation (Icc 0 2)).zeta
      (region (oneShellPopulation (Icc 0 2)) 0 0)).toReal = 3
    rw [mass_02]
    norm_num
  · change ((oneShellPopulation (Icc 1 2)).zeta
      (region (oneShellPopulation (Icc 1 2)) 0 0)).toReal = 3
    rw [mass_12]
    norm_num
