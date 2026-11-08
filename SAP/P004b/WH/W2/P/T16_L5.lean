import SAP.P004b.WH.W2.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P004b.WH.W2.P.T16_L5

open MeasureTheory
open scoped BigOperators Classical Topology

private theorem abs_coord_sub_le_dist (x y : EuclideanSpace ℝ (Fin 2)) (k : Fin 2) :
    |x k - y k| ≤ dist x y := by
  simpa only [Real.dist_eq] using PiLp.dist_apply_le x y k

private theorem infDist_ge_coord {x : EuclideanSpace ℝ (Fin 2)} {s : Set (EuclideanSpace ℝ (Fin 2))}
    {k : Fin 2} {c : ℝ} (hne : s.Nonempty)
    (hgap : ∀ y ∈ s, c ≤ |x k - y k|) : c ≤ Metric.infDist x s := by
  apply (Metric.le_infDist hne).mpr
  intro y hy
  exact (hgap y hy).trans (abs_coord_sub_le_dist x y k)

private theorem distance_zero_false :
    nodeDistance positiveRectangleWitness 0 (positiveAtom false) = 1 := by
  change Metric.infDist (planePoint (1/2) 2) (rectangle 0 1 0 1) = 1
  apply le_antisymm
  · calc
      Metric.infDist (planePoint (1/2) 2) (rectangle 0 1 0 1) ≤
          dist (planePoint (1/2) 2) (planePoint (1/2) 1) :=
        Metric.infDist_le_dist_of_mem (by norm_num [rectangle, planePoint])
      _ = 1 := by norm_num [EuclideanSpace.dist_eq, planePoint, Fin.sum_univ_succ, Real.dist_eq]
  · apply infDist_ge_coord (x := planePoint (1/2) 2) (s := rectangle 0 1 0 1)
      (k := 1) (c := 1) ⟨planePoint 0 0, by norm_num [rectangle, planePoint]⟩
    intro y hy
    change 0 ≤ y 0 ∧ y 0 ≤ 1 ∧ 0 ≤ y 1 ∧ y 1 ≤ 1 at hy
    have hy1 : y 1 ≤ 1 := hy.2.2.2
    have hcoord : 1 ≤ |(planePoint (1/2) 2) 1 - y 1| := by
      have hnonneg : 0 ≤ (planePoint (1/2) 2) 1 - y 1 := by
        simp [planePoint]
        linarith
      rw [abs_of_nonneg hnonneg]
      simp [planePoint]
      linarith
    exact hcoord

private theorem distance_one_true :
    nodeDistance positiveRectangleWitness 1 (positiveAtom true) = 1 := by
  change Metric.infDist (planePoint (21/2) 2) (rectangle 10 11 0 1) = 1
  apply le_antisymm
  · calc
      Metric.infDist (planePoint (21/2) 2) (rectangle 10 11 0 1) ≤
          dist (planePoint (21/2) 2) (planePoint (21/2) 1) :=
        Metric.infDist_le_dist_of_mem (by norm_num [rectangle, planePoint])
      _ = 1 := by norm_num [EuclideanSpace.dist_eq, planePoint, Fin.sum_univ_succ, Real.dist_eq]
  · apply infDist_ge_coord (x := planePoint (21/2) 2) (s := rectangle 10 11 0 1)
      (k := 1) (c := 1) ⟨planePoint 10 0, by norm_num [rectangle, planePoint]⟩
    intro y hy
    change 10 ≤ y 0 ∧ y 0 ≤ 11 ∧ 0 ≤ y 1 ∧ y 1 ≤ 1 at hy
    have hy1 : y 1 ≤ 1 := hy.2.2.2
    have hcoord : 1 ≤ |(planePoint (21/2) 2) 1 - y 1| := by
      have hnonneg : 0 ≤ (planePoint (21/2) 2) 1 - y 1 := by
        simp [planePoint]
        linarith
      rw [abs_of_nonneg hnonneg]
      simp [planePoint]
      linarith
    exact hcoord

private theorem distance_two (a : Bool) :
    nodeDistance positiveRectangleWitness 2 (positiveAtom a) = 1 := by
  cases a with
  | false =>
      change Metric.infDist (planePoint (1/2) 2) (rectangle 0 11 3 4) = 1
      apply le_antisymm
      · calc
          Metric.infDist (planePoint (1/2) 2) (rectangle 0 11 3 4) ≤
              dist (planePoint (1/2) 2) (planePoint (1/2) 3) :=
            Metric.infDist_le_dist_of_mem (by norm_num [rectangle, planePoint])
          _ = 1 := by norm_num [EuclideanSpace.dist_eq, planePoint, Fin.sum_univ_succ, Real.dist_eq]
      · apply infDist_ge_coord (x := planePoint (1/2) 2) (s := rectangle 0 11 3 4)
          (k := 1) (c := 1) ⟨planePoint 0 3, by norm_num [rectangle, planePoint]⟩
        intro y hy
        change 0 ≤ y 0 ∧ y 0 ≤ 11 ∧ 3 ≤ y 1 ∧ y 1 ≤ 4 at hy
        have hy1 : 3 ≤ y 1 := hy.2.2.1
        have hnonpos : (planePoint (1/2) 2) 1 - y 1 ≤ 0 := by
          simp [planePoint]
          linarith
        have hcoord : 1 ≤ |(planePoint (1/2) 2) 1 - y 1| := by
          rw [abs_of_nonpos hnonpos]
          simp [planePoint]
          linarith
        exact hcoord
  | true =>
      change Metric.infDist (planePoint (21/2) 2) (rectangle 0 11 3 4) = 1
      apply le_antisymm
      · calc
          Metric.infDist (planePoint (21/2) 2) (rectangle 0 11 3 4) ≤
              dist (planePoint (21/2) 2) (planePoint (21/2) 3) :=
            Metric.infDist_le_dist_of_mem (by norm_num [rectangle, planePoint])
          _ = 1 := by norm_num [EuclideanSpace.dist_eq, planePoint, Fin.sum_univ_succ, Real.dist_eq]
      · apply infDist_ge_coord (x := planePoint (21/2) 2) (s := rectangle 0 11 3 4)
          (k := 1) (c := 1) ⟨planePoint 0 3, by norm_num [rectangle, planePoint]⟩
        intro y hy
        change 0 ≤ y 0 ∧ y 0 ≤ 11 ∧ 3 ≤ y 1 ∧ y 1 ≤ 4 at hy
        have hy1 : 3 ≤ y 1 := hy.2.2.1
        have hnonpos : (planePoint (21/2) 2) 1 - y 1 ≤ 0 := by
          simp [planePoint]
          linarith
        have hcoord : 1 ≤ |(planePoint (21/2) 2) 1 - y 1| := by
          rw [abs_of_nonpos hnonpos]
          simp [planePoint]
          linarith
        exact hcoord

private theorem distance_zero_true_far :
    (1 : ℝ) < nodeDistance positiveRectangleWitness 0 (positiveAtom true) := by
  change 1 < Metric.infDist (planePoint (21/2) 2) (rectangle 0 1 0 1)
  apply lt_of_lt_of_le (by norm_num : (1 : ℝ) < 19/2)
  apply infDist_ge_coord (x := planePoint (21/2) 2) (s := rectangle 0 1 0 1)
    (k := 0) (c := 19/2) ⟨planePoint 0 0, by norm_num [rectangle, planePoint]⟩
  intro y hy
  change 0 ≤ y 0 ∧ y 0 ≤ 1 ∧ 0 ≤ y 1 ∧ y 1 ≤ 1 at hy
  have hy0 : y 0 ≤ 1 := hy.2.1
  have hnonneg : 0 ≤ (planePoint (21/2) 2) 0 - y 0 := by
    simp [planePoint]
    linarith
  rw [abs_of_nonneg hnonneg]
  simp [planePoint]
  linarith

private theorem distance_one_false_far :
    (1 : ℝ) < nodeDistance positiveRectangleWitness 1 (positiveAtom false) := by
  change 1 < Metric.infDist (planePoint (1/2) 2) (rectangle 10 11 0 1)
  apply lt_of_lt_of_le (by norm_num : (1 : ℝ) < 19/2)
  apply infDist_ge_coord (x := planePoint (1/2) 2) (s := rectangle 10 11 0 1)
    (k := 0) (c := 19/2) ⟨planePoint 10 0, by norm_num [rectangle, planePoint]⟩
  intro y hy
  change 10 ≤ y 0 ∧ y 0 ≤ 11 ∧ 0 ≤ y 1 ∧ y 1 ≤ 1 at hy
  have hy0 : 10 ≤ y 0 := hy.1
  have hnonpos : (planePoint (1/2) 2) 0 - y 0 ≤ 0 := by
    simp [planePoint]
    linarith
  rw [abs_of_nonpos hnonpos]
  simp [planePoint]
  linarith

private theorem distance_zero_true_ne :
    nodeDistance positiveRectangleWitness 0 (positiveAtom true) ≠ 1 :=
  ne_of_gt distance_zero_true_far

private theorem distance_one_false_ne :
    nodeDistance positiveRectangleWitness 1 (positiveAtom false) ≠ 1 :=
  ne_of_gt distance_one_false_far

private theorem atom_mem_region (i : Fin 3) (a : Bool) :
    positiveAtom a ∈ region positiveRectangleWitness i 1 ↔
      (i = 2 ∨ (i = 0 ∧ a = false) ∨ (i = 1 ∧ a = true)) := by
  change nodeDistance positiveRectangleWitness i (positiveAtom a) ∈ ({1} : Set ℝ) ↔ _
  fin_cases i <;> cases a <;>
    simp [distance_zero_false, distance_one_true, distance_two,
      distance_zero_true_ne, distance_one_false_ne]

private theorem region_measurable (i : Fin 3) :
    MeasurableSet (region positiveRectangleWitness i 1) := by
  change MeasurableSet
    ((fun x : EuclideanSpace ℝ (Fin 2) =>
      Metric.infDist x (positiveRectangleWitness.node i)) ⁻¹' ({1} : Set ℝ))
  exact (measurableSet_singleton (1 : ℝ)).preimage measurable_infDist

private theorem region_mass (i : Fin 3) :
    positiveRectangleWitness.zeta (region positiveRectangleWitness i 1) =
      if i = 2 then 2 else 1 := by
  classical
  rw [show positiveRectangleWitness.zeta =
      Measure.dirac (positiveAtom false) + Measure.dirac (positiveAtom true) by rfl]
  rw [Measure.add_apply,
    Measure.dirac_apply' _ (region_measurable i),
    Measure.dirac_apply' _ (region_measurable i)]
  simp only [Set.indicator, Pi.one_apply]
  fin_cases i <;> norm_num [atom_mem_region]

private theorem integrable_on_region (i : Fin 3) (z : Assignment 3) :
    IntegrableOn (fun x => positiveRectangleWitness.outcome x z)
      (region positiveRectangleWitness i 1) positiveRectangleWitness.zeta := by
  change Integrable (fun x => positiveRectangleWitness.outcome x z)
    ((Measure.dirac (positiveAtom false) + Measure.dirac (positiveAtom true)).restrict
      (region positiveRectangleWitness i 1))
  rw [Measure.restrict_add, integrable_add_measure]
  exact ⟨(integrable_dirac (by simp)).restrict, (integrable_dirac (by simp)).restrict⟩

private theorem numerator (i : Fin 3) (z : Assignment 3) :
    (∫ x in region positiveRectangleWitness i 1,
      positiveRectangleWitness.outcome x z ∂positiveRectangleWitness.zeta) =
      (if positiveAtom false ∈ region positiveRectangleWitness i 1 then bit (z 2) else 0) +
      (if positiveAtom true ∈ region positiveRectangleWitness i 1 then bit (z 2) else 0) := by
  classical
  let s := region positiveRectangleWitness i 1
  let f := fun x => positiveRectangleWitness.outcome x z
  have hf0 : Integrable f ((Measure.dirac (positiveAtom false)).restrict s) :=
    (integrable_dirac (by simp)).restrict
  have hf1 : Integrable f ((Measure.dirac (positiveAtom true)).restrict s) :=
    (integrable_dirac (by simp)).restrict
  change (∫ x, f x ∂((Measure.dirac (positiveAtom false) +
      Measure.dirac (positiveAtom true)).restrict s)) = _
  rw [Measure.restrict_add, integral_add_measure hf0 hf1]
  change (∫ x in s, f x ∂Measure.dirac (positiveAtom false)) +
      (∫ x in s, f x ∂Measure.dirac (positiveAtom true)) = _
  rw [setIntegral_dirac, setIntegral_dirac]
  have hout0 : positiveRectangleWitness.outcome (positiveAtom false) z = bit (z 2) := by
    simp [positiveRectangleWitness, positiveAtom, planePoint]
  have hout1 : positiveRectangleWitness.outcome (positiveAtom true) z = bit (z 2) := by
    simp [positiveRectangleWitness, positiveAtom, planePoint]
  change f (positiveAtom false) = bit (z 2) at hout0
  change f (positiveAtom true) = bit (z 2) at hout1
  rw [hout0, hout1]

private theorem circle_average (i : Fin 3) (z : Assignment 3) :
    circleAverage positiveRectangleWitness 1 i z = bit (z 2) := by
  unfold circleAverage
  rw [numerator, region_mass]
  rw [atom_mem_region, atom_mem_region]
  fin_cases i <;> cases hz : z 2 <;> norm_num [bit, hz]

end SAP.P004b.WH.W2.P.T16_L5

namespace SAP.P004b.WH.W2

open SAP.P004b.WH.W2.P.T16_L5

theorem T16_L5_proof : SAP.P004b.WH.W2.T16_L5 := by
  refine ⟨?_, ?_, ?_⟩
  · intro i
    refine ⟨region_measurable i, ?_, ?_, fun z => integrable_on_region i z⟩
    · rw [region_mass]
      by_cases hi : i = 2
      · simp [hi]
      · simp [hi]
    · rw [region_mass]
      by_cases hi : i = 2
      · simp [hi]
      · simp [hi]
  · intro i
    exact region_mass i
  · exact circle_average

end SAP.P004b.WH.W2
