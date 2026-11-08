import SAP.P008a.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P008a.WH.W1.P.T7_L5

open MeasureTheory
open scoped BigOperators Classical

noncomputable section

theorem point_injective (hi : Function.Injective wholeRiskEmbedding)
    (i j : Fin 4) : Function.Injective (wholeRiskPoint i j) := by
  intro k l h
  have hwhole : wholeRiskEmbedding (Sum.inr (i, j, k)) =
      wholeRiskEmbedding (Sum.inr (i, j, l)) := by
    simpa [wholeRiskEmbedding] using h
  have hp : ((i, j, k) : WholeRiskTriple) = (i, j, l) := Sum.inr.inj (hi hwhole)
  exact congrArg Prod.snd (congrArg Prod.snd hp)

theorem circle_set_eq (companion : Bool) (i j : Fin 4) :
    (wholeRiskModel companion).circle i (wholeRiskRadius j) =
      (wholeRiskCircle i j : Set Plane) := by
  ext x
  simp [SpatialModel.circle, wholeRiskModel, wholeRiskCircle, wholeRiskField]

theorem circle_measure_eq (hi : Function.Injective wholeRiskEmbedding)
    (hc : WholeRiskCircles) (companion : Bool) (i j : Fin 4) :
    (wholeRiskModel companion).circleMeasure i (wholeRiskRadius j) =
      ∑ k : RiskCell, Measure.dirac (wholeRiskPoint i j k) := by
  let C := wholeRiskCircle i j
  have hcircle : (wholeRiskModel companion).circle i (wholeRiskRadius j) = (C : Set Plane) := by
    simpa [C] using circle_set_eq companion i j
  have hcirclemeas : MeasurableSet (C : Set Plane) := C.measurableSet
  have hmodel : (wholeRiskModel companion).circleMeasure i (wholeRiskRadius j) =
      (Measure.count.restrict (↑wholeRiskField : Set Plane)).restrict (C : Set Plane) := by
    change (Measure.count.restrict (↑wholeRiskField : Set Plane)).restrict
      ((wholeRiskModel companion).circle i (wholeRiskRadius j)) = _
    rw [hcircle]
  have hsubset : (C : Set Plane) ⊆ (↑wholeRiskField : Set Plane) := by
    intro x hx
    exact (Finset.mem_filter.mp (show x ∈ wholeRiskCircle i j from by simpa [C] using hx)).1
  have hmem : ∀ᵐ x ∂((wholeRiskModel companion).circleMeasure i (wholeRiskRadius j)), x ∈ C := by
    rw [hmodel]
    exact ae_restrict_mem hcirclemeas
  have hsumC : (wholeRiskModel companion).circleMeasure i (wholeRiskRadius j) =
      ∑ x ∈ C, ((wholeRiskModel companion).circleMeasure i (wholeRiskRadius j)) {x} • Measure.dirac x :=
    (Measure.ae_mem_finset_iff (μ := (wholeRiskModel companion).circleMeasure i (wholeRiskRadius j))
      (s := C)).mp hmem
  have hsingleton : ∀ x ∈ C,
      ((wholeRiskModel companion).circleMeasure i (wholeRiskRadius j)) {x} = 1 := by
    intro x hx
    rw [hmodel, Measure.restrict_apply (MeasurableSet.singleton x)]
    rw [Measure.restrict_apply
      (MeasurableSet.inter (MeasurableSet.singleton x) C.measurableSet)]
    have hset : ({x} ∩ (C : Set Plane) ∩ (↑wholeRiskField : Set Plane)) = {x} := by
      ext y
      simp [hx, hsubset hx]
    rw [hset]
    simp
  have hpt : Function.Injective (wholeRiskPoint i j) := point_injective hi i j
  have himage : C = Finset.univ.image (wholeRiskPoint i j) := (hc.2 i j).1
  calc
    (wholeRiskModel companion).circleMeasure i (wholeRiskRadius j) =
        ∑ x ∈ C, ((wholeRiskModel companion).circleMeasure i (wholeRiskRadius j)) {x} •
          Measure.dirac x := hsumC
    _ = ∑ x ∈ C, Measure.dirac x := by
      apply Finset.sum_congr rfl
      intro x hx
      simp [hsingleton x hx]
    _ = ∑ k : RiskCell, Measure.dirac (wholeRiskPoint i j k) := by
      rw [himage, Finset.sum_image hpt.injOn]

/-- Apply the finite Dirac-sum rules before specializing the index set. -/
theorem dirac_sum_total {ι : Type*} (s : Finset ι) (p : ι → Plane) :
    (∑ k ∈ s, Measure.dirac (p k)) Set.univ = (s.card : ENNReal) := by
  simp [Measure.finsetSum_apply]

theorem dirac_sum_integrable {ι : Type*} (s : Finset ι) (p : ι → Plane)
    (f : Plane → ℝ) : Integrable f (∑ k ∈ s, Measure.dirac (p k)) := by
  exact integrable_finsetSum_measure.mpr (fun k _ => integrable_dirac (by simp))

theorem dirac_sum_integral {ι : Type*} (s : Finset ι) (p : ι → Plane)
    (f : Plane → ℝ) :
    (∫ x, f x ∂(∑ k ∈ s, Measure.dirac (p k))) = ∑ k ∈ s, f (p k) := by
  rw [integral_finsetSum_measure (fun k _ => integrable_dirac (by simp))]
  exact Finset.sum_congr rfl (fun k _ => integral_dirac f (p k))

end
end SAP.P008a.WH.W1.P.T7_L5

open SAP.P008a SAP.P008a.WH.W1 MeasureTheory
open scoped BigOperators Classical

theorem SAP.P008a.WH.W1.T7_L5_proof : SAP.P008a.WH.W1.T7_L5 := by
  intro hi hc companion i j
  have hmeas := SAP.P008a.WH.W1.P.T7_L5.circle_measure_eq hi hc companion i j
  have htotal : (wholeRiskModel companion).circleMeasure i (wholeRiskRadius j) Set.univ =
      (40000 : ENNReal) := by
    rw [hmeas, SAP.P008a.WH.W1.P.T7_L5.dirac_sum_total]
    exact congrArg (fun n : ℕ => (n : ENNReal))
      (Finset.card_univ.trans (Fintype.card_fin 40000))
  refine ⟨?_, hmeas, ?_, ?_, ?_⟩
  · exact SAP.P008a.WH.W1.P.T7_L5.circle_set_eq companion i j
  · change ((wholeRiskModel companion).circleMeasure i (wholeRiskRadius j) Set.univ).toReal = _
    rw [htotal]
    exact ENNReal.toReal_ofNat 40000
  · rw [htotal]
    exact ENNReal.ofNat_ne_top
  · intro f
    constructor
    · rw [hmeas]
      exact SAP.P008a.WH.W1.P.T7_L5.dirac_sum_integrable _ _ f
    · rw [hmeas]
      exact SAP.P008a.WH.W1.P.T7_L5.dirac_sum_integral _ _ f

