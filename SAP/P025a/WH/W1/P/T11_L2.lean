import SAP.P025a.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

namespace SAP.P025a.WH.W1.P.T11_L2
end SAP.P025a.WH.W1.P.T11_L2

theorem SAP.P025a.WH.W1.T11_L2_proof : SAP.P025a.WH.W1.T11_L2 := by
  intro N J hN hJ z y cls hsurj hzy
  have hfiber : ∀ j, 0 < SAP.P025a.wholeClassSize cls j := by
    intro j
    obtain ⟨i, hi⟩ := hsurj j
    apply Finset.card_pos.mpr
    refine ⟨i, ?_⟩
    simp [hi]
  have hcard := Finset.card_eq_sum_card_fiberwise
    (s := (Finset.univ : Finset (Fin N)))
    (t := (Finset.univ : Finset (Fin J))) (f := cls)
    (fun _ _ => Finset.mem_univ _)
  have hsize : (∑ j, SAP.P025a.wholeClassSize cls j) = N := by
    simpa [SAP.P025a.wholeClassSize] using hcard.symm
  have hden :
      (∑ j, (SAP.P025a.wholeClassSize cls j : ℝ)) = (N : ℝ) := by
    exact_mod_cast hsize
  have hmap : ∀ i ∈ (Finset.univ : Finset (Fin N)),
      cls i ∈ (Finset.univ : Finset (Fin J)) := by
    intro i hi
    exact Finset.mem_univ _
  have hnum :
      (∑ j, (SAP.P025a.wholeClassSize cls j : ℝ) * y j) =
        ∑ i, z i := by
    rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ)
      (t := Finset.univ) (g := cls) hmap z]
    apply Finset.sum_congr rfl
    intro j hj
    symm
    calc
      (∑ i ∈ (Finset.univ : Finset (Fin N)) with cls i = j, z i) =
          ∑ i ∈ (Finset.univ : Finset (Fin N)) with cls i = j, y j := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [hzy i, (Finset.mem_filter.mp hi).2]
      _ = (SAP.P025a.wholeClassSize cls j : ℝ) * y j := by
        simp [SAP.P025a.wholeClassSize, Finset.sum_const, nsmul_eq_mul]
  refine ⟨hfiber, hsize, ?_⟩
  unfold SAP.P025a.populationMean
  rw [hnum, hden]

