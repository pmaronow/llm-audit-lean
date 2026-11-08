import SAP.P001c.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory
open scoped ENNReal

namespace SAP.P001c.WH.W1.P.T57_L2

end SAP.P001c.WH.W1.P.T57_L2

theorem SAP.P001c.WH.W1.T57_L2_proof : SAP.P001c.WH.W1.T57_L2 := by
  intro _ _ ν _ H hH0 htight η hη
  by_cases hηtop : η = ∞
  · refine ⟨∅, isCompact_empty, Set.empty_subset _, ?_⟩
    simp [hηtop]
  · obtain ⟨N, hHcN, hNmeas, hN0⟩ := exists_measurable_superset_of_null hH0
    let A : Set SAP.P001c.CDFSpace := Nᶜ
    have hAmeas : MeasurableSet A := hNmeas.compl
    have hhalf : 0 < η / 2 := ENNReal.div_pos (ne_of_gt hη) (by norm_num)
    obtain ⟨F, hFA, hFclosed, hdiff⟩ :=
      hAmeas.exists_isClosed_sdiff_lt (measure_ne_top ν A) hhalf.ne'
    obtain ⟨C, hCcompact, hCmass⟩ :=
      (isTightMeasureSet_iff_exists_isCompact_measure_compl_le.mp htight) (η / 2) hhalf
    have hCmass' : ν Cᶜ ≤ η / 2 := hCmass ν (by simp)
    have hFH : F ⊆ H := by
      intro x hxF
      by_contra hxH
      exact hFA hxF (hHcN hxH)
    refine ⟨C ∩ F, hCcompact.inter_right hFclosed, Set.inter_subset_right.trans hFH, ?_⟩
    have hcompl : (C ∩ F)ᶜ ⊆ Cᶜ ∪ ((A \ F) ∪ N) := by
      intro x hx
      simp only [Set.mem_compl_iff, Set.mem_inter_iff, not_and_or] at hx
      rcases hx with hxC | hxF
      · exact Set.mem_union_left _ hxC
      · by_cases hxN : x ∈ N
        · exact Set.mem_union_right _ (Set.mem_union_right _ hxN)
        · exact Set.mem_union_right _ (Set.mem_union_left _ ⟨hxN, hxF⟩)
    calc
      ν (C ∩ F)ᶜ ≤ ν (Cᶜ ∪ ((A \ F) ∪ N)) := measure_mono hcompl
      _ ≤ ν Cᶜ + ν ((A \ F) ∪ N) := measure_union_le _ _
      _ ≤ ν Cᶜ + (ν (A \ F) + ν N) := by
        calc
          ν Cᶜ + ν ((A \ F) ∪ N) = ν ((A \ F) ∪ N) + ν Cᶜ := add_comm _ _
          _ ≤ (ν (A \ F) + ν N) + ν Cᶜ :=
            add_le_add_left (measure_union_le (A \ F) N) _
          _ = ν Cᶜ + (ν (A \ F) + ν N) := add_comm _ _
      _ ≤ η / 2 + (η / 2 + 0) := by
        rw [hN0]
        simpa only [add_zero] using add_le_add hCmass' hdiff.le
      _ = η := by rw [add_zero, ENNReal.add_halves]
