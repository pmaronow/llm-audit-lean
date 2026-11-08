import SAP.P003a.WH.W3.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P003a.WH.W3.P.T17_L1

open SAP.P003a

end SAP.P003a.WH.W3.P.T17_L1

theorem SAP.P003a.WH.W3.T17_L1_proof : SAP.P003a.WH.W3.T17_L1 := by
  change Fintype.card (Assignment 5 2) = 10 ∧
    tableCounts wholeZeroTable = ⟨0, 0, 0, 5⟩ ∧
    ∀ z : Assignment 5 2,
      unitObserved (unitOutcomes wholeZeroTable z.val) z.val = ⟨0, 2, 0, 3⟩
  constructor
  · rw [Fintype.card_finset_len]
    norm_num [Nat.choose]
  constructor
  · norm_num [tableCounts, wholeZeroTable]
  · intro z
    have hz : z.val.card = 2 := z.property
    have hcomp : (Finset.univ \ z.val).card = 3 := by
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ,
        Fintype.card_fin]
      omega
    have hcomp' : (Finset.univ.filter fun i : Fin 5 => i ∉ z.val).card = 3 := by
      simpa [Finset.sdiff_eq_filter] using hcomp
    simp [unitObserved, unitOutcomes, wholeZeroTable, hz, hcomp']
