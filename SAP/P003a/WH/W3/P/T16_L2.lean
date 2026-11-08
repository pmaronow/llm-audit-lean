import SAP.P003a.WH.W3.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P003a.WH.W3.P.T16_L2

open SAP.P003a
open SAP.P003a.WH.W3

theorem t16_l2_aux : SAP.P003a.WH.W3.T16_L2 := by
  classical
  intro n m hm hn i
  constructor
  · intro ω
    rcases ω with ⟨j, b, r⟩
    change (insert (if b then i else j.val) r.val).card = m
    have hnot : (if b then i else j.val) ∉ r.val := by
      by_cases hb : b
      · simp [hb, r.property.2.1]
      · simp [hb, j.property, r.property.2.2]
    rw [Finset.card_insert_of_notMem hnot]
    rw [r.property.1]
    omega
  · intro z
    let Arm : Type := {k : Fin n // if i ∈ z.val then k ∉ z.val else k ∈ z.val}
    let toArm : {ω : WholePairSource n m i // wholePairSample ω = z.val} → Arm := fun x => by
      rcases x with ⟨⟨j, b, r⟩, hx⟩
      change (insert (if b then i else j.val) r.val) = z.val at hx
      refine ⟨j.val, ?_⟩
      ·
        by_cases hb : b
        · simp only [if_pos hb] at hx
          have hi : i ∈ z.val := by rw [← hx]; simp
          simp only [if_pos hi]
          have hj : j.val ∉ z.val := by
            rw [← hx]
            simp only [Finset.mem_insert, not_or]
            exact ⟨j.property, r.property.2.2⟩
          exact hj
        · simp only [if_neg hb] at hx
          have hi : i ∉ z.val := by
            rw [← hx]
            simp only [Finset.mem_insert, not_or]
            exact ⟨Ne.symm j.property, r.property.2.1⟩
          simp only [if_neg hi]
          have hj : j.val ∈ z.val := by rw [← hx]; simp
          exact hj
    let fromArm : Arm → {ω : WholePairSource n m i // wholePairSample ω = z.val} := fun k =>
      if hi : i ∈ z.val then
        have hk : k.val ∉ z.val := by simpa [hi] using k.property
        let j : WholePartner n i := ⟨k.val, by
          intro hki
          apply hk
          simpa [hki] using hi⟩
        let r : WholeResidualAssignment n m i j.val :=
          ⟨z.val.erase i, by
            constructor
            · rw [Finset.card_erase_of_mem hi, z.property]
            constructor
            · simp
            · intro h
              exact hk (Finset.mem_erase.mp h).2⟩
        ⟨⟨j, (true, r)⟩, by
          change insert i (z.val.erase i) = z.val
          exact Finset.insert_erase hi⟩
      else
        have hk : k.val ∈ z.val := by simpa [hi] using k.property
        let j : WholePartner n i := ⟨k.val, by
          intro hki
          apply hi
          simpa [hki] using hk⟩
        let r : WholeResidualAssignment n m i j.val :=
          ⟨z.val.erase j.val, by
            constructor
            · rw [Finset.card_erase_of_mem hk, z.property]
            constructor
            · intro h
              exact hi (Finset.mem_erase.mp h).2
            · exact Finset.notMem_erase _ _⟩
        ⟨⟨j, (false, r)⟩, by
          change insert k.val (z.val.erase k.val) = z.val
          exact Finset.insert_erase hk⟩
    have hEquiv : {ω : WholePairSource n m i // wholePairSample ω = z.val} ≃ Arm :=
      { toFun := toArm
        invFun := fromArm
        left_inv := by
          intro x
          rcases x with ⟨⟨j, b, r⟩, hx⟩
          apply Subtype.ext
          cases b with
          | false =>
              change insert j.val r.val = z.val at hx
              have hi : i ∉ z.val := by
                rw [← hx]
                simp [Ne.symm j.property, r.property.2.1]
              have hj : j.val ∈ z.val := by rw [← hx]; simp
              have hr : z.val.erase j.val = r.val := by
                rw [← hx]
                exact Finset.erase_insert r.property.2.2
              simp [fromArm, toArm, hi, hj, hr]
              constructor
              · apply Subtype.ext
                rfl
              · apply Subtype.ext
                exact hr
          | true =>
              change insert i r.val = z.val at hx
              have hi : i ∈ z.val := by rw [← hx]; simp
              have hj : j.val ∉ z.val := by
                rw [← hx]
                simp only [Finset.mem_insert, not_or]
                exact ⟨j.property, r.property.2.2⟩
              have hr : z.val.erase i = r.val := by
                rw [← hx]
                exact Finset.erase_insert r.property.2.1
              simp [fromArm, toArm, hi, hj, hr]
              apply Subtype.ext
              rfl
        right_inv := by
          intro k
          apply Subtype.ext
          by_cases hi : i ∈ z.val
          · simp [toArm, fromArm, hi]
            rfl
          · simp [toArm, fromArm, hi]
            rfl }
    have harm : Fintype.card Arm = m := by
      by_cases hi : i ∈ z.val
      · simp only [Arm, if_pos hi]
        rw [Fintype.card_subtype_compl (p := fun k : Fin n => k ∈ z.val)]
        have hmem : Fintype.card {k : Fin n // k ∈ z.val} = m := by
          rw [Fintype.card_subtype]
          simpa using z.property
        rw [hmem, Fintype.card_fin]
        omega
      · simp only [Arm, hi]
        have hmem : Fintype.card {k : Fin n // k ∈ z.val} = m := by
          rw [Fintype.card_subtype]
          simpa using z.property
        simpa [if_neg hi] using hmem
    simpa [Arm] using (Fintype.card_congr hEquiv).trans harm

end SAP.P003a.WH.W3.P.T16_L2

theorem SAP.P003a.WH.W3.T16_L2_proof : SAP.P003a.WH.W3.T16_L2 :=
  SAP.P003a.WH.W3.P.T16_L2.t16_l2_aux
