import SAP.P022.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P022.WH.W1.P.T1_L1

theorem originPartitionMesh_contains_zero : SAP.P022.WH.W1.T1_L1 := by
  classical
  intro P s η hη hη2 hmesh
  rcases hmesh with ⟨hmono, hfirst, hlast, hcell⟩
  by_contra hno
  let A : Finset (Fin (P + 1)) := Finset.univ.filter (fun j => 0 ≤ s j)
  have hA : A.Nonempty := by
    refine ⟨Fin.last P, ?_⟩
    simp [A, hlast]
  let j : Fin (P + 1) := A.min' hA
  have hjmem : j ∈ A := Finset.min'_mem A hA
  have hjnonneg : 0 ≤ s j := (Finset.mem_filter.mp hjmem).2
  have hjne : j ≠ 0 := by
    intro heq
    have hbot : 0 ≤ (⊥ : EReal) := by simpa [heq, hfirst] using hjnonneg
    exact (not_le_of_gt EReal.bot_lt_zero) hbot
  have hjvalne : j.val ≠ 0 := by
    intro hv
    apply hjne
    exact Fin.ext hv
  have hjvalpos : 0 < j.val := Nat.pos_of_ne_zero hjvalne
  let k : Fin (P + 1) := ⟨j.val - 1, by omega⟩
  have hkjval : k.val < j.val := by
    dsimp [k]
    omega
  have hkj : k < j := Fin.lt_iff_val_lt_val.mpr hkjval
  have hknmem : k ∉ A := by
    intro hkmem
    have hmin : j ≤ k := Finset.min'_le A k hkmem
    exact (not_le_of_gt hkj) hmin
  have hknonneg : ¬ 0 ≤ s k := by
    intro hsk
    apply hknmem
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ k, hsk⟩
  have hskneg : s k < 0 := lt_of_not_ge hknonneg
  have hsjpos : 0 < s j := by
    rcases lt_or_eq_of_le hjnonneg with h | h
    · exact h
    · exact False.elim (hno ⟨j, h.symm⟩)
  let i : Fin P := ⟨j.val - 1, by omega⟩
  have hcast : i.castSucc = k := by
    apply Fin.ext
    rfl
  have hsucc : i.succ = j := by
    apply Fin.ext
    dsimp [i]
    omega
  have hcross := hcell i
  rw [hsucc, hcast] at hcross
  simp [SAP.P022.originExtendedLeftCDF, SAP.P022.originExtendedCDF,
    hsjpos, hknonneg] at hcross
  have hηhalf : η / 2 ≤ 1 := by linarith
  linarith

end SAP.P022.WH.W1.P.T1_L1

theorem SAP.P022.WH.W1.T1_L1_proof : SAP.P022.WH.W1.T1_L1 :=
  SAP.P022.WH.W1.P.T1_L1.originPartitionMesh_contains_zero
