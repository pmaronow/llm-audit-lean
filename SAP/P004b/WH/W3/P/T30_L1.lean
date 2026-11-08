import SAP.P004b.WH.W3.Leaves
import AronowAudit.P004.P004_ConditioningCompletion

set_option autoImplicit false
set_option relaxedAutoImplicit false

open SAP.P004b
open AronowAudit.P004.ConditioningCompletion
open scoped Classical

theorem SAP.P004b.WH.W3.T30_L1_proof : SAP.P004b.WH.W3.T30_L1 := by
  intro N n1 hn1lo hn1hi i a
  let α := {j : Fin N // j ≠ i}
  let k := n1 - (if a then 1 else 0)
  have hα : Fintype.card α = N - 1 := by
    dsimp [α]
    rw [Fintype.card_subtype_compl (p := fun j : Fin N => j = i)]
    simp
  have hk : k ≤ Fintype.card α := by
    rw [hα]
    dsimp [k]
    cases a <;> simp <;> omega
  obtain ⟨t, ht, htcard⟩ := Finset.exists_subset_card_eq (s := Finset.univ) hk
  let u : α → Bool := fun j => if j ∈ t then true else false
  have hu (j : α) : u j = true ↔ j ∈ t := by
    simp [u]
  have hcount : (Finset.univ.filter (fun j : α => u j = true)).card = k := by
    have hfilter : Finset.univ.filter (fun j : α => u j = true) = t := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact hu j
    rw [hfilter, htcard]
  have htotal : (Finset.univ.filter (fun j : Fin N => AronowAudit.P004.joinAssignment i a u j = true)).card = n1 := by
    rw [AronowAudit.P004.ConditioningCompletion.join_treated_count, hcount]
    cases a <;> simp [k] <;> omega
  let z : Assignment N := AronowAudit.P004.joinAssignment i a u
  have hz : z ∈ completeSupport N n1 := by
    change z ∈ Finset.univ.filter (fun z : Assignment N =>
      (Finset.univ.filter (fun j => z j = true)).card = n1)
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, by simpa [z] using htotal⟩
  have hzi : z i = a := by
    simp [z, AronowAudit.P004.joinAssignment]
  have hcond : z ∈ (completeSupport N n1).filter (fun z => z i = a) := by
    exact Finset.mem_filter.mpr ⟨hz, hzi⟩
  have huSupport : u ∈ remainderSupport n1 i a := by
    change u ∈ Finset.univ.filter (fun v : α → Bool =>
      (Finset.univ.filter (fun j => v j = true)).card =
        n1 - (if a then 1 else 0))
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, by simpa [k] using hcount⟩
  constructor
  · exact Finset.card_pos.mpr ⟨z, hcond⟩
  · exact Finset.card_pos.mpr ⟨u, huSupport⟩

