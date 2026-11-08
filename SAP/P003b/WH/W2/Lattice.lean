import SAP.P003b.WH.W2.Support

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P003b.WH.W2
open scoped BigOperators
open SAP.P003b.Bridge
attribute [local instance 0] Classical.propDecidable
noncomputable section
set_option maxRecDepth 4000
set_option maxHeartbeats 1600000

theorem possible_candidate (o v : Counts) (hv : Possible o v) : tau v ∈ candidateLattice o := by
  have h := AronowAudit.P003.possible_table_facts (toCounts o) (toCounts v) ((possible_eq o v).mpr hv)
  refine ⟨v.effect,?_,?_⟩
  · exact h.2
  · simp only [tau, tauQ, Rat.cast_div, Rat.cast_intCast, Rat.cast_natCast]
    rw [show v.total = o.total from h.1]

theorem j_eq_accepted (o : Counts) (α : ℝ) :
    wholeJ α o = (↑(accepted α o) : Set ℝ) := by
  ext t
  simp only [wholeJ, Set.mem_ofPred_eq, Finset.mem_coe, accepted, Finset.mem_image,
    List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨_,v,hv,rfl,hp⟩
    exact ⟨v,⟨hv,hp⟩,rfl⟩
  · rintro ⟨v,⟨hv,hp⟩,rfl⟩
    exact ⟨possible_candidate o v hv,v,hv,rfl,hp⟩

theorem j_subset (o : Counts) (α : ℝ) :
    wholeJ α o ⊆ exactInterval α o ∩ candidateLattice o := by
  intro t ht
  refine ⟨?_,ht.1⟩
  rw [j_eq_accepted] at ht
  exact ⟨t,ht,t,ht,le_rfl,le_rfl⟩

theorem cplus_max (o : Counts) (hn : 0 < o.total) :
    wholeCPlus o ∈ candidateLattice o ∧ (∀ t ∈ candidateLattice o, t ≤ wholeCPlus o) := by
  have hR : (0 : ℝ) < o.total := by exact_mod_cast hn
  constructor
  · refine ⟨(o.a : ℤ)-o.c-(o.a+o.b : ℕ)+o.total,?_,?_⟩
    · exact List.mem_map.mpr ⟨o.total,List.mem_range.mpr (by omega),rfl⟩
    · simp [wholeCPlus]
  · rintro t ⟨d,hd,rfl⟩
    obtain ⟨k,hk,rfl⟩ := List.mem_map.mp hd
    have hk' : k ≤ o.total := by have := List.mem_range.mp hk; omega
    dsimp [wholeCPlus]
    apply (div_le_div_iff_of_pos_right hR).mpr
    push_cast
    have hkR : (k : ℝ) ≤ o.total := by exact_mod_cast hk'
    linarith

theorem balanced_j (o : Counts) (α : ℝ)
    (ho : 0 < o.a+o.b ∧ o.a+o.b = o.c+o.d) (hα : 0 < α ∧ α < 1) :
    wholeJ α o = exactInterval α o ∩ candidateLattice o ∧
    (Set.Icc (estimate o) (wholeCPlus o) ∩ wholeJ α o) =
      Set.Icc (estimate o) (upper α o) ∩ candidateLattice o ∧
    (accepted α o).Nonempty ∧ lower α o ≤ estimate o ∧ estimate o ≤ upper α o ∧
    upper α o ≤ wholeCPlus o ∧ wholeCPlus o ∈ candidateLattice o ∧
    (∀ t ∈ candidateLattice o, t ≤ wholeCPlus o) := by
  have h := AronowAudit.P003.Wave1.corrected_lattice_interval_proof (toCounts o) α ho hα
  simp only [accepted_eq,interval_eq,candidateLattice_eq,estimate_eq,upper_eq,total_eq] at h
  have hc : wholeCPlus o = ((o.a : ℝ)-o.c+(o.a+o.b))/o.total := by
    have ht : o.total = 2*(o.a+o.b) := by dsimp [Counts.total]; omega
    dsimp [wholeCPlus]
    rw [ht]
    push_cast
    ring
  have hm := balanced_membership o α ho hα
  have hne : (accepted α o).Nonempty := ⟨estimate o,hm.1⟩
  have hmax := cplus_max o (by dsimp [Counts.total]; omega)
  refine ⟨by rw [j_eq_accepted]; exact h.1,?_,hne,hm.2.2.1,hm.2.2.2,?_,hmax⟩
  · rw [j_eq_accepted, hc]
    exact h.2
  · have hu : upper α o ∈ accepted α o := hne.csSup_mem
    have hu' : upper α o ∈ wholeJ α o := by rwa [j_eq_accepted]
    exact hmax.2 _ hu'.1

end
end SAP.P003b.WH.W2
