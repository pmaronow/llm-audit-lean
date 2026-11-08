import SAP.P012a.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P012a.WH.W1.P.T1_L4

open Finset
open scoped Classical
noncomputable section

open SAP.P012a
open SAP.P012a.WH.W1

theorem a_relabel (v : Vertex) (hv : v ∉ proposalStart.vertices) (t : Bool) :
    WholeRelabeling proposalData
      (wholeBadPending proposalStart 1 (u 3 0) v t) (proposalBad t) := by
  have hv1 : v ≠ s 1 := by
    intro h
    subst v
    exact hv (by simp [proposalStart])
  have hv2 : v ≠ s 2 := by
    intro h
    subst v
    exact hv (by simp [proposalStart])
  have hv3 : v ≠ u 3 0 := by
    intro h
    subst v
    exact hv (by simp [proposalStart])
  have hn1 : u 4 0 ≠ s 1 := by decide
  have hn2 : u 4 0 ≠ s 2 := by decide
  have hn3 : u 4 0 ≠ u 3 0 := by decide
  have hpos : ∀ x ∈ (wholeBadPending proposalStart 1 (u 3 0) (u 4 0) t).vertices,
      graphDegree (wholeBadPending proposalStart 1 (u 3 0) (u 4 0) t) x ≠ 0 := by
    intro x hx
    simp [wholeBadPending, removeEdge, addVertex, addEdge, proposalStart, s, u] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · apply Nat.ne_of_gt
      apply Finset.card_pos.mpr
      refine ⟨{s 1, u 4 0}, ?_⟩
      simp [graphDegree, wholeBadPending, removeEdge, addVertex, addEdge, proposalStart, s, u]
    · apply Nat.ne_of_gt
      apply Finset.card_pos.mpr
      refine ⟨{s 1, s 2}, ?_⟩
      simp [graphDegree, wholeBadPending, removeEdge, addVertex, addEdge, proposalStart, s, u]
    · apply Nat.ne_of_gt
      apply Finset.card_pos.mpr
      refine ⟨{s 1, s 2}, ?_⟩
      simp [graphDegree, wholeBadPending, removeEdge, addVertex, addEdge, proposalStart, s, u]
    · apply Nat.ne_of_gt
      apply Finset.card_pos.mpr
      refine ⟨{u 3 0, u 4 0}, ?_⟩
      simp [graphDegree, wholeBadPending, removeEdge, addVertex, addEdge, proposalStart, s, u]
  have hcleanV : (proposalBad t).vertices =
      (wholeBadPending proposalStart 1 (u 3 0) (u 4 0) t).vertices := by
    dsimp [proposalBad, cleanup]
    ext x
    simp only [mem_filter]
    constructor
    · intro h
      exact h.1
    · intro hx
      exact ⟨hx, by simpa [wholeBadPending, removeEdge, addVertex, addEdge] using hpos x hx⟩
  have hbase : proposalStart.edges.erase {s 1, u 3 0} = {{s 1, s 2}} := by
    decide
  have hswap1 : (Equiv.swap v (u 4 0)) (s 1) = s 1 := by
    simp [Equiv.swap_apply_def, hv1.symm, hn1.symm]
  have hswap2 : (Equiv.swap v (u 4 0)) (s 2) = s 2 := by
    simp [Equiv.swap_apply_def, hv2.symm, hn2.symm]
  have hswap3 : (Equiv.swap v (u 4 0)) (u 3 0) = u 3 0 := by
    simp [Equiv.swap_apply_def, hv3.symm, hn3.symm]
  let e : Equiv.Perm Vertex := Equiv.swap v (u 4 0)
  refine ⟨e, ?_, ?_, ?_, ?_⟩
  · intro i hi
    have hi' : i = 1 ∨ i = 2 := by simpa [proposalData] using hi
    rcases hi' with rfl | rfl
    · simpa [e] using hswap1
    · simpa [e] using hswap2
  · rw [hcleanV]
    simp [wholeBadPending, removeEdge, addVertex, addEdge, proposalStart, e,
      hswap1, hswap2, hswap3]
  · change (insert {u 3 0, v} (insert {s 1, v}
        (proposalStart.edges.erase {s 1, u 3 0}))).image
        (fun edge => edge.image e) = (proposalBad t).edges
    simp only [proposalBad, cleanup, State.edges]
    simp only [wholeBadPending, removeEdge, addVertex, addEdge, State.edges]
    rw [hbase]
    simp [e, hswap1, hswap2, hswap3]
  · simp only [proposalBad, cleanup, State.trait]
    simp only [wholeBadPending, removeEdge, addVertex, addEdge, State.trait]
    intro x hx
    have hx' : x = v ∨ x = s 1 ∨ x = s 2 ∨ x = u 3 0 := by
      simpa [wholeBadPending, removeEdge, addVertex, addEdge, proposalStart] using hx
    rcases hx' with rfl | rfl | rfl | rfl
    · simp [wholeBadPending, removeEdge, addVertex, addEdge, proposalStart, e,
        Equiv.swap_apply_def, hv1.symm, hv2.symm, hv3.symm,
        hn1.symm, hn2.symm, hn3.symm]
    · simp [wholeBadPending, removeEdge, addVertex, addEdge, proposalStart, e,
        Equiv.swap_apply_def, hv1.symm, hn1.symm]
    · simp [wholeBadPending, removeEdge, addVertex, addEdge, proposalStart, e,
        Equiv.swap_apply_def, hv2.symm, hn2.symm]
    · simp [wholeBadPending, removeEdge, addVertex, addEdge, proposalStart, e,
        Equiv.swap_apply_def, hv3.symm, hn3.symm]

theorem b_relabel (v : Vertex) (hv : v ∉ proposalStartB.vertices) (t : Bool) :
    WholeRelabeling proposalDataB
      (wholeBadPending proposalStartB 2 (u 4 0) v t) (proposalBadB t) := by
  have hv1 : v ≠ s 1 := by
    intro h
    subst v
    exact hv (by simp [proposalStartB])
  have hv2 : v ≠ s 2 := by
    intro h
    subst v
    exact hv (by simp [proposalStartB])
  have hv3 : v ≠ s 3 := by
    intro h
    subst v
    exact hv (by simp [proposalStartB])
  have hv4 : v ≠ u 4 0 := by
    intro h
    subst v
    exact hv (by simp [proposalStartB])
  have hn1 : u 5 0 ≠ s 1 := by decide
  have hn2 : u 5 0 ≠ s 2 := by decide
  have hn3 : u 5 0 ≠ s 3 := by decide
  have hn4 : u 5 0 ≠ u 4 0 := by decide
  have hpos : ∀ x ∈ (wholeBadPending proposalStartB 2 (u 4 0) (u 5 0) t).vertices,
      graphDegree (wholeBadPending proposalStartB 2 (u 4 0) (u 5 0) t) x ≠ 0 := by
    intro x hx
    simp [wholeBadPending, removeEdge, addVertex, addEdge, proposalStartB, s, u] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · apply Nat.ne_of_gt
      apply Finset.card_pos.mpr
      refine ⟨{s 2, u 5 0}, ?_⟩
      simp [graphDegree, wholeBadPending, removeEdge, addVertex, addEdge, proposalStartB, s, u]
    · apply Nat.ne_of_gt
      apply Finset.card_pos.mpr
      refine ⟨{s 1, s 2}, ?_⟩
      simp [graphDegree, wholeBadPending, removeEdge, addVertex, addEdge, proposalStartB, s, u]
    · apply Nat.ne_of_gt
      apply Finset.card_pos.mpr
      refine ⟨{s 1, s 2}, ?_⟩
      simp [graphDegree, wholeBadPending, removeEdge, addVertex, addEdge, proposalStartB, s, u]
    · apply Nat.ne_of_gt
      apply Finset.card_pos.mpr
      refine ⟨{s 2, s 3}, ?_⟩
      simp [graphDegree, wholeBadPending, removeEdge, addVertex, addEdge, proposalStartB, s, u]
    · apply Nat.ne_of_gt
      apply Finset.card_pos.mpr
      refine ⟨{u 4 0, u 5 0}, ?_⟩
      simp [graphDegree, wholeBadPending, removeEdge, addVertex, addEdge, proposalStartB, s, u]
  have hcleanV : (proposalBadB t).vertices =
      (wholeBadPending proposalStartB 2 (u 4 0) (u 5 0) t).vertices := by
    dsimp [proposalBadB, cleanup]
    ext x
    simp only [mem_filter]
    constructor
    · intro h
      exact h.1
    · intro hx
      exact ⟨hx, by simpa [wholeBadPending, removeEdge, addVertex, addEdge] using hpos x hx⟩
  have hbase : proposalStartB.edges.erase {s 2, u 4 0} =
      {{s 1, s 2}, {s 2, s 3}} := by decide
  have hswap1 : (Equiv.swap v (u 5 0)) (s 1) = s 1 := by
    simp [Equiv.swap_apply_def, hv1.symm, hn1.symm]
  have hswap2 : (Equiv.swap v (u 5 0)) (s 2) = s 2 := by
    simp [Equiv.swap_apply_def, hv2.symm, hn2.symm]
  have hswap3 : (Equiv.swap v (u 5 0)) (s 3) = s 3 := by
    simp [Equiv.swap_apply_def, hv3.symm, hn3.symm]
  have hswap4 : (Equiv.swap v (u 5 0)) (u 4 0) = u 4 0 := by
    simp [Equiv.swap_apply_def, hv4.symm, hn4.symm]
  let e : Equiv.Perm Vertex := Equiv.swap v (u 5 0)
  refine ⟨e, ?_, ?_, ?_, ?_⟩
  · intro i hi
    have hi' : i = 1 ∨ i = 2 ∨ i = 3 := by simpa [proposalDataB] using hi
    rcases hi' with rfl | rfl | rfl
    · simpa [e] using hswap1
    · simpa [e] using hswap2
    · simpa [e] using hswap3
  · rw [hcleanV]
    simp [wholeBadPending, removeEdge, addVertex, addEdge, proposalStartB, e,
      hswap1, hswap2, hswap3, hswap4]
  · change (insert {u 4 0, v} (insert {s 2, v}
        (proposalStartB.edges.erase {s 2, u 4 0}))).image
        (fun edge => edge.image e) = (proposalBadB t).edges
    simp only [proposalBadB, cleanup, State.edges]
    simp only [wholeBadPending, removeEdge, addVertex, addEdge, State.edges]
    rw [hbase]
    simp [e, hswap1, hswap2, hswap3, hswap4]
  · simp only [proposalBadB, cleanup, State.trait]
    simp only [wholeBadPending, removeEdge, addVertex, addEdge, State.trait]
    intro x hx
    have hx' : x = v ∨ x = s 1 ∨ x = s 2 ∨ x = s 3 ∨ x = u 4 0 := by
      simpa [wholeBadPending, removeEdge, addVertex, addEdge, proposalStartB] using hx
    rcases hx' with rfl | rfl | rfl | rfl | rfl
    · simp [wholeBadPending, removeEdge, addVertex, addEdge, proposalStartB, e,
        Equiv.swap_apply_def, hv1.symm, hv2.symm, hv3.symm, hv4.symm,
        hn1.symm, hn2.symm, hn3.symm, hn4.symm]
    · simp [wholeBadPending, removeEdge, addVertex, addEdge, proposalStartB, e,
        Equiv.swap_apply_def, hv1.symm, hn1.symm]
    · simp [wholeBadPending, removeEdge, addVertex, addEdge, proposalStartB, e,
        Equiv.swap_apply_def, hv2.symm, hn2.symm]
    · simp [wholeBadPending, removeEdge, addVertex, addEdge, proposalStartB, e,
        Equiv.swap_apply_def, hv3.symm, hn3.symm]
    · simp [wholeBadPending, removeEdge, addVertex, addEdge, proposalStartB, e,
        Equiv.swap_apply_def, hv4.symm, hn4.symm]

end
end SAP.P012a.WH.W1.P.T1_L4

theorem SAP.P012a.WH.W1.T1_L4_proof : SAP.P012a.WH.W1.T1_L4 := by
  exact ⟨SAP.P012a.WH.W1.P.T1_L4.a_relabel, SAP.P012a.WH.W1.P.T1_L4.b_relabel⟩
