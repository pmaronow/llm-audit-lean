import SAP.P012a.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P012a.WH.W1.P.T10_L3

open Finset
open scoped Classical
noncomputable section

theorem shared_not_leaf (D : Data) (i j x : ℕ) :
    u i 0 ∉ r1WholeLeaves D i j x := by
  intro h
  obtain ⟨k, hk, hku⟩ := Finset.mem_image.mp h
  have hpair := Sum.inr.inj hku
  have hx : x = i := congrArg Prod.fst hpair
  have hk0 : k = 0 := congrArg Prod.snd hpair
  subst x
  subst k
  simp at hk

theorem shared_not_sampled (D : Data) (i : ℕ) :
    u i 0 ∉ sampledVertices D := by
  simp [sampledVertices, s, u]

theorem state_ext_fields (A B : State)
    (hv : A.vertices = B.vertices) (he : A.edges = B.edges)
    (ht : A.trait = B.trait) : A = B := by
  cases A with
  | mk av ae at_ =>
    cases B with
    | mk bv be bt =>
      simp_all

end
end SAP.P012a.WH.W1.P.T10_L3

namespace SAP.P012a.WH.W1

open Finset
open scoped Classical
noncomputable section

theorem T10_L3_proof : SAP.P012a.WH.W1.T10_L3 := by
  intro D hD i j hi hj htime hnot hdi hdj τ
  let H : State := r1WholeStart D i j τ
  let q : Vertex := u i 0
  let M : State := addEdge (removeEdge (removeEdge H (s i) q) (s j) q) (s i) (s j)
  have hMEdges : M.edges = insert {s i, s j} ((H.edges.erase {s i, q}).erase {s j, q}) := rfl
  have hHVertices : H.vertices = sampledVertices D ∪ insert q
      (D.sampled.biUnion (r1WholeLeaves D i j)) := rfl
  have hHEdges : H.edges = recruitmentEdges D ∪ {{s i, q}, {s j, q}} ∪
      D.sampled.biUnion (fun x => (r1WholeLeaves D i j x).image (fun w => {s x, w})) := rfl

  have hMNoQ : ∀ e ∈ M.edges, q ∉ e := by
    intro e he hqe
    rw [hMEdges] at he
    rcases Finset.mem_insert.mp he with hnew | herest
    · subst e
      simp [q, s, u] at hqe
    · have hrest : e ∈ H.edges.erase {s i, q} := (Finset.mem_erase.mp herest).2
      have hnotj : e ≠ {s j, q} := (Finset.mem_erase.mp herest).1
      have hnoti : e ≠ {s i, q} := (Finset.mem_erase.mp hrest).1
      have heH : e ∈ H.edges := (Finset.mem_erase.mp hrest).2
      rw [hHEdges] at heH
      change e ∈ (recruitmentEdges D ∪ {{s i, q}, {s j, q}}) ∪
        D.sampled.biUnion (fun x => (r1WholeLeaves D i j x).image (fun w => {s x, w})) at heH
      rcases Finset.mem_union.mp heH with hcore | hleaf
      · rcases Finset.mem_union.mp hcore with hrec | hpairs
        · change e ∈ (nonseeds D).image (fun k => {s (D.parent k), s k}) at hrec
          obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hrec
          simp [q, s, u] at hqe
        · simp only [Finset.mem_insert, Finset.mem_singleton] at hpairs
          rcases hpairs with hEi | hEj
          · exact hnoti hEi
          · exact hnotj hEj
      · change e ∈ D.sampled.biUnion
          (fun x => (r1WholeLeaves D i j x).image (fun w => {s x, w})) at hleaf
        obtain ⟨x, hx, hxedge⟩ := Finset.mem_biUnion.mp hleaf
        obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hxedge
        simp only [Finset.mem_insert, Finset.mem_singleton] at hqe
        rcases hqe with hqs | hqw
        · simp [q, s, u] at hqs
        · have hshared : q ∈ r1WholeLeaves D i j x := hqw ▸ hw
          exact SAP.P012a.WH.W1.P.T10_L3.shared_not_leaf D i j x hshared

  have hqDegree : graphDegree M q = 0 := by
    unfold graphDegree
    have hempty : M.edges.filter (fun e => q ∈ e) = ∅ := by
      ext e
      constructor
      · intro he
        have he' := Finset.mem_filter.mp he
        have hfalse := hMNoQ e he'.1 he'.2
        simp [hfalse]
      · simp
    rw [hempty]
    simp

  have hverts : (cleanup D true M).vertices = H.vertices.erase q := by
    apply Finset.ext
    intro v
    simp only [cleanup, Finset.mem_filter, Finset.mem_erase]
    constructor
    · rintro ⟨hv, hkeep⟩
      refine ⟨?_, ?_⟩
      · intro hvq
        subst v
        rcases hkeep with ⟨_, hsample⟩ | hdegree
        · exact SAP.P012a.WH.W1.P.T10_L3.shared_not_sampled D i hsample
        · rw [hqDegree] at hdegree
          exact hdegree rfl
      · exact hv
    · rintro ⟨hne, hv⟩
      refine ⟨hv, ?_⟩
      by_cases hsample : v ∈ sampledVertices D
      · exact Or.inl ⟨trivial, hsample⟩
      · right
        have hvLeaves : v ∈ D.sampled.biUnion (r1WholeLeaves D i j) := by
          rw [hHVertices] at hv
          rcases Finset.mem_union.mp hv with hsample' | hrest
          · exact False.elim (hsample hsample')
          · rcases Finset.mem_insert.mp hrest with hvq | hvLeaves
            · exact False.elim (hne hvq)
            · exact hvLeaves
        obtain ⟨x, hx, hxleaf⟩ := Finset.mem_biUnion.mp hvLeaves
        obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hxleaf
        have hbase : {s x, u x k} ∈ H.edges := by
          rw [hHEdges]
          exact Finset.mem_union.mpr (Or.inr
            (Finset.mem_biUnion.mpr ⟨x, hx,
              Finset.mem_image.mpr ⟨u x k, hxleaf, rfl⟩⟩))
        have hno : u i 0 ∉ r1WholeLeaves D i j x := SAP.P012a.WH.W1.P.T10_L3.shared_not_leaf D i j x
        have hneI : ({s x, u x k} : Finset Vertex) ≠ {s i, q} := by
          intro he
          rcases (AronowAudit.P012.pair_edge_eq _ _ _ _).mp he with ⟨_, hqeq⟩ | ⟨hs, hu⟩
          · have hqmem : q ∈ r1WholeLeaves D i j x := hqeq ▸ hxleaf
            exact hno (by simpa [q] using hqmem)
          · simp [q, s, u] at hs
        have hneJ : ({s x, u x k} : Finset Vertex) ≠ {s j, q} := by
          intro he
          rcases (AronowAudit.P012.pair_edge_eq _ _ _ _).mp he with ⟨_, hqeq⟩ | ⟨hs, hu⟩
          · have hqmem : q ∈ r1WholeLeaves D i j x := hqeq ▸ hxleaf
            exact hno (by simpa [q] using hqmem)
          · simp [q, s, u] at hs
        have hMbase : {s x, u x k} ∈ M.edges := by
          rw [hMEdges]
          exact Finset.mem_insert_of_mem
            (Finset.mem_erase.mpr ⟨hneJ,
              Finset.mem_erase.mpr ⟨hneI, hbase⟩⟩)
        have hdegree : graphDegree M (u x k) ≠ 0 := by
          unfold graphDegree
          exact Nat.ne_of_gt
            (Finset.card_pos.mpr ⟨{s x, u x k},
              Finset.mem_filter.mpr ⟨hMbase, by simp⟩⟩)
        exact hdegree

  have hresult : cleanup D true M =
      ⟨H.vertices.erase q,
        insert {s i, s j} ((H.edges.erase {s i, q}).erase {s j, q}), τ⟩ := by
    apply SAP.P012a.WH.W1.P.T10_L3.state_ext_fields
    · exact hverts
    · exact hMEdges
    · rfl
  change cleanup D true M = r1WholeEnd D i j τ
  change cleanup D true M =
    ⟨H.vertices.erase q,
      insert {s i, s j} ((H.edges.erase {s i, q}).erase {s j, q}), τ⟩
  exact hresult

end
end SAP.P012a.WH.W1
