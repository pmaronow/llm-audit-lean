import SAP.P012a.WH.W2.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P012a.WH.W2.P.T2_L3

open SAP.P012a Finset
open scoped Classical

end SAP.P012a.WH.W2.P.T2_L3

open SAP.P012a Finset
open scoped Classical

theorem SAP.P012a.WH.W2.T2_L3_proof : SAP.P012a.WH.W2.T2_L3 := by
  intro D H i j v w hD hH hi hj hne hnot hv hw hiv hjw
  have hv' := Finset.mem_sdiff.mp hv
  have hw' := Finset.mem_sdiff.mp hw
  obtain ⟨l, hl, hlj⟩ := hH.1.2 {j, w} hjw
  have hlj' : s l = j := by
    rcases mem_insert.mp hlj with h | h
    · exact h
    · exact False.elim (hw'.2 ((mem_singleton.mp h) ▸ mem_image_of_mem s hl))
  have hjs : j ∈ sampledVertices D := by
    rw [← hlj']
    exact mem_image_of_mem s hl
  have hli : i ≠ l := by
    intro h
    apply hne
    rw [← hlj', h]
  have hvS : v ∉ sampledVertices D := hv'.2
  have hwS : w ∉ sampledVertices D := hw'.2
  have hkv : ∀ k ∈ D.sampled, s k ≠ v := by
    intro k hk h
    exact hvS (h ▸ mem_image_of_mem s hk)
  have hkw : ∀ k ∈ D.sampled, s k ≠ w := by
    intro k hk h
    exact hwS (h ▸ mem_image_of_mem s hk)
  have hedge_ne : ({s i, v} : Finset Vertex) ≠ {j, w} := by
    intro heq
    rcases (AronowAudit.P012.pair_edge_eq (s i) v j w).mp heq with h | h
    · exact hne h.1
    · exact hwS (h.1 ▸ mem_image_of_mem s hi)
  have hr1 : {s i, v} ∉ recruitmentEdges D := by
    intro he
    have hmem := AronowAudit.P012.recruitment_edge_sampled (Bridge.data D)
      (by simpa using hD) _ (by simpa using he)
    exact hvS (by simpa using hmem (by simp))
  have hr2 : {j, w} ∉ recruitmentEdges D := by
    intro he
    have hmem := AronowAudit.P012.recruitment_edge_sampled (Bridge.data D)
      (by simpa using hD) _ (by simpa using he)
    exact hwS (by simpa using hmem (by simp))
  let R := removeEdge (removeEdge H (s i) v) j w
  let A := addEdge R (s i) j
  have hjw' : {j, w} ∈ (removeEdge H (s i) v).edges :=
    mem_erase.mpr ⟨Ne.symm hedge_ne, hjw⟩
  have hadd_absent : {s i, j} ∉ R.edges := by
    intro he
    exact hnot (mem_erase.mp (mem_erase.mp he).2).2
  have hloss (x : Vertex) :
      graphDegree R x + (if x ∈ ({s i, v} : Finset Vertex) then 1 else 0) +
        (if x ∈ ({j, w} : Finset Vertex) then 1 else 0) = graphDegree H x := by
    have h1 := AronowAudit.P012.degree_remove_step (Bridge.state H) (s i) v x
      (by simpa using hiv)
    have h2 := AronowAudit.P012.degree_remove_step
      (Bridge.state (removeEdge H (s i) v)) j w x (by simpa using hjw')
    have h1' : graphDegree (removeEdge H (s i) v) x +
        (if x ∈ ({s i, v} : Finset Vertex) then 1 else 0) = graphDegree H x := by
      simpa using h1
    have h2' : graphDegree (removeEdge (removeEdge H (s i) v) j w) x +
        (if x ∈ ({j, w} : Finset Vertex) then 1 else 0) =
          graphDegree (removeEdge H (s i) v) x := by
      simpa using h2
    dsimp [R]
    omega
  refine ⟨hjs, hedge_ne, hr1, hr2, ?_, ?_, ?_, ?_⟩
  · intro x
    exact hloss x
  · intro k hk
    have hI : (s k ∈ ({s i, v} : Finset Vertex)) ↔ k = i := by
      constructor
      · intro hx
        rcases Finset.mem_insert.mp hx with hi' | hv'
        · simpa [s] using hi'
        · exact False.elim (hkv k hk (Finset.mem_singleton.mp hv'))
      · intro h
        subst k
        simp
    have hJ : (s k ∈ ({j, w} : Finset Vertex)) ↔ k = l := by
      rw [← hlj']
      constructor
      · intro hx
        rcases Finset.mem_insert.mp hx with hl' | hw'
        · simpa [s] using hl'
        · exact False.elim (hkw k hk (Finset.mem_singleton.mp hw'))
      · intro h
        subst k
        simp
    have hA : (s k ∈ ({s i, j} : Finset Vertex)) ↔ k = i ∨ k = l := by
      rw [← hlj']
      constructor
      · intro hx
        rcases Finset.mem_insert.mp hx with hi' | hl'
        · exact Or.inl (by simpa [s] using hi')
        · exact Or.inr (by simpa [s] using Finset.mem_singleton.mp hl')
      · rintro (h | h)
        · subst k
          simp
        · subst k
          simp
    have h1 := hloss (s k)
    have h2ext := AronowAudit.P012.degree_add_step (Bridge.state R) (s i) j (s k)
      (by simpa using hadd_absent)
    have h2 : graphDegree A (s k) = graphDegree R (s k) +
        (if s k ∈ ({s i, j} : Finset Vertex) then 1 else 0) := by
      simpa only [A, Bridge.addEdge_eq, Bridge.graphDegree_eq] using h2ext
    have hli' : i ≠ l := hli
    simp only [hI, hJ, hA, A, R] at h1 h2
    by_cases hki : k = i
    · subst k
      simp [hli] at h1 h2 ⊢
      omega
    · by_cases hkl : k = l
      · subst k
        simp [Ne.symm hli] at h1 h2 ⊢
        omega
      · simp [hki, hkl] at h1 h2 ⊢
        omega
  · have hvA : v ∈ A.vertices := by
      simpa [A, R, addEdge, removeEdge] using hv'.1
    change v ∉ A.vertices.filter (fun x =>
      (true = true ∧ x ∈ sampledVertices D) ∨ graphDegree A x ≠ 0) ↔
        graphDegree A v = 0
    simp [hvA, hvS]
  · have hwA : w ∈ A.vertices := by
      simpa [A, R, addEdge, removeEdge] using hw'.1
    change w ∉ A.vertices.filter (fun x =>
      (true = true ∧ x ∈ sampledVertices D) ∨ graphDegree A x ≠ 0) ↔
        graphDegree A w = 0
    simp [hwA, hwS]

