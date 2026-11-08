import SAP.P012a.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P012a.WH.W1.P.T1_L3

open Finset
open scoped Classical

private theorem graphDegree_pos_of_incident (H : SAP.P012a.State) (x : SAP.P012a.Vertex)
    (h : ∃ e ∈ H.edges, x ∈ e) : 0 < SAP.P012a.graphDegree H x := by
  rcases h with ⟨e, he, hx⟩
  unfold SAP.P012a.graphDegree
  exact Finset.card_pos.mpr ⟨e, Finset.mem_filter.mpr ⟨he, hx⟩⟩

private theorem cleanup_false_eq_of_degree_ne_zero (D : SAP.P012a.Data) (H : SAP.P012a.State)
    (hdeg : ∀ x ∈ H.vertices, SAP.P012a.graphDegree H x ≠ 0) :
    SAP.P012a.cleanup D false H = H := by
  cases H with
  | mk verts edges tr =>
    have hdeg' : ∀ x ∈ verts,
        SAP.P012a.graphDegree ⟨verts, edges, tr⟩ x ≠ 0 := by
      simpa using hdeg
    have hverts :
        (verts.filter (fun x => (false = true ∧ x ∈ SAP.P012a.sampledVertices D) ∨
          SAP.P012a.graphDegree ⟨verts, edges, tr⟩ x ≠ 0)) = verts := by
      ext x
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨hx, _⟩
        exact hx
      · intro hx
        exact ⟨hx, Or.inr (hdeg' x hx)⟩
    apply congrArg (fun vs : Finset SAP.P012a.Vertex => SAP.P012a.State.mk vs edges tr)
    exact hverts

private theorem outputA (v : SAP.P012a.Vertex) (hv : v ∉ SAP.P012a.proposalStart.vertices)
    (t : Bool) : SAP.P012a.WholeBadOutput SAP.P012a.proposalData
      SAP.P012a.proposalStart 1 (SAP.P012a.u 3 0) v t := by
  classical
  let P := SAP.P012a.wholeBadPending SAP.P012a.proposalStart 1 (SAP.P012a.u 3 0) v t
  have hv' : v ≠ SAP.P012a.s 1 ∧ v ≠ SAP.P012a.s 2 ∧ v ≠ SAP.P012a.u 3 0 := by
    simpa [SAP.P012a.proposalStart, SAP.P012a.s, SAP.P012a.u] using hv
  have hV : P.vertices = insert v SAP.P012a.proposalStart.vertices := by
    simp [P, SAP.P012a.wholeBadPending, SAP.P012a.addVertex, SAP.P012a.addEdge,
      SAP.P012a.removeEdge]
  have hE : P.edges = insert {SAP.P012a.u 3 0, v}
      (insert {SAP.P012a.s 1, v}
        (SAP.P012a.proposalStart.edges.erase {SAP.P012a.s 1, SAP.P012a.u 3 0})) := by
    rfl
  have hinc : ∀ x ∈ P.vertices, ∃ e ∈ P.edges, x ∈ e := by
    intro x hx
    rw [hV] at hx
    simp only [Finset.mem_insert] at hx
    rcases hx with hxv | hx
    · subst x
      exact ⟨{SAP.P012a.u 3 0, v}, by rw [hE]; simp, by simp⟩
    · simp [SAP.P012a.proposalStart] at hx
      rcases hx with rfl | rfl | rfl
      · exact ⟨{SAP.P012a.s 1, SAP.P012a.s 2}, by rw [hE]; simp [SAP.P012a.proposalStart, SAP.P012a.s, SAP.P012a.u, hv'], by simp⟩
      · exact ⟨{SAP.P012a.s 1, SAP.P012a.s 2}, by rw [hE]; simp [SAP.P012a.proposalStart, SAP.P012a.s, SAP.P012a.u, hv'], by simp⟩
      · exact ⟨{SAP.P012a.u 3 0, v}, by rw [hE]; simp [SAP.P012a.s, SAP.P012a.u, hv'], by simp⟩
  have hdeg : ∀ x ∈ P.vertices, SAP.P012a.graphDegree P x ≠ 0 := by
    intro x hx
    exact ne_of_gt (graphDegree_pos_of_incident P x (hinc x hx))
  have hclean : SAP.P012a.cleanup SAP.P012a.proposalData false P = P :=
    cleanup_false_eq_of_degree_ne_zero SAP.P012a.proposalData P hdeg
  have hvs1 : Sum.inl 1 ≠ v := by simpa [SAP.P012a.s] using Ne.symm hv'.1
  have hvs2 : Sum.inl 2 ≠ v := by simpa [SAP.P012a.s] using Ne.symm hv'.2.1
  have hvsOld : Sum.inr (3, 0) ≠ v := by simpa [SAP.P012a.u] using Ne.symm hv'.2.2
  have hNo : ∀ k ∈ SAP.P012a.proposalData.sampled,
      {SAP.P012a.s k, SAP.P012a.u 3 0} ∉ P.edges := by
    intro k hk
    have hk' : k = 1 ∨ k = 2 := by simpa [SAP.P012a.proposalData] using hk
    rcases hk' with rfl | rfl
    · rw [hE]
      simp [SAP.P012a.proposalStart, SAP.P012a.s, SAP.P012a.u] <;>
        exact ⟨Ne.symm hv'.1, Ne.symm hv'.2.2⟩
    · rw [hE]
      simp [SAP.P012a.proposalStart, SAP.P012a.s, SAP.P012a.u] <;>
        exact Ne.symm hv'.2.1
  change SAP.P012a.cleanup SAP.P012a.proposalData false P = P ∧
    P.vertices = insert v SAP.P012a.proposalStart.vertices ∧
    P.edges = insert {SAP.P012a.u 3 0, v}
      (insert {SAP.P012a.s 1, v}
        (SAP.P012a.proposalStart.edges.erase {SAP.P012a.s 1, SAP.P012a.u 3 0})) ∧
    P.trait = Function.update SAP.P012a.proposalStart.trait v t ∧
    (∀ x ∈ P.vertices, SAP.P012a.graphDegree P x ≠ 0) ∧
    SAP.P012a.u 3 0 ∉ SAP.P012a.sampledVertices SAP.P012a.proposalData ∧
    v ∉ SAP.P012a.sampledVertices SAP.P012a.proposalData ∧
    {SAP.P012a.u 3 0, v} ∈ P.edges ∧
    (∀ k ∈ SAP.P012a.proposalData.sampled, {SAP.P012a.s k, SAP.P012a.u 3 0} ∉ P.edges) ∧
    SAP.P012a.sampledVertices SAP.P012a.proposalData ⊆ P.vertices ∧
    SAP.P012a.recruitmentEdges SAP.P012a.proposalData ⊆ P.edges ∧
    (∀ k ∈ SAP.P012a.proposalData.sampled,
      P.trait (SAP.P012a.s k) = SAP.P012a.proposalData.trait k) ∧
    (∀ k ∈ SAP.P012a.proposalData.sampled,
      SAP.P012a.graphDegree P (SAP.P012a.s k) = SAP.P012a.proposalData.degree k) ∧
    ¬ SAP.P012a.Compatible SAP.P012a.proposalData P
  refine ⟨hclean, hV, hE, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · exact hdeg
  · simp [SAP.P012a.proposalData, SAP.P012a.sampledVertices, SAP.P012a.s, SAP.P012a.u]
  · intro hs
    simp [SAP.P012a.sampledVertices, SAP.P012a.proposalData, SAP.P012a.s] at hs
    rcases hs with hs | hs
    · exact hv'.1 hs
    · exact hv'.2.1 hs
  · simp [hE, SAP.P012a.proposalStart, SAP.P012a.s, SAP.P012a.u, hv']
  · exact hNo
  · rw [hV]
    exact (show SAP.P012a.sampledVertices SAP.P012a.proposalData ⊆
      SAP.P012a.proposalStart.vertices by decide).trans
        (Finset.subset_insert v SAP.P012a.proposalStart.vertices)
  · intro e he
    have he' : ∃ i ∈ SAP.P012a.nonseeds SAP.P012a.proposalData,
        {SAP.P012a.s (SAP.P012a.proposalData.parent i), SAP.P012a.s i} = e := by
      simpa [SAP.P012a.recruitmentEdges] using he
    rcases he' with ⟨i, hi, he'⟩
    have hi' : i = 2 := by
      simp [SAP.P012a.nonseeds, SAP.P012a.proposalData] at hi
      omega
    subst i
    have horig : {SAP.P012a.s 1, SAP.P012a.s 2} ∈ SAP.P012a.proposalStart.edges := by
      simp [SAP.P012a.proposalStart, SAP.P012a.s, SAP.P012a.u]
    have hne : ({SAP.P012a.s 1, SAP.P012a.s 2} : Finset SAP.P012a.Vertex) ≠
        {SAP.P012a.s 1, SAP.P012a.u 3 0} := by decide
    have herase : {SAP.P012a.s 1, SAP.P012a.s 2} ∈
        SAP.P012a.proposalStart.edges.erase {SAP.P012a.s 1, SAP.P012a.u 3 0} :=
      Finset.mem_erase.mpr ⟨hne, horig⟩
    rw [← he']
    rw [hE]
    exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem herase)
  · intro k hk
    have hk' : k = 1 ∨ k = 2 := by simpa [SAP.P012a.proposalData] using hk
    rcases hk' with rfl | rfl
    · change Function.update SAP.P012a.proposalStart.trait v t (SAP.P012a.s 1) = false
      rw [Function.update_of_ne (Ne.symm hv'.1)]
      rfl
    · change Function.update SAP.P012a.proposalStart.trait v t (SAP.P012a.s 2) = true
      rw [Function.update_of_ne (Ne.symm hv'.2.1)]
      rfl
  · constructor
    · intro k hk
      have hk' : k = 1 ∨ k = 2 := by simpa [SAP.P012a.proposalData] using hk
      rcases hk' with rfl | rfl
      · simp [SAP.P012a.graphDegree, SAP.P012a.proposalData,
          SAP.P012a.proposalStart, SAP.P012a.s, SAP.P012a.u, P,
          hvs1, hvs2, hvsOld,
          SAP.P012a.wholeBadPending, SAP.P012a.addVertex, SAP.P012a.addEdge,
          SAP.P012a.removeEdge, Finset.filter_insert, Finset.filter_erase,
          Finset.filter_singleton]
        have hErase :
            (({{Sum.inl 1, Sum.inl 2}, {Sum.inl 1, Sum.inr (3, 0)}} :
              Finset (Finset SAP.P012a.Vertex)).erase {Sum.inl 1, Sum.inr (3, 0)}) =
              {{Sum.inl 1, Sum.inl 2}} := by decide
        rw [hErase]
        have hnot : ({Sum.inl 1, v} : Finset SAP.P012a.Vertex) ∉
            ({{Sum.inl 1, Sum.inl 2}} : Finset (Finset SAP.P012a.Vertex)) := by
          simp [hvs1, hvs2, Ne.symm hvs1, Ne.symm hvs2]
        rw [Finset.card_insert_of_notMem hnot]
        simp
      · simp [SAP.P012a.graphDegree, SAP.P012a.proposalData,
          SAP.P012a.proposalStart, SAP.P012a.s, SAP.P012a.u, P,
          hvs1, hvs2, hvsOld,
          SAP.P012a.wholeBadPending, SAP.P012a.addVertex, SAP.P012a.addEdge,
          SAP.P012a.removeEdge, Finset.filter_insert, Finset.filter_erase,
          Finset.filter_singleton]
    · intro hcompat
      have holdV : SAP.P012a.u 3 0 ∈ P.vertices := by
        rw [hV]
        simp [SAP.P012a.proposalStart, SAP.P012a.s, SAP.P012a.u]
      have holdS : SAP.P012a.u 3 0 ∉ SAP.P012a.sampledVertices SAP.P012a.proposalData := by
        simp [SAP.P012a.proposalData, SAP.P012a.sampledVertices, SAP.P012a.s,
          SAP.P012a.u]
      obtain ⟨i, hi, he⟩ := hcompat.2.2.2.2.1 _ holdV holdS
      exact hNo i hi he

private theorem outputB (v : SAP.P012a.Vertex) (hv : v ∉ SAP.P012a.proposalStartB.vertices)
    (t : Bool) : SAP.P012a.WholeBadOutput SAP.P012a.proposalDataB
      SAP.P012a.proposalStartB 2 (SAP.P012a.u 4 0) v t := by
  classical
  let P := SAP.P012a.wholeBadPending SAP.P012a.proposalStartB 2 (SAP.P012a.u 4 0) v t
  have hv' : v ≠ SAP.P012a.s 1 ∧ v ≠ SAP.P012a.s 2 ∧
      v ≠ SAP.P012a.s 3 ∧ v ≠ SAP.P012a.u 4 0 := by
    simpa [SAP.P012a.proposalStartB, SAP.P012a.s, SAP.P012a.u] using hv
  have hV : P.vertices = insert v SAP.P012a.proposalStartB.vertices := by
    simp [P, SAP.P012a.wholeBadPending, SAP.P012a.addVertex, SAP.P012a.addEdge,
      SAP.P012a.removeEdge]
  have hE : P.edges = insert {SAP.P012a.u 4 0, v}
      (insert {SAP.P012a.s 2, v}
        (SAP.P012a.proposalStartB.edges.erase {SAP.P012a.s 2, SAP.P012a.u 4 0})) := by
    rfl
  have hinc : ∀ x ∈ P.vertices, ∃ e ∈ P.edges, x ∈ e := by
    intro x hx
    rw [hV] at hx
    simp only [Finset.mem_insert] at hx
    rcases hx with hxv | hx
    · subst x
      exact ⟨{SAP.P012a.u 4 0, v}, by rw [hE]; simp, by simp⟩
    · simp [SAP.P012a.proposalStartB] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact ⟨{SAP.P012a.s 1, SAP.P012a.s 2}, by rw [hE]; simp [SAP.P012a.proposalStartB, SAP.P012a.s, SAP.P012a.u, hv'], by simp⟩
      · exact ⟨{SAP.P012a.s 1, SAP.P012a.s 2}, by rw [hE]; simp [SAP.P012a.proposalStartB, SAP.P012a.s, SAP.P012a.u, hv'], by simp⟩
      · exact ⟨{SAP.P012a.s 2, SAP.P012a.s 3}, by rw [hE]; simp [SAP.P012a.proposalStartB, SAP.P012a.s, SAP.P012a.u, hv'], by simp⟩
      · exact ⟨{SAP.P012a.u 4 0, v}, by rw [hE]; simp [SAP.P012a.s, SAP.P012a.u, hv'], by simp⟩
  have hdeg : ∀ x ∈ P.vertices, SAP.P012a.graphDegree P x ≠ 0 := by
    intro x hx
    exact ne_of_gt (graphDegree_pos_of_incident P x (hinc x hx))
  have hclean : SAP.P012a.cleanup SAP.P012a.proposalDataB false P = P :=
    cleanup_false_eq_of_degree_ne_zero SAP.P012a.proposalDataB P hdeg
  have hvs1 : Sum.inl 1 ≠ v := by simpa [SAP.P012a.s] using Ne.symm hv'.1
  have hvs2 : Sum.inl 2 ≠ v := by simpa [SAP.P012a.s] using Ne.symm hv'.2.1
  have hvs3 : Sum.inl 3 ≠ v := by simpa [SAP.P012a.s] using Ne.symm hv'.2.2.1
  have hvsOld : Sum.inr (4, 0) ≠ v := by simpa [SAP.P012a.u] using Ne.symm hv'.2.2.2
  have hNo : ∀ k ∈ SAP.P012a.proposalDataB.sampled,
      {SAP.P012a.s k, SAP.P012a.u 4 0} ∉ P.edges := by
    intro k hk
    have hk' : k = 1 ∨ k = 2 ∨ k = 3 := by simpa [SAP.P012a.proposalDataB] using hk
    rcases hk' with rfl | rfl | rfl
    · rw [hE]
      simp [SAP.P012a.proposalStartB, SAP.P012a.s, SAP.P012a.u] <;>
        exact Ne.symm hv'.1
    · rw [hE]
      simp [SAP.P012a.proposalStartB, SAP.P012a.s, SAP.P012a.u] <;>
        exact ⟨Ne.symm hv'.2.1, Ne.symm hv'.2.2.2⟩
    · rw [hE]
      simp [SAP.P012a.proposalStartB, SAP.P012a.s, SAP.P012a.u] <;>
        exact Ne.symm hv'.2.2.1
  change SAP.P012a.cleanup SAP.P012a.proposalDataB false P = P ∧
    P.vertices = insert v SAP.P012a.proposalStartB.vertices ∧
    P.edges = insert {SAP.P012a.u 4 0, v}
      (insert {SAP.P012a.s 2, v}
        (SAP.P012a.proposalStartB.edges.erase {SAP.P012a.s 2, SAP.P012a.u 4 0})) ∧
    P.trait = Function.update SAP.P012a.proposalStartB.trait v t ∧
    (∀ x ∈ P.vertices, SAP.P012a.graphDegree P x ≠ 0) ∧
    SAP.P012a.u 4 0 ∉ SAP.P012a.sampledVertices SAP.P012a.proposalDataB ∧
    v ∉ SAP.P012a.sampledVertices SAP.P012a.proposalDataB ∧
    {SAP.P012a.u 4 0, v} ∈ P.edges ∧
    (∀ k ∈ SAP.P012a.proposalDataB.sampled, {SAP.P012a.s k, SAP.P012a.u 4 0} ∉ P.edges) ∧
    SAP.P012a.sampledVertices SAP.P012a.proposalDataB ⊆ P.vertices ∧
    SAP.P012a.recruitmentEdges SAP.P012a.proposalDataB ⊆ P.edges ∧
    (∀ k ∈ SAP.P012a.proposalDataB.sampled,
      P.trait (SAP.P012a.s k) = SAP.P012a.proposalDataB.trait k) ∧
    (∀ k ∈ SAP.P012a.proposalDataB.sampled,
      SAP.P012a.graphDegree P (SAP.P012a.s k) = SAP.P012a.proposalDataB.degree k) ∧
    ¬ SAP.P012a.Compatible SAP.P012a.proposalDataB P
  refine ⟨hclean, hV, hE, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · exact hdeg
  · simp [SAP.P012a.proposalDataB, SAP.P012a.sampledVertices, SAP.P012a.s, SAP.P012a.u]
  · intro hs
    simp [SAP.P012a.sampledVertices, SAP.P012a.proposalDataB, SAP.P012a.s] at hs
    rcases hs with hs | hs | hs
    · exact hv'.1 hs
    · exact hv'.2.1 hs
    · exact hv'.2.2.1 hs
  · simp [hE, SAP.P012a.proposalStartB, SAP.P012a.s, SAP.P012a.u, hv']
  · exact hNo
  · rw [hV]
    exact (show SAP.P012a.sampledVertices SAP.P012a.proposalDataB ⊆
      SAP.P012a.proposalStartB.vertices by decide).trans
        (Finset.subset_insert v SAP.P012a.proposalStartB.vertices)
  · intro e he
    have he' : ∃ i ∈ SAP.P012a.nonseeds SAP.P012a.proposalDataB,
        {SAP.P012a.s (SAP.P012a.proposalDataB.parent i), SAP.P012a.s i} = e := by
      simpa [SAP.P012a.recruitmentEdges] using he
    rcases he' with ⟨i, hi, he'⟩
    have hi' : i = 2 ∨ i = 3 := by
      simp [SAP.P012a.nonseeds, SAP.P012a.proposalDataB] at hi
      omega
    rcases hi' with rfl | rfl
    · rw [← he']
      rw [hE]
      have horig : {SAP.P012a.s 1, SAP.P012a.s 2} ∈ SAP.P012a.proposalStartB.edges := by
        simp [SAP.P012a.proposalStartB, SAP.P012a.s, SAP.P012a.u]
      have hne : ({SAP.P012a.s 1, SAP.P012a.s 2} : Finset SAP.P012a.Vertex) ≠
          {SAP.P012a.s 2, SAP.P012a.u 4 0} := by decide
      have herase : {SAP.P012a.s 1, SAP.P012a.s 2} ∈
          SAP.P012a.proposalStartB.edges.erase {SAP.P012a.s 2, SAP.P012a.u 4 0} :=
        Finset.mem_erase.mpr ⟨hne, horig⟩
      exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem herase)
    · rw [← he']
      rw [hE]
      have horig : {SAP.P012a.s 2, SAP.P012a.s 3} ∈ SAP.P012a.proposalStartB.edges := by
        simp [SAP.P012a.proposalStartB, SAP.P012a.s, SAP.P012a.u]
      have hne : ({SAP.P012a.s 2, SAP.P012a.s 3} : Finset SAP.P012a.Vertex) ≠
          {SAP.P012a.s 2, SAP.P012a.u 4 0} := by decide
      have herase : {SAP.P012a.s 2, SAP.P012a.s 3} ∈
          SAP.P012a.proposalStartB.edges.erase {SAP.P012a.s 2, SAP.P012a.u 4 0} :=
        Finset.mem_erase.mpr ⟨hne, horig⟩
      exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem herase)
  · intro k hk
    have hk' : k = 1 ∨ k = 2 ∨ k = 3 := by simpa [SAP.P012a.proposalDataB] using hk
    rcases hk' with rfl | rfl | rfl
    · change Function.update SAP.P012a.proposalStartB.trait v t (SAP.P012a.s 1) = false
      rw [Function.update_of_ne (Ne.symm hv'.1)]
      rfl
    · change Function.update SAP.P012a.proposalStartB.trait v t (SAP.P012a.s 2) = true
      rw [Function.update_of_ne (Ne.symm hv'.2.1)]
      rfl
    · change Function.update SAP.P012a.proposalStartB.trait v t (SAP.P012a.s 3) = false
      rw [Function.update_of_ne (Ne.symm hv'.2.2.1)]
      rfl
  · constructor
    · intro k hk
      have hk' : k = 1 ∨ k = 2 ∨ k = 3 := by simpa [SAP.P012a.proposalDataB] using hk
      rcases hk' with rfl | rfl | rfl
      · simp [SAP.P012a.graphDegree, SAP.P012a.proposalDataB,
          SAP.P012a.proposalStartB, SAP.P012a.s, SAP.P012a.u, P,
          hvs1, hvs2, hvs3, hvsOld,
          SAP.P012a.wholeBadPending, SAP.P012a.addVertex, SAP.P012a.addEdge,
          SAP.P012a.removeEdge, Finset.filter_insert, Finset.filter_erase,
          Finset.filter_singleton]
      · simp [SAP.P012a.graphDegree, SAP.P012a.proposalDataB,
          SAP.P012a.proposalStartB, SAP.P012a.s, SAP.P012a.u, P,
          hvs1, hvs2, hvs3, hvsOld,
          SAP.P012a.wholeBadPending, SAP.P012a.addVertex, SAP.P012a.addEdge,
          SAP.P012a.removeEdge, Finset.filter_insert, Finset.filter_erase,
          Finset.filter_singleton]
        have hErase :
            (({{Sum.inl 1, Sum.inl 2}, {Sum.inl 2, Sum.inl 3},
              {Sum.inl 2, Sum.inr (4, 0)}} : Finset (Finset SAP.P012a.Vertex)).erase
                {Sum.inl 2, Sum.inr (4, 0)}) =
              {{Sum.inl 1, Sum.inl 2}, {Sum.inl 2, Sum.inl 3}} := by decide
        rw [hErase]
        have hnot : ({Sum.inl 2, v} : Finset SAP.P012a.Vertex) ∉
            ({{Sum.inl 1, Sum.inl 2}, {Sum.inl 2, Sum.inl 3}} :
              Finset (Finset SAP.P012a.Vertex)) := by
          simp [hvs1, hvs2, hvs3, Ne.symm hvs1, Ne.symm hvs2, Ne.symm hvs3]
        rw [Finset.card_insert_of_notMem hnot]
        simp
      · simp [SAP.P012a.graphDegree, SAP.P012a.proposalDataB,
          SAP.P012a.proposalStartB, SAP.P012a.s, SAP.P012a.u, P,
          hvs1, hvs2, hvs3, hvsOld,
          SAP.P012a.wholeBadPending, SAP.P012a.addVertex, SAP.P012a.addEdge,
          SAP.P012a.removeEdge, Finset.filter_insert, Finset.filter_erase,
          Finset.filter_singleton]
    · intro hcompat
      have holdV : SAP.P012a.u 4 0 ∈ P.vertices := by
        rw [hV]
        simp [SAP.P012a.proposalStartB, SAP.P012a.s, SAP.P012a.u]
      have holdS : SAP.P012a.u 4 0 ∉ SAP.P012a.sampledVertices SAP.P012a.proposalDataB := by
        simp [SAP.P012a.proposalDataB, SAP.P012a.sampledVertices, SAP.P012a.s,
          SAP.P012a.u]
      obtain ⟨i, hi, he⟩ := hcompat.2.2.2.2.1 _ holdV holdS
      exact hNo i hi he

end SAP.P012a.WH.W1.P.T1_L3

theorem SAP.P012a.WH.W1.T1_L3_proof : SAP.P012a.WH.W1.T1_L3 := by
  constructor
  · intro v hv t
    exact SAP.P012a.WH.W1.P.T1_L3.outputA v hv t
  · intro v hv t
    exact SAP.P012a.WH.W1.P.T1_L3.outputB v hv t
