import SAP.P012a.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P012a.WH.W1.P.T11_L1

open Finset
open scoped Classical

theorem private_leaf_swap_slots_graph
    (D : AronowAudit.P012.Data) (hD : AronowAudit.P012.Admissible D)
    (H : AronowAudit.P012.State)
    (hv : H.vertices = (AronowAudit.P012.leafCompletion D true).vertices)
    (he : H.edges = (AronowAudit.P012.leafCompletion D true).edges)
    (ht : ∀ k ∈ D.sampled, H.trait (AronowAudit.P012.s k) = D.trait k)
    (i j x y : ℕ) (hi : i ∈ D.sampled) (hj : j ∈ D.sampled)
    (hdi : AronowAudit.P012.recruitmentDegree D i < D.degree i)
    (hdj : AronowAudit.P012.recruitmentDegree D j < D.degree j)
    (hx : x < AronowAudit.P012.spare D i) (hy : y < AronowAudit.P012.spare D j)
    (hij : i ≠ j) :
    let K := AronowAudit.P012.addEdge
      (AronowAudit.P012.addEdge
        (AronowAudit.P012.removeEdge
          (AronowAudit.P012.removeEdge H (AronowAudit.P012.s i) (AronowAudit.P012.u i x))
          (AronowAudit.P012.s j) (AronowAudit.P012.u j y))
        (AronowAudit.P012.s i) (AronowAudit.P012.u j y))
      (AronowAudit.P012.s j) (AronowAudit.P012.u i x)
    AronowAudit.P012.Compatible D H ∧ AronowAudit.P012.Compatible D K ∧
    {AronowAudit.P012.s i,AronowAudit.P012.u i x} ∈ H.edges ∧
    {AronowAudit.P012.s j,AronowAudit.P012.u j y} ∈ H.edges ∧
    {AronowAudit.P012.s i,AronowAudit.P012.u j y} ∉ H.edges ∧
    {AronowAudit.P012.s j,AronowAudit.P012.u i x} ∉ H.edges ∧
    H.vertices = K.vertices ∧ H.trait = K.trait ∧ H.edges.card = K.edges.card ∧
    (∀ v, AronowAudit.P012.graphDegree H v = AronowAudit.P012.graphDegree K v) := by
  dsimp only
  let A := AronowAudit.P012.removeEdge H (AronowAudit.P012.s i) (AronowAudit.P012.u i x)
  let B := AronowAudit.P012.removeEdge A (AronowAudit.P012.s j) (AronowAudit.P012.u j y)
  let C := AronowAudit.P012.addEdge B (AronowAudit.P012.s i) (AronowAudit.P012.u j y)
  let K := AronowAudit.P012.addEdge C (AronowAudit.P012.s j) (AronowAudit.P012.u i x)
  have hH := AronowAudit.P012.compatible_same_graph D _ H
    (AronowAudit.P012.leafCompletion_compatible D hD true) hv he ht
  obtain ⟨hvi,hpi⟩ := AronowAudit.P012.private_leaf_member D hD true i x hi hx
  obtain ⟨hvj,hpj⟩ := AronowAudit.P012.private_leaf_member D hD true j y hj hy
  have hviH : AronowAudit.P012.u i x ∈ AronowAudit.P012.unsampled D H := by
    simpa only [AronowAudit.P012.unsampled,hv] using hvi
  have hvjH : AronowAudit.P012.u j y ∈ AronowAudit.P012.unsampled D H := by
    simpa only [AronowAudit.P012.unsampled,hv] using hvj
  have hE1 : {AronowAudit.P012.s i,AronowAudit.P012.u i x} ∈ H.edges := by rw [he]; exact (hpi i hi).2 rfl
  have hE2 : {AronowAudit.P012.s j,AronowAudit.P012.u j y} ∈ H.edges := by rw [he]; exact (hpj j hj).2 rfl
  have hE3 : {AronowAudit.P012.s i,AronowAudit.P012.u j y} ∉ H.edges := by rw [he]; exact fun h => hij ((hpj i hi).1 h)
  have hE4 : {AronowAudit.P012.s j,AronowAudit.P012.u i x} ∉ H.edges := by rw [he]; exact fun h => hij ((hpi j hj).1 h).symm
  have hn12 : ({AronowAudit.P012.s j,AronowAudit.P012.u j y}:Finset AronowAudit.P012.Vertex) ≠
      {AronowAudit.P012.s i,AronowAudit.P012.u i x} := by
    intro h
    rcases (AronowAudit.P012.pair_edge_eq _ _ _ _).mp h with ⟨hs,hu⟩ | ⟨hs,hu⟩
    · exact hij (Sum.inl.inj hs).symm
    · simp [AronowAudit.P012.s, AronowAudit.P012.u] at hs
  have hn34 : ({AronowAudit.P012.s j,AronowAudit.P012.u i x}:Finset AronowAudit.P012.Vertex) ≠
      {AronowAudit.P012.s i,AronowAudit.P012.u j y} := by
    intro h
    rcases (AronowAudit.P012.pair_edge_eq _ _ _ _).mp h with ⟨hs,hu⟩ | ⟨hs,hu⟩
    · exact hij (Sum.inl.inj hs).symm
    · simp [AronowAudit.P012.s, AronowAudit.P012.u] at hs
  have hE2A : {AronowAudit.P012.s j,AronowAudit.P012.u j y} ∈ A.edges := mem_erase.mpr ⟨hn12,hE2⟩
  have hE3B : {AronowAudit.P012.s i,AronowAudit.P012.u j y} ∉ B.edges := fun h => hE3 ((mem_erase.mp (mem_erase.mp h).2).2)
  have hE4C : {AronowAudit.P012.s j,AronowAudit.P012.u i x} ∉ C.edges := by
    intro h
    rcases mem_insert.mp h with h | h
    · exact hn34 h
    · exact hE4 ((mem_erase.mp (mem_erase.mp h).2).2)
  have hbase : AronowAudit.P012.ProposalBase D H := ⟨hH.1,hH.2.1,hH.2.2.1,hH.2.2.2.1⟩
  have hr1 : {AronowAudit.P012.s i,AronowAudit.P012.u i x} ∉ AronowAudit.P012.recruitmentEdges D := fun h =>
    (mem_sdiff.mp hviH).2 (AronowAudit.P012.recruitment_edge_sampled D hD _ h (by simp))
  have hr2 : {AronowAudit.P012.s j,AronowAudit.P012.u j y} ∉ AronowAudit.P012.recruitmentEdges D := fun h =>
    (mem_sdiff.mp hvjH).2 (AronowAudit.P012.recruitment_edge_sampled D hD _ h (by simp))
  have hA : AronowAudit.P012.ProposalBase D A := AronowAudit.P012.remove_edge_base D H _ _ hbase hr1
  have hB : AronowAudit.P012.ProposalBase D B := AronowAudit.P012.remove_edge_base D A _ _ hA hr2
  have hC : AronowAudit.P012.ProposalBase D C := AronowAudit.P012.add_edge_base D B i (AronowAudit.P012.u j y) hB hi
    (mem_sdiff.mp hvjH).1 (by simp [AronowAudit.P012.s,AronowAudit.P012.u])
  have hbaseK : AronowAudit.P012.ProposalBase D K := AronowAudit.P012.add_edge_base D C j (AronowAudit.P012.u i x) hC hj
    (mem_sdiff.mp hviH).1 (by simp [AronowAudit.P012.s,AronowAudit.P012.u])
  have hdeg : ∀ w, AronowAudit.P012.graphDegree H w = AronowAudit.P012.graphDegree K w := by
    intro w
    have h1 := AronowAudit.P012.degree_remove_step H (AronowAudit.P012.s i) (AronowAudit.P012.u i x) w hE1
    have h2 := AronowAudit.P012.degree_remove_step A (AronowAudit.P012.s j) (AronowAudit.P012.u j y) w hE2A
    have h3 := AronowAudit.P012.degree_add_step B (AronowAudit.P012.s i) (AronowAudit.P012.u j y) w hE3B
    have h4 := AronowAudit.P012.degree_add_step C (AronowAudit.P012.s j) (AronowAudit.P012.u i x) w hE4C
    change AronowAudit.P012.graphDegree A w+_ = AronowAudit.P012.graphDegree H w at h1
    change AronowAudit.P012.graphDegree B w+_ = AronowAudit.P012.graphDegree A w at h2
    change AronowAudit.P012.graphDegree C w = AronowAudit.P012.graphDegree B w+_ at h3
    change AronowAudit.P012.graphDegree K w = AronowAudit.P012.graphDegree C w+_ at h4
    simp only [mem_insert,mem_singleton] at h1 h2 h3 h4
    by_cases ha : w = AronowAudit.P012.s i <;> by_cases hb : w = AronowAudit.P012.s j <;>
      by_cases hc : w = AronowAudit.P012.u i x <;> by_cases hd : w = AronowAudit.P012.u j y <;>
      simp only [ha,hb,hc,hd,or_true,true_or,false_or,or_false,if_true,if_false] at h1 h2 h3 h4 ⊢ <;>
      simp [AronowAudit.P012.s,AronowAudit.P012.u,hij] at h1 h2 h3 h4 ⊢ <;> omega
  have hclean : AronowAudit.P012.cleanup D true K = K := by
    have hf : K.vertices.filter (fun v =>
        (true = true ∧ v ∈ AronowAudit.P012.sampledVertices D) ∨ AronowAudit.P012.graphDegree K v ≠ 0) = K.vertices := by
      apply filter_eq_self.mpr
      intro v hvK
      by_cases hs : v ∈ AronowAudit.P012.sampledVertices D
      · exact Or.inl ⟨rfl,hs⟩
      · right
        have hvH : v ∈ H.vertices := hvK
        obtain ⟨k,hk,hkv⟩ := hH.2.2.2.2.1 v hvH hs
        have hpos : 0 < AronowAudit.P012.graphDegree H v := card_pos.mpr ⟨{AronowAudit.P012.s k,v},mem_filter.mpr ⟨hkv,by simp⟩⟩
        rw [hdeg] at hpos
        omega
    exact congrArg (fun V => {K with vertices := V}) hf
  have hK : AronowAudit.P012.Compatible D K := by
    rw [← hclean]
    apply AronowAudit.P012.cleanup_compatible D K hbaseK
    intro k hk
    rw [← hdeg]
    exact hH.2.2.2.2.2 k hk
  have hm : H.edges.card = K.edges.card := by
    have h1 := AronowAudit.P012.degree_sum_twice_edges H hH.1.1
    have h2 := AronowAudit.P012.degree_sum_twice_edges K hK.1.1
    have hs : (∑ v ∈ H.vertices, AronowAudit.P012.graphDegree H v) =
        ∑ v ∈ K.vertices, AronowAudit.P012.graphDegree K v := sum_congr rfl (fun v hv => hdeg v)
    omega
  exact ⟨hH,hK,hE1,hE2,hE3,hE4,rfl,rfl,hm,hdeg⟩

end SAP.P012a.WH.W1.P.T11_L1

theorem SAP.P012a.WH.W1.T11_L1_proof : SAP.P012a.WH.W1.T11_L1 := by
  intro D hD i j x y hi hj hdi hdj hti htj hx hy H hv he ht
  have hD' : AronowAudit.P012.Admissible (SAP.P012a.Bridge.data D) := by
    simpa only [SAP.P012a.Bridge.Admissible_eq] using hD
  have hv' : (SAP.P012a.Bridge.state H).vertices =
      (AronowAudit.P012.leafCompletion (SAP.P012a.Bridge.data D) true).vertices := by
    simpa only [SAP.P012a.Bridge.vertices_eq, SAP.P012a.Bridge.leafCompletion_eq,
      SAP.P012a.Bridge.vertices_eq] using hv
  have he' : (SAP.P012a.Bridge.state H).edges =
      (AronowAudit.P012.leafCompletion (SAP.P012a.Bridge.data D) true).edges := by
    simpa only [SAP.P012a.Bridge.edges_eq, SAP.P012a.Bridge.leafCompletion_eq,
      SAP.P012a.Bridge.edges_eq] using he
  have ht' : ∀ k ∈ (SAP.P012a.Bridge.data D).sampled,
      (SAP.P012a.Bridge.state H).trait (AronowAudit.P012.s k) =
        (SAP.P012a.Bridge.data D).trait k := by
    simpa only [SAP.P012a.Bridge.data, SAP.P012a.Bridge.state,
      SAP.P012a.Bridge.s_eq] using ht
  have hdi' : AronowAudit.P012.recruitmentDegree (SAP.P012a.Bridge.data D) i <
      (SAP.P012a.Bridge.data D).degree i := by simpa using hdi
  have hdj' : AronowAudit.P012.recruitmentDegree (SAP.P012a.Bridge.data D) j <
      (SAP.P012a.Bridge.data D).degree j := by simpa using hdj
  have hij : i ≠ j := by
    intro heq
    subst j
    rw [hti] at htj
    cases htj
  have hp := SAP.P012a.WH.W1.P.T11_L1.private_leaf_swap_slots_graph
    (SAP.P012a.Bridge.data D) hD' (SAP.P012a.Bridge.state H) hv' he' ht'
    i j x y hi hj hdi' hdj' hx hy hij
  simpa only [SAP.P012a.Bridge.Compatible_eq,
      SAP.P012a.Bridge.addEdge_eq,
      SAP.P012a.Bridge.removeEdge_eq, SAP.P012a.Bridge.graphDegree_eq,
      SAP.P012a.Bridge.vertices_eq, SAP.P012a.Bridge.edges_eq,
      SAP.P012a.Bridge.trait_eq, SAP.P012a.Bridge.s_eq, SAP.P012a.Bridge.u_eq,
      SAP.P012a.wholeSwap] using hp
