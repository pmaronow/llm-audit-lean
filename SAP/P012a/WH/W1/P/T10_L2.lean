import SAP.P012a.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P012a.WH.W1.P.T10_L2

open SAP.P012a
open SAP.P012a.WH.W1
open Finset
open scoped Classical
noncomputable section

theorem T10_L2_proof : SAP.P012a.WH.W1.T10_L2 := by
  intro D hD i j hi hj ht hr hdi hdj τ hτ
  let L := leafCompletion D true
  let v := u i 0
  let w := u j 0
  let P := removeEdge L (s j) w
  let G := cleanup D true (addEdge P (s j) v)
  have hij : i ≠ j := by
    intro h
    subst j
    exact (Nat.lt_irrefl _ ht)
  have hiSp : 0 < spare D i := by unfold spare; omega
  have hjSp : 0 < spare D j := by unfold spare; omega
  have hDAr : AronowAudit.P012.Admissible (Bridge.data D) := by
    simpa only [Bridge.Admissible_eq] using hD
  obtain ⟨hvAr,hviAr⟩ := AronowAudit.P012.private_leaf_member
    (Bridge.data D) hDAr true i 0 hi hiSp
  obtain ⟨hwAr,hwjAr⟩ := AronowAudit.P012.private_leaf_member
    (Bridge.data D) hDAr true j 0 hj hjSp
  have hv : v ∈ unsampled D L := by
    simpa only [v, Bridge.unsampled_eq, Bridge.sampledVertices_eq,
      Bridge.leafCompletion_eq, Bridge.s_eq, Bridge.u_eq] using hvAr
  have hvi : ∀ k ∈ D.sampled, {s k,v} ∈ L.edges ↔ k = i := by
    intro k hk
    have hk' : k ∈ (Bridge.data D).sampled := hk
    have hh := hviAr k hk'
    simpa only [v, Bridge.edges_eq, Bridge.leafCompletion_eq,
      Bridge.s_eq, Bridge.u_eq] using hh
  have hw : w ∈ unsampled D L := by
    simpa only [w, Bridge.unsampled_eq, Bridge.sampledVertices_eq,
      Bridge.leafCompletion_eq, Bridge.s_eq, Bridge.u_eq] using hwAr
  have hwj : ∀ k ∈ D.sampled, {s k,w} ∈ L.edges ↔ k = j := by
    intro k hk
    have hk' : k ∈ (Bridge.data D).sampled := hk
    have hh := hwjAr k hk'
    simpa only [w, Bridge.edges_eq, Bridge.leafCompletion_eq,
      Bridge.s_eq, Bridge.u_eq] using hh
  have hLAr := AronowAudit.P012.leafCompletion_compatible (Bridge.data D) hDAr true
  have hL : Compatible D L := by
    simpa only [L, Bridge.Compatible_eq, Bridge.leafCompletion_eq] using hLAr
  have hne : s j ≠ w := by simp [w, s, u]
  have he : {s j,w} ∈ L.edges := (hwj j hj).2 rfl
  have hrw : {s j,w} ∉ recruitmentEdges D := by
    intro he'
    have hnot := (mem_sdiff.mp hwAr).2
    apply hnot
    simpa only [Bridge.sampledVertices_eq, Bridge.s_eq, Bridge.u_eq] using
      (AronowAudit.P012.recruitment_edge_sampled (Bridge.data D) hDAr _ he'
        (by simp [w, Bridge.u_eq]))
  have hpv : v ∈ replacementPool D L j := by
    apply mem_filter.mpr
    refine ⟨hv, ?_⟩
    intro he'
    exact hij ((hvi j hj).1 he').symm
  have hP : GraphProposal D true L G := by
    have hproposal : GraphProposal D true L
        (cleanup D true (addEdge (removeEdge L (s j) w) (s j) v)) := by
      exact GraphProposal.deleteUnobserved j w v (removeEdge L (s j) w)
        hj (mem_sdiff.mp hw).1 hne he hrw (mem_sdiff.mp hw).2
        (Replacement.existing v hpv)
    simpa only [L, P, G] using hproposal
  have hG : Compatible D G := by
    have hD' : AronowAudit.P012.Admissible (Bridge.data D) := hDAr
    have hL' : AronowAudit.P012.Compatible (Bridge.data D) (Bridge.state L) := by
      simpa only [Bridge.Compatible_eq] using hL
    have hP' : AronowAudit.P012.GraphProposal (Bridge.data D) true
        (Bridge.state L) (Bridge.state G) :=
      (Bridge.graph_eq D true L G).2 hP
    have hG' := AronowAudit.P012.corrected_graph_preserves
      (Bridge.data D) (Bridge.state L) (Bridge.state G) hD' hL' hP'
    simpa only [Bridge.Compatible_eq] using hG'
  have hEdgeL (e : Finset Vertex) : e ∈ G.edges ↔
      e = {s j,v} ∨ (e ≠ {s j,w} ∧
        (e ∈ recruitmentEdges D ∨ ∃ a ∈ D.sampled, ∃ k < spare D a,
          {s a,u a k} = e)) := by
    simp [G, cleanup, addEdge, P, removeEdge, L, leafCompletion, leafEdges]
  have hDegreeNZ (H : State) (x : Vertex) : graphDegree H x ≠ 0 ↔
      ∃ e ∈ H.edges, x ∈ e := by
    unfold graphDegree
    constructor
    · intro h
      have hp : 0 < (H.edges.filter (fun e => x ∈ e)).card := Nat.pos_of_ne_zero h
      obtain ⟨e,he⟩ := Finset.card_pos.mp hp
      exact ⟨e,(mem_filter.mp he).1,(mem_filter.mp he).2⟩
    · rintro ⟨e,he,hx⟩
      apply Nat.ne_of_gt
      exact Finset.card_pos.mpr ⟨e,mem_filter.mpr ⟨he,hx⟩⟩
  have hWNoEdge : ∀ e ∈ G.edges, w ∉ e := by
    intro e he hx
    rcases (hEdgeL e).mp he with hnew | ⟨hnotdel, hold⟩
    · subst e
      have hnot : w ∉ ({s j,v} : Finset Vertex) := by
        intro hm
        simp [v,w,s,u] at hm
        exact hij hm.symm
      exact hnot hx
    · rcases hold with hrecruit | ⟨a,ha,k,hk,hedge⟩
      · have hxAr : AronowAudit.P012.u j 0 ∈ e := by simpa [w,Bridge.u_eq] using hx
        have hsampled := AronowAudit.P012.recruitment_edge_sampled
          (Bridge.data D) hDAr e (by simpa only [Bridge.recruitmentEdges_eq] using hrecruit) hxAr
        have hwsampled : w ∈ sampledVertices D := by
          simpa only [Bridge.sampledVertices_eq, Bridge.u_eq] using hsampled
        exact (mem_sdiff.mp hw).2 hwsampled
      · have hx' : w ∈ ({s a,u a k} : Finset Vertex) := by
          rw [← hedge] at hx
          exact hx
        have hp' : j = a ∧ 0 = k := by simpa [w,s,u] using hx'
        have hp : a = j ∧ k = 0 := ⟨hp'.1.symm,hp'.2.symm⟩
        apply hnotdel
        calc
          e = {s a,u a k} := hedge.symm
          _ = {s j,w} := by rw [hp.1,hp.2]
  have hTargetL : (r1WholeStart D i j τ).vertices = L.vertices.erase w := by
    ext x
    cases x with
    | inl a => simp [r1WholeStart,r1WholeLeaves,L,leafCompletion,leafVertices,
        sampledVertices,s,u,w]
    | inr p =>
      rcases p with ⟨a,k⟩
      simp [r1WholeStart,r1WholeLeaves,L,leafCompletion,leafVertices,
        sampledVertices,s,u,w]
      constructor
      · rintro (⟨hai,hk0⟩ | ⟨ha,hk,hcond⟩)
        · subst a
          subst k
          refine ⟨?_, ?_, ?_⟩
          · intro hji
            exact False.elim (hij hji)
          · exact hi
          · simpa [spare] using hiSp
        · refine ⟨?_,ha,hk⟩
          intro haj
          subst a
          rcases hcond with hk0 | ⟨_,haj⟩
          · exact hk0
          · exact False.elim (haj rfl)
      · rintro ⟨hnot0,ha,hk⟩
        by_cases hk0 : k = 0
        · by_cases hai : a = i
          · exact Or.inl ⟨hai,hk0⟩
          · right
            refine ⟨ha,hk,Or.inr ⟨hai,?_⟩⟩
            intro haj
            subst a
            exact hnot0 rfl (by simpa using hk0)
        · exact Or.inr ⟨ha,hk,Or.inl hk0⟩
  have hcleanup : G.vertices = L.vertices.erase w := by
    ext x
    simp only [G, cleanup, Finset.mem_filter, Finset.mem_erase,
      addEdge, P, removeEdge]
    constructor
    · rintro ⟨hxL, hxkeep⟩
      refine ⟨?_, hxL⟩
      intro hxw
      rcases hxkeep with ⟨_,hxsample⟩ | hdeg
      · exact (mem_sdiff.mp hw).2 (by simpa [hxw] using hxsample)
      · have hdeg' : graphDegree G w ≠ 0 := by
          simpa [G,cleanup,graphDegree,addEdge,P,removeEdge,L,hxw] using hdeg
        obtain ⟨e,he,hwe⟩ := (hDegreeNZ G w).mp hdeg'
        exact hWNoEdge e he (by simpa [hxw] using hwe)
    · rintro ⟨hxw,hxL⟩
      constructor
      · exact hxL
      · by_cases hxs : x ∈ sampledVertices D
        · exact Or.inl ⟨True.intro,hxs⟩
        · right
          obtain ⟨a,ha,he⟩ := hL.2.2.2.2.1 x hxL hxs
          have hneEdge : ({s a,x} : Finset Vertex) ≠ ({s j,w} : Finset Vertex) := by
            intro heq
            have hxm : x ∈ ({s j,w} : Finset Vertex) := by
              rw [← heq]
              simp
            rcases mem_insert.mp hxm with hxj | hxw'
            · subst x
              exact hxs (mem_image_of_mem s hj)
            · exact hxw (mem_singleton.mp hxw')
          have hkeepEdge : {s a,x} ∈ G.edges := by
            change {s a,x} ∈ insert {s j,v} (L.edges.erase {s j,w})
            exact mem_insert_of_mem (mem_erase.mpr ⟨hneEdge,he⟩)
          change graphDegree G x ≠ 0
          exact (hDegreeNZ G x).mpr ⟨{s a,x},hkeepEdge,by simp⟩
  have hvertices : G.vertices = (r1WholeStart D i j τ).vertices :=
    hcleanup.trans hTargetL.symm
  have hEdgeT (e : Finset Vertex) : e ∈ (r1WholeStart D i j τ).edges ↔
      e = {s i,v} ∨ e = {s j,v} ∨ e ∈ recruitmentEdges D ∨
        ∃ a ∈ D.sampled, ∃ k, (k < spare D a ∧
          (k ≠ 0 ∨ (a ≠ i ∧ a ≠ j))) ∧ {s a,u a k} = e := by
    simp [v, r1WholeStart, r1WholeLeaves, leafEdges, spare]
  have hedges : G.edges = (r1WholeStart D i j τ).edges := by
    apply Finset.ext
    intro e
    rw [hEdgeL, hEdgeT]
    constructor
    · rintro (heNew | ⟨heNotDel, heOld⟩)
      · exact Or.inr (Or.inl heNew)
      · rcases heOld with heRec | ⟨a,ha,k,hk,heq⟩
        · exact Or.inr (Or.inr (Or.inl heRec))
        · subst e
          by_cases hk0 : k = 0
          · subst k
            by_cases hai : a = i
            · subst a
              exact Or.inl (by simp [v, s, u])
            · have haj : a ≠ j := by
                intro h; subst a
                apply heNotDel
                simp [v, w, s, u]
              exact Or.inr (Or.inr (Or.inr ⟨a,ha,0,⟨by omega,
                Or.inr ⟨hai,haj⟩⟩,rfl⟩))
          · exact Or.inr (Or.inr (Or.inr ⟨a,ha,k,⟨hk,
              Or.inl hk0⟩,rfl⟩))
    · rintro (heI | heJ | heRec | ⟨a,ha,k,⟨hk,hcond⟩,heq⟩)
      · subst e
        have hneq : ({s i,v} : Finset Vertex) ≠ ({s j,w} : Finset Vertex) := by
          simp [v,w,s,u,hij]
        apply Or.inr
        refine ⟨hneq, Or.inr ?_⟩
        exact ⟨i,hi,0,by omega,by simp [v,s,u]⟩
      · exact Or.inl heJ
      · apply Or.inr
        refine ⟨?_, Or.inl heRec⟩
        intro heq'
        apply hrw
        simpa [heq'] using heRec
      ·
        have hnotDel : ({s a,u a k} : Finset Vertex) ≠ ({s j,w} : Finset Vertex) := by
          intro hEq
          have hp : a = j ∧ k = 0 := by
            simpa [w,s,u] using hEq
          rcases hcond with hk0 | ⟨_,haj⟩
          · exact hk0 hp.2
          · exact haj hp.1
        have hnotdelE : e ≠ {s j,w} := by
          intro h
          apply hnotDel
          exact heq.trans h
        apply Or.inr
        exact ⟨hnotdelE, Or.inr ⟨a,ha,k,hk,heq⟩⟩
  have hGAr : AronowAudit.P012.Compatible (Bridge.data D) (Bridge.state G) := by
    simpa only [Bridge.Compatible_eq] using hG
  let T := Bridge.state (r1WholeStart D i j τ)
  have hvAr' : T.vertices = (Bridge.state G).vertices := by
    change (r1WholeStart D i j τ).vertices = G.vertices
    exact hvertices.symm
  have heAr' : T.edges = (Bridge.state G).edges := by
    change (r1WholeStart D i j τ).edges = G.edges
    exact hedges.symm
  have htAr : ∀ k ∈ (Bridge.data D).sampled,
      T.trait (AronowAudit.P012.s k) = (Bridge.data D).trait k := by
    intro k hk
    change τ (s k) = D.trait k
    exact hτ k hk
  have hTargetCompat := AronowAudit.P012.compatible_same_graph
    (Bridge.data D) (Bridge.state G) T hGAr hvAr' heAr' htAr
  simpa only [T, Bridge.Compatible_eq] using hTargetCompat

end
end SAP.P012a.WH.W1.P.T10_L2

theorem SAP.P012a.WH.W1.T10_L2_proof : SAP.P012a.WH.W1.T10_L2 :=
  SAP.P012a.WH.W1.P.T10_L2.T10_L2_proof
