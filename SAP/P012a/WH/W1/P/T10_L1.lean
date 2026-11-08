import SAP.P012a.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P012a.WH.W1.P.T10_L1

open SAP.P012a
open Finset
open scoped Classical
noncomputable section

def privateEdges (D : Data) (i j : ℕ) : Finset (Finset Vertex) :=
  D.sampled.biUnion (fun v => (r1WholeLeaves D i j v).image (fun w => {s v,w}))

theorem leaves_card (D : Data) (i j v : ℕ) (hi : v ∈ D.sampled)
    (hsi : 0 < spare D i) (hsj : 0 < spare D j) :
    (r1WholeLeaves D i j v).card =
      if v = i ∨ v = j then spare D v - 1 else spare D v := by
  unfold r1WholeLeaves
  rw [Finset.card_image_of_injective _ (by
    intro k l h
    exact congrArg Prod.snd (Sum.inr.inj h))]
  by_cases hvi : v = i
  · subst v
    have hz : 0 ∈ range (spare D i) := mem_range.mpr hsi
    have hf : (range (spare D i)).filter
        (fun k => k ≠ 0 ∨ (i ≠ i ∧ i ≠ j)) =
        (range (spare D i)).erase 0 := by
      ext k
      simp [and_comm]
    rw [hf, card_erase_of_mem hz]
    simp [card_range]
  · by_cases hvj : v = j
    · subst v
      have hz : 0 ∈ range (spare D j) := mem_range.mpr hsj
      have hf : (range (spare D j)).filter
          (fun k => k ≠ 0 ∨ (j ≠ i ∧ j ≠ j)) =
          (range (spare D j)).erase 0 := by
        ext k
        simp [hvi, and_comm]
      rw [hf, card_erase_of_mem hz]
      simp [hvi, card_range]
    · simp [hvi, hvj]

theorem leaves_mem_iff (D : Data) (i j v : ℕ) (w : Vertex) :
    w ∈ r1WholeLeaves D i j v ↔
      ∃ k, k < spare D v ∧ (k ≠ 0 ∨ (v ≠ i ∧ v ≠ j)) ∧ u v k = w := by
  constructor
  · intro hw
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hw
    obtain ⟨hk, hp⟩ := Finset.mem_filter.mp hk
    exact ⟨k, Finset.mem_range.mp hk, hp, rfl⟩
  · rintro ⟨k, hk, hp, rfl⟩
    apply Finset.mem_image.mpr
    refine ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hk, hp⟩, rfl⟩

theorem leaves_not_sampled (D : Data) (i j v : ℕ) :
    Disjoint (r1WholeLeaves D i j v) (sampledVertices D) := by
  rw [Finset.disjoint_left]
  intro w hw hs
  obtain ⟨k, hk, hkp, rfl⟩ := (leaves_mem_iff D i j v w).mp hw
  obtain ⟨l, hl, he⟩ := Finset.mem_image.mp hs
  exact (by simp [s, u] at he)

theorem leaves_not_shared (D : Data) (i j v : ℕ) (hvi : v = i ∨ v = j) :
    u i 0 ∉ r1WholeLeaves D i j v := by
  intro hw
  obtain ⟨k, hk, hkp, he⟩ := (leaves_mem_iff D i j v (u i 0)).mp hw
  have hpair : (v,k) = (i,0) := Sum.inr.inj he
  have hv : v = i := congrArg Prod.fst hpair
  have hk0 : k = 0 := congrArg Prod.snd hpair
  subst v
  subst k
  rcases hkp with hne | hbad
  · exact hne rfl
  · exact hbad.1 rfl

theorem leaves_not_shared_general (D : Data) (i j v : ℕ) :
    u i 0 ∉ r1WholeLeaves D i j v := by
  intro hw
  obtain ⟨k, hk, hkp, he⟩ := (leaves_mem_iff D i j v (u i 0)).mp hw
  have hpair : (v,k) = (i,0) := Sum.inr.inj he
  have hv : v = i := congrArg Prod.fst hpair
  have hk0 : k = 0 := congrArg Prod.snd hpair
  subst v
  subst k
  rcases hkp with hne | hbad
  · exact hne rfl
  · exact hbad.1 rfl

theorem leaves_disjoint (D : Data) (i j v w : ℕ) (hvw : v ≠ w) :
    Disjoint (r1WholeLeaves D i j v) (r1WholeLeaves D i j w) := by
  rw [Finset.disjoint_left]
  intro x hx hy
  obtain ⟨k, hk, hkp, rfl⟩ := (leaves_mem_iff D i j v x).mp hx
  obtain ⟨l, hl, hlp, he⟩ := (leaves_mem_iff D i j w (u v k)).mp hy
  have hp := Sum.inr.inj he
  exact hvw (congrArg Prod.fst hp).symm

theorem recruitment_edge_sampled_local (D : Data) (hD : Admissible D)
    (e : Finset Vertex) (he : e ∈ recruitmentEdges D) :
    e ⊆ sampledVertices D := by
  have hr := AronowAudit.P012.recruitment_edge_sampled (Bridge.data D) hD e
    (by simpa using he)
  simpa using hr

theorem private_edge_collection_mem (D : Data) (i j : ℕ) (e : Finset Vertex) :
    e ∈ privateEdges D i j ↔
      ∃ v ∈ D.sampled, ∃ w ∈ r1WholeLeaves D i j v, ({s v,w} : Finset Vertex) = e := by
  constructor
  · intro he
    obtain ⟨v,hv,he⟩ := Finset.mem_biUnion.mp he
    obtain ⟨w,hw,heq⟩ := Finset.mem_image.mp he
    exact ⟨v,hv,w,hw,heq⟩
  · rintro ⟨v,hv,w,hw,heq⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨v,hv,Finset.mem_image.mpr ?_⟩
    exact ⟨w,hw,heq⟩

theorem private_edge_not_sampled (D : Data) (i j : ℕ) (e : Finset Vertex)
    (he : e ∈ privateEdges D i j) : ¬ e ⊆ sampledVertices D := by
  intro hsub
  obtain ⟨v,hv,w,hw,rfl⟩ := (private_edge_collection_mem D i j e).mp he
  have hws : w ∈ sampledVertices D := hsub (by simp)
  have hdis := Finset.disjoint_left.mp (leaves_not_sampled D i j v)
  exact hdis hw hws

theorem private_edge_not_shared_vertex (D : Data) (i j : ℕ)
    (hzero : ∀ v, u i 0 ∉ r1WholeLeaves D i j v) (e : Finset Vertex)
    (he : e ∈ privateEdges D i j) : u i 0 ∉ e := by
  obtain ⟨v,hv,w,hw,rfl⟩ := (private_edge_collection_mem D i j e).mp he
  intro hs
  simp only [Finset.mem_insert, Finset.mem_singleton] at hs
  rcases hs with hs | hs
  · cases hs
  · exact hzero v (hs ▸ hw)

theorem private_edge_incidence (D : Data) (i j v : ℕ) (w : Vertex)
    (hw : w ∈ r1WholeLeaves D i j v) (e : Finset Vertex)
    (he : e ∈ privateEdges D i j) (hwe : w ∈ e) :
    e = {s v,w} := by
  obtain ⟨v',hv',w',hw',heq⟩ := (private_edge_collection_mem D i j e).mp he
  have hsample : s v' ∈ sampledVertices D := Finset.mem_image_of_mem s hv'
  have hnot : w ∉ sampledVertices D :=
    (Finset.disjoint_left.mp (leaves_not_sampled D i j v)) hw
  have hcase : w = s v' ∨ w = w' := by
    have hm := hwe
    rw [← heq] at hm
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hm
  have hww : w = w' := hcase.resolve_left (fun h => hnot (h ▸ hsample))
  have hvo : v' = v := by
    by_contra hne
    exact (Finset.disjoint_left.mp (leaves_disjoint D i j v' v hne)) hw' (hww ▸ hw)
  subst v'
  subst w'
  exact heq.symm

theorem private_edge_not_shared (D : Data) (i j v : ℕ) (w : Vertex)
    (hw : w ∈ r1WholeLeaves D i j v) (hzero : u i 0 ∉ r1WholeLeaves D i j v) :
    ({s v,w} : Finset Vertex) ≠ {s i,u i 0} ∧
      ({s v,w} : Finset Vertex) ≠ {s j,u i 0} := by
  obtain ⟨k, hk, hkp, rfl⟩ := (leaves_mem_iff D i j v w).mp hw
  constructor
  · intro he
    have hp := (AronowAudit.P012.pair_edge_eq _ _ _ _).mp he
    rcases hp with ⟨_, hwu⟩ | ⟨hvu, hws⟩
    · exact hzero (hwu ▸ Finset.mem_image.mpr ⟨k, Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr hk, hkp⟩, rfl⟩)
    · cases hvu
  · intro he
    have hp := (AronowAudit.P012.pair_edge_eq _ _ _ _).mp he
    rcases hp with ⟨_, hwu⟩ | ⟨hvu, hws⟩
    · exact hzero (hwu ▸ Finset.mem_image.mpr ⟨k, Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr hk, hkp⟩, rfl⟩)
    · cases hvu

end
end SAP.P012a.WH.W1.P.T10_L1

theorem SAP.P012a.WH.W1.T10_L1_proof : SAP.P012a.WH.W1.T10_L1 := by
  intro D hD i j hi hj htime hnon hdi hdj
  have hposi : 0 < spare D i := by
    unfold spare
    omega
  have hposj : 0 < spare D j := by
    unfold spare
    omega
  have hij : i ≠ j := by
    intro he
    subst j
    omega
  have hnotrec : {s i,s j} ∉ recruitmentEdges D := by
    intro he
    obtain ⟨k,hk,hpair⟩ := Finset.mem_image.mp he
    rcases (AronowAudit.P012.pair_edge_eq _ _ _ _).mp hpair with
      ⟨hparent,hchild⟩ | ⟨hparent,hchild⟩
    · have hk' : k = j := by simpa [s] using hchild
      have hp : D.parent j = i := by
        rw [hk'] at hparent
        simpa [s] using hparent
      rw [hk'] at hk
      have hjns : j ∈ nonseeds D := by simpa [nonseeds] using hk
      exact hnon ⟨hjns,hp⟩
    · have hk' : k = i := by simpa [s] using hchild
      have hp : D.parent i = j := by
        rw [hk'] at hparent
        simpa [s] using hparent
      rw [hk'] at hk
      have hins : i ∈ nonseeds D := by simpa [nonseeds] using hk
      have hback := (hD.2.2.1 i hins).2
      rw [hp] at hback
      omega
  have hzero : ∀ v ∈ D.sampled, u i 0 ∉ r1WholeLeaves D i j v := by
    intro v hv
    exact SAP.P012a.WH.W1.P.T10_L1.leaves_not_shared_general D i j v
  refine ⟨hposi,hposj,hnotrec,?_,?_,?_,?_⟩
  · intro v hv
    exact SAP.P012a.WH.W1.P.T10_L1.leaves_card D i j v hv hposi hposj
  · intro v hv
    exact ⟨SAP.P012a.WH.W1.P.T10_L1.leaves_not_sampled D i j v,
      hzero v hv⟩
  · intro v hv w hw hvw
    exact SAP.P012a.WH.W1.P.T10_L1.leaves_disjoint D i j v w hvw
  · intro τ
    let H := r1WholeStart D i j τ
    let K := r1WholeEnd D i j τ
    have hEdges (e : Finset Vertex) :
        e ∈ H.edges ↔ e = {s i,u i 0} ∨ e = {s j,u i 0} ∨
          e ∈ recruitmentEdges D ∨
          e ∈ SAP.P012a.WH.W1.P.T10_L1.privateEdges D i j := by
      simp [H,r1WholeStart,SAP.P012a.WH.W1.P.T10_L1.privateEdges,or_assoc]
    have hsharedNotSample : u i 0 ∉ sampledVertices D := by
      simp [sampledVertices,s,u]
    have hsharedVert : u i 0 ∈ H.vertices := by
      simp [H,r1WholeStart]
    have hsharedUnsamp : u i 0 ∈ unsampled D H := by
      exact Finset.mem_sdiff.mpr ⟨hsharedVert,hsharedNotSample⟩
    have hleafShared : ∀ e, e ∈ SAP.P012a.WH.W1.P.T10_L1.privateEdges D i j →
        u i 0 ∉ e := by
      intro e he
      exact SAP.P012a.WH.W1.P.T10_L1.private_edge_not_shared_vertex
        D i j (fun v => SAP.P012a.WH.W1.P.T10_L1.leaves_not_shared_general D i j v) e he
    have hsampled_edge : ∀ e, e ∈ H.edges → e ⊆ sampledVertices D →
        e ∈ recruitmentEdges D := by
      intro e he hsub
      rcases (hEdges e).mp he with hiEdge | hjEdge | hr | hpEdge
      · have hs : u i 0 ∈ e := by rw [hiEdge]; simp
        exact (hsharedNotSample (hsub hs)).elim
      · have hs : u i 0 ∈ e := by rw [hjEdge]; simp
        exact (hsharedNotSample (hsub hs)).elim
      · exact hr
      · exact False.elim (SAP.P012a.WH.W1.P.T10_L1.private_edge_not_sampled D i j e hpEdge hsub)
    have hrec_h : ∀ e ∈ recruitmentEdges D, e ∈ H.edges := by
      intro e he
      exact (hEdges e).mpr (Or.inr (Or.inr (Or.inl he)))
    have hsharedNeighbors :
        wholeNeighbors H (u i 0) = {s i,s j} := by
      ext z
      constructor
      · intro hz
        rcases Finset.mem_filter.mp hz with ⟨_,hze⟩
        rcases (hEdges {u i 0,z}).mp hze with hiEdge | hjEdge | hr | hpEdge
        · have hp := (AronowAudit.P012.pair_edge_eq _ _ _ _).mp hiEdge
          rcases hp with ⟨hbad,_⟩ | ⟨_,hz⟩
          · cases hbad
          · simp [hz]
        · have hp := (AronowAudit.P012.pair_edge_eq _ _ _ _).mp hjEdge
          rcases hp with ⟨hbad,_⟩ | ⟨_,hz⟩
          · cases hbad
          · simp [hz]
        · have hsub := SAP.P012a.WH.W1.P.T10_L1.recruitment_edge_sampled_local D hD {u i 0,z} hr
          have hu : u i 0 ∈ ({u i 0,z} : Finset Vertex) := by simp
          exact False.elim (hsharedNotSample (hsub hu))
        · have hu : u i 0 ∈ ({u i 0,z} : Finset Vertex) := by simp
          exact False.elim (hleafShared {u i 0,z} hpEdge hu)
      · intro hz
        simp only [Finset.mem_insert,Finset.mem_singleton] at hz
        rcases hz with hz | hz
        · subst z
          apply Finset.mem_filter.mpr
          constructor
          · exact Finset.mem_union_left _ (Finset.mem_image_of_mem s hi)
          · exact (hEdges {u i 0,s i}).mpr
              (Or.inl (by ext <;> simp [Finset.pair_comm]))
        · subst z
          apply Finset.mem_filter.mpr
          constructor
          · exact Finset.mem_union_left _ (Finset.mem_image_of_mem s hj)
          · exact (hEdges {u i 0,s j}).mpr
              (Or.inr (Or.inl (by ext <;> simp [Finset.pair_comm])))
    have hPrivateH : ∀ v ∈ D.sampled, ∀ w ∈ r1WholeLeaves D i j v,
        wholeNeighbors H w = {s v} := by
      intro v hv w hw
      have hwNotSample : w ∉ sampledVertices D :=
        (Finset.disjoint_left.mp (SAP.P012a.WH.W1.P.T10_L1.leaves_not_sampled D i j v)) hw
      have hwNotShared : w ≠ u i 0 := by
        intro h
        exact hzero v hv (h ▸ hw)
      have hwVert : w ∈ H.vertices := by
        change w ∈ sampledVertices D ∪
          insert (u i 0) (D.sampled.biUnion (r1WholeLeaves D i j))
        exact Finset.mem_union_right _ (Finset.mem_insert_of_mem
          (Finset.mem_biUnion.mpr ⟨v,hv,hw⟩))
      ext z
      constructor
      · intro hz
        rcases Finset.mem_filter.mp hz with ⟨_,hze⟩
        rcases (hEdges {w,z}).mp hze with hiEdge | hjEdge | hr | hpEdge
        · have hp := (AronowAudit.P012.pair_edge_eq _ _ _ _).mp hiEdge
          rcases hp with ⟨hwsi,_⟩ | ⟨hwu,_⟩
          · have hsiSample : s i ∈ sampledVertices D := Finset.mem_image_of_mem s hi
            exact False.elim (hwNotSample (hwsi ▸ hsiSample))
          · exact False.elim (hwNotShared hwu)
        · have hp := (AronowAudit.P012.pair_edge_eq _ _ _ _).mp hjEdge
          rcases hp with ⟨hwsi,_⟩ | ⟨hwu,_⟩
          · have hsjSample : s j ∈ sampledVertices D := Finset.mem_image_of_mem s hj
            exact False.elim (hwNotSample (hwsi ▸ hsjSample))
          · exact False.elim (hwNotShared hwu)
        · have hsub := SAP.P012a.WH.W1.P.T10_L1.recruitment_edge_sampled_local D hD {w,z} hr
          have hwmem : w ∈ ({w,z} : Finset Vertex) := by simp
          exact False.elim (hwNotSample (hsub hwmem))
        ·
          have hinc := SAP.P012a.WH.W1.P.T10_L1.private_edge_incidence D i j v w hw {w,z} hpEdge (by simp)
          have hp := (AronowAudit.P012.pair_edge_eq _ _ _ _).mp hinc
          rcases hp with ⟨hbad,hz⟩ | ⟨_,hz⟩
          · have hsamp : w ∈ sampledVertices D := hbad ▸ Finset.mem_image_of_mem s hv
            exact False.elim (hwNotSample hsamp)
          · simpa [hz]
      · intro hz
        have hz : z = s v := Finset.mem_singleton.mp hz
        subst z
        apply Finset.mem_filter.mpr
        constructor
        · exact Finset.mem_union_left _ (Finset.mem_image_of_mem s hv)
        · have hleafEdge : {s v,w} ∈ SAP.P012a.WH.W1.P.T10_L1.privateEdges D i j :=
            (SAP.P012a.WH.W1.P.T10_L1.private_edge_collection_mem D i j _).mpr
              ⟨v,hv,w,hw,rfl⟩
          exact (hEdges {w,s v}).mpr (Or.inr (Or.inr (Or.inr (by
            simpa only [Finset.pair_comm] using hleafEdge))))
    have hPrivateK : ∀ v ∈ D.sampled, ∀ w ∈ r1WholeLeaves D i j v,
        wholeNeighbors K w = {s v} := by
      intro v hv w hw
      have hwNotSample : w ∉ sampledVertices D :=
        (Finset.disjoint_left.mp (SAP.P012a.WH.W1.P.T10_L1.leaves_not_sampled D i j v)) hw
      have hwNotShared : w ≠ u i 0 := by
        intro h
        exact hzero v hv (h ▸ hw)
      have hwVertH : w ∈ H.vertices := by
        change w ∈ sampledVertices D ∪
          insert (u i 0) (D.sampled.biUnion (r1WholeLeaves D i j))
        exact Finset.mem_union_right _ (Finset.mem_insert_of_mem
          (Finset.mem_biUnion.mpr ⟨v,hv,hw⟩))
      have hsvVertH : s v ∈ H.vertices :=
        Finset.mem_union_left _ (Finset.mem_image_of_mem s hv)
      have hprivEdge : ({s v,w} : Finset Vertex) ∈ H.edges := by
        have hp := (SAP.P012a.WH.W1.P.T10_L1.private_edge_collection_mem D i j _).mpr
          ⟨v,hv,w,hw,rfl⟩
        exact (hEdges _).mpr (Or.inr (Or.inr (Or.inr hp)))
      have hnotDel := SAP.P012a.WH.W1.P.T10_L1.private_edge_not_shared D i j v w hw
        (hzero v hv)
      ext z
      constructor
      · intro hz
        rcases Finset.mem_filter.mp hz with ⟨hzK,hze⟩
        have hKedge := hze
        simp only [K,r1WholeEnd,Finset.mem_insert,Finset.mem_erase] at hKedge
        rcases hKedge with hnew | ⟨_,⟨_,hOld⟩⟩
        · have hp := (AronowAudit.P012.pair_edge_eq _ _ _ _).mp
            (by simpa only [Finset.pair_comm] using hnew)
          rcases hp with ⟨hwi,_⟩ | ⟨hwj,_⟩
          · have hsamp : w ∈ sampledVertices D := hwi ▸ Finset.mem_image_of_mem s hi
            exact False.elim (hwNotSample hsamp)
          · have hsamp : w ∈ sampledVertices D := hwj ▸ Finset.mem_image_of_mem s hj
            exact False.elim (hwNotSample hsamp)
        · have hzVertH : z ∈ H.vertices := by
            simp only [K,r1WholeEnd,Finset.mem_erase] at hzK
            exact hzK.2
          have hzH : z ∈ wholeNeighbors H w := Finset.mem_filter.mpr ⟨hzVertH,hOld⟩
          have hzEq := (hPrivateH v hv w hw) ▸ hzH
          simpa using hzEq
      · intro hz
        have hz : z = s v := Finset.mem_singleton.mp hz
        subst z
        apply Finset.mem_filter.mpr
        constructor
        · have hsvNotShared : s v ≠ u i 0 := by intro h; cases h
          exact Finset.mem_erase.mpr ⟨hsvNotShared,hsvVertH⟩
        · have hnotI : ({s v,w} : Finset Vertex) ≠ {s i,u i 0} := hnotDel.1
          have hnotJ : ({s v,w} : Finset Vertex) ≠ {s j,u i 0} := hnotDel.2
          have hnotI' : ({w,s v} : Finset Vertex) ≠ {s i,u i 0} := by
            simpa only [Finset.pair_comm] using hnotI
          have hnotJ' : ({w,s v} : Finset Vertex) ≠ {s j,u i 0} := by
            simpa only [Finset.pair_comm] using hnotJ
          have hprivEdge' : ({w,s v} : Finset Vertex) ∈ H.edges := by
            simpa only [Finset.pair_comm] using hprivEdge
          simp only [K,r1WholeEnd,Finset.mem_insert,Finset.mem_erase]
          right
          exact ⟨hnotJ',⟨hnotI',hprivEdge'⟩⟩
    have hInducedH : (induced D H).edges = recruitmentEdges D := by
      unfold induced
      ext e
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨he,hs⟩
        exact hsampled_edge e he hs
      · intro he
        exact ⟨hrec_h e he,
          SAP.P012a.WH.W1.P.T10_L1.recruitment_edge_sampled_local D hD e he⟩
    have hInducedK : (induced D K).edges = insert {s i,s j} (recruitmentEdges D) := by
      unfold induced
      ext e
      simp only [Finset.mem_filter,Finset.mem_insert]
      constructor
      · rintro ⟨heK,hs⟩
        simp only [K,r1WholeEnd,Finset.mem_insert,Finset.mem_erase] at heK
        rcases heK with heNew | ⟨hneJ,⟨hneI,heH⟩⟩
        · exact Or.inl heNew
        · exact Or.inr (hsampled_edge e heH hs)
      · intro he
        rcases he with he | he
        · refine ⟨?_,?_⟩
          · change e ∈ insert {s i,s j}
              ((H.edges.erase {s i,u i 0}).erase {s j,u i 0})
            rw [he]
            simp
          · intro x hx
            rw [he] at hx
            simp only [Finset.mem_insert,Finset.mem_singleton] at hx
            rcases hx with hx | hx
            · exact hx ▸ Finset.mem_image_of_mem s hi
            · exact hx ▸ Finset.mem_image_of_mem s hj
        · have heH := hrec_h e he
          have hneI : e ≠ {s i,u i 0} := by
            intro heq
            have hu : u i 0 ∈ e := by rw [heq]; simp
            exact hsharedNotSample
              ((SAP.P012a.WH.W1.P.T10_L1.recruitment_edge_sampled_local D hD e he) hu)
          have hneJ : e ≠ {s j,u i 0} := by
            intro heq
            have hu : u i 0 ∈ e := by rw [heq]; simp
            exact hsharedNotSample
              ((SAP.P012a.WH.W1.P.T10_L1.recruitment_edge_sampled_local D hD e he) hu)
          refine ⟨?_,SAP.P012a.WH.W1.P.T10_L1.recruitment_edge_sampled_local D hD e he⟩
          simp only [K,r1WholeEnd,Finset.mem_insert,Finset.mem_erase]
          exact Or.inr ⟨hneJ,⟨hneI,heH⟩⟩
    have hpairsub : ({s i,s j} : Finset Vertex) ⊆ sampledVertices D := by
      intro x hx
      simp only [Finset.mem_insert,Finset.mem_singleton] at hx
      rcases hx with hx | hx
      · exact hx ▸ Finset.mem_image_of_mem s hi
      · exact hx ▸ Finset.mem_image_of_mem s hj
    have hpairAbsent : {s i,s j} ∉ H.edges := by
      intro he
      rcases (hEdges {s i,s j}).mp he with hiEdge | hjEdge | hr | hpEdge
      · have hp := (AronowAudit.P012.pair_edge_eq _ _ _ _).mp hiEdge
        rcases hp with ⟨_,hbad⟩ | ⟨hbad,_⟩
        · simp [s,u] at hbad
        · simp [s,u] at hbad
      · have hp := (AronowAudit.P012.pair_edge_eq _ _ _ _).mp hjEdge
        rcases hp with ⟨_,hbad⟩ | ⟨hbad,_⟩
        · simp [s,u] at hbad
        · simp [s,u] at hbad
      · exact hnotrec hr
      · exact SAP.P012a.WH.W1.P.T10_L1.private_edge_not_sampled D i j
          {s i,s j} hpEdge hpairsub
    have hedgeK : {s i,s j} ∈ K.edges := by
      change {s i,s j} ∈ insert {s i,s j}
        ((H.edges.erase {s i,u i 0}).erase {s j,u i 0})
      simp
    have hPrivateBoth : ∀ v ∈ D.sampled, ∀ w ∈ r1WholeLeaves D i j v,
        wholeNeighbors H w = {s v} ∧ wholeNeighbors K w = {s v} := by
      intro v hv w hw
      exact ⟨hPrivateH v hv w hw,hPrivateK v hv w hw⟩
    exact ⟨hsharedUnsamp,hsharedNeighbors,hPrivateBoth,hpairAbsent,hedgeK,
      hInducedH,hInducedK⟩

