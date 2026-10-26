import AronowAudit.P012.Wave1.Gap.GLP013P012P012B1
import Mathlib.Topology.Algebra.Order.LiminfLimsup

/-!
Annealing convergence using a direct finite-state drift
argument. A nonoptimal compatible graph has a strictly improving corrected
proposal: delete an optional sampled--sampled edge in favor of two mixed leaves,
or redirect a homogeneous sampled--unsampled edge to a fresh mixed leaf. If
neither operation applies, its counts attain the sharp opposite-leaf endpoint.
Consequently the zero-temperature expected objective gain is uniformly positive
relative to the gap from the optimum. The actual expected gain converges to this
limit, giving a contraction with vanishing error for the expected objective gap.
-/

namespace AronowAudit.P012.Wave1

open Finset Filter
open scoped Topology
noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 3000
set_option linter.unusedVariables false

attribute [local simp] Finset.filter_insert Finset.image_insert Finset.sdiff_insert
  Finset.insert_sdiff_of_mem Finset.insert_sdiff_of_notMem Finset.insert_subset_iff
  Finset.filter_singleton Finset.image_singleton Finset.sdiff_singleton_eq_erase
  Finset.erase_insert_of_ne

lemma GLP013P012P012B1c_formula (D : Data) (H : State) (hH : Compatible D H)
    (h0 : 0 < sampledTraitDegree D false) (h1 : 0 < sampledTraitDegree D true) :
    hValue H = phi (edgeCount H true) (edgeCount H false) (mixedCount H) ∧
    0 < 2 * (edgeCount H true : ℝ) + mixedCount H ∧
    0 < 2 * (edgeCount H false : ℝ) + mixedCount H := by
  have ht0 := sampled_trait_positive_transfer D H hH false h0
  have ht1 := sampled_trait_positive_transfer D H hH true h1
  refine ⟨(graph_homophily_formula H hH.1.1 ht0 ht1).2.2.2, ?_, ?_⟩
  · exact_mod_cast ((binary_edge_counts H hH.1.1).1 ▸ ht1)
  · exact_mod_cast ((binary_edge_counts H hH.1.1).2.1 ▸ ht0)

lemma GLP013P012P012B1c_strict_counts (D : Data) (H L : State)
    (hH : Compatible D H) (hL : Compatible D L)
    (h0 : 0 < sampledTraitDegree D false) (h1 : 0 < sampledTraitDegree D true)
    (hx : edgeCount L true ≤ edgeCount H true)
    (hy : edgeCount L false ≤ edgeCount H false)
    (hc : mixedCount H < mixedCount L)
    (hh : 0 < edgeCount H true ∨ 0 < edgeCount H false) : hValue L < hValue H := by
  obtain ⟨hfH,hHx,hHy⟩ := GLP013P012P012B1c_formula D H hH h0 h1
  obtain ⟨hfL,hLx,hLy⟩ := GLP013P012P012B1c_formula D L hL h0 h1
  have hxR : (edgeCount L true : ℝ) ≤ edgeCount H true := by exact_mod_cast hx
  have hyR : (edgeCount L false : ℝ) ≤ edgeCount H false := by exact_mod_cast hy
  have hcR : (mixedCount H : ℝ) < mixedCount L := by exact_mod_cast hc
  have hhR : 0 < (edgeCount H true : ℝ) ∨ 0 < (edgeCount H false : ℝ) := by
    rcases hh with h | h
    · exact Or.inl (by exact_mod_cast h)
    · exact Or.inr (by exact_mod_cast h)
  rw [hfH,hfL]
  apply lt_of_le_of_lt (phi_mono_x _ _ _ _ (Nat.cast_nonneg _) hxR hLx (by linarith))
  apply lt_of_le_of_lt (phi_mono_y _ _ _ _ (Nat.cast_nonneg _) hyR hLy (by linarith))
  exact phi_strict_anti_c _ _ _ _ (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    hhR hcR hHx hHy

/-- Fresh opposite-trait leaves cannot create a homogeneous edge. -/
lemma GLP013P012P012B1c_surgery_counts (H L : State) (e : Finset Vertex)
    (F : Finset (Finset Vertex)) (he : e ∈ H.edges) (hS : Simple H)
    (hE : L.edges = H.edges.erase e ∪ F)
    (ht : ∀ v ∈ H.vertices, L.trait v = H.trait v)
    (hF : ∀ f ∈ F, ∀ b : Bool, ¬ ∀ v ∈ f, L.trait v = b) :
    ∀ b, edgeCount L b + (if ∀ v ∈ e, H.trait v = b then 1 else 0) = edgeCount H b := by
  classical
  intro b
  have hold : (H.edges.erase e).filter (fun f => ∀ v ∈ f, L.trait v = b) =
      (H.edges.filter (fun f => ∀ v ∈ f, H.trait v = b)).erase e := by
    ext f
    simp only [mem_filter,mem_erase]
    constructor
    · rintro ⟨⟨hne,hf⟩,hz⟩
      exact ⟨hne,hf,fun v hv => (ht v ((hS f hf).2 hv)).symm.trans (hz v hv)⟩
    · rintro ⟨hne,hf,hz⟩
      exact ⟨⟨hne,hf⟩,fun v hv => (ht v ((hS f hf).2 hv)).trans (hz v hv)⟩
  have hnew : F.filter (fun f => ∀ v ∈ f, L.trait v = b) = ∅ :=
    filter_eq_empty_iff.mpr (fun f hf => hF f hf b)
  unfold edgeCount
  rw [hE,filter_union,hold,hnew,union_empty]
  split_ifs with hb
  · exact card_erase_add_one (mem_filter.mpr ⟨he,hb⟩)
  · rw [erase_eq_of_notMem (fun h => hb (mem_filter.mp h).2)]
    omega

lemma GLP013P012P012B1c_fresh (H : State) : ∃ v : Vertex, v ∉ H.vertices := by
  exact Infinite.exists_notMem_finset H.vertices

/-- Redirecting a homogeneous sampled--unsampled edge to a fresh opposite leaf
strictly decreases homophily. -/
lemma GLP013P012P012B1c_redirect (D : Data) (hD : Admissible D)
    (H : State) (hH : Compatible D H)
    (h0 : 0 < sampledTraitDegree D false) (h1 : 0 < sampledTraitDegree D true)
    (i : ℕ) (hi : i ∈ D.sampled) (j : Vertex) (hj : j ∉ sampledVertices D)
    (he : {s i,j} ∈ H.edges) (hz : H.trait (s i) = H.trait j) :
    ∃ L, Proposal D true H L ∧ Compatible D L ∧ hValue L < hValue H := by
  classical
  obtain ⟨v,hv⟩ := GLP013P012P012B1c_fresh H
  have hsi : s i ∈ H.vertices := hH.2.1 (mem_image_of_mem s hi)
  have hnsi : s i ≠ v := fun h => hv (h ▸ hsi)
  let L := cleanup D true (addEdge (addVertex (removeEdge H (s i) j) v
    (!H.trait (s i))) (s i) v)
  have hp : Proposal D true H L := by
    apply Or.inl
    simpa only [L,ite_true] using GraphProposal.deleteUnobserved (D := D) (repaired := true) (H := H) i j v
      (addVertex (removeEdge H (s i) j) v (!H.trait (s i))) hi
      ((hH.1.1 _ he).2 (by simp))
      (fun h => hj (h ▸ mem_image_of_mem s hi)) he
      (fun h => hj (recruitment_edge_sampled D hD _ h (by simp))) hj
      (Replacement.fresh (pendingState := removeEdge H (s i) j) v hv (!H.trait (s i)))
  have hL := corrected_proposal_preserves D H L hD hH hp
  have hnew : ({s i,v} : Finset Vertex) ∉ H.edges :=
    fun h => hv ((hH.1.1 _ h).2 (by simp))
  have ht : ∀ w ∈ H.vertices, L.trait w = H.trait w := by
    intro w hw
    have hne : w ≠ v := fun h => hv (h ▸ hw)
    simp [L,cleanup,addEdge,addVertex,removeEdge,Function.update_of_ne hne]
  have hc := GLP013P012P012B1c_surgery_counts H L {s i,j} {{s i,v}} he hH.1.1
    (by simp [L,cleanup,addEdge,addVertex,removeEdge]) ht (by
      intro f hf b
      rw [mem_singleton] at hf
      subst f
      intro hb
      have hbi := hb (s i) (by simp)
      have hbv := hb v (by simp)
      simp only [L,cleanup,addEdge,addVertex,Function.update_of_ne hnsi,
        Function.update_self] at hbi hbv
      cases hzi : H.trait (s i) <;> cases b <;> simp_all)
  have hcard : L.edges.card = H.edges.card := by
    change (insert {s i,v} (H.edges.erase {s i,j})).card = _
    rw [card_insert_of_notMem (fun h => hnew (mem_erase.mp h).2)]
    have := card_erase_add_one he
    omega
  have hhom : (∀ w ∈ ({s i,j} : Finset Vertex), H.trait w = H.trait (s i)) := by
    simp [hz]
  have hdrop := hc (H.trait (s i))
  rw [ite_eq_left hhom] at hdrop
  have hh : 0 < edgeCount H true ∨ 0 < edgeCount H false := by
    cases hzi : H.trait (s i)
    · right
      have := hc false
      simp only [hzi] at hdrop
      omega
    · left
      simp only [hzi] at hdrop
      omega
  have hx := hc true
  have hy := hc false
  have hmH := (binary_edge_counts H hH.1.1).2.2
  have hmL := (binary_edge_counts L hL.1.1).2.2
  refine ⟨L,hp,hL,GLP013P012P012B1c_strict_counts D H L hH hL h0 h1
    (by split_ifs at hx <;> omega) (by split_ifs at hy <;> omega) ?_ hh⟩
  cases hzi : H.trait (s i) <;> simp only [hzi] at hdrop <;>
    split_ifs at hx hy <;> omega


lemma GLP013P012P012B1c_delete_observed (D : Data) (hD : Admissible D)
    (H : State) (hH : Compatible D H)
    (h0 : 0 < sampledTraitDegree D false) (h1 : 0 < sampledTraitDegree D true)
    (i j : ℕ) (hi : i ∈ D.sampled) (hj : j ∈ D.sampled) (hij : i ≠ j)
    (he : {s i,s j} ∈ H.edges) (hr : {s i,s j} ∉ recruitmentEdges D)
    (hh : 0 < edgeCount H true ∨ 0 < edgeCount H false) :
    ∃ L, Proposal D true H L ∧ Compatible D L ∧ hValue L < hValue H := by
  classical
  obtain ⟨v,hv⟩ := GLP013P012P012B1c_fresh H
  obtain ⟨w,hw⟩ := Infinite.exists_notMem_finset (insert v H.vertices)
  have hwH : w ∉ H.vertices := fun h => hw (mem_insert_of_mem h)
  have hwv : w ≠ v := fun h => hw (by simp [h])
  have hsi : s i ∈ H.vertices := hH.2.1 (mem_image_of_mem s hi)
  have hsj : s j ∈ H.vertices := hH.2.1 (mem_image_of_mem s hj)
  have hniv : s i ≠ v := fun h => hv (h ▸ hsi)
  have hnjv : s j ≠ v := fun h => hv (h ▸ hsj)
  have hniw : s i ≠ w := fun h => hwH (h ▸ hsi)
  have hnjw : s j ≠ w := fun h => hwH (h ▸ hsj)
  let P := addVertex (removeEdge H (s i) (s j)) v (!H.trait (s i))
  let Q := addVertex (addEdge P (s i) v) w (!H.trait (s j))
  let L := cleanup D true (addEdge Q (s j) w)
  have hp : Proposal D true H L := Or.inl
    (GraphProposal.deleteObserved i j v w P Q hi hj hij he hr
      (Replacement.fresh (pendingState := removeEdge H (s i) (s j)) v hv (!H.trait (s i)))
      (Replacement.fresh (pendingState := addEdge P (s i) v) w hw (!H.trait (s j))))
  have hL := corrected_proposal_preserves D H L hD hH hp
  have ht : ∀ z ∈ H.vertices, L.trait z = H.trait z := by
    intro z hz
    have hzv : z ≠ v := fun h => hv (h ▸ hz)
    have hzw : z ≠ w := fun h => hwH (h ▸ hz)
    simp [L,Q,P,cleanup,addEdge,addVertex,removeEdge,hzv,hzw]
  have hvtrait : L.trait v = !H.trait (s i) := by
    simp [L,Q,P,cleanup,addEdge,addVertex,Ne.symm hwv]
  have hwtrait : L.trait w = !H.trait (s j) := by
    simp [L,Q,cleanup,addEdge,addVertex]
  have hnewi : ({s i,v} : Finset Vertex) ∉ H.edges :=
    fun h => hv ((hH.1.1 _ h).2 (by simp))
  have hnewj : ({s j,w} : Finset Vertex) ∉ H.edges :=
    fun h => hwH ((hH.1.1 _ h).2 (by simp))
  have hnewne : ({s j,w} : Finset Vertex) ≠ {s i,v} := by
    intro h
    have hm : w ∈ ({s i,v} : Finset Vertex) := h ▸ (by simp)
    simp only [mem_insert,mem_singleton] at hm
    exact hm.elim (fun h => hniw h.symm) hwv
  have hc := GLP013P012P012B1c_surgery_counts H L {s i,s j}
    {{s i,v},{s j,w}} he hH.1.1
    (by ext f; simp [L,Q,P,cleanup,addEdge,addVertex,removeEdge]; tauto) ht (by
      intro f hf b hb
      simp only [mem_insert,mem_singleton] at hf
      rcases hf with rfl | rfl
      · have hbi := (ht (s i) hsi).symm.trans (hb (s i) (by simp))
        have hbv := hvtrait.symm.trans (hb v (by simp))
        cases hzi : H.trait (s i) <;> cases b <;> simp_all
      · have hbj := (ht (s j) hsj).symm.trans (hb (s j) (by simp))
        have hbw := hwtrait.symm.trans (hb w (by simp))
        cases hzj : H.trait (s j) <;> cases b <;> simp_all)
  have hcard : L.edges.card = H.edges.card + 1 := by
    change (insert {s j,w} (insert {s i,v} (H.edges.erase {s i,s j}))).card = _
    rw [card_insert_of_notMem (by
      simp only [mem_insert]
      exact not_or.mpr ⟨hnewne,fun h => hnewj (mem_erase.mp h).2⟩),
      card_insert_of_notMem (fun h => hnewi (mem_erase.mp h).2)]
    have := card_erase_add_one he
    omega
  have hx := hc true
  have hy := hc false
  have hmH := (binary_edge_counts H hH.1.1).2.2
  have hmL := (binary_edge_counts L hL.1.1).2.2
  refine ⟨L,hp,hL,GLP013P012P012B1c_strict_counts D H L hH hL h0 h1
    (by split_ifs at hx <;> omega) (by split_ifs at hy <;> omega) ?_ hh⟩
  split_ifs at hx hy <;> omega

/-- If every optional edge has exactly one sampled endpoint and is mixed,
the opposite-leaf endpoint counts are already attained. -/
lemma GLP013P012P012B1c_terminal_counts (D : Data) (hD : Admissible D)
    (H : State) (hH : Compatible D H)
    (hobs : ∀ i ∈ D.sampled, ∀ j ∈ D.sampled,
      {s i,s j} ∈ H.edges → {s i,s j} ∈ recruitmentEdges D)
    (hmix : ∀ i ∈ D.sampled, ∀ j, j ∉ sampledVertices D →
      {s i,j} ∈ H.edges → H.trait (s i) ≠ H.trait j) :
    edgeCount H true = a D ∧ edgeCount H false = b D ∧
      mixedCount H = cR D + totalSpare D := by
  classical
  let F := H.edges \ recruitmentEdges D
  let N := fun i => F.filter (fun e => s i ∈ e)
  have hN : ∀ i ∈ D.sampled, (N i).card = spare D i := by
    intro i hi
    have hsub : (recruitmentEdges D).filter (fun e => s i ∈ e) ⊆
        H.edges.filter (fun e => s i ∈ e) := fun e he =>
      mem_filter.mpr ⟨hH.2.2.1 (mem_filter.mp he).1,(mem_filter.mp he).2⟩
    have hfilter : N i = (H.edges.filter (fun e => s i ∈ e)) \
        ((recruitmentEdges D).filter (fun e => s i ∈ e)) := by
      ext e
      simp only [N,F,Finset.mem_filter,Finset.mem_sdiff]
      tauto
    rw [hfilter,card_sdiff_of_subset hsub]
    change graphDegree H (s i)-recruitmentDegree D i = spare D i
    rw [hH.2.2.2.2.2 i hi]
    rfl
  have hpair : ∀ e ∈ H.edges, ∀ i j, i ≠ j → s i ∈ e → s j ∈ e →
      e = {s i,s j} := by
    intro e he i j hij hi hj
    symm
    apply eq_of_subset_of_card_le
    · intro v hv
      rcases mem_insert.mp hv with rfl | hv
      · exact hi
      · exact mem_singleton.mp hv ▸ hj
    · simp [(hH.1.1 e he).1,show s i ≠ s j from fun h => hij (Sum.inl.inj h)]
  have hdis : (D.sampled : Set ℕ).PairwiseDisjoint N := by
    intro i hi j hj hij
    apply disjoint_left.mpr
    intro e hei hej
    obtain ⟨heF,hie⟩ := mem_filter.mp hei
    obtain ⟨he,hr⟩ := Finset.mem_sdiff.mp heF
    have hje := (mem_filter.mp hej).2
    have heq := hpair e he i j hij hie hje
    exact hr (heq ▸ hobs i hi j hj (heq ▸ he))
  have hcover : F = D.sampled.biUnion N := by
    ext e
    constructor
    · intro he
      obtain ⟨i,hi,hie⟩ := hH.1.2 e (mem_sdiff.mp he).1
      exact mem_biUnion.mpr ⟨i,hi,mem_filter.mpr ⟨he,hie⟩⟩
    · intro he
      obtain ⟨i,hi,hie⟩ := mem_biUnion.mp he
      exact (mem_filter.mp hie).1
  have hcard : F.card = totalSpare D := by
    rw [hcover,card_biUnion hdis]
    exact sum_congr rfl hN
  have hmono : ∀ b : Bool, edgeCount H b = edgeCount (recruitmentState D) b := by
    intro b
    unfold edgeCount
    congr 1
    ext e
    simp only [mem_filter]
    have hagree : ∀ v ∈ e, e ∈ recruitmentEdges D →
        H.trait v = (recruitmentState D).trait v := by
      intro v hv he
      obtain ⟨i,hi,rfl⟩ := mem_image.mp (recruitment_edge_sampled D hD e he hv)
      exact hH.2.2.2.1 i hi
    constructor
    · rintro ⟨he,hz⟩
      have her : e ∈ recruitmentEdges D := by
        by_contra hr
        obtain ⟨i,hi,hie⟩ := hH.1.2 e he
        have hex : ∃ j, j ∈ e ∧ s i ≠ j ∧ e = {s i,j} := by
          rcases Finset.card_eq_two.mp (hH.1.1 e he).1 with ⟨v,w,hvw,heq⟩
          rw [heq] at hie
          simp only [mem_insert,mem_singleton] at hie
          rcases hie with rfl | rfl
          · exact ⟨w,by rw [heq]; simp,hvw,heq⟩
          · exact ⟨v,by rw [heq]; simp,Ne.symm hvw,by rw [heq,pair_comm]⟩
        obtain ⟨j,hje,hij,heq⟩ := hex
        have hju : j ∉ sampledVertices D := by
          intro hjs
          obtain ⟨k,hk,hkj⟩ := mem_image.mp hjs
          exact hr (heq ▸ hkj ▸ hobs i hi k hk (hkj ▸ heq ▸ he))
        exact hmix i hi j hju (heq ▸ he) ((hz _ hie).trans (hz _ hje).symm)
      exact ⟨her,fun v hv => (hagree v hv her).symm.trans (hz v hv)⟩
    · rintro ⟨he,hz⟩
      exact ⟨hH.2.2.1 he,fun v hv => (hagree v hv he).trans (hz v hv)⟩
  have hsumH := (binary_edge_counts H hH.1.1).2.2
  have hsumR := (binary_edge_counts (recruitmentState D)
    (recruitment_skeleton_counts D hD).1).2.2
  have hdiff : F.card = H.edges.card - (recruitmentEdges D).card :=
    card_sdiff_of_subset hH.2.2.1
  have hle := card_le_card hH.2.2.1
  have hx := hmono true
  have hy := hmono false
  change edgeCount H true = a D at hx
  change edgeCount H false = b D at hy
  change (recruitmentEdges D).card = a D+b D+cR D at hsumR
  exact ⟨hx,hy,by omega⟩


/-- Every nonminimal compatible graph has a single strictly improving move. -/
lemma GLP013P012P012B1c_improve (D : Data) (hD : Admissible D)
    (H : State) (hH : Compatible D H)
    (h0 : 0 < sampledTraitDegree D false) (h1 : 0 < sampledTraitDegree D true) :
    (∀ L, Compatible D L → hValue H ≤ hValue L) ∨
    ∃ L, Proposal D true H L ∧ Compatible D L ∧ hValue L < hValue H := by
  classical
  by_cases hh : 0 < edgeCount H true ∨ 0 < edgeCount H false
  · by_cases ho : ∀ i ∈ D.sampled, ∀ j ∈ D.sampled,
        {s i,s j} ∈ H.edges → {s i,s j} ∈ recruitmentEdges D
    · by_cases hu : ∀ i ∈ D.sampled, ∀ j, j ∉ sampledVertices D →
          {s i,j} ∈ H.edges → H.trait (s i) ≠ H.trait j
      · left
        obtain ⟨hx,hy,hc⟩ := GLP013P012P012B1c_terminal_counts D hD H hH ho hu
        have hf := (GLP013P012P012B1c_formula D H hH h0 h1).1
        have hvalue : hValue H = hLower D := by
          rw [hf,hx,hy,hc]
          simp only [hLower,Nat.cast_add]
        intro L hL
        rw [hvalue]
        obtain ⟨_,_,_,_,_,_,_,_,_,hl,_⟩ := (exact_h_region D hD h0 h1).1 L hL
        exact hl
      · right
        push Not at hu
        obtain ⟨i,hi,j,hju,he,hz⟩ := hu
        exact GLP013P012P012B1c_redirect D hD H hH h0 h1 i hi j hju he hz
    · right
      push Not at ho
      obtain ⟨i,hi,j,hj,he,hr⟩ := ho
      have hij : i ≠ j := by
        intro hij
        subst j
        have := (hH.1.1 _ he).1
        simp at this
      exact GLP013P012P012B1c_delete_observed D hD H hH h0 h1 i j hi hj hij he hr hh
  · left
    have hx : edgeCount H true = 0 := by omega
    have hy : edgeCount H false = 0 := by omega
    obtain ⟨hf,hpx,hpy⟩ := GLP013P012P012B1c_formula D H hH h0 h1
    have hc : (mixedCount H : ℝ) ≠ 0 := by
      simp only [hx,Nat.cast_zero,mul_zero,zero_add] at hpx
      exact ne_of_gt hpx
    have hvalue : hValue H = -1 := by simp [hf,hx,hy,phi,hc]
    intro L hL
    rw [hvalue]
    exact (compatible_objective_bounds D L hL h0 h1 1 (by norm_num)).2.1

lemma GLP013P012P012B1c_relabel_counts (D : Data) (H L : State)
    (hS : Simple H) (hR : Relabeling D H L) :
    (∀ b, edgeCount L b = edgeCount H b) ∧ mixedCount L = mixedCount H := by
  classical
  obtain ⟨e,he,hV,hE,ht⟩ := hR
  have hinj : Function.Injective (fun f : Finset Vertex => f.image e) :=
    Finset.image_injective e.injective
  have hmono : ∀ b, edgeCount L b = edgeCount H b := by
    intro b
    unfold edgeCount
    rw [← hE,filter_image]
    have hf : H.edges.filter (fun f => ∀ v ∈ f.image e, L.trait v = b) =
        H.edges.filter (fun f => ∀ v ∈ f, H.trait v = b) := by
      apply filter_congr
      intro f hf
      constructor
      · intro hb v hv
        rw [← ht v ((hS f hf).2 hv)]
        exact hb (e v) (mem_image_of_mem e hv)
      · intro hb v hv
        obtain ⟨w,hw,rfl⟩ := mem_image.mp hv
        rw [ht w ((hS f hf).2 hw)]
        exact hb w hw
    rw [hf,card_image_of_injective _ hinj]
  refine ⟨hmono,?_⟩
  unfold mixedCount
  rw [← hE,filter_image]
  have hf : H.edges.filter (fun f =>
      (∃ v ∈ f.image e, L.trait v = true) ∧ (∃ v ∈ f.image e, L.trait v = false)) =
      H.edges.filter (fun f =>
        (∃ v ∈ f, H.trait v = true) ∧ (∃ v ∈ f, H.trait v = false)) := by
    apply filter_congr
    intro f hf
    have hb : ∀ b, (∃ v ∈ f.image e, L.trait v = b) ↔ ∃ v ∈ f, H.trait v = b := by
      intro b
      constructor
      · rintro ⟨v,hv,hb⟩
        obtain ⟨w,hw,rfl⟩ := mem_image.mp hv
        exact ⟨w,hw,(ht w ((hS f hf).2 hw)).symm.trans hb⟩
      · rintro ⟨v,hv,hb⟩
        exact ⟨e v,mem_image_of_mem e hv,(ht v ((hS f hf).2 hv)).trans hb⟩
    rw [hb,hb]
  rw [hf,card_image_of_injective _ hinj]

lemma GLP013P012P012B1c_relabel_value (D : Data) (H L : State)
    (hH : Compatible D H) (hL : Compatible D L)
    (h0 : 0 < sampledTraitDegree D false) (h1 : 0 < sampledTraitDegree D true)
    (hr : Relabeling D H L) : hValue L = hValue H := by
  obtain ⟨hm,hc⟩ := GLP013P012P012B1c_relabel_counts D H L hH.1.1 hr
  rw [(GLP013P012P012B1c_formula D L hL h0 h1).1,
    (GLP013P012P012B1c_formula D H hH h0 h1).1,hm,hm,hc]

lemma GLP013P012P012B1c_index_improves {X : Type*} (D : Data) (hD : Admissible D)
    (repr : X → State) (hC : EnumeratesCompatible D repr)
    (h0 : 0 < sampledTraitDegree D false) (h1 : 0 < sampledTraitDegree D true)
    (K : X → X → ℝ) [Fintype X] (hK : ProposalKernel D repr K)
    (ε : ℝ) (hε : 0 < ε) (x : X)
    (hx : ¬ ∀ y, objective ε (hValue (repr y)) 0 ≤ objective ε (hValue (repr x)) 0) :
    ∃ y, 0 < K x y ∧ objective ε (hValue (repr x)) 0 < objective ε (hValue (repr y)) 0 := by
  rcases GLP013P012P012B1c_improve D hD (repr x) (hC.1 x) h0 h1 with hmin | himp
  · exfalso
    apply hx
    intro y
    unfold objective
    apply one_div_le_one_div_of_le
      (by have := (compatible_objective_bounds D (repr x) (hC.1 x) h0 h1 ε hε).2.1; linarith)
    linarith [hmin (repr y) (hC.1 y)]
  · obtain ⟨L,hp,hL,hl⟩ := himp
    obtain ⟨y,hy⟩ := hC.2.1 L hL
    have hv := GLP013P012P012B1c_relabel_value D L (repr y) hL (hC.1 y) h0 h1 hy
    refine ⟨y,(hK.2.2 x y).2 ⟨repr x,L,cfn_relabel_refl D _,cfn_relabel_symm D hy,hp⟩,?_⟩
    rw [hv]
    unfold objective
    apply one_div_lt_one_div_of_lt
      (by have := (compatible_objective_bounds D L hL h0 h1 ε hε).2.1; linarith)
    linarith


/-- A bounded nonnegative sequence with a fixed contraction and a vanishing
additive error tends to zero. -/
lemma GLP013P012P012B1c_contraction (d e : ℕ → ℝ) (q B : ℝ)
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hd0 : ∀ n, 0 ≤ d n) (hdB : ∀ n, d n ≤ B)
    (he : Tendsto e atTop (𝓝 0))
    (hrec : ∀ n, d (n+1) ≤ q*d n+e n) : Tendsto d atTop (𝓝 0) := by
  have hdhi : IsBoundedUnder (· ≤ ·) atTop d :=
    isBoundedUnder_of_eventually_le (Eventually.of_forall hdB)
  have hdlo : IsBoundedUnder (· ≥ ·) atTop d :=
    isBoundedUnder_of_eventually_ge (Eventually.of_forall hd0)
  have hqlo : IsBoundedUnder (· ≥ ·) atTop (fun n => q*d n) :=
    isBoundedUnder_of_eventually_ge (Eventually.of_forall (fun n => mul_nonneg hq0 (hd0 n)))
  have hqhi : IsBoundedUnder (· ≤ ·) atTop (fun n => q*d n) :=
    isBoundedUnder_of_eventually_le
      (Eventually.of_forall (fun n => mul_le_mul_of_nonneg_left (hdB n) hq0))
  have hs : limsup (fun n => d (n+1)) atTop = limsup d atTop := by
    rw [show (fun n => d (n+1)) = d ∘ (fun n => n+1) from rfl,
      limsup_comp,map_add_atTop_eq_nat]
  have hmul : limsup (fun n => q*d n) atTop ≤ q*limsup d atTop := by
    have h := limsup_mul_le (u := fun _ : ℕ => q) (v := d)
      (Frequently.of_forall (fun _ => hq0)) tendsto_const_nhds.isBoundedUnder_le
      (Eventually.of_forall hd0) hdhi
    change limsup (fun n => q*d n) atTop ≤
      limsup (fun _ : ℕ => q) atTop * limsup d atTop at h
    simpa only [limsup_const] using h
  have hadd : limsup (fun n => q*d n+e n) atTop ≤ q*limsup d atTop := by
    have h := limsup_add_le (u := fun n => q*d n) (v := e)
      hqlo hqhi he.isCoboundedUnder_le he.isBoundedUnder_le
    simp only [he.limsup_eq,add_zero] at h
    exact h.trans hmul
  have hbound := limsup_le_limsup (Eventually.of_forall hrec)
    (isBoundedUnder_of_eventually_ge (Eventually.of_forall (fun n => hd0 (n+1)))).isCoboundedUnder_le
    (isBoundedUnder_le_add hqhi he.isBoundedUnder_le)
  rw [hs] at hbound
  have hsle : limsup d atTop ≤ 0 := by nlinarith [hbound.trans hadd]
  exact tendsto_of_le_liminf_of_limsup_le
    (le_liminf_of_le hdhi.isCoboundedUnder_ge (Eventually.of_forall hd0)) hsle hdhi hdlo

lemma GLP013P012P012B1c_uniform_gain {X : Type*} (S : Finset X) (d g : X → ℝ)
    (hd : ∀ x ∈ S, 0 ≤ d x) (hg : ∀ x ∈ S, 0 ≤ g x)
    (hpos : ∀ x ∈ S, 0 < d x → 0 < g x) :
    ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧ ∀ x ∈ S, c*d x ≤ g x := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨1,by norm_num,le_rfl,by simp⟩
  | @insert a S ha ih =>
    obtain ⟨c,hc,hc1,hcg⟩ := ih
      (fun x hx => hd x (mem_insert_of_mem hx))
      (fun x hx => hg x (mem_insert_of_mem hx))
      (fun x hx => hpos x (mem_insert_of_mem hx))
    by_cases hda : d a = 0
    · refine ⟨c,hc,hc1,?_⟩
      intro x hx
      rcases mem_insert.mp hx with rfl | hx
      · simpa [hda] using hg x (mem_insert_self _ _)
      · exact hcg x hx
    · have hda0 : 0 < d a := lt_of_le_of_ne (hd a (mem_insert_self _ _)) (Ne.symm hda)
      let c' := min c (g a/d a)
      have hc' : 0 < c' := lt_min hc (div_pos (hpos a (mem_insert_self _ _) hda0) hda0)
      refine ⟨c',hc',(min_le_left _ _).trans hc1,?_⟩
      intro x hx
      rcases mem_insert.mp hx with rfl | hx
      · exact (le_div_iff₀ hda0).mp (min_le_right _ _)
      · exact (mul_le_mul_of_nonneg_right (min_le_left _ _) (hd x (mem_insert_of_mem hx))).trans (hcg x hx)

lemma GLP013P012P012B1c_accept_limit (T : ℕ → ℝ) (hT : ∀ n, 0 < T n)
    (hlim : Tendsto T atTop (𝓝 0)) (a : ℝ) :
    Tendsto (fun n => min 1 (Real.exp (a/T n))*a) atTop (𝓝 (max a 0)) := by
  by_cases ha : 0 ≤ a
  · have heq : ∀ n, min 1 (Real.exp (a/T n))*a = a := by
      intro n
      rw [min_eq_left ((Real.one_le_exp_iff).2 (div_nonneg ha (hT n).le)),one_mul]
    simpa only [heq,max_eq_left ha] using (tendsto_const_nhds (x := a) :
      Tendsto (fun _ : ℕ => a) atTop (𝓝 a))
  · have ha0 : a < 0 := lt_of_not_ge ha
    have hinv : Tendsto (fun n => (T n)⁻¹) atTop atTop :=
      tendsto_inv_nhdsGT_zero.comp
        (tendsto_inf.2 ⟨hlim,tendsto_principal.2 (Eventually.of_forall hT)⟩)
    have hexp : Tendsto (fun n => Real.exp (a/T n)) atTop (𝓝 0) := by
      simp only [div_eq_mul_inv]
      exact Real.tendsto_exp_atBot.comp (hinv.const_mul_atTop_of_neg ha0)
    have hm := (tendsto_const_nhds (x := (1:ℝ))).min hexp
    simpa only [min_eq_right zero_le_one,zero_mul,max_eq_right ha0.le] using hm.mul_const a

/-- Rejected mass at the current state gives precisely the accepted objective drift. -/
lemma GLP013P012P012B1c_row_drift {X : Type*} [Fintype X] [DecidableEq X]
    (repr : X → State) (K : X → X → ℝ) (ε T : ℝ) (x : X)
    (hrow : ∑ y, K x y = 1) :
    (∑ y, annealingTransition repr K ε T x y * objective ε (hValue (repr y)) 0) =
      objective ε (hValue (repr x)) 0 +
        ∑ y, K x y * min 1 (Real.exp
          ((objective ε (hValue (repr y)) 0 - objective ε (hValue (repr x)) 0)/T)) *
          (objective ε (hValue (repr y)) 0 - objective ε (hValue (repr x)) 0) := by
  classical
  let J := fun y => objective ε (hValue (repr y)) 0
  let A := fun y => min 1 (Real.exp ((J y-J x)/T))
  change (∑ y, (K x y*A y + if y=x then ∑ b, K x b*(1-A b) else 0)*J y) =
    J x + ∑ y, K x y*A y*(J y-J x)
  simp_rw [add_mul,ite_mul,zero_mul]
  rw [sum_add_distrib]
  simp only [sum_ite_eq',mem_univ,ite_true]
  simp_rw [mul_sub,mul_one,sum_sub_distrib]
  rw [hrow,sub_mul,one_mul]
  simp only [← sum_mul]
  ring

lemma GLP013P012P012B1c_row_sum {X : Type*} [Fintype X] [DecidableEq X]
    (repr : X → State) (K : X → X → ℝ) (ε T : ℝ) (x : X)
    (hrow : ∑ y, K x y = 1) : ∑ y, annealingTransition repr K ε T x y = 1 := by
  classical
  unfold annealingTransition
  dsimp only
  rw [sum_add_distrib]
  simp only [sum_ite_eq',mem_univ,ite_true]
  simp_rw [mul_sub,mul_one,sum_sub_distrib]
  rw [hrow]
  ring


lemma GLP013P012P012B1c_row_deficit {X : Type*} [Fintype X] [DecidableEq X]
    (repr : X → State) (K : X → X → ℝ) (ε T M : ℝ) (x : X)
    (hrow : ∑ y, K x y = 1) :
    (∑ y, annealingTransition repr K ε T x y * (M-objective ε (hValue (repr y)) 0)) =
      M-objective ε (hValue (repr x)) 0 -
        ∑ y, K x y * min 1 (Real.exp
          ((objective ε (hValue (repr y)) 0 - objective ε (hValue (repr x)) 0)/T)) *
          (objective ε (hValue (repr y)) 0 - objective ε (hValue (repr x)) 0) := by
  calc
    _ = (∑ y, annealingTransition repr K ε T x y)*M -
        ∑ y, annealingTransition repr K ε T x y*objective ε (hValue (repr y)) 0 := by
      simp only [mul_sub,sum_sub_distrib,← sum_mul]
    _ = _ := by
      rw [GLP013P012P012B1c_row_sum repr K ε T x hrow,
        GLP013P012P012B1c_row_drift repr K ε T x hrow]
      ring

/-- The objective has no suboptimal local maximum for the corrected proposals.
This permits a direct drift proof, requiring only positive temperatures tending
to zero rather than a general barrier-depth annealing theorem. -/
theorem annealing_convergence_proof {X : Type*} [Fintype X] [Nonempty X] [DecidableEq X]
    (D : Data) (hD : Admissible D)
    (h0 : 0 < sampledTraitDegree D false) (h1 : 0 < sampledTraitDegree D true)
    (hN : D.seeds.card < D.sampled.card)
    (repr : X → State) (hC : EnumeratesCompatible D repr)
    (K : X → X → ℝ) (hK : ProposalKernel D repr K)
    (ε T₁ : ℝ) (hε : 0 < ε) (hfirst : 1/(ε*Real.log 2) ≤ T₁)
    (μ : ℕ → X → ℝ) (hμ : ChainLaw repr K ε T₁ μ) :
    Tendsto (fun n => ∑ x ∈ optimumSet repr ε, μ n x) atTop (𝓝 1) := by
  classical
  let J := fun x => objective ε (hValue (repr x)) 0
  obtain ⟨m,_,hm⟩ := exists_max_image univ J univ_nonempty
  have hmax : ∀ x, J x ≤ J m := fun x => hm x (mem_univ x)
  let d := fun x => J m-J x
  let g := fun x => ∑ y, K x y * max (J y-J x) 0
  let b := fun n x => ∑ y, K x y * min 1 (Real.exp ((J y-J x)/cooling ε T₁ n)) * (J y-J x)
  let e := fun n => ∑ x, |b n x-g x|
  let v := fun n => ∑ x, μ n x*d x
  have hd : ∀ x, 0 ≤ d x := fun x => sub_nonneg.mpr (hmax x)
  have hg : ∀ x, 0 ≤ g x := fun x =>
    sum_nonneg (fun y _ => mul_nonneg (hK.1 x y) (le_max_right _ _))
  have hgpos : ∀ x, 0 < d x → 0 < g x := by
    intro x hx
    have hnot : ¬ ∀ y, J y ≤ J x := by
      intro h
      have := h m
      dsimp only [d] at hx
      linarith
    obtain ⟨y,hy,hxy⟩ := GLP013P012P012B1c_index_improves D hD repr hC h0 h1 K hK ε hε x hnot
    have hterm : 0 < K x y * max (J y-J x) 0 :=
      mul_pos hy (lt_of_lt_of_le (sub_pos.mpr hxy) (le_max_left _ _))
    apply hterm.trans_le
    exact single_le_sum (f := fun z => K x z * max (J z-J x) 0)
      (fun z _ => mul_nonneg (hK.1 x z) (le_max_right _ _)) (mem_univ y)
  obtain ⟨c,hc,hc1,hcg⟩ := GLP013P012P012B1c_uniform_gain univ d g
    (fun x _ => hd x) (fun x _ => hg x) (fun x _ => hgpos x)
  obtain ⟨hT,_,_,hTlim⟩ := cooling_properties ε T₁ hε hfirst
  have hblim : ∀ x, Tendsto (fun n => b n x) atTop (𝓝 (g x)) := by
    intro x
    apply tendsto_finsetSum
    intro y hy
    have h := (GLP013P012P012B1c_accept_limit (cooling ε T₁) hT hTlim (J y-J x)).const_mul (K x y)
    convert h using 1
    funext n
    ring
  have helim : Tendsto e atTop (𝓝 0) := by
    have h : Tendsto e atTop (𝓝 (∑ x : X, (0 : ℝ))) := by
      apply tendsto_finsetSum
      intro x hx
      simpa only [sub_self,abs_zero] using ((hblim x).sub_const (g x)).abs
    simpa only [sum_const_zero] using h
  have hv0 : ∀ n, 0 ≤ v n := fun n => sum_nonneg (fun x _ => mul_nonneg (hμ.1 n x) (hd x))
  have hdB : ∀ x, d x ≤ ∑ y, d y := fun x => single_le_sum (fun y _ => hd y) (mem_univ x)
  have hvB : ∀ n, v n ≤ ∑ x, d x := by
    intro n
    calc
      v n ≤ ∑ x, μ n x * (∑ y, d y) :=
        sum_le_sum (fun x _ => mul_le_mul_of_nonneg_left (hdB x) (hμ.1 n x))
      _ = ∑ x, d x := by rw [← sum_mul,hμ.2.1 n,one_mul]
  have hb : ∀ n x, c*d x-e n ≤ b n x := by
    intro n x
    have hle : |b n x-g x| ≤ e n := by
      exact single_le_sum (f := fun y => |b n y-g y|) (fun y _ => abs_nonneg _) (mem_univ x)
    have hlo := neg_abs_le (b n x-g x)
    have hcgx := hcg x (mem_univ x)
    linarith
  have hrow : ∀ n x,
      (∑ y, annealingTransition repr K ε (cooling ε T₁ n) x y*d y) = d x-b n x := by
    intro n x
    exact GLP013P012P012B1c_row_deficit repr K ε (cooling ε T₁ n) (J m) x (hK.2.1 x)
  have hvrec : ∀ n, v (n+1) = v n - ∑ x, μ n x*b n x := by
    intro n
    calc
      v (n+1) = ∑ y, (∑ x, μ n x * annealingTransition repr K ε (cooling ε T₁ n) x y)*d y := by
        simp only [v,hμ.2.2 n]
      _ = ∑ x, μ n x * (∑ y, annealingTransition repr K ε (cooling ε T₁ n) x y*d y) := by
        simp_rw [sum_mul]
        rw [sum_comm]
        apply sum_congr rfl
        intro x hx
        rw [mul_sum]
        apply sum_congr rfl
        intro y hy
        ring
      _ = v n - ∑ x, μ n x*b n x := by
        simp_rw [hrow,mul_sub,sum_sub_distrib]
        rfl
  have hrec : ∀ n, v (n+1) ≤ (1-c)*v n+e n := by
    intro n
    have hbound : c*v n-e n ≤ ∑ x, μ n x*b n x := by
      calc
        c*v n-e n = ∑ x, μ n x*(c*d x-e n) := by
          simp only [mul_sub,sum_sub_distrib,← sum_mul,hμ.2.1 n,one_mul,v]
          congr 1
          rw [mul_sum]
          apply sum_congr rfl
          intro x hx
          ring
        _ ≤ ∑ x, μ n x*b n x :=
          sum_le_sum (fun x _ => mul_le_mul_of_nonneg_left (hb n x) (hμ.1 n x))
    rw [hvrec n]
    nlinarith
  have hvlim : Tendsto v atTop (𝓝 0) :=
    GLP013P012P012B1c_contraction v e (1-c) (∑ x, d x)
      (by linarith) (by linarith) hv0 hvB helim hrec
  have hbad : ∀ x, x ∉ optimumSet repr ε → Tendsto (fun n => μ n x) atTop (𝓝 0) := by
    intro x hx
    have hdx : 0 < d x := by
      by_contra h
      have hdeq : d x = 0 := le_antisymm (le_of_not_gt h) (hd x)
      have heq : J x = J m := by dsimp only [d] at hdeq; linarith
      apply hx
      apply mem_filter.mpr
      exact ⟨mem_univ x,fun y => (hmax y).trans_eq heq.symm⟩
    have hle : ∀ n, μ n x ≤ v n/d x := by
      intro n
      apply (le_div_iff₀ hdx).2
      exact single_le_sum (fun y _ => mul_nonneg (hμ.1 n y) (hd y)) (mem_univ x)
    have hdiv := hvlim.div_const (d x)
    simp only [zero_div] at hdiv
    exact squeeze_zero (fun n => hμ.1 n x) hle hdiv
  have hbadlim : Tendsto (fun n => ∑ x ∈ univ \ optimumSet repr ε, μ n x) atTop (𝓝 0) := by
    have h := tendsto_finsetSum (univ \ optimumSet repr ε)
      (fun x hx => hbad x (Finset.mem_sdiff.mp hx).2)
    simpa only [sum_const_zero] using h
  have hsum : ∀ n, (∑ x ∈ optimumSet repr ε, μ n x) =
      1-(∑ x ∈ univ \ optimumSet repr ε, μ n x) := by
    intro n
    have h := sum_sdiff (subset_univ (optimumSet repr ε)) (f := μ n)
    rw [hμ.2.1 n] at h
    linarith
  simpa only [hsum,sub_zero] using hbadlim.const_sub 1

end
end AronowAudit.P012.Wave1
