import SAP.P012b.WH.W1.Leaves
import AronowAudit.P012.P012_Identification

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Finset SAP.P012b.Bridge

theorem SAP.P012b.WH.W1.T22_L1_proof : SAP.P012b.WH.W1.T22_L1 := by
  classical
  intro H v hstar ht1 ht2
  have hv1 : v ≠ s 1 := by
    have hnot : v ∉ ({s 1, s 2} : Finset Vertex) :=
      Finset.disjoint_left.mp hstar.1 (by simp : v ∈ ({v} : Finset Vertex))
    intro h
    exact hnot (by simp [h])
  have hv2 : v ≠ s 2 := by
    have hnot : v ∉ ({s 1, s 2} : Finset Vertex) :=
      Finset.disjoint_left.mp hstar.1 (by simp : v ∈ ({v} : Finset Vertex))
    intro h
    exact hnot (by simp [h])
  have hs1 : s 1 ≠ s 2 := by decide
  have hs2 : s 2 ≠ s 1 := Ne.symm hs1
  have hedges : H.edges = insert ({s 1, s 2} : Finset Vertex)
      (({{s 2, v}} : Finset (Finset Vertex))) := by
    rw [hstar.2.2]
    simp [s]
  have hEdgeNe : ({s 1, s 2} : Finset Vertex) ≠ {s 2, v} := by
    intro he
    rcases (AronowAudit.P012.pair_edge_eq (s 1) (s 2) (s 2) v).mp he with hh | hh
    · exact hs1 hh.1
    · exact hv1 hh.1.symm
  let hE1 : Finset Vertex := {s 1, s 2}
  let hE2 : Finset Vertex := {s 2, v}
  have hsub1 : ({s 1, s 2} : Finset Vertex) ⊆ H.vertices := by
    rw [hstar.2.1]
    simp
  have hsub2 : ({s 2, v} : Finset Vertex) ⊆ H.vertices := by
    rw [hstar.2.1]
    simp
  have hsimple : SAP.P012b.Simple H := by
    rw [SAP.P012b.Simple, hedges]
    intro e he
    simp only [Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with he | he
    · subst e
      exact ⟨by simp [hs1], hsub1⟩
    · subst e
      exact ⟨by simp [Ne.symm hv2], hsub2⟩
  have hdeg1 : SAP.P012b.graphDegree H (s 1) = 1 := by
    have h11 : s 1 ∈ ({s 1, s 2} : Finset Vertex) := by simp
    have h12 : s 1 ∉ ({s 2, v} : Finset Vertex) := by simp [hs1, Ne.symm hv1]
    unfold SAP.P012b.graphDegree
    rw [hedges, Finset.filter_insert]
    simp [h11, h12, Finset.filter_singleton]
  have hdeg2 : SAP.P012b.graphDegree H (s 2) = 2 := by
    have h21 : s 2 ∈ ({s 1, s 2} : Finset Vertex) := by simp
    have h22 : s 2 ∈ ({s 2, v} : Finset Vertex) := by simp
    unfold SAP.P012b.graphDegree
    rw [hedges, Finset.filter_insert]
    simp [h21, h22, hEdgeNe, Ne.symm hEdgeNe, Finset.filter_singleton,
      Finset.card_insert_of_notMem]
  have hvertices1 : s 1 ∈ H.vertices := by rw [hstar.2.1]; simp
  have hvertices2 : s 2 ∈ H.vertices := by rw [hstar.2.1]; simp
  have htd0 : 0 < SAP.P012b.traitDegree H false := by
    unfold SAP.P012b.traitDegree
    have hm : s 1 ∈ H.vertices.filter (fun x => H.trait x = false) := by
      simp [hvertices1, ht1]
    have hs := Finset.single_le_sum (f := fun x => SAP.P012b.graphDegree H x)
      (fun x hx => Nat.zero_le _) hm
    rw [hdeg1] at hs
    omega
  have htd1 : 0 < SAP.P012b.traitDegree H true := by
    unfold SAP.P012b.traitDegree
    have hm : s 2 ∈ H.vertices.filter (fun x => H.trait x = true) := by
      simp [hvertices2, ht2]
    have hs := Finset.single_le_sum (f := fun x => SAP.P012b.graphDegree H x)
      (fun x hx => Nat.zero_le _) hm
    rw [hdeg2] at hs
    omega
  have hformula := AronowAudit.P012.graph_homophily_formula
    (SAP.P012b.Bridge.toState H)
    (by simpa only [SAP.P012b.Bridge.Simple_eq] using hsimple)
    (by simpa only [SAP.P012b.Bridge.traitDegree_eq] using htd0)
    (by simpa only [SAP.P012b.Bridge.traitDegree_eq] using htd1)
  have hden : SAP.P012b.HomophilyDefined H := by
    constructor
    · have hm := hformula.1
      simpa only [SAP.P012b.Bridge.state_edges] using hm
    · have hn := ne_of_gt hformula.2.2.1
      simpa only [SAP.P012b.Bridge.hDenominator_eq] using hn
  have hEdgesAr : (SAP.P012b.Bridge.toState H).edges = insert hE1 {hE2} := by
    simpa [SAP.P012b.Bridge.toState] using hedges
  have hpref : SAP.P012b.preferential SAP.P012b.oneLeafData H = some 0 := by
    have hsusc : SAP.P012b.susceptible SAP.P012b.oneLeafData H 1 2 = {s 2} := by
      have hnotadj : ∀ w : Vertex, w ≠ s 2 → {s 1, w} ∉ H.edges := by
        intro w hne he
        rw [hedges] at he
        simp only [Finset.mem_insert, Finset.mem_singleton] at he
        rcases he with he | he
        · rcases (AronowAudit.P012.pair_edge_eq (s 1) w (s 1) (s 2)).mp he with hh | hh
          · exact hne hh.2
          · exact hs1 hh.1
        · rcases (AronowAudit.P012.pair_edge_eq (s 1) w (s 2) v).mp he with hh | hh
          · exact hs1 hh.1
          · exact hv1 hh.1.symm
      ext w
      constructor
      · intro hw
        rcases Finset.mem_filter.mp hw with ⟨hwv, hadj, htime⟩
        have hweq : w = s 2 := by
          by_contra hne
          exact hnotadj w hne hadj
        simp [hweq]
      · intro hw
        have hweq : w = s 2 := Finset.mem_singleton.mp hw
        subst w
        have hdyad : ({s 1, s 2} : Finset Vertex) ∈ H.edges := by
          rw [hedges]
          simp
        refine Finset.mem_filter.mpr ⟨hvertices2, ?_⟩
        constructor
        · exact hdyad
        · simp [SAP.P012b.notYetSampled, SAP.P012b.oneLeafData, s]
    have hsame : SAP.P012b.sameSusceptible SAP.P012b.oneLeafData H 1 2 = ∅ := by
      simp [SAP.P012b.sameSusceptible, hsusc, ht1, ht2]
    have hns : SAP.P012b.nonseeds SAP.P012b.oneLeafData = {2} := by
      decide
    have hsuscParent : SAP.P012b.susceptible SAP.P012b.oneLeafData H
        (SAP.P012b.oneLeafData.parent 2) 2 = {s 2} := by
      simpa [SAP.P012b.oneLeafData] using hsusc
    have hdef : SAP.P012b.PreferentialDefined SAP.P012b.oneLeafData H := by
      unfold SAP.P012b.PreferentialDefined
      rw [hns]
      constructor
      · simp
      · intro j hj
        have : j = 2 := Finset.mem_singleton.mp hj
        subst j
        rw [hsuscParent]
        norm_num
    have hps : SAP.P012b.pSum SAP.P012b.oneLeafData H = 0 := by
      unfold SAP.P012b.pSum
      rw [hns]
      simp only [Finset.sum_singleton]
      have hp : SAP.P012b.oneLeafData.parent 2 = 1 := rfl
      rw [hp, ht1, ht2, hsame, hsusc]
      norm_num
    rw [SAP.P012b.preferential, if_pos hdef, SAP.P012b.pValue, hps, hns]
    norm_num
  refine ⟨hpref, ?_⟩
  cases hb : H.trait v
  · have hct : AronowAudit.P012.edgeCount (SAP.P012b.Bridge.toState H) true = 0 := by
      have hn1 : ¬ (∀ x ∈ hE1, H.trait x = true) := by simp [hE1, ht1]
      have hn2 : ¬ (∀ x ∈ hE2, H.trait x = true) := by simp [hE2, ht2, hb]
      unfold AronowAudit.P012.edgeCount
      change # (H.edges.filter (fun e => ∀ x ∈ e, H.trait x = true)) = 0
      rw [hedges, Finset.filter_insert]
      rw [if_neg hn1, Finset.filter_singleton, if_neg hn2]
      simp
    have hcf : AronowAudit.P012.edgeCount (SAP.P012b.Bridge.toState H) false = 0 := by
      have hn1 : ¬ (∀ x ∈ hE1, H.trait x = false) := by simp [hE1, ht2]
      have hn2 : ¬ (∀ x ∈ hE2, H.trait x = false) := by simp [hE2, ht2]
      unfold AronowAudit.P012.edgeCount
      change # (H.edges.filter (fun e => ∀ x ∈ e, H.trait x = false)) = 0
      rw [hedges, Finset.filter_insert]
      rw [if_neg hn1, Finset.filter_singleton, if_neg hn2]
      simp
    have hcm : AronowAudit.P012.mixedCount (SAP.P012b.Bridge.toState H) = 2 := by
      have hm1 : (∃ x ∈ hE1, H.trait x = true) ∧ (∃ x ∈ hE1, H.trait x = false) := by
        simp [hE1, ht1, ht2]
      have hm2 : (∃ x ∈ hE2, H.trait x = true) ∧ (∃ x ∈ hE2, H.trait x = false) := by
        simp [hE2, ht2, hb]
      unfold AronowAudit.P012.mixedCount
      change # (H.edges.filter (fun e =>
        (∃ x ∈ e, H.trait x = true) ∧ (∃ x ∈ e, H.trait x = false))) = 2
      rw [hedges, Finset.filter_insert]
      rw [if_pos hm1, Finset.filter_singleton, if_pos hm2]
      simp [Finset.card_insert_of_notMem, hEdgeNe]
    have hval : SAP.P012b.hValue H = AronowAudit.P012.phi (0:ℝ) 0 2 := by
      simpa [hct, hcf, hcm] using hformula.2.2.2
    rw [SAP.P012b.homophily, if_pos hden, hval]
    norm_num [AronowAudit.P012.phi]
  · have hct : AronowAudit.P012.edgeCount (SAP.P012b.Bridge.toState H) true = 1 := by
      have hn1 : ¬ (∀ x ∈ hE1, H.trait x = true) := by simp [hE1, ht1]
      have hy2 : ∀ x ∈ hE2, H.trait x = true := by simp [hE2, ht2, hb]
      unfold AronowAudit.P012.edgeCount
      change # (H.edges.filter (fun e => ∀ x ∈ e, H.trait x = true)) = 1
      rw [hedges, Finset.filter_insert]
      rw [if_neg hn1, Finset.filter_singleton, if_pos hy2]
      simp
    have hcf : AronowAudit.P012.edgeCount (SAP.P012b.Bridge.toState H) false = 0 := by
      have hn1 : ¬ (∀ x ∈ hE1, H.trait x = false) := by simp [hE1, ht2]
      have hn2 : ¬ (∀ x ∈ hE2, H.trait x = false) := by simp [hE2, ht2]
      unfold AronowAudit.P012.edgeCount
      change # (H.edges.filter (fun e => ∀ x ∈ e, H.trait x = false)) = 0
      rw [hedges, Finset.filter_insert]
      rw [if_neg hn1, Finset.filter_singleton, if_neg hn2]
      simp
    have hcm : AronowAudit.P012.mixedCount (SAP.P012b.Bridge.toState H) = 1 := by
      have hm1 : (∃ x ∈ hE1, H.trait x = true) ∧ (∃ x ∈ hE1, H.trait x = false) := by
        simp [hE1, ht1, ht2]
      have hn2 : ¬ ((∃ x ∈ hE2, H.trait x = true) ∧
          (∃ x ∈ hE2, H.trait x = false)) := by simp [hE2, ht2, hb]
      unfold AronowAudit.P012.mixedCount
      change # (H.edges.filter (fun e =>
        (∃ x ∈ e, H.trait x = true) ∧ (∃ x ∈ e, H.trait x = false))) = 1
      rw [hedges, Finset.filter_insert]
      rw [if_pos hm1, Finset.filter_singleton, if_neg hn2]
      simp
    have hval : SAP.P012b.hValue H = AronowAudit.P012.phi (1:ℝ) 0 1 := by
      simpa [hct, hcf, hcm] using hformula.2.2.2
    rw [SAP.P012b.homophily, if_pos hden, hval]
    norm_num [AronowAudit.P012.phi]

