import SAP.P012b.WH.W2.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P012b.WH.W2.P.T23_L1

private def flipState (H : AronowAudit.P012.State) : AronowAudit.P012.State :=
  { H with trait := fun v => !(H.trait v) }

private theorem toState_complement (H : SAP.P012b.State) :
    SAP.P012b.Bridge.toState (SAP.P012b.wholeComplementState H) =
      flipState (SAP.P012b.Bridge.toState H) := rfl

private theorem flip_traitDegree_true (H : AronowAudit.P012.State) :
    AronowAudit.P012.traitDegree (flipState H) true =
      AronowAudit.P012.traitDegree H false := by
  have hf : H.vertices.filter (fun v => (!H.trait v) = true) =
      H.vertices.filter (fun v => H.trait v = false) := by
    apply Finset.filter_congr
    intro v hv
    cases ht : H.trait v <;> simp [ht]
  unfold AronowAudit.P012.traitDegree
  change (∑ v ∈ H.vertices.filter (fun v => (!H.trait v) = true),
      AronowAudit.P012.graphDegree H v) =
    ∑ v ∈ H.vertices.filter (fun v => H.trait v = false),
      AronowAudit.P012.graphDegree H v
  rw [hf]

private theorem flip_traitDegree_false (H : AronowAudit.P012.State) :
    AronowAudit.P012.traitDegree (flipState H) false =
      AronowAudit.P012.traitDegree H true := by
  have hf : H.vertices.filter (fun v => (!H.trait v) = false) =
      H.vertices.filter (fun v => H.trait v = true) := by
    apply Finset.filter_congr
    intro v hv
    cases ht : H.trait v <;> simp [ht]
  unfold AronowAudit.P012.traitDegree
  change (∑ v ∈ H.vertices.filter (fun v => (!H.trait v) = false),
      AronowAudit.P012.graphDegree H v) =
    ∑ v ∈ H.vertices.filter (fun v => H.trait v = true),
      AronowAudit.P012.graphDegree H v
  rw [hf]

private theorem flip_edgeCount_true (H : AronowAudit.P012.State) :
    AronowAudit.P012.edgeCount (flipState H) true =
      AronowAudit.P012.edgeCount H false := by
  have hf : H.edges.filter (fun e => ∀ v ∈ e, (flipState H).trait v = true) =
      H.edges.filter (fun e => ∀ v ∈ e, H.trait v = false) := by
    apply Finset.filter_congr
    intro e he
    simp [flipState]
  change (H.edges.filter (fun e => ∀ v ∈ e, (flipState H).trait v = true)).card =
    (H.edges.filter (fun e => ∀ v ∈ e, H.trait v = false)).card
  exact congrArg Finset.card hf

private theorem flip_edgeCount_false (H : AronowAudit.P012.State) :
    AronowAudit.P012.edgeCount (flipState H) false =
      AronowAudit.P012.edgeCount H true := by
  have hf : H.edges.filter (fun e => ∀ v ∈ e, (flipState H).trait v = false) =
      H.edges.filter (fun e => ∀ v ∈ e, H.trait v = true) := by
    apply Finset.filter_congr
    intro e he
    simp [flipState]
  change (H.edges.filter (fun e => ∀ v ∈ e, (flipState H).trait v = false)).card =
    (H.edges.filter (fun e => ∀ v ∈ e, H.trait v = true)).card
  exact congrArg Finset.card hf

private theorem flip_mixedCount (H : AronowAudit.P012.State) :
    AronowAudit.P012.mixedCount (flipState H) = AronowAudit.P012.mixedCount H := by
  have hf : H.edges.filter (fun e =>
      (∃ v ∈ e, (flipState H).trait v = true) ∧
      (∃ v ∈ e, (flipState H).trait v = false)) =
      H.edges.filter (fun e =>
      (∃ v ∈ e, H.trait v = true) ∧ (∃ v ∈ e, H.trait v = false)) := by
    apply Finset.filter_congr
    intro e he
    simp [flipState, and_comm]
  change (H.edges.filter (fun e =>
      (∃ v ∈ e, (flipState H).trait v = true) ∧
      (∃ v ∈ e, (flipState H).trait v = false))).card =
    (H.edges.filter (fun e =>
      (∃ v ∈ e, H.trait v = true) ∧ (∃ v ∈ e, H.trait v = false))).card
  exact congrArg Finset.card hf

theorem proof : SAP.P012b.WH.W2.T23_L1 := by
  intro H hS
  let HC := SAP.P012b.wholeComplementState H
  change SAP.P012b.homophily HC = SAP.P012b.homophily H
  have hEdges : HC.edges = H.edges := rfl
  have hSC : SAP.P012b.Simple HC := by
    intro e he
    apply hS e
    simpa [HC, SAP.P012b.wholeComplementState] using he
  have hSCsrc : AronowAudit.P012.Simple (SAP.P012b.Bridge.toState HC) := by
    simpa only [SAP.P012b.Bridge.Simple_eq] using hSC
  have hSsrc : AronowAudit.P012.Simple (SAP.P012b.Bridge.toState H) := by
    simpa only [SAP.P012b.Bridge.Simple_eq] using hS
  have hdt : AronowAudit.P012.traitDegree
      (SAP.P012b.Bridge.toState HC) true =
        AronowAudit.P012.traitDegree (SAP.P012b.Bridge.toState H) false := by
    rw [toState_complement]
    exact flip_traitDegree_true _
  have hdf : AronowAudit.P012.traitDegree
      (SAP.P012b.Bridge.toState HC) false =
        AronowAudit.P012.traitDegree (SAP.P012b.Bridge.toState H) true := by
    rw [toState_complement]
    exact flip_traitDegree_false _
  have hct : AronowAudit.P012.edgeCount
      (SAP.P012b.Bridge.toState HC) true =
        AronowAudit.P012.edgeCount (SAP.P012b.Bridge.toState H) false := by
    rw [toState_complement]
    exact flip_edgeCount_true _
  have hcf : AronowAudit.P012.edgeCount
      (SAP.P012b.Bridge.toState HC) false =
        AronowAudit.P012.edgeCount (SAP.P012b.Bridge.toState H) true := by
    rw [toState_complement]
    exact flip_edgeCount_false _
  have hcm : AronowAudit.P012.mixedCount
      (SAP.P012b.Bridge.toState HC) =
        AronowAudit.P012.mixedCount (SAP.P012b.Bridge.toState H) := by
    rw [toState_complement]
    exact flip_mixedCount _
  cases hm : H.edges.card with
  | zero =>
      have hmC : HC.edges.card = 0 := by rw [hEdges, hm]
      have hnH : ¬ SAP.P012b.HomophilyDefined H := by
        simp [SAP.P012b.HomophilyDefined, hm]
      have hnC : ¬ SAP.P012b.HomophilyDefined HC := by
        simp [SAP.P012b.HomophilyDefined, hmC]
      simp only [SAP.P012b.homophily, if_neg hnC, if_neg hnH]
  | succ n =>
      have hmH : 0 < H.edges.card := by omega
      have hmC : 0 < HC.edges.card := by rw [hEdges]; omega
      have hmHsrc : 0 < (SAP.P012b.Bridge.toState H).edges.card := hmH
      have hmCsrc : 0 < (SAP.P012b.Bridge.toState HC).edges.card := hmC
      have hdomH : SAP.P012b.HomophilyDefined H ↔
          0 < SAP.P012b.traitDegree H false ∧ 0 < SAP.P012b.traitDegree H true := by
        simpa only [SAP.P012b.Bridge.HomophilyDefined_eq,
          SAP.P012b.Bridge.traitDegree_eq] using
          (AronowAudit.P012.homophily_domain (SAP.P012b.Bridge.toState H)
            hSsrc hmHsrc).2.2.2.1
      have hdomC : SAP.P012b.HomophilyDefined HC ↔
          0 < SAP.P012b.traitDegree HC false ∧ 0 < SAP.P012b.traitDegree HC true := by
        simpa only [SAP.P012b.Bridge.HomophilyDefined_eq,
          SAP.P012b.Bridge.traitDegree_eq] using
          (AronowAudit.P012.homophily_domain (SAP.P012b.Bridge.toState HC)
            hSCsrc hmCsrc).2.2.2.1
      have hdom : SAP.P012b.HomophilyDefined HC ↔ SAP.P012b.HomophilyDefined H := by
        rw [hdomC, hdomH]
        rw [← SAP.P012b.Bridge.traitDegree_eq HC false,
          ← SAP.P012b.Bridge.traitDegree_eq HC true]
        rw [hdf, hdt]
        exact and_comm
      by_cases hdH : SAP.P012b.HomophilyDefined H
      · have hdC : SAP.P012b.HomophilyDefined HC := hdom.mpr hdH
        have hpH := hdomH.mp hdH
        have hpC := hdomC.mp hdC
        have hformHsrc := AronowAudit.P012.graph_homophily_formula
          (SAP.P012b.Bridge.toState H) hSsrc
          (by simpa only [SAP.P012b.Bridge.traitDegree_eq] using hpH.1)
          (by simpa only [SAP.P012b.Bridge.traitDegree_eq] using hpH.2)
        have hformCsrc := AronowAudit.P012.graph_homophily_formula
          (SAP.P012b.Bridge.toState HC) hSCsrc
          (by simpa only [SAP.P012b.Bridge.traitDegree_eq] using hpC.1)
          (by simpa only [SAP.P012b.Bridge.traitDegree_eq] using hpC.2)
        have hformH : SAP.P012b.hValue H = AronowAudit.P012.phi
            (AronowAudit.P012.edgeCount (SAP.P012b.Bridge.toState H) true)
            (AronowAudit.P012.edgeCount (SAP.P012b.Bridge.toState H) false)
            (AronowAudit.P012.mixedCount (SAP.P012b.Bridge.toState H)) := by
          simpa only [SAP.P012b.Bridge.hValue_eq] using hformHsrc.2.2.2
        have hformC : SAP.P012b.hValue HC = AronowAudit.P012.phi
            (AronowAudit.P012.edgeCount (SAP.P012b.Bridge.toState HC) true)
            (AronowAudit.P012.edgeCount (SAP.P012b.Bridge.toState HC) false)
            (AronowAudit.P012.mixedCount (SAP.P012b.Bridge.toState HC)) := by
          simpa only [SAP.P012b.Bridge.hValue_eq] using hformCsrc.2.2.2
        have hval : SAP.P012b.hValue HC = SAP.P012b.hValue H := by
          rw [hformC, hformH, hct, hcf, hcm]
          unfold AronowAudit.P012.phi
          ring
        simp only [SAP.P012b.homophily, if_pos hdC, if_pos hdH, hval]
      · have hdC : ¬ SAP.P012b.HomophilyDefined HC := by
          intro hC
          exact hdH (hdom.mp hC)
        simp only [SAP.P012b.homophily, if_neg hdC, if_neg hdH]

end SAP.P012b.WH.W2.P.T23_L1

theorem SAP.P012b.WH.W2.T23_L1_proof : SAP.P012b.WH.W2.T23_L1 :=
  SAP.P012b.WH.W2.P.T23_L1.proof
