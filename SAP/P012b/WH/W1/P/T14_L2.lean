import SAP.P012b.WH.W1.Leaves
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000
namespace SAP.P012b.WH.W1.P.T14_L2
open Finset SAP.P012b.Bridge
private def leafEdge (v : Vertex) : Finset Vertex := {s 2, v}
private theorem leaf_ne {H : State} {U : Finset Vertex}
    (hstar : StarAtTwo H U) (v : Vertex) (hv : v ∈ U) :
    v ≠ s 1 ∧ v ≠ s 2 := by
  have hnot : v ∉ ({s 1, s 2} : Finset Vertex) := Finset.disjoint_left.mp hstar.1 hv
  simpa using hnot
private theorem leafEdge_injective {H : State} {U : Finset Vertex}
    (hstar : StarAtTwo H U) : Function.Injective (leafEdge) := by
  intro v w h
  change ({s 2, v} : Finset Vertex) = {s 2, w} at h
  have hmem : v ∈ ({s 2, w} : Finset Vertex) := by
    rw [← h]
    simp
  have hmem' : w ∈ ({s 2, v} : Finset Vertex) := by
    rw [h]
    simp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem'
  rcases hmem with h | h
  · subst v
    rcases hmem' with h' | h' <;> exact h'.symm
  · exact h
private theorem main_not_leafImage {H : State} {U : Finset Vertex}
    (hstar : StarAtTwo H U) : ({s 1, s 2} : Finset Vertex) ∉ U.image leafEdge := by
  intro h
  rcases Finset.mem_image.mp h with ⟨v, hv, he⟩
  change ({s 2, v} : Finset Vertex) = {s 1, s 2} at he
  have hmem : s 1 ∈ ({s 2, v} : Finset Vertex) := by
    rw [he]
    simp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with h | h
  · exact (by decide : s 1 ≠ s 2) h
  · exact (leaf_ne hstar v hv).1 h.symm
private theorem star_edge_card {H : State} {U : Finset Vertex}
    (hstar : StarAtTwo H U) (hU : U.card = 3) : H.edges.card = 4 := by
  rw [hstar.2.2]
  change # (insert ({s 1, s 2} : Finset Vertex) (U.image leafEdge)) = 4
  rw [Finset.card_insert_of_notMem (main_not_leafImage hstar)]
  rw [Finset.card_image_of_injective U (leafEdge_injective hstar), hU]
private theorem star_simple {H : State} {U : Finset Vertex}
    (hstar : StarAtTwo H U) : AronowAudit.P012.Simple (toState H) := by
  have hsimple : Simple H := by
    intro e he
    rw [hstar.2.2] at he
    rcases Finset.mem_insert.mp he with he | he
    · subst e
      constructor
      · norm_num [Finset.card_pair, (by decide : s 1 ≠ s 2)]
      · rw [hstar.2.1]
        exact Finset.subset_union_left
    · rcases Finset.mem_image.mp he with ⟨v, hv, rfl⟩
      constructor
      · norm_num [Finset.card_pair, (leaf_ne hstar v hv).2.symm]
      · rw [hstar.2.1]
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with hx | hx
        · subst x
          exact Finset.mem_union_left _ (by simp)
        · subst x
          exact Finset.mem_union_right _ hv
  simpa only [Simple_eq] using hsimple
private theorem edge_from_one_eq {H : State} {U : Finset Vertex}
    (hstar : StarAtTwo H U) (v : Vertex)
    (he : ({s 1, v} : Finset Vertex) ∈ H.edges) : v = s 2 := by
  rw [hstar.2.2] at he
  rcases Finset.mem_insert.mp he with he | he
  · have hmem : s 2 ∈ ({s 1, v} : Finset Vertex) := by rw [he]; simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h | h
    · exact False.elim ((by decide : s 2 ≠ s 1) h)
    · exact h.symm
  · rcases Finset.mem_image.mp he with ⟨w, hw, heq⟩
    change ({s 2, w} : Finset Vertex) = {s 1, v} at heq
    have hmem : s 1 ∈ ({s 2, w} : Finset Vertex) := by
      rw [heq]
      simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h | h
    · exact False.elim ((by decide : s 1 ≠ s 2) h)
    · exact False.elim ((leaf_ne hstar w hw).1 h.symm)
private theorem star_susceptible (H : State) (U : Finset Vertex)
    (hstar : StarAtTwo H U) (ht1 : H.trait (s 1) = true)
    (ht2 : H.trait (s 2) = true) :
    susceptible domainD H 1 2 = {s 2} := by
  ext v
  constructor
  · intro hv
    have he : ({s 1, v} : Finset Vertex) ∈ H.edges := (Finset.mem_filter.mp hv).2.1
    have := edge_from_one_eq hstar v he
    simpa [this]
  · intro hv
    have : v = s 2 := Finset.mem_singleton.mp hv
    subst v
    simp [susceptible, hstar.2.1, hstar.2.2, notYetSampled, domainD, s]
private theorem star_sameSusceptible (H : State) (U : Finset Vertex)
    (hstar : StarAtTwo H U) (ht1 : H.trait (s 1) = true)
    (ht2 : H.trait (s 2) = true) :
    sameSusceptible domainD H 1 2 = {s 2} := by
  unfold sameSusceptible
  rw [star_susceptible H U hstar ht1 ht2]
  simp [ht1, ht2]
private theorem star_preferential (H : State) (U : Finset Vertex)
    (hstar : StarAtTwo H U) (ht1 : H.trait (s 1) = true)
    (ht2 : H.trait (s 2) = true) : preferential domainD H = some 0 := by
  have hsus : susceptible domainD H 1 2 = {s 2} := star_susceptible H U hstar ht1 ht2
  have hsame : sameSusceptible domainD H 1 2 = {s 2} := star_sameSusceptible H U hstar ht1 ht2
  have hnon : nonseeds domainD = {2} := by decide
  have hdef : PreferentialDefined domainD H := by
    unfold PreferentialDefined
    rw [hnon]
    constructor
    · norm_num
    · intro j hj
      have hj2 : j = 2 := by simpa using hj
      subst j
      change 0 < (susceptible domainD H 1 2).card
      rw [hsus]
      exact Finset.card_pos.mpr ⟨s 2, by simp⟩
  rw [preferential, if_pos hdef]
  unfold pValue pSum
  rw [hnon]
  simp only [Finset.sum_singleton]
  rw [show domainD.parent 2 = 1 by rfl, hsame, hsus]
  simp [ht1, ht2]
private theorem star_edgeCount_true (H : State) (U : Finset Vertex)
    (hstar : StarAtTwo H U) (ht1 : H.trait (s 1) = true)
    (ht2 : H.trait (s 2) = true) :
    AronowAudit.P012.edgeCount (toState H) true = 1 + onesOn H U := by
  have hmain : ∀ v ∈ ({s 1, s 2} : Finset Vertex), H.trait v = true := by
    intro v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with h | h
    · subst v
      simpa using ht1
    · subst v
      simpa using ht2
  have hfilter :
      ((toState H).edges.filter (fun e => ∀ v ∈ e, (toState H).trait v = true)) = insert ({s 1, s 2} : Finset Vertex)
          ((U.filter (fun v => H.trait v = true)).image (fun v => ({s 2, v} : Finset Vertex))) := by
    change (H.edges.filter (fun e => ∀ v ∈ e, H.trait v = true)) = _
    rw [hstar.2.2, Finset.filter_insert]
    have hmainP : ∀ v ∈ ({s 1, s 2} : Finset Vertex), H.trait v = true := by
      intro v hv
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with hv | hv
      · subst v
        exact ht1
      · subst v
        exact ht2
    rw [if_pos hmainP]
    rw [Finset.filter_image]
    have hpred : ∀ v, (∀ w ∈ ({s 2, v} : Finset Vertex), H.trait w = true) ↔
        H.trait v = true := by
      intro v
      simp [ht2]
    have hff : U.filter (fun v => ∀ w ∈ ({s 2, v} : Finset Vertex), H.trait w = true) =
        U.filter (fun v => H.trait v = true) := by
      apply Finset.filter_congr
      intro v hv
      exact hpred v
    rw [hff]
  unfold AronowAudit.P012.edgeCount
  rw [hfilter]
  have hnot : ({s 1, s 2} : Finset Vertex) ∉
      (U.filter (fun v => H.trait v = true)).image leafEdge := by
    intro he
    apply main_not_leafImage hstar
    rcases Finset.mem_image.mp he with ⟨v, hv, he⟩
    exact Finset.mem_image.mpr ⟨v, (Finset.mem_filter.mp hv).1, he⟩
  change # (insert ({s 1, s 2} : Finset Vertex)
      ((U.filter (fun v => H.trait v = true)).image leafEdge)) = 1 + onesOn H U
  rw [Finset.card_insert_of_notMem hnot]
  rw [Finset.card_image_of_injective _ (leafEdge_injective hstar)]
  simp [onesOn]
  omega
private theorem star_degreeTraitSum (H : State) (U : Finset Vertex)
    (hstar : StarAtTwo H U) (hU : U.card = 3)
    (ht1 : H.trait (s 1) = true) (ht2 : H.trait (s 2) = true) :
    AronowAudit.P012.degreeTraitSum (toState H) =
      (5 + onesOn H U : ℝ) := by
  have hV : H.vertices = {s 1, s 2} ∪ U := hstar.2.1
  have hds1 : graphDegree H (s 1) = 1 := by
    rw [graphDegree, hstar.2.2, Finset.filter_insert]
    rw [if_pos (by simp : s 1 ∈ ({s 1, s 2} : Finset Vertex))]
    rw [Finset.filter_image]
    change # (insert ({s 1, s 2} : Finset Vertex)
      ((U.filter (fun v => s 1 ∈ leafEdge v)).image leafEdge)) = 1
    have hnot : ({s 1, s 2} : Finset Vertex) ∉
        (U.filter (fun v => s 1 ∈ leafEdge v)).image leafEdge := by
      intro he
      apply main_not_leafImage hstar
      rcases Finset.mem_image.mp he with ⟨v, hv, he⟩
      exact Finset.mem_image.mpr ⟨v, (Finset.mem_filter.mp hv).1, he⟩
    rw [Finset.card_insert_of_notMem hnot]
    rw [Finset.card_image_of_injective _ (leafEdge_injective hstar)]
    have hnone : U.filter (fun v => s 1 ∈ leafEdge v) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro v hv
      rcases Finset.mem_filter.mp hv with ⟨hvU, hm⟩
      simp only [leafEdge, Finset.mem_insert, Finset.mem_singleton] at hm
      rcases hm with hm | hm
      · exact False.elim ((by decide : s 1 ≠ s 2) hm)
      · exact False.elim ((leaf_ne hstar v hvU).1 hm.symm)
    simp [hnone]
  have hds2 : graphDegree H (s 2) = 4 := by
    rw [graphDegree, hstar.2.2, Finset.filter_insert]
    rw [if_pos (by simp : s 2 ∈ ({s 1, s 2} : Finset Vertex))]
    rw [Finset.filter_image]
    change # (insert ({s 1, s 2} : Finset Vertex)
      ((U.filter (fun v => s 2 ∈ leafEdge v)).image leafEdge)) = 4
    have hnot : ({s 1, s 2} : Finset Vertex) ∉
        (U.filter (fun v => s 2 ∈ leafEdge v)).image leafEdge := by
      intro he
      apply main_not_leafImage hstar
      rcases Finset.mem_image.mp he with ⟨v, hv, he⟩
      exact Finset.mem_image.mpr ⟨v, (Finset.mem_filter.mp hv).1, he⟩
    rw [Finset.card_insert_of_notMem hnot]
    rw [Finset.card_image_of_injective _ (leafEdge_injective hstar)]
    simp [leafEdge, hU]
  have hdu : ∀ v ∈ U, graphDegree H v = 1 := by
    intro v hv
    have hne := leaf_ne hstar v hv
    rw [graphDegree, hstar.2.2, Finset.filter_insert]
    have hnot : v ∉ ({s 1, s 2} : Finset Vertex) := by
      simpa using hne
    rw [if_neg hnot]
    rw [Finset.filter_image]
    change # ((U.filter (fun w => v ∈ leafEdge w)).image leafEdge) = 1
    rw [Finset.card_image_of_injective _ (leafEdge_injective hstar)]
    have hpre : U.filter (fun w => v ∈ leafEdge w) = {v} := by
      ext w
      simp only [Finset.mem_filter, Finset.mem_singleton]
      constructor
      · rintro ⟨hw, hmem⟩
        simp only [leafEdge, Finset.mem_insert, Finset.mem_singleton] at hmem
        rcases hmem with hmem | hmem
        · exact False.elim (hne.2 hmem)
        · exact hmem.symm
      · intro hw
        subst w
        exact ⟨hv, by simp [leafEdge]⟩
    rw [hpre]
    simp
  have hdis : Disjoint ({s 1, s 2} : Finset Vertex) U := hstar.1.symm
  have hsum :
      (∑ v ∈ H.vertices, (graphDegree H v : ℝ) * z H v) =
        (∑ v ∈ ({s 1, s 2} : Finset Vertex), (graphDegree H v : ℝ) * z H v) +
          ∑ v ∈ U, (graphDegree H v : ℝ) * z H v := by
    rw [hV, Finset.sum_union hdis]
  rw [Bridge.degreeTraitSum_eq]
  change (∑ v ∈ H.vertices, (graphDegree H v : ℝ) * z H v) = _
  rw [hsum]
  rw [show (∑ v ∈ ({s 1, s 2} : Finset Vertex),
      (graphDegree H v : ℝ) * z H v) = 5 by
    rw [Finset.sum_pair (by decide : s 1 ≠ s 2)]
    norm_num [hds1, hds2, z, ht1, ht2]]
  have hleaves :
      (∑ v ∈ U, (graphDegree H v : ℝ) * z H v) = (onesOn H U : ℝ) := by
    calc
      (∑ v ∈ U, (graphDegree H v : ℝ) * z H v) =
          ∑ v ∈ U, if H.trait v = true then (1 : ℝ) else 0 := by
        apply Finset.sum_congr rfl
        intro v hv
        rw [hdu v hv]
        simp [z]
      _ = (onesOn H U : ℝ) := by
        unfold onesOn
        simp only [Finset.sum_boole, Nat.cast_id]
  rw [hleaves]
private theorem star_statistics : SAP.P012b.WH.W1.T14_L2 := by
  intro H U hstar hU ht1 ht2
  let r : ℝ := onesOn H U
  have hcard := star_edge_card hstar hU
  have hsimp := star_simple hstar
  have hnumSrc := AronowAudit.P012.numerator_edge_identity (toState H) hsimp
  have hdenSrc := AronowAudit.P012.denominator_sum_identity (toState H)
  have hcount := star_edgeCount_true H U hstar ht1 ht2
  have hq := star_degreeTraitSum H U hstar hU ht1 ht2
  refine ⟨hcard, ?_, ?_, star_preferential H U hstar ht1 ht2⟩
  · have hnum : hNumerator H = 2 * (1 + r) - (5 + r)^2 / 8 := by
      rw [← Bridge.hNumerator_eq H]
      rw [hnumSrc, hcount, hq, Bridge.state_edges H, hcard]
      norm_num [r]
    exact hnum
  · have hden : hDenominator H = (5 + r) - (5 + r)^2 / 8 := by
      rw [← Bridge.hDenominator_eq H]
      rw [hdenSrc, hq, Bridge.state_edges H, hcard]
      norm_num [r]
    exact hden
end SAP.P012b.WH.W1.P.T14_L2
theorem SAP.P012b.WH.W1.T14_L2_proof : SAP.P012b.WH.W1.T14_L2 :=
  SAP.P012b.WH.W1.P.T14_L2.star_statistics
