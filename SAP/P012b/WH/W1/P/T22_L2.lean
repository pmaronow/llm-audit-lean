import SAP.P012b.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace SAP.P012b.WH.W1.P.T22_L2

open Finset SAP.P012b.Bridge

lemma wholeEdgeCount_erase_qual (F : Finset (Finset Vertex))
    (Z : Vertex → Bool) (e : Finset Vertex) (b : Bool)
    (he : e ∈ F) (hq : ∀ v ∈ e, Z v = b) :
    wholeEdgeCount (F.erase e) Z b + 1 =
      (F.filter (fun f => ∀ v ∈ f, Z v = b)).card := by
  unfold wholeEdgeCount
  rw [Finset.filter_erase]
  have hm : e ∈ F.filter (fun f => ∀ v ∈ f, Z v = b) :=
    Finset.mem_filter.mpr ⟨he, hq⟩
  rw [Finset.card_erase_add_one hm]

lemma wholeEdgeCount_erase_nonqual (F : Finset (Finset Vertex))
    (Z : Vertex → Bool) (e : Finset Vertex) (b : Bool)
    (hn : ¬ ∀ v ∈ e, Z v = b) :
    wholeEdgeCount (F.erase e) Z b =
      (F.filter (fun f => ∀ v ∈ f, Z v = b)).card := by
  unfold wholeEdgeCount
  rw [Finset.filter_erase]
  have hm : e ∉ F.filter (fun f => ∀ v ∈ f, Z v = b) := by
    simp only [Finset.mem_filter]
    exact fun h => hn h.2
  rw [Finset.erase_eq_of_notMem hm]

lemma wholeMixedCount_erase_nonqual (F : Finset (Finset Vertex))
    (Z : Vertex → Bool) (e : Finset Vertex)
    (hn : ¬ ((∃ v ∈ e, Z v = true) ∧ (∃ v ∈ e, Z v = false))) :
    wholeMixedCount (F.erase e) Z =
      (F.filter (fun f =>
        (∃ v ∈ f, Z v = true) ∧ (∃ v ∈ f, Z v = false))).card := by
  unfold wholeMixedCount
  rw [Finset.filter_erase]
  have hm : e ∉ F.filter (fun f =>
      (∃ v ∈ f, Z v = true) ∧ (∃ v ∈ f, Z v = false)) := by
    simp only [Finset.mem_filter]
    exact fun h => hn h.2
  rw [Finset.erase_eq_of_notMem hm]

end SAP.P012b.WH.W1.P.T22_L2

namespace SAP.P012b.WH.W1

open Finset SAP.P012b.Bridge SAP.P012b.WH.W1.P.T22_L2

theorem T22_L2_proof : T22_L2 := by
  intro D hD h0 h1 i hi hdi
  let H := leafCompletion D true
  let v := u i 0
  let K := flipTrait H v
  let e₀ : Finset Vertex := {s i, v}
  let E := H.edges.erase e₀
  let x : ℝ := wholeEdgeCount E H.trait true
  let y : ℝ := wholeEdgeCount E H.trait false
  let c : ℝ := wholeMixedCount E H.trait
  change HomophilyDefined H ∧ HomophilyDefined K ∧
    v ∈ unsampled D H ∧ graphDegree H v = 1 ∧
    H.trait v = D.trait i ∧ K.trait v = !D.trait i ∧
    (D.trait i = true → 0 < 2*y+c ∧
      hValue H = wholePhi (x+1) y c ∧ hValue K = wholePhi x y (c+1))

  have hsp : 0 < spare D i := by
    unfold spare
    omega

  have hjoint := by
    sap_transfer (AronowAudit.P012.joint_leaf_flip_witness
      (toData D) hD h0 h1 i hi hdi)
  have hH : Compatible D H := hjoint.1
  have hK : Compatible D K := hjoint.2.1

  have hfull : ∀ G : State, Compatible D G → HomophilyDefined G := by
    have h := (AronowAudit.P012.full_domain_conditions (toData D) hD).2 ⟨h0, h1⟩
    simpa only [forall_state, Compatible_eq, HomophilyDefined_eq] using h

  have hprivate := by
    sap_transfer (AronowAudit.P012.private_leaf_member
      (toData D) hD true i 0 hi hsp)
  have hv : v ∈ unsampled D H := by
    simpa [v] using hprivate.1
  have hpriv : ∀ j ∈ D.sampled, {s j, v} ∈ H.edges ↔ j = i := by
    simpa [v] using hprivate.2
  have he₀ : e₀ ∈ H.edges := by
    have := (hpriv i hi).2 rfl
    simpa [e₀, v] using this

  have hHsrc : AronowAudit.P012.Compatible (toData D) (toState H) := by
    simpa only [Compatible_eq] using hH
  have hvsrc : v ∈ AronowAudit.P012.unsampled (toData D) (toState H) := by
    simpa only [unsampled_eq] using hv
  have hprivsrc : ∀ j ∈ (toData D).sampled,
      {AronowAudit.P012.s j, v} ∈ (toState H).edges ↔ j = i := by
    simpa only [data_sampled, state_edges, sampled_name_eq] using hpriv
  have hinc : ∀ e : Finset Vertex, e ∈ H.edges → v ∈ e → e = e₀ := by
    intro e he hve
    have hsrc := AronowAudit.P012.private_edge_incidence
      (toData D) (toState H) hHsrc i hi v hvsrc hprivsrc e
      (by simpa only [state_edges] using he) hve
    simpa only [e₀, sampled_name_eq] using hsrc

  have hincident : H.edges.filter (fun e => v ∈ e) = {e₀} := by
    ext e
    simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨he, hve⟩
      exact hinc e he hve
    · intro he
      subst e
      exact ⟨he₀, by simp [e₀, v]⟩
  have hdegree : graphDegree H v = 1 := by
    simp [graphDegree, hincident]

  have htrait : H.trait v = D.trait i := by
    simp [H, v, leafCompletion, u]
  have htraitK : K.trait v = !D.trait i := by
    simp [K, H, v, flipTrait, leafCompletion, u]

  have howner : H.trait (s i) = D.trait i := by
    simp [H, leafCompletion, s]
  refine ⟨hfull H hH, hfull K hK, hv, hdegree, htrait, htraitK, ?_⟩
  intro hti
  have hhomTrue : ∀ w ∈ e₀, H.trait w = true := by
    intro w hw
    simp only [e₀, Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with hw | hw
    · subst w
      simpa [howner] using hti
    · subst w
      simpa [htrait] using hti
  have hnotFalse : ¬ ∀ w ∈ e₀, H.trait w = false := by
    intro h
    have hfalse := h (s i) (by simp [e₀])
    rw [howner] at hfalse
    rw [hti] at hfalse
    cases hfalse
  have hnotMixed : ¬ ((∃ w ∈ e₀, H.trait w = true) ∧
      (∃ w ∈ e₀, H.trait w = false)) := by
    rintro ⟨_, ⟨w, hw, hfalse⟩⟩
    have htrue := hhomTrue w hw
    cases htrue.symm.trans hfalse

  have hcountsEraseTrue :
      wholeEdgeCount E H.trait true + 1 =
        AronowAudit.P012.edgeCount (toState H) true := by
    change wholeEdgeCount (H.edges.erase e₀) H.trait true + 1 =
      (H.edges.filter (fun e => ∀ w ∈ e, H.trait w = true)).card
    exact wholeEdgeCount_erase_qual H.edges H.trait e₀ true he₀ hhomTrue
  have hcountsEraseFalse :
      wholeEdgeCount E H.trait false =
        AronowAudit.P012.edgeCount (toState H) false := by
    change wholeEdgeCount (H.edges.erase e₀) H.trait false =
      (H.edges.filter (fun e => ∀ w ∈ e, H.trait w = false)).card
    exact wholeEdgeCount_erase_nonqual H.edges H.trait e₀ false hnotFalse
  have hcountsEraseMixed :
      wholeMixedCount E H.trait = AronowAudit.P012.mixedCount (toState H) := by
    change wholeMixedCount (H.edges.erase e₀) H.trait =
      (H.edges.filter (fun e =>
        (∃ w ∈ e, H.trait w = true) ∧ (∃ w ∈ e, H.trait w = false))).card
    exact wholeMixedCount_erase_nonqual H.edges H.trait e₀ hnotMixed

  have hflipCounts := by
    simpa only [leafCompletion_eq, flipTrait_eq] using
      (AronowAudit.P012.leaf_flip_edge_counts (toData D) hD i hi hsp)
  have htrueFlip :
      AronowAudit.P012.edgeCount (toState K) true + 1 =
        AronowAudit.P012.edgeCount (toState H) true := by
    simpa [H, K, v, hti] using hflipCounts.1 true
  have hfalseFlip :
      AronowAudit.P012.edgeCount (toState K) false =
        AronowAudit.P012.edgeCount (toState H) false := by
    simpa [H, K, v, hti] using hflipCounts.1 false
  have hmixedFlip :
      AronowAudit.P012.mixedCount (toState K) =
        AronowAudit.P012.mixedCount (toState H) + 1 := by
    simpa [H, K, v] using hflipCounts.2

  have hxKNat : wholeEdgeCount E H.trait true =
      AronowAudit.P012.edgeCount (toState K) true := by
    omega
  have hyKNat : wholeEdgeCount E H.trait false =
      AronowAudit.P012.edgeCount (toState K) false := by
    omega
  have hcKNat : wholeMixedCount E H.trait + 1 =
      AronowAudit.P012.mixedCount (toState K) := by
    omega

  have hHsimple : AronowAudit.P012.Simple (toState H) := by
    simpa only [Simple_eq] using hH.1.1
  have hKsimple : AronowAudit.P012.Simple (toState K) := by
    simpa only [Simple_eq] using hK.1.1
  have h0src : 0 < AronowAudit.P012.sampledTraitDegree (toData D) false := by
    simpa only [sampledTraitDegree_eq] using h0
  have h1src : 0 < AronowAudit.P012.sampledTraitDegree (toData D) true := by
    simpa only [sampledTraitDegree_eq] using h1
  have hH0src := AronowAudit.P012.sampled_trait_positive_transfer
    (toData D) (toState H) hHsrc false h0src
  have hH1src := AronowAudit.P012.sampled_trait_positive_transfer
    (toData D) (toState H) hHsrc true h1src
  have hK0src := AronowAudit.P012.sampled_trait_positive_transfer
    (toData D) (toState K)
    (by simpa only [Compatible_eq] using hK) false h0src
  have hK1src := AronowAudit.P012.sampled_trait_positive_transfer
    (toData D) (toState K)
    (by simpa only [Compatible_eq] using hK) true h1src

  have hformulaH := AronowAudit.P012.graph_homophily_formula
    (toState H) hHsimple hH0src hH1src
  have hformulaK := AronowAudit.P012.graph_homophily_formula
    (toState K) hKsimple hK0src hK1src
  have hvalueH : hValue H = AronowAudit.P012.phi
      (AronowAudit.P012.edgeCount (toState H) true)
      (AronowAudit.P012.edgeCount (toState H) false)
      (AronowAudit.P012.mixedCount (toState H)) := by
    simpa only [hValue_eq] using hformulaH.2.2.2
  have hvalueK : hValue K = AronowAudit.P012.phi
      (AronowAudit.P012.edgeCount (toState K) true)
      (AronowAudit.P012.edgeCount (toState K) false)
      (AronowAudit.P012.mixedCount (toState K)) := by
    simpa only [hValue_eq] using hformulaK.2.2.2

  have hyc : 0 < 2*y+c := by
    have hdeg := (AronowAudit.P012.binary_edge_counts
      (toState H) hHsimple).2.1
    have hposNat : 0 < 2 * AronowAudit.P012.edgeCount (toState H) false +
        AronowAudit.P012.mixedCount (toState H) := by
      rw [← hdeg]
      exact hH0src
    have hposReal : (0:ℝ) <
        2 * (AronowAudit.P012.edgeCount (toState H) false : ℝ) +
          AronowAudit.P012.mixedCount (toState H) := by
      exact_mod_cast hposNat
    have hyR : y = (AronowAudit.P012.edgeCount (toState H) false : ℝ) := by
      dsimp [y]
      exact_mod_cast hcountsEraseFalse
    have hcR : c = (AronowAudit.P012.mixedCount (toState H) : ℝ) := by
      dsimp [c]
      exact_mod_cast hcountsEraseMixed
    rw [hyR, hcR]
    exact hposReal

  have hformulaH' : hValue H = wholePhi (x+1) y c := by
    have hxR : x + 1 =
        (AronowAudit.P012.edgeCount (toState H) true : ℝ) := by
      dsimp [x]
      exact_mod_cast hcountsEraseTrue
    have hyR : y =
        (AronowAudit.P012.edgeCount (toState H) false : ℝ) := by
      dsimp [y]
      exact_mod_cast hcountsEraseFalse
    have hcR : c =
        (AronowAudit.P012.mixedCount (toState H) : ℝ) := by
      dsimp [c]
      exact_mod_cast hcountsEraseMixed
    rw [hvalueH, ← hxR, ← hyR, ← hcR]
    simp [wholePhi, AronowAudit.P012.phi]

  have hformulaK' : hValue K = wholePhi x y (c+1) := by
    have hxR : x =
        (AronowAudit.P012.edgeCount (toState K) true : ℝ) := by
      dsimp [x]
      exact_mod_cast hxKNat
    have hyR : y =
        (AronowAudit.P012.edgeCount (toState K) false : ℝ) := by
      dsimp [y]
      exact_mod_cast hyKNat
    have hcR : c + 1 =
        (AronowAudit.P012.mixedCount (toState K) : ℝ) := by
      dsimp [c]
      exact_mod_cast hcKNat
    rw [hvalueK, ← hxR, ← hyR, ← hcR]
    simp [wholePhi, AronowAudit.P012.phi]

  exact ⟨hyc, hformulaH', hformulaK'⟩

end SAP.P012b.WH.W1
