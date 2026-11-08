import SAP.P011a.Bridge.Part2

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P011a.Bridge

open MeasureTheory ProbabilityTheory Filter Finset
open scoped BigOperators Topology Classical Matrix NNReal ENNReal
noncomputable section
set_option maxRecDepth 4000
set_option maxHeartbeats 1500000

/-- No data change in the degree-constrained optimization problem. -/
def problem {n : ℕ} (P : SAP.P011a.DegreeProblem n) : AronowAudit.P011.DegreeProblem n where
  forced := P.forced
  cap := P.cap
  weight := P.weight

/-- SAP uses sum data for the two kinds of gadget edge. -/
def edgeEquiv {n : ℕ} (P : SAP.P011a.DegreeProblem n) :
    SAP.P011a.GadgetEdge P ≃ AronowAudit.P011.GadgetEdge (problem P) :=
  (AronowAudit.P011.gadgetEdgeEquiv (problem P)).symm

def matchingEquiv {n : ℕ} (P : SAP.P011a.DegreeProblem n) :
    Finset (SAP.P011a.GadgetEdge P) ≃ Finset (AronowAudit.P011.GadgetEdge (problem P)) :=
  (edgeEquiv P).finsetCongr

theorem ends_eq {n : ℕ} (P : SAP.P011a.DegreeProblem n) (e : SAP.P011a.GadgetEdge P) :
    AronowAudit.P011.gadgetEnds (edgeEquiv P e) = SAP.P011a.gadgetEnds e := by
  rcases e with e | ⟨e,side,slot⟩ <;> rfl

theorem weight_eq {n : ℕ} (P : SAP.P011a.DegreeProblem n) (e : SAP.P011a.GadgetEdge P) :
    AronowAudit.P011.gadgetWeight (edgeEquiv P e) = SAP.P011a.gadgetWeight e := by
  rcases e with e | ⟨e,side,slot⟩ <;> rfl

theorem sum_eq {n : ℕ} (P : SAP.P011a.DegreeProblem n) (J : Finset (SAP.P011a.GadgetEdge P)) :
    (∑ e ∈ matchingEquiv P J, AronowAudit.P011.gadgetWeight e) =
      ∑ e ∈ J, SAP.P011a.gadgetWeight e := by
  simp only [matchingEquiv, Equiv.finsetCongr_apply, Finset.sum_map, Equiv.coe_toEmbedding, weight_eq]

theorem matching_iff {n : ℕ} (P : SAP.P011a.DegreeProblem n)
    (J : Finset (SAP.P011a.GadgetEdge P)) :
    SAP.P011a.IsMatching J ↔ AronowAudit.P011.IsMatching (matchingEquiv P J) := by
  constructor
  · intro h e he f hf hne
    change e ∈ J.map (edgeEquiv P).toEmbedding at he
    change f ∈ J.map (edgeEquiv P).toEmbedding at hf
    rcases Finset.mem_map.mp he with ⟨e₀,he₀,rfl⟩
    rcases Finset.mem_map.mp hf with ⟨f₀,hf₀,rfl⟩
    have hne' : e₀ ≠ f₀ := fun h => hne (congrArg (edgeEquiv P) h)
    simp only [Equiv.coe_toEmbedding, ends_eq]
    exact h e₀ he₀ f₀ hf₀ hne'
  · intro h e he f hf hne
    have hne' : edgeEquiv P e ≠ edgeEquiv P f := fun h => hne ((edgeEquiv P).injective h)
    have H := h (edgeEquiv P e) (Finset.mem_map.mpr ⟨e,he,rfl⟩)
      (edgeEquiv P f) (Finset.mem_map.mpr ⟨f,hf,rfl⟩) hne'
    rw [ends_eq, ends_eq] at H
    exact H

theorem decode_eq {n : ℕ} (P : SAP.P011a.DegreeProblem n)
    (J : Finset (SAP.P011a.GadgetEdge P)) :
    AronowAudit.P011.decodeMatching (problem P) (matchingEquiv P J) =
      SAP.P011a.decodeMatching P J := by
  apply Finset.ext
  intro e
  have hmem (a : SAP.P011a.GadgetEdge P) :
      edgeEquiv P a ∈ matchingEquiv P J ↔ a ∈ J := by
    simp [matchingEquiv]
  change e ∈ (AronowAudit.P011.optionalEdges (problem P)).filter _ ↔
    e ∈ (SAP.P011a.optionalEdges P).filter _
  rw [Finset.mem_filter, Finset.mem_filter]
  change (e ∈ SAP.P011a.optionalEdges P ∧ ∃ he : e ∈ SAP.P011a.optionalEdges P,
    (∃ s, edgeEquiv P (Sum.inr ⟨⟨e,he⟩,false,s⟩) ∈ matchingEquiv P J) ∧
    (∃ s, edgeEquiv P (Sum.inr ⟨⟨e,he⟩,true,s⟩) ∈ matchingEquiv P J)) ↔ _
  simp only [hmem]

theorem MatchingReduction_proved : SAP.P011a.MatchingReduction := by
  intro n hn P
  have H := AronowAudit.P011.Wave1.matching_reduction_proof hn (problem P)
  refine ⟨H.1, ?_, H.2.2.1, H.2.2.2⟩
  intro hf
  refine ⟨(H.2.1 hf).1, ?_⟩
  intro J hJ hopt
  have hopt' : ∀ J' : Finset (AronowAudit.P011.GadgetEdge (problem P)), AronowAudit.P011.IsMatching J' →
      (∑ e ∈ J', AronowAudit.P011.gadgetWeight e) ≤
        ∑ e ∈ matchingEquiv P J, AronowAudit.P011.gadgetWeight e := by
    intro J' hJ'
    obtain ⟨K,rfl⟩ := (matchingEquiv P).surjective J'
    simpa only [sum_eq] using hopt K ((matching_iff P K).mpr hJ')
  have hres := (H.2.1 hf).2 (matchingEquiv P J) ((matching_iff P J).mp hJ) hopt'
  rw [decode_eq P J, sum_eq P J] at hres
  convert hres using 1 <;> rfl

theorem MatchingCounts_proved : SAP.P011a.MatchingCounts := by
  intro n P
  have H := AronowAudit.P011.matching_gadget_exact_counts (problem P)
  refine ⟨H.1, ?_⟩
  rw [Nat.card_congr (edgeEquiv P)]
  exact H.2

theorem witness_eq (second : Bool) :
    problem (SAP.P011a.matchingWitness second) = AronowAudit.P011.matchingWitness second := rfl

theorem MatchingInstances_proved : SAP.P011a.MatchingInstances := by
  have H := AronowAudit.P011.Wave1.matching_exact_instances_proof
  refine ⟨H.1, H.2.1, H.2.2.1, H.2.2.2.1, H.2.2.2.2.1, H.2.2.2.2.2.1, ?_⟩
  intro second
  let P := SAP.P011a.matchingWitness second
  have hinst : ∃ J : Finset (AronowAudit.P011.GadgetEdge (problem P)),
      AronowAudit.P011.IsMatching J ∧
      (∑ e ∈ J, AronowAudit.P011.gadgetWeight e) = (if second then 200 else 166) ∧
      (∀ J' : Finset (AronowAudit.P011.GadgetEdge (problem P)), AronowAudit.P011.IsMatching J' →
        (∑ e ∈ J', AronowAudit.P011.gadgetWeight e) ≤ ∑ e ∈ J, AronowAudit.P011.gadgetWeight e) :=
    H.2.2.2.2.2.2 second
  obtain ⟨J,hJ,hval,hopt⟩ := hinst
  change ∃ J : Finset (SAP.P011a.GadgetEdge P), _
  obtain ⟨K,rfl⟩ := (matchingEquiv P).surjective J
  refine ⟨K,(matching_iff P K).mpr hJ, ?_, ?_⟩
  · rw [sum_eq P K] at hval
    exact hval
  · intro J' hJ'
    have hle := hopt (matchingEquiv P J') ((matching_iff P J').mp hJ')
    rw [sum_eq P J', sum_eq P K] at hle
    exact hle

end
end SAP.P011a.Bridge
