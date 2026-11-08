import SAP.P012b.Defs.WholeW1
import SAP.P012b.Bridge

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 3000

namespace SAP.P012b.WH.W1

open Finset SAP.P012b.Bridge
noncomputable section

theorem restricted14 : SAP.P012b.T14Statement := by
  unfold T14Statement
  sap_transfer (AronowAudit.P012.domain_counterexamples)

theorem restricted15 : SAP.P012b.T15Statement := by
  constructor
  · intro H hS hm
    have hd := AronowAudit.P012.homophily_domain (toState H) hS hm
    simp only [hDenominator_eq, traitDegree_eq, state_edges, HomophilyDefined_eq] at hd
    have hpart : traitDegree H true + traitDegree H false = 2 * H.edges.card :=
      (AronowAudit.P012.trait_degree_partition (toState H)).trans
        (AronowAudit.P012.degree_sum_twice_edges (toState H) hS)
    have hpartR : (traitDegree H true : ℝ) + traitDegree H false =
        2 * (H.edges.card : ℝ) := by exact_mod_cast hpart
    have hzero : (traitDegree H false : ℝ) =
        2 * (H.edges.card : ℝ) - traitDegree H true := by linarith
    refine ⟨AronowAudit.P012.degreeTraitSum_eq (toState H), hpart,
      hd.1, hd.2.1, ?_, hd.2.2.1, hd.2.2.2.1, hd.2.2.2.2⟩
    rw [hd.2.1, hzero]
  · intro D hD
    have hh : (∀ H, Compatible D H → HomophilyDefined H) ↔
        0 < sampledTraitDegree D false ∧ 0 < sampledTraitDegree D true := by
      sap_transfer (AronowAudit.P012.full_domain_conditions (toData D) hD)
    have hp : (∀ H, Compatible D H → PreferentialDefined D H) ↔
        D.seeds.card < D.sampled.card := by
      sap_transfer (AronowAudit.P012.full_p_domain_conditions (toData D) hD)
    have hr := AronowAudit.P012.result_domain_conditions (toData D) hD
    refine ⟨?_, hh, hp, hr.1, hr.2, ?_, ?_, ?_⟩
    · intro H hH
      have hs : ∀ j ∈ nonseeds D,
          s j ∈ susceptible D H (D.parent j) j ∧
            0 < (susceptible D H (D.parent j) j).card :=
        fun j hj => AronowAudit.P012.recruit_is_susceptible (toData D) (toState H) hH j hj
      refine ⟨⟨?_, fun hn => hp.mpr hn H hH⟩, hs⟩
      intro hdom
      have hn := hdom.1
      rw [nonseeds, card_sdiff_of_subset hD.1] at hn
      omega
    · intro hs L U
      exact ⟨fun h => h.2, fun h => ⟨hh.mpr hs, h⟩⟩
    · intro hn L U
      exact ⟨fun h => h.2, fun h => ⟨hp.mpr hn, h⟩⟩
    · rintro hs ⟨L, U, hregion⟩
      exact hs (hh.mp hregion.1)

theorem restricted17 : SAP.P012b.T17Statement := by
  unfold T17Statement
  sap_transfer (@AronowAudit.P012.induced_compatibility)

theorem restricted22 : SAP.P012b.T22Statement := by
  refine ⟨?_, ?_, ?_⟩
  · sap_transfer (@AronowAudit.P012.joint_identification)
  · sap_transfer (@AronowAudit.P012.joint_leaf_flip_witness)
  · sap_transfer (@AronowAudit.P012.preferential_identification)

end
end SAP.P012b.WH.W1
