import SAP.P053.Defs
import SAP.P053.Bridge
import AronowAudit.P053.P053_Audit
import AronowAudit.P053.P053_MomentConsistency
import AronowAudit.P053.P053_CLT
import SAP.P053.WH.W1.Proofs.T2

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P053
open Filter
open scoped BigOperators Topology
noncomputable section

theorem T1 {S : Type*} : T1Statement S := by
  intro n1 n0 h1 h0 y
  obtain ⟨ha, hb⟩ := AronowAudit.P053.binary_support_identification n1 n0 h1 h0 y
  refine ⟨ha, hb, ?_, ?_, ?_, ?_⟩
  · intro h
    exact ⟨tableFactor n1 n0 (totalSuccesses y) h, rfl,
      AronowAudit.P053.explicit_table_factor n1 n0 (totalSuccesses y) h1 h0 h⟩
  · intro F hinv
    obtain ⟨g, hg⟩ := AronowAudit.P053.ordered_sample_statistic_factors n1 n0 h1 h0 y F hinv
    refine ⟨g, ?_⟩
    intro s hs
    exact ⟨(Finset.mem_powersetCard.mp hs).2,
      AronowAudit.P053.binary_control_card n1 n0 s hs, hg s hs⟩
  · exact AronowAudit.P053.table_samples_invariant n1 n0
  · exact AronowAudit.P053.factor_iff_table_constant n1 n0 h1 h0 y

theorem T2 : T2WholeStatement := SAP.P053.WH.W1.T2_whole

theorem T3 : T3Statement := by
  refine ⟨AronowAudit.P053.six_difference_distribution,
    AronowAudit.P053.six_upper_tail_difference,
    AronowAudit.P053.four_counterexample_values.1,
    AronowAudit.P053.four_upper_tail_difference, ?_⟩
  intro n1 n0 _h1 _h0 y g
  dsimp only
  intro hg z hz
  exact AronowAudit.P053.increasing_same_p n1
    (fun s => sampleMean s y-sampleMean sᶜ y) g hg z hz

theorem T4 : T4Statement := by
  intro p S1 S0 hp hp1 hS1 hS0
  exact ⟨AronowAudit.P053.limit_difference_identity p S1 S0 hp hp1,
    AronowAudit.P053.apparent_paradox_condition p S1 S0 hp hp1 hS1 hS0⟩

theorem T5 : T5Statement := by
  intro E p v1 v0 vt tauInf h
  exact AronowAudit.P053.fisher_ols_asymptotics (fun k => Bridge.toPopulation (E k))
    p v1 v0 vt tauInf (Bridge.toRegularity h)

theorem T6 : T6Statement := by
  intro E p v1 v0 vt tauInf h
  have hr := Bridge.toRegularity h
  refine ⟨?_, ?_, ?_⟩
  · intro hl
    obtain ⟨ha, hb⟩ := AronowAudit.P053.local_alternative_equivalence
      (fun k => Bridge.toPopulation (E k)) p v1 v0 vt tauInf hr hl
    exact ⟨ha, fun hv _hpos => hb hv⟩
  · intro hc
    exact AronowAudit.P053.constant_effect_asymptotics
      (fun k => Bridge.toPopulation (E k)) p v1 v0 vt tauInf hr hc
  · intro hs hv _hpos
    exact AronowAudit.P053.sharp_null_wald_validity
      (fun k => Bridge.toPopulation (E k)) p v1 v0 vt tauInf hr hs hv

theorem T7 : T7Statement := by
  intro E p σ1 σ0 vt tauInf _hσ1 _hσ0 h
  have hr := Bridge.toRegularity h
  have hw := AronowAudit.P053.wald_comparison_asymptotics
    (fun k => Bridge.toPopulation (E k)) p (σ1^2) (σ0^2) vt tauInf hr
  refine ⟨hw, ?_, ?_⟩
  · intro hne
    obtain ⟨hvar, hp⟩ := AronowAudit.P053.unequal_wald_limits_necessary p (σ1^2) (σ0^2) hne
    exact ⟨fun he => hvar (congrArg (fun x : ℝ => x^2) he), hp⟩
  · intro hl
    exact AronowAudit.P053.fisher_neyman_local_comparison
      (fun k => Bridge.toPopulation (E k)) p (σ1^2) (σ0^2) vt tauInf hr hl

theorem T8 : T8Statement := by
  refine ⟨?_, ?_, ?_, AronowAudit.P053.witness_limit_numbers.2.2.2⟩
  · intro E p v1 v0 vt tauInf h
    have hr := Bridge.toRegularity h
    refine ⟨AronowAudit.P053.neyman_asymptotic_bound
      (fun k => Bridge.toPopulation (E k)) p v1 v0 vt tauInf hr, ?_⟩
    intro hc
    have ha := AronowAudit.P053.constant_effect_limit_agreement
      (fun k => Bridge.toPopulation (E k)) p v1 v0 vt tauInf hr hc
    refine ⟨ha, ?_⟩
    intro k
    have hf : populationVariance (E k) (E k).Y1 = populationVariance (E k) (E k).Y0 ∧
        populationVariance (E k) (unitEffects (E k)) = 0 := ha.1 k
    exact ⟨congrArg Real.sqrt hf.1, by rw [hf.2]; exact Real.sqrt_zero⟩
  · exact AronowAudit.P053.heterogeneous_witness_finite
  · have hw := AronowAudit.P053.anticonservative_limit_exists
    exact ⟨Bridge.fromRegularity hw.1, hw.2⟩

end
end SAP.P053
