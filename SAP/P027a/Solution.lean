import SAP.P027a.Defs
import SAP.P027a.Bridge
import AronowAudit.P027.P027_Audit
import AronowAudit.P027.Wave1.Gap.GLP027P016P031B1
import AronowAudit.P027.Wave1.Gap.T2Conjunction
import AronowAudit.P027.Wave1.AePartition
import SAP.P027a.WH.W1.Proofs.T1
import SAP.P027a.WH.W1.Proofs.T2
import SAP.P027a.WH.W1.Proofs.T3
import SAP.P027a.WH.W1.Proofs.T4
import SAP.P027a.WH.W1.Proofs.T10
import SAP.P027a.WH.W2.Proofs.T11
import SAP.P027a.WH.W2.Proofs.T13

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators Topology
open Filter MeasureTheory ProbabilityTheory
open SAP.P027a SAP.P027a.Bridge

theorem SAP.P027a.T1 : SAP.P027a.T1WholeStatement :=
  SAP.P027a.WH.W1.T1_whole

theorem SAP.P027a.T2 : SAP.P027a.T2WholeStatement :=
  SAP.P027a.WH.W1.T2_whole

theorem SAP.P027a.T3 : SAP.P027a.T3WholeStatement :=
  SAP.P027a.WH.W1.T3_whole

theorem SAP.P027a.T4 : SAP.P027a.T4WholeStatement :=
  SAP.P027a.WH.W1.T4_whole

theorem SAP.P027a.T5 : SAP.P027a.T5Statement := by
  refine ⟨AronowAudit.P027.a3_grouped_table_refutation, AronowAudit.P027.row21_exact_witness, ?_⟩
  have h : Row21Witness := AronowAudit.P027.row21_exact_witness
  rcases h with ⟨_, _, _, hv, hh, hu, hg⟩
  dsimp only [Row21MeanValues]
  rw [hv, hh, hu, hg]
  norm_num

theorem SAP.P027a.T6 : SAP.P027a.T6Statement := by
  refine ⟨periodic_inclusions, AronowAudit.P027.periodic_finite_correction, ?_, AronowAudit.P027.realized_ratio_example⟩
  intro Ξ _ μ _ r m hr hm β σ2 hσ ε hε
  dsimp only
  intro hguard
  rcases AronowAudit.P027.periodic_model_moments μ r m hr hm β σ2 hσ ε hε with
    ⟨hY, hA, hV, hH, hQ, hUc, hGc, hratios, hbias, hWR⟩
  exact ⟨hY, hV, hGc, fun hL => (hratios hL).2⟩

theorem SAP.P027a.T10 : SAP.P027a.T10WholeStatement :=
  SAP.P027a.WH.W1.T10_whole

theorem SAP.P027a.T11 : SAP.P027a.T11WholeStatement :=
  SAP.P027a.WH.W2.T11_whole

theorem SAP.P027a.T12 : SAP.P027a.T12Statement := by
  refine ⟨?_, ?_, AronowAudit.P027.Wave1.nb_generated_witness_proof, ?_, ?_⟩
  · rcases AronowAudit.P027.invalid_pps_counterexample with ⟨hs, hpi, hsum, hdiff, hn⟩
    exact ⟨hs, hpi, hsum, hdiff, fun Ω _ D hv => hn Ω (toAudit D hv)⟩
  · refine ⟨?_, ?_, ?_⟩
    · have hs : (∑ k, invalidSize8 k) = 37 := AronowAudit.P027.invalid_pps_counterexample.1
      intro k
      rw [printedPPS, hs]
      by_cases hk : k = 0 <;> simp [invalidSize8, hk] <;> norm_num
    · intro Ω _ D hv k
      exact AronowAudit.P027.pi_le_one (toAudit D hv) k
    · intro k
      by_cases hk : k = 0 <;> norm_num [nbWitness, invalidSize8, hk]
  · intro k
    exact ⟨(AronowAudit.P027.Wave1.nb_generated_coordinate_integral 8 k (fun j => (j:ℝ)) 6
        (fun j => by positivity) AronowAudit.P027.Wave1.nb_generated_first_sum).1,
      (AronowAudit.P027.Wave1.nb_generated_coordinate_integral 8 k (fun j => ((j:ℝ)-6)^2) 16
        (fun j => sq_nonneg _) AronowAudit.P027.Wave1.nb_generated_centered_sum).1⟩
  · intro row
    rcases AronowAudit.P027.Wave1.all_pps_configurations_invalid_proof row with
      ⟨hN, hm, hmN, hL, hsum, hx, hbad, hprob, hpos, hn⟩
    exact ⟨hN, hm, hmN, hL, hsum, hx, hbad, hprob, hpos,
      fun Ω _ D hv => hn Ω (toAudit D hv)⟩

theorem SAP.P027a.T13 : SAP.P027a.T13WholeStatement :=
  SAP.P027a.WH.W2.T13_whole
