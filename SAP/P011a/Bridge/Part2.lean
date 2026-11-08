import SAP.P011a.Bridge.Part1
import AronowAudit.P011.P011_Audit
import AronowAudit.P011.P011_BlockOLSCompletion
import AronowAudit.P011.P011_CorrectedAsymptoticCompletion
import AronowAudit.P011.P011_DataMatrixCompletion
import AronowAudit.P011.P011_DenseVarianceCompletion
import AronowAudit.P011.P011_ExpectationCompletion
import AronowAudit.P011.P011_FiniteCompletion
import AronowAudit.P011.P011_FiniteLawCompletion
import AronowAudit.P011.P011_HomoskedasticCompletion
import AronowAudit.P011.P011_MeanCompletion
import AronowAudit.P011.P011_OracleCompletion
import AronowAudit.P011.P011_QuadraticCompletion
import AronowAudit.P011.P011_SampleCompletion
import AronowAudit.P011.P011_SpectralCompletion
import AronowAudit.P011.Wave1.Gap.FidP011
import AronowAudit.P011.Wave1.Gap.GLP011B1
import AronowAudit.P011.Wave1.Gap.GLP011B2
import AronowAudit.P011.Wave1.Gap.GLP011B3
import AronowAudit.P011.Wave1.Gap.GLP011B6
import AronowAudit.P011.Wave1.Gap.GLP011B7
import AronowAudit.P011.Wave1.Gap.GLP011B8
import AronowAudit.P011.Wave1.Gap.GP011B1
import AronowAudit.P011.Wave1.Gap.GP011B2
import AronowAudit.P011.Wave1.Gap.GP011B2b
import AronowAudit.P011.Wave1.Gap.GP011B3

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P011a.Bridge

open MeasureTheory ProbabilityTheory Filter Finset
open scoped BigOperators Topology Classical Matrix NNReal ENNReal
noncomputable section
set_option maxRecDepth 4000
set_option maxHeartbeats 1500000

theorem CycleCounterexample_proved : SAP.P011a.CycleCounterexample := by
  exact AronowAudit.P011.Wave1.cycle_counterexample_proof

theorem PathCounterexample_proved : SAP.P011a.PathCounterexample := by
  intro t ht
  exact AronowAudit.P011.Wave1.path_counterexample_proof t ht

theorem PathMoments_proved : SAP.P011a.PathMoments := by
  intro t ht
  exact AronowAudit.P011.Wave1.path_block_moments_with_covariance t ht

theorem OracleConvergence_proved : SAP.P011a.OracleConvergence := by
  intro F c1 c2 c3 c4 h
  exact AronowAudit.P011.revised_oracle_convergence (family F) c1 c2 c3 c4 h

theorem OracleExpectation_proved : SAP.P011a.OracleExpectation := by
  intro F c1 c2 c3 c4 h k
  exact AronowAudit.P011.revised_oracle_expectation (family F) c1 c2 c3 c4 h k

theorem SampleVarianceConvergence_proved : SAP.P011a.SampleVarianceConvergence := by
  intro F c1 c2 c3 c4 h
  exact AronowAudit.P011.revised_sample_variance (family F) c1 c2 c3 c4 h

theorem OracleMeanConditions_proved : SAP.P011a.OracleMeanConditions := by
  intro F c1 c2 c3 c4 h
  exact AronowAudit.P011.oracle_mean_conditions (family F) c1 c2 c3 c4 h

theorem CliqueCharacterization_proved : SAP.P011a.CliqueCharacterization := by
  intro n hn A
  exact AronowAudit.P011.clique_characterization A

theorem DeterministicExpansion_proved : SAP.P011a.DeterministicExpansion := by
  intro F c1 c2 c3 c4 K h M hM hK
  exact AronowAudit.P011.deterministic_quadratic_expansion (family F) c1 c2 c3 c4 K h M hM hK

theorem QuadraticExpectation_proved : SAP.P011a.QuadraticExpectation := by
  intro n hn m hL2 M hM
  exact AronowAudit.P011.quadratic_expectation hn (model m) hL2 M hM

theorem DataDependentFailure_proved : SAP.P011a.DataDependentFailure := by
  exact AronowAudit.P011.data_dependent_expansion_failure

theorem CorrectedFinite_proved : SAP.P011a.CorrectedFinite := by
  intro n hn R A d hA x
  exact AronowAudit.P011.corrected_finite hn R A d hA x

theorem CorrectedAsymptotic_proved : SAP.P011a.CorrectedAsymptotic := by
  intro F c1 c2 c3 c4 h hv A hm
  exact AronowAudit.P011.corrected_asymptotic (family F) c1 c2 c3 c4 h hv A hm

theorem CorrectedMatrix_proved : SAP.P011a.CorrectedMatrix := by
  intro n hn R A d hA x
  exact AronowAudit.P011.corrected_matrix_majorant R A d hA x

theorem PositivePartFinite_proved : SAP.P011a.PositivePartFinite := by
  intro n hn A
  exact AronowAudit.P011.positive_part_finite A

theorem PositivePartConservative_proved : SAP.P011a.PositivePartConservative := by
  intro F c1 c2 c3 c4 h
  exact AronowAudit.P011.positive_part_conservative (family F) c1 c2 c3 c4 h

theorem PositivePartUnique_proved : SAP.P011a.PositivePartUnique := by
  intro n A M hM hnearest
  exact AronowAudit.P011.positive_part_nearest_unique A M hM hnearest

theorem PositivePartCycle_proved : SAP.P011a.PositivePartCycle := by
  exact AronowAudit.P011.Wave1.positive_part_cycle_claims_proof

theorem PositivePartNonaffine_proved : SAP.P011a.PositivePartNonaffine := by
  exact AronowAudit.P011.positive_part_objective_nonaffine

theorem CycleSpectrum_proved : SAP.P011a.CycleSpectrum := by
  exact AronowAudit.P011.cycle_spectral_certificate

theorem DegreeOnlyFinite_proved : SAP.P011a.DegreeOnlyFinite := by
  intro n hn d D hd x A Ap hm hp
  exact AronowAudit.P011.Wave1.degree_only_finite_proof hn d D hd x A Ap hm hp

theorem DegreeOnlyIdentity_proved : SAP.P011a.DegreeOnlyIdentity := by
  intro n hn A x
  exact AronowAudit.P011.degree_only_edge_identity A x

theorem DegreeOnlyConservative_proved : SAP.P011a.DegreeOnlyConservative := by
  intro F c1 c2 c3 c4 h hv hr A hm
  exact AronowAudit.P011.Wave1.degree_only_conservative_proof (family F) c1 c2 c3 c4 h hv hr A hm

theorem UnboundedDegreeGap_proved : SAP.P011a.UnboundedDegreeGap := by
  intro A hm
  exact AronowAudit.P011.Wave1.unbounded_caps_gap_proof A hm

theorem RevisedCorollaries_proved : SAP.P011a.RevisedCorollaries := by
  intro F c1 c2 c3 c4 h V hV
  exact AronowAudit.P011.Wave1.revised_corollaries_proof (family F) c1 c2 c3 c4 h V hV

theorem ResidualRootRate_proved : SAP.P011a.ResidualRootRate := by
  intro F c1 c2 c3 c4 h p D γ γhat hmeas hmean hbound hrate A hv hm
  exact AronowAudit.P011.Wave1.residual_root_n_proof (family F) c1 c2 c3 c4 h p D γ γhat hmeas hmean hbound hrate A hv hm

theorem ResidualPrediction_proved : SAP.P011a.ResidualPrediction := by
  intro F c1 c2 c3 c4 h p D γ γhat hmeas hmean hz herr A hv hm
  exact AronowAudit.P011.Wave1.residual_prediction_stability_proof (family F) c1 c2 c3 c4 h p D γ γhat hmeas hmean hz herr A hv hm

theorem ResidualMisspecification_proved : SAP.P011a.ResidualMisspecification := by
  intro F c1 c2 c3 c4 h p D γstar γhat hmeas hz herr
  exact AronowAudit.P011.Wave1.misspecified_residual_limit_proof (family F) c1 c2 c3 c4 h p D γstar γhat hmeas hz herr

theorem ResidualFailure_proved : SAP.P011a.ResidualFailure := by
  exact AronowAudit.P011.Wave1.residual_missing_regularity_proof

theorem ResidualPerturbation_proved : SAP.P011a.ResidualPerturbation := by
  intro n M hM r z
  exact AronowAudit.P011.residual_perturbation M hM r z

theorem UniversalImpossibility_proved : SAP.P011a.UniversalImpossibility := by
  intro a b ha hb
  exact AronowAudit.P011.Wave1.universal_consistency_impossible_proof a b ha hb

theorem MixtureMoments_proved : SAP.P011a.MixtureMoments := by
  intro a b s n hn
  exact AronowAudit.P011.mixture_finite_moments a b s n hn

theorem AlternatingCounterexample_proved : SAP.P011a.AlternatingCounterexample := by
  exact AronowAudit.P011.Wave1.alternating_counterexample_proof

theorem AlternatingMoments_proved : SAP.P011a.AlternatingMoments := by
  intro k
  exact AronowAudit.P011.Wave1.alternating_finite_moments_proof k

theorem HomoskedasticRepair_proved : SAP.P011a.HomoskedasticRepair := by
  intro F c1 c2 c3 c4 h hs
  exact AronowAudit.P011.homoskedastic_repair (family F) c1 c2 c3 c4 h hs

theorem RelaxationUpperBound_proved : SAP.P011a.RelaxationUpperBound := by
  intro n hn R d w U hU
  exact AronowAudit.P011.relaxation_upper_bound hn R d w U hU

theorem RelaxationGaps_proved : SAP.P011a.RelaxationGaps := by
  exact AronowAudit.P011.relaxation_gaps

end
end SAP.P011a.Bridge
