import SAP.P001g.Defs
import SAP.P001g.Bridge.GuardedF
import SAP.P001g.Bridge.KLStatistic
import SAP.P001g.Bridge.SieveMSE
import AronowAudit.P001.P001_Foundations
import AronowAudit.P001.Wave1.Gap.GLP0011B2
import AronowAudit.P001.Wave1.Gap.DecideP001T116
import AronowAudit.P001.Wave1.CausalIpwDr
import AronowAudit.P001.P001_PrintedRefutations
import AronowAudit.P001.Wave1.MeanHadamard
import AronowAudit.P001.Wave1.SieveRate
import AronowAudit.P001.Wave1.Gap.RepairT120b
import AronowAudit.P001.Wave1.Gap.WP001bB1
import AronowAudit.P001.Wave1.Gap.PlaceboFTest
import AronowAudit.P001.Wave1.Gap.WP001bB2

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables false

namespace SAP.P001g.Bridge

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology
universe u v w z u1 v1

/-! Every correspondence is definitional; no project proof is copied. -/

theorem prob_eq : @SAP.P001g.prob = @AronowAudit.P001.prob := rfl

theorem mean_eq : @SAP.P001g.mean = @AronowAudit.P001.mean := rfl

theorem var_eq : @SAP.P001g.var = @AronowAudit.P001.var := rfl

theorem cdf_eq : @SAP.P001g.cdf = @AronowAudit.P001.cdf := rfl

theorem CP_eq : @SAP.P001g.CP = @AronowAudit.P001.CP := rfl

theorem CD_eq : @SAP.P001g.CD = @AronowAudit.P001.CD := rfl

theorem IID_eq : @SAP.P001g.IID = @AronowAudit.P001.IID := rfl

theorem sampleMean_eq : @SAP.P001g.sampleMean = @AronowAudit.P001.sampleMean := rfl

theorem empirical_eq : @SAP.P001g.empirical = @AronowAudit.P001.empirical := rfl

theorem HasPDF_eq : @SAP.P001g.HasPDF = @AronowAudit.P001.HasPDF := rfl

theorem IsCEF_eq : @SAP.P001g.IsCEF = @AronowAudit.P001.IsCEF := rfl

theorem CI_eq : @SAP.P001g.CI = @AronowAudit.P001.CI := rfl

theorem firstSample_eq : @SAP.P001g.firstSample = @AronowAudit.P001.firstSample := rfl

theorem observedOutcome_eq : @SAP.P001g.observedOutcome = @AronowAudit.P001.observedOutcome := rfl

theorem censored_eq : @SAP.P001g.censored = @AronowAudit.P001.censored := rfl

theorem missingEndpoint_eq : @SAP.P001g.missingEndpoint = @AronowAudit.P001.missingEndpoint := rfl

theorem conditionalMeanAt_eq : @SAP.P001g.conditionalMeanAt = @AronowAudit.P001.conditionalMeanAt := rfl

theorem standardizedMean_eq : @SAP.P001g.standardizedMean = @AronowAudit.P001.standardizedMean := rfl

theorem VarianceConsistent_eq : @SAP.P001g.VarianceConsistent = @AronowAudit.P001.VarianceConsistent := rfl

theorem kernelDensity_eq : @SAP.P001g.kernelDensity = @AronowAudit.P001.kernelDensity := rfl

theorem rectangleKernel_eq : @SAP.P001g.rectangleKernel = @AronowAudit.P001.rectangleKernel := rfl

theorem polynomialSieveLeastSquares_eq : @SAP.P001g.polynomialSieveLeastSquares =
    @AronowAudit.P001.IsSieveLS := rfl

theorem uniformNorm_eq : @SAP.P001g.uniformNorm = @AronowAudit.P001.uniformNorm := rfl

theorem IsRealCDF_eq : @SAP.P001g.IsRealCDF = @AronowAudit.P001.IsRealCDF := rfl

theorem CDFHadamard_eq : @SAP.P001g.CDFHadamard = @AronowAudit.P001.CDFHadamard := rfl

theorem HadamardAt_eq : @SAP.P001g.HadamardAt = @AronowAudit.P001.HadamardAt := rfl

theorem KolmogorovSpace_eq : @SAP.P001g.KolmogorovSpace = @AronowAudit.P001.KolmogorovSpace := rfl

theorem kolmogorovEmbed_eq : @SAP.P001g.kolmogorovEmbed = @AronowAudit.P001.kolmogorovEmbed := rfl

theorem finiteSecondCDF_eq : @SAP.P001g.finiteSecondCDF = @AronowAudit.P001.finiteSecondCDF := rfl

theorem cdfMeanFunctional_eq : @SAP.P001g.cdfMeanFunctional = @AronowAudit.P001.cdfMeanFunctional := rfl

theorem conditionalModelLaw_eq : @SAP.P001g.conditionalModelLaw = @AronowAudit.P001.conditionalModelLaw := rfl

theorem conditionalKL_eq : @SAP.P001g.conditionalKL = @AronowAudit.P001.conditionalKL := rfl

theorem expectedLogLikelihood_eq : @SAP.P001g.expectedLogLikelihood = @AronowAudit.P001.expectedLogLikelihood := rfl

theorem sampleLogLikelihood_eq : @SAP.P001g.sampleLogLikelihood = @AronowAudit.P001.sampleLogLikelihood := rfl

theorem sampleLikelihood_eq : @SAP.P001g.sampleLikelihood = @AronowAudit.P001.sampleLikelihood := rfl

theorem disjointMixture_eq : @SAP.P001g.disjointMixture = @AronowAudit.P001.disjointMixture := rfl

theorem olsRSS_eq : @SAP.P001g.olsRSS = @AronowAudit.P001.olsRSS := rfl

theorem olsCoef_eq : @SAP.P001g.olsCoef = @AronowAudit.P001.olsCoef := rfl

theorem placeboFStatistic_eq : @SAP.P001g.placeboFStatistic = @AronowAudit.P001.placeboFStatistic := rfl

theorem fReference_eq : @SAP.P001g.fReference = @AronowAudit.P001.fReference := rfl

theorem PluginPositiveNormalLimit_eq :
    SAP.P001g.PluginPositiveNormalLimit.{u} =
      AronowAudit.P001.PrintedConfidence.PrintedPluginPositiveNormalLimit.{u} := rfl

theorem t115 : SAP.P001g.T115Statement.{u} := by
  exact @AronowAudit.P001.random_assignment_ate_and_selection_bias

theorem t116 : SAP.P001g.T116Statement.{u, v, w, z, u1, v1} := by
  exact ⟨@AronowAudit.P001.Wave1.discrete_strong_ignorability_ate_sum_proof, @AronowAudit.P001.Wave1.strong_ignorability_repaired⟩

theorem t117 : SAP.P001g.T117Statement.{u} := by
  exact @AronowAudit.P001.Wave1.causal_ipw_and_dr_paper_contract

theorem t118 : SAP.P001g.T118Statement.{u} := by
  exact ⟨@AronowAudit.P001.PrintedConfidence.printed_plugin_positive_normal_limit_refuted, @AronowAudit.P001.Wave1.printed_finite_variance_mean_hadamard_refuted⟩

theorem t121 : SAP.P001g.T121Statement.{u} := by
  exact @AronowAudit.P001.Wave1.printed_subset_full_vector_consistency_refuted

theorem t125 : SAP.P001g.T125Statement.{u} := by
  exact @AronowAudit.P001.weak_law_finite_variance

theorem t126 : SAP.P001g.T126Statement.{u, v, w} := by
  exact ⟨@AronowAudit.P001.central_limit_finite_variance, @AronowAudit.P001.central_limit_standardized_mean, @AronowAudit.P001.standardized_mean_fixed_sample_moments⟩

theorem t127 : SAP.P001g.T127Statement.{u} := by
  exact @AronowAudit.P001.rectangular_kernel_consistency

theorem t128 : SAP.P001g.T128Statement.{u} := by
  exact @AronowAudit.P001.normal_approximation_confidence_interval

theorem t129 : SAP.P001g.T129Statement.{u, v} := by
  exact ⟨@AronowAudit.P001.product_maximum_likelihood_consistency, @AronowAudit.P001.Wave1.true_model_expected_log_maximum_with_support_zeros⟩

theorem t130 : SAP.P001g.T130Statement.{u} := by
  exact @AronowAudit.P001.Wave1.expected_value_bounds_paper_contract

end SAP.P001g.Bridge
