import SAP.P001c.Defs
import AronowAudit.P001.P001_Foundations
import AronowAudit.P001.Wave1.Gap.GLP0013B2
import AronowAudit.P001.Wave1.Gap.GLP0013B3
import AronowAudit.P001.Wave1.QuadraticUniqueBlp
import AronowAudit.P001.Wave1.FinitePopulationPlugin
import AronowAudit.P001.Wave1.Gap.RepairT55
import AronowAudit.P001.Wave1.Gap.TailA.CDFDelta

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P001c.Bridge

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology Classical

theorem probability_eq : @probability = @AronowAudit.P001.prob := rfl
theorem expectation_eq : @expectation = @AronowAudit.P001.mean := rfl
theorem meanSquaredError_eq : @meanSquaredError = @AronowAudit.P001.mse := rfl
theorem cdfAt_eq : @cdfAt = @AronowAudit.P001.cdf := rfl
theorem convergesInProbability_eq :
    @convergesInProbability = @AronowAudit.P001.CP := rfl
theorem convergesInDistribution_eq :
    @convergesInDistribution = @AronowAudit.P001.CD := rfl
theorem isIID_eq : @isIID = @AronowAudit.P001.IID := rfl
theorem sampleAverage_eq : @sampleAverage = @AronowAudit.P001.sampleMean := rfl
theorem empiricalLaw_eq : @empiricalLaw = @AronowAudit.P001.empirical := rfl
theorem pluginVariance_eq : @pluginVariance = @AronowAudit.P001.sampleVariance := rfl
theorem correlationCoefficient_eq :
    @correlationCoefficient = @AronowAudit.P001.correlation := rfl
theorem affineRisk_eq : @affineRisk = @AronowAudit.P001.linearRisk := rfl
theorem regressionSlope_eq : @regressionSlope = @AronowAudit.P001.blpSlope := rfl
theorem regressionIntercept_eq :
    @regressionIntercept = @AronowAudit.P001.blpIntercept := rfl
theorem isConditionalMean_eq : @isConditionalMean = @AronowAudit.P001.IsCEF := rfl
theorem varianceConsistent_eq :
    @varianceConsistent = @AronowAudit.P001.VarianceConsistent := rfl
theorem standardErrorConsistent_eq :
    @standardErrorConsistent = @AronowAudit.P001.SEConsistent := rfl

/-- The project bundles the weights and their validity proofs; SAP uses the weights. -/
theorem finiteMean_eq {n : ℕ} (P : AronowAudit.P001.FiniteLaw n) (X : Fin n → ℝ) :
    finiteMean P.weight X = AronowAudit.P001.fmean P X := rfl
theorem finiteProbability_eq {n : ℕ} (P : AronowAudit.P001.FiniteLaw n)
    (A : Fin n → Prop) [DecidablePred A] :
    finiteProbability P.weight A = AronowAudit.P001.fprob P A := rfl
theorem finiteVariance_eq {n : ℕ} (P : AronowAudit.P001.FiniteLaw n) (X : Fin n → ℝ) :
    finiteVariance P.weight X = AronowAudit.P001.fvar P X := rfl
theorem finiteCovariance_eq {n : ℕ} (P : AronowAudit.P001.FiniteLaw n) (X Y : Fin n → ℝ) :
    finiteCovariance P.weight X Y = AronowAudit.P001.fcov P X Y := rfl
theorem finiteCorrelation_eq {n : ℕ} (P : AronowAudit.P001.FiniteLaw n) (X Y : Fin n → ℝ) :
    finiteCorrelation P.weight X Y = AronowAudit.P001.fcorrelation P X Y := rfl
theorem nullWeights_eq : nullWeights = AronowAudit.P001.nullPointLaw.weight := rfl
theorem signWeights_eq : signWeights = AronowAudit.P001.signLaw.weight := rfl
theorem equalWeights_eq (N : ℕ) (hN : 0 < N) :
    equalWeights N = (AronowAudit.P001.uniformFiniteLaw N hN).weight := rfl

theorem fairCoinLoss_eq : fairCoinLoss = AronowAudit.P001.coinLoss := rfl
theorem normalPDF_eq : normalPDF = AronowAudit.P001.normalDensity := rfl
theorem bivariatePDF_eq : bivariatePDF = AronowAudit.P001.bivariateNormalPDF := rfl
theorem isJointDensity_eq : isJointDensity = AronowAudit.P001.HasJointPDF := rfl
theorem intervalUniform_eq : intervalUniform = AronowAudit.P001.uniformLaw := rfl
theorem covarianceEntries_eq :
    @covarianceEntries = @AronowAudit.P001.covarianceMatrix := rfl
theorem affinePredictor_eq : @affinePredictor = @AronowAudit.P001.linearPredictor := rfl
theorem coordinatePartial_eq : @coordinatePartial = @AronowAudit.P001.partialAt := rfl
theorem powerTailMass_eq : powerTailMass = AronowAudit.P001.heavyMomentMass := rfl

theorem hadamardDerivative_eq : @hadamardDerivative = @AronowAudit.P001.HadamardAt := rfl
theorem supNorm_eq : supNorm = AronowAudit.P001.uniformNorm := rfl
theorem isCDF_eq : isCDF = AronowAudit.P001.IsRealCDF := rfl
theorem cdfHadamard_eq : cdfHadamard = AronowAudit.P001.CDFHadamard := rfl
theorem embedCDF_eq : embedCDF = AronowAudit.P001.kolmogorovEmbed := rfl
theorem cdfSet_eq : cdfSet = AronowAudit.P001.cdfDomain := rfl
theorem empiricalCDF_eq : @empiricalCDF = @AronowAudit.P001.empiricalCDFElement := rfl
theorem cdfTangent_eq : cdfTangent = AronowAudit.P001.CDFTangent := rfl
theorem isCDFBridge_eq : @isCDFBridge = @AronowAudit.P001.IsCDFBridge := rfl
theorem upperExpectation_eq : @upperExpectation = @AronowAudit.P001.outerMean := rfl
theorem outerWeakConvergence_eq :
    @outerWeakConvergence = @AronowAudit.P001.OuterWeakLimit := rfl
theorem quadraticFunctional_eq : quadraticFunctional = AronowAudit.P001.quadraticCDFFunctional := rfl

end SAP.P001c.Bridge
