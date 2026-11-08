import SAP.P015b.Defs
import AronowAudit.P015.P015_Regression
import AronowAudit.P015.P015_PaperAssessments
import AronowAudit.P015.Wave1.Gap.FidP015
import AronowAudit.P015.P015_PositivityRefutation

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P015b.Bridge

universe u v

open SAP.P015b Matrix Finset MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology ENNReal NNReal

theorem finiteMean_eq : @SAP.P015b.finiteMean = @AronowAudit.P015.fExpectation := rfl

theorem IsFiniteLaw_eq : @SAP.P015b.IsFiniteLaw = @AronowAudit.P015.IsLaw := rfl

theorem finiteMass_eq : @SAP.P015b.finiteMass = @AronowAudit.P015.fMass := rfl

theorem finiteCellMean_eq : @SAP.P015b.finiteCellMean = @AronowAudit.P015.fCondMean := rfl

theorem finiteCellProbability_eq : @SAP.P015b.finiteCellProbability = @AronowAudit.P015.fCondProb := rfl

theorem finiteWeight_eq : @SAP.P015b.finiteWeight = @AronowAudit.P015.fWeight := rfl

theorem finiteEffective_eq : @SAP.P015b.finiteEffective = @AronowAudit.P015.fEffective := rfl

theorem finiteUnconfounded_eq : @SAP.P015b.finiteUnconfounded = @AronowAudit.P015.fCondIndep := rfl

theorem finiteVariance_eq : @SAP.P015b.finiteVariance = @AronowAudit.P015.fVariance := rfl

theorem populationCoefficients_eq : @SAP.P015b.populationCoefficients = @AronowAudit.P015.populationOLS := rfl

theorem sampleCoefficients_eq : @SAP.P015b.sampleCoefficients = @AronowAudit.P015.ols := rfl

theorem treatmentResidual_eq : @SAP.P015b.treatmentResidual = @AronowAudit.P015.sampleResidual := rfl

theorem precisionMatrix_eq : @SAP.P015b.precisionMatrix = @AronowAudit.P015.groupPrecision := rfl

theorem pooledCoefficients_eq : @SAP.P015b.pooledCoefficients = @AronowAudit.P015.pooledGLS := rfl

theorem precisionLoss_eq : @SAP.P015b.precisionLoss = @AronowAudit.P015.poolingLoss := rfl

theorem sigmoidMean_eq : @SAP.P015b.sigmoidMean = @AronowAudit.P015.logistic := rfl

theorem logOdds_eq : @SAP.P015b.logOdds = @AronowAudit.P015.logit := rfl

theorem binomialLogLikelihoodSAP_eq : @SAP.P015b.binomialLogLikelihoodSAP = @AronowAudit.P015.binomialLogLikelihood := rfl

theorem residualEquation_eq : @SAP.P015b.residualEquation = @AronowAudit.P015.groupedResidual := rfl

theorem binaryLogLikelihood_eq : @SAP.P015b.binaryLogLikelihood = @AronowAudit.P015.groupedLikelihood := rfl

theorem linkScoreMultiplier_eq : @SAP.P015b.linkScoreMultiplier = @AronowAudit.P015.scoreMultiplier := rfl

theorem affineCoefficients_eq : @SAP.P015b.affineCoefficients = @AronowAudit.P015.affineTheta := rfl

theorem controlVector_eq : @SAP.P015b.controlVector = @AronowAudit.P015.controlRow := rfl

theorem regressorVector_eq : @SAP.P015b.regressorVector = @AronowAudit.P015.regressorRow := rfl

theorem linearOutcome_eq : @SAP.P015b.linearOutcome = @AronowAudit.P015.affineOutcome := rfl

theorem controlDesign_eq : @SAP.P015b.controlDesign = @AronowAudit.P015.designV := rfl

theorem regressionDesign_eq : @SAP.P015b.regressionDesign = @AronowAudit.P015.designW := rfl

theorem fittedTreatmentCoefficients_eq : @SAP.P015b.fittedTreatmentCoefficients = @AronowAudit.P015.omegaHat := rfl

theorem fittedTreatmentResidual_eq : @SAP.P015b.fittedTreatmentResidual = @AronowAudit.P015.residualHat := rfl

theorem treatmentEstimate_eq : @SAP.P015b.treatmentEstimate = @AronowAudit.P015.betaHat := rfl

theorem squaredPopulationResidual_eq : @SAP.P015b.squaredPopulationResidual = @AronowAudit.P015.populationWeight := rfl

theorem MomentConvergence_eq : @SAP.P015b.MomentConvergence = @AronowAudit.P015.MomentLLN := rfl

theorem RegressionRegularity_eq : @SAP.P015b.RegressionRegularity = @AronowAudit.P015.OLSRegularity := rfl

theorem EffectiveMeanRegularity_eq : @SAP.P015b.EffectiveMeanRegularity = @AronowAudit.P015.CovariateRegularity := rfl

theorem firstGroupDesign_eq : @SAP.P015b.firstGroupDesign = @AronowAudit.P015.groupZ₁ := rfl

theorem secondGroupDesign_eq : @SAP.P015b.secondGroupDesign = @AronowAudit.P015.groupZ₂ := rfl

theorem firstGroupPrecision_eq : @SAP.P015b.firstGroupPrecision = @AronowAudit.P015.groupP₁ := rfl

theorem secondGroupPrecision_eq : @SAP.P015b.secondGroupPrecision = @AronowAudit.P015.groupP₂ := rfl

theorem poolingInverse_eq : @SAP.P015b.poolingInverse = @AronowAudit.P015.groupHinv := rfl

theorem binaryProfile_eq : @SAP.P015b.binaryProfile = @AronowAudit.P015.binaryX := rfl

theorem binaryTreatment_eq : @SAP.P015b.binaryTreatment = @AronowAudit.P015.binaryD := rfl

theorem leveragePopulation_eq : @SAP.P015b.leveragePopulation = @AronowAudit.P015.leverageLaw := rfl

theorem leverageDesign_eq : @SAP.P015b.leverageDesign = @AronowAudit.P015.leverageW := rfl

theorem leverageMoment_eq : @SAP.P015b.leverageMoment = @AronowAudit.P015.leverageQ := rfl

theorem leverageMomentInverse_eq : @SAP.P015b.leverageMomentInverse = @AronowAudit.P015.leverageQinv := rfl

theorem scaledLeverage_eq : @SAP.P015b.scaledLeverage = @AronowAudit.P015.populationLeverage := rfl

theorem RoundsWithin_eq : @SAP.P015b.RoundsWithin = @AronowAudit.P015.RoundsTo := rfl

theorem sigmoidTaylor_eq : @SAP.P015b.sigmoidTaylor = @AronowAudit.P015.logisticTaylor := rfl

theorem twoCellLogLikelihood_eq : @SAP.P015b.twoCellLogLikelihood = @AronowAudit.P015.extremeLikelihood := rfl

theorem TaylorFailure_eq : @SAP.P015b.TaylorFailure = @AronowAudit.P015.TaylorCounterexample := rfl

theorem squareProfile_eq : @SAP.P015b.squareProfile = @AronowAudit.P015.rootX := rfl

theorem squareTreatment_eq : @SAP.P015b.squareTreatment = @AronowAudit.P015.rootD := rfl

theorem squarePopulation_eq : @SAP.P015b.squarePopulation = @AronowAudit.P015.rootLaw := rfl

theorem squarePropensity_eq : @SAP.P015b.squarePropensity = @AronowAudit.P015.rootE := rfl

theorem squareBaseline_eq : @SAP.P015b.squareBaseline = @AronowAudit.P015.rootBaseline := rfl

theorem squareDesign_eq : @SAP.P015b.squareDesign = @AronowAudit.P015.rootZ := rfl

theorem squarePotential_eq : @SAP.P015b.squarePotential = @AronowAudit.P015.rootPotential := rfl

theorem squareProbability_eq : @SAP.P015b.squareProbability = @AronowAudit.P015.rootProbability := rfl

theorem squareMean_eq : @SAP.P015b.squareMean = @AronowAudit.P015.rootMean := rfl

theorem squareLogLikelihood_eq : @SAP.P015b.squareLogLikelihood = @AronowAudit.P015.rootLikelihood := rfl

theorem SquareAdmissible_eq : @SAP.P015b.SquareAdmissible = @AronowAudit.P015.rootAdmissible := rfl

theorem SquareMLDerivative_eq : @SAP.P015b.SquareMLDerivative = @AronowAudit.P015.RootMLDerivative := rfl

theorem squareUniformLaw_eq : @SAP.P015b.squareUniformLaw = @AronowAudit.P015.rootUniformLaw := rfl

theorem squareUnitLaw_eq : @SAP.P015b.squareUnitLaw = @AronowAudit.P015.rootUnitLaw := rfl

theorem squareUnitProfile_eq : @SAP.P015b.squareUnitProfile = @AronowAudit.P015.rootUnitX := rfl

theorem squareUnitTreatment_eq : @SAP.P015b.squareUnitTreatment = @AronowAudit.P015.rootUnitD := rfl

theorem squareUnitUniform_eq : @SAP.P015b.squareUnitUniform = @AronowAudit.P015.rootUnitU := rfl

theorem squareUnitOutcome_eq : @SAP.P015b.squareUnitOutcome = @AronowAudit.P015.rootUnitY := rfl

theorem squareUnitEffect_eq : @SAP.P015b.squareUnitEffect = @AronowAudit.P015.rootUnitTau := rfl

theorem profileLaw_eq : @SAP.P015b.profileLaw = @AronowAudit.P015.cellLaw := rfl

theorem profileMean_eq : @SAP.P015b.profileMean = @AronowAudit.P015.cellMean := rfl

theorem profileVariance_eq : @SAP.P015b.profileVariance = @AronowAudit.P015.cellVar := rfl

theorem profileProbability_eq : @SAP.P015b.profileProbability = @AronowAudit.P015.cellProb := rfl

theorem profileWeight_eq : @SAP.P015b.profileWeight = @AronowAudit.P015.discreteWeight := rfl

theorem effectiveProfileLaw_eq : @SAP.P015b.effectiveProfileLaw = @AronowAudit.P015.discreteEffective := rfl

theorem smallWeightPopulation_eq : @SAP.P015b.smallWeightPopulation = @AronowAudit.P015.rareLaw := rfl

theorem smallWeightOutcome_eq : @SAP.P015b.smallWeightOutcome = @AronowAudit.P015.rareY := rfl

theorem smallWeightIPW_eq : @SAP.P015b.smallWeightIPW = @AronowAudit.P015.rareZ := rfl

theorem inverseWeightedOutcome_eq : @SAP.P015b.inverseWeightedOutcome = @AronowAudit.P015.ipw := rfl

theorem productMass_eq : @SAP.P015b.productMass = @AronowAudit.P015.iidLaw := rfl

theorem sampleMean_eq : @SAP.P015b.sampleMean = @AronowAudit.P015.sampleAverage := rfl

theorem uniformFourPopulation_eq : @SAP.P015b.uniformFourPopulation = @AronowAudit.P015.multiLaw := rfl

theorem zeroWeightControlDesign_eq : @SAP.P015b.zeroWeightControlDesign = @AronowAudit.P015.zeroSampleV := rfl

theorem zeroWeightRegressionDesign_eq : @SAP.P015b.zeroWeightRegressionDesign = @AronowAudit.P015.zeroSampleW := rfl

theorem zeroWeightTreatment_eq : @SAP.P015b.zeroWeightTreatment = @AronowAudit.P015.zeroSampleD := rfl

theorem FittedZeroFailure_eq : @SAP.P015b.FittedZeroFailure = @AronowAudit.P015.FittedZeroCounterexample := rfl

theorem squareLinkFailure_of_existing
    (h : AronowAudit.P015.RootLinkCounterexample) : SquareLinkFailure := by
  rcases h with ⟨hBranches, hMatrices, hMeanOLS, hUniform, hUnit, hCausal, hScore⟩
  have hgram : (fun j k => finiteMean squarePopulation
      (fun i => squareDesign i j*squareDesign i k)) =
      (!![1,0,0;0,5/24,0;0,0,2/3] : Matrix (Fin 3) (Fin 3) ℝ) := hMatrices.2.1
  have hdet : Matrix.det (fun j k => finiteMean squarePopulation
      (fun i => squareDesign i j*squareDesign i k)) ≠ 0 := by
    rw [hgram]
    norm_num [Matrix.det_fin_three]
  exact ⟨hUnit, hMatrices.1, hgram, hdet, hBranches.1, hBranches.2.1,
    hMeanOLS, hScore.2.1, hBranches.2.2.2.2, hUniform, hUnit, hCausal⟩


theorem missingPairPopulation_eq : missingPairPopulation =
    AronowAudit.P015.PositivityRefutation.P := rfl

theorem missingPairProfile_eq : missingPairProfile =
    AronowAudit.P015.PositivityRefutation.X := rfl

theorem missingPairTreatment_eq : missingPairTreatment =
    AronowAudit.P015.PositivityRefutation.D := rfl


end SAP.P015b.Bridge
