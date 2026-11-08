import SAP.P036.Defs
import AronowAudit.P036.P036_Unadjusted

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P036.Bridge

open MeasureTheory

/-! All correspondences below are definitional equalities. The shared SAP
definitions contain only Mathlib notions; project names enter only here. -/

theorem peers_eq {ι : Type*} : @peers ι = @AronowAudit.P036.peers ι := rfl

theorem covariateContribution_eq {Ω : Type*} {k : ℕ} :
    @covariateContribution Ω k = @AronowAudit.P036.covariateContribution Ω k := rfl

theorem linearPredictor_eq {Ω : Type*} {k : ℕ} :
    @linearPredictor Ω k = @AronowAudit.P036.linearPredictor Ω k := rfl

theorem regressorSigma_eq {Ω : Type*} {k : ℕ} :
    @regressorSigma Ω k = @AronowAudit.P036.regressorSigma Ω k := rfl

theorem assignmentSigma_eq {Ω : Type*} :
    @assignmentSigma Ω = @AronowAudit.P036.assignmentSigma Ω := rfl

theorem conditionalArmMean_eq {Ω : Type*} [MeasurableSpace Ω] :
    @conditionalArmMean Ω _ = @AronowAudit.P036.conditionalArmMean Ω _ := rfl

theorem armMean_eq {ι : Type*} : @armMean ι = @AronowAudit.P036.armMean ι := rfl

theorem armSS_eq {ι : Type*} : @armSS ι = @AronowAudit.P036.armSS ι := rfl

theorem sampleVariance_eq {ι : Type*} :
    @sampleVariance ι = @AronowAudit.P036.sampleVariance ι := rfl

theorem rss_eq {ι : Type*} [Fintype ι] :
    @rss ι _ = @AronowAudit.P036.rss ι _ := rfl

theorem olsCoefficients_eq {ι : Type*} [Fintype ι] [DecidableEq ι] :
    @olsCoefficients ι _ _ = @AronowAudit.P036.olsCoefficients ι _ _ := rfl

theorem tableCoefficients_eq : tableCoefficients = AronowAudit.P036.tableCoefficients := rfl

theorem roundsToThree_eq : roundsToThree = AronowAudit.P036.roundsToThree := rfl

theorem designRow_eq {ι : Type*} :
    @designRow ι = @AronowAudit.P036.designRow ι := rfl

theorem gram_eq {ι : Type*} [Fintype ι] :
    @gram ι _ = @AronowAudit.P036.gram ι _ := rfl

theorem gramInverse_eq {ι : Type*} [Fintype ι] [DecidableEq ι] :
    @gramInverse ι _ _ = @AronowAudit.P036.gramInverse ι _ _ := rfl

theorem regressionCoefficient_eq {ι : Type*} [Fintype ι] [DecidableEq ι] :
    @regressionCoefficient ι _ _ = @AronowAudit.P036.regressionCoefficient ι _ _ := rfl

theorem olsResidual_eq {ι : Type*} [Fintype ι] [DecidableEq ι] :
    @olsResidual ι _ _ = @AronowAudit.P036.olsResidual ι _ _ := rfl

theorem leverage_eq {ι : Type*} [Fintype ι] [DecidableEq ι] :
    @leverage ι _ _ = @AronowAudit.P036.leverage ι _ _ := rfl

theorem hc2Covariance_eq {ι : Type*} [Fintype ι] [DecidableEq ι] :
    @hc2Covariance ι _ _ = @AronowAudit.P036.hc2Covariance ι _ _ := rfl

theorem hc2Variance_eq {ι : Type*} [Fintype ι] [DecidableEq ι] :
    @hc2Variance ι _ _ = @AronowAudit.P036.hc2Variance ι _ _ := rfl

theorem neymanEstimate_eq {ι : Type*} [Fintype ι] [DecidableEq ι] :
    @neymanEstimate ι _ _ = @AronowAudit.P036.neymanEstimate ι _ _ := rfl

theorem binaryHC2Arm_eq : binaryHC2Arm = AronowAudit.P036.binaryHC2Arm := rfl

theorem tableHC2_eq : tableHC2 = AronowAudit.P036.tableHC2 := rfl

theorem assignments_eq {ι : Type*} [Fintype ι] :
    @assignments ι _ = @AronowAudit.P036.assignments ι _ := rfl

theorem designExpectation_eq {ι : Type*} [Fintype ι] :
    @designExpectation ι _ = @AronowAudit.P036.designExpectation ι _ := rfl

theorem designVariance_eq {ι : Type*} [Fintype ι] :
    @designVariance ι _ = @AronowAudit.P036.designVariance ι _ := rfl

theorem observedOutcome_eq {ι : Type*} [DecidableEq ι] :
    @observedOutcome ι _ = @AronowAudit.P036.observedOutcome ι _ := rfl

theorem populationMean_eq {ι : Type*} [Fintype ι] :
    @populationMean ι _ = @AronowAudit.P036.populationMean ι _ := rfl

theorem populationVariance_eq {ι : Type*} [Fintype ι] :
    @populationVariance ι _ = @AronowAudit.P036.populationVariance ι _ := rfl

theorem unitEffect_eq {ι : Type*} :
    @unitEffect ι = @AronowAudit.P036.unitEffect ι := rfl

theorem estimatedEffect_eq {ι : Type*} [Fintype ι] [DecidableEq ι] :
    @estimatedEffect ι _ _ = @AronowAudit.P036.estimatedEffect ι _ _ := rfl

end SAP.P036.Bridge
