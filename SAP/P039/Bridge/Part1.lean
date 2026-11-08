import SAP.P039.Defs
import AronowAudit.P039.P039_Income
import AronowAudit.P039.P039_Extremism
import AronowAudit.P039.P039_Regression
import AronowAudit.P039.P039_PaperInstances
import AronowAudit.P039.P039_GaussianCompletion

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P039.Bridge
open scoped BigOperators Matrix NNReal
open MeasureTheory ProbabilityTheory

/- Each SAP notion is definitionally the same ordinary mathematical function or data
as its source counterpart. No project declaration is redefined in its original namespace. -/

theorem QuarterGrowth_eq : @SAP.P039.QuarterGrowth = @AronowAudit.P039.QuarterGrowth := rfl

theorem incomeNumerator_eq : @SAP.P039.incomeNumerator = @AronowAudit.P039.incomeNumerator := rfl

theorem incomeDenominator_eq : @SAP.P039.incomeDenominator = @AronowAudit.P039.incomeDenominator := rfl

theorem incomeGrowth_eq : @SAP.P039.incomeGrowth = @AronowAudit.P039.incomeGrowth := rfl

theorem describedNumerator_eq : @SAP.P039.describedNumerator = @AronowAudit.P039.describedNumerator := rfl

theorem describedDenominator_eq : @SAP.P039.describedDenominator = @AronowAudit.P039.describedDenominator := rfl

theorem describedGrowth_eq : @SAP.P039.describedGrowth = @AronowAudit.P039.describedGrowth := rfl

theorem firstQuarterOnly_eq : @SAP.P039.firstQuarterOnly = @AronowAudit.P039.firstQuarterOnly := rfl

theorem squaredLength_eq : @SAP.P039.squaredLength = @AronowAudit.P039.squaredLength := rfl

theorem FullColumnRank_eq : @SAP.P039.FullColumnRank = @AronowAudit.P039.FullColumnRank := rfl

theorem ols_eq : @SAP.P039.ols = @AronowAudit.P039.ols := rfl

theorem olsResidual_eq : @SAP.P039.olsResidual = @AronowAudit.P039.olsResidual := rfl

theorem olsSSE_eq : @SAP.P039.olsSSE = @AronowAudit.P039.olsSSE := rfl

theorem olsSESquared_eq : @SAP.P039.olsSESquared = @AronowAudit.P039.olsSESquared := rfl

theorem olsResidualStandardError_eq : @SAP.P039.olsResidualStandardError = @AronowAudit.P039.olsResidualStandardError := rfl

theorem olsT_eq : @SAP.P039.olsT = @AronowAudit.P039.olsT := rfl

theorem olsTSquared_eq : @SAP.P039.olsTSquared = @AronowAudit.P039.olsTSquared := rfl

theorem IsLeastSquares_eq : @SAP.P039.IsLeastSquares = @AronowAudit.P039.IsLeastSquares := rfl

theorem witnessU_eq : @SAP.P039.witnessU = @AronowAudit.P039.witnessU := rfl

theorem witnessV_eq : @SAP.P039.witnessV = @AronowAudit.P039.witnessV := rfl

theorem witnessW_eq : @SAP.P039.witnessW = @AronowAudit.P039.witnessW := rfl

theorem witnessY_eq : @SAP.P039.witnessY = @AronowAudit.P039.witnessY := rfl

theorem witnessZ_eq : @SAP.P039.witnessZ = @AronowAudit.P039.witnessZ := rfl

theorem residualLine_eq : @SAP.P039.residualLine = @AronowAudit.P039.residualLine := rfl

theorem fullDesign_eq : @SAP.P039.fullDesign = @AronowAudit.P039.fullDesign := rfl

theorem controlProjection_eq : @SAP.P039.controlProjection = @AronowAudit.P039.controlProjection := rfl

theorem residualMaker_eq : @SAP.P039.residualMaker = @AronowAudit.P039.residualMaker := rfl

theorem studentFourTail_eq : @SAP.P039.studentFourTail = @AronowAudit.P039.studentFourTail := rfl

theorem studentThreeTail_eq : @SAP.P039.studentThreeTail = @AronowAudit.P039.studentThreeTail := rfl

theorem studentLaw_eq : @SAP.P039.studentLaw = @AronowAudit.P039.studentLaw := rfl

theorem chiSquaredLaw_eq : @SAP.P039.chiSquaredLaw = @AronowAudit.P039.chiSquaredLaw := rfl

theorem vectorCovariance_eq : @SAP.P039.vectorCovariance = @AronowAudit.P039.vectorCovariance := rfl

theorem tableTwoInputs_eq : @SAP.P039.tableTwoInputs = @AronowAudit.P039.tableTwoInputs := rfl

theorem tableTwoOutcome_eq : @SAP.P039.tableTwoOutcome = @AronowAudit.P039.tableTwoOutcome := rfl

theorem tableA1_eq : @SAP.P039.tableA1 = @AronowAudit.P039.tableA1 := rfl

theorem tableA2_eq : @SAP.P039.tableA2 = @AronowAudit.P039.tableA2 := rfl

theorem tableA3_eq : @SAP.P039.tableA3 = @AronowAudit.P039.tableA3 := rfl

theorem ExtremismMeasure_eq : @SAP.P039.ExtremismMeasure = @AronowAudit.P039.ExtremismMeasure := rfl

theorem relativeExtremism_eq : @SAP.P039.relativeExtremism = @AronowAudit.P039.relativeExtremism := rfl

theorem extremismElections_eq : @SAP.P039.extremismElections = @AronowAudit.P039.extremismElections := rfl

theorem depositedExtremism_eq : @SAP.P039.depositedExtremism = @AronowAudit.P039.depositedExtremism := rfl

theorem magnitudeWinner_eq : @SAP.P039.magnitudeWinner = @AronowAudit.P039.magnitudeWinner := rfl

theorem signedWinner_eq : @SAP.P039.signedWinner = @AronowAudit.P039.signedWinner := rfl

theorem magnitudeMargin_eq : @SAP.P039.magnitudeMargin = @AronowAudit.P039.magnitudeMargin := rfl

theorem closestCompetitor_eq : @SAP.P039.closestCompetitor = @AronowAudit.P039.closestCompetitor := rfl

theorem modelElections_eq : @SAP.P039.modelElections = @AronowAudit.P039.modelElections := rfl

theorem maximumEffect_eq : @SAP.P039.maximumEffect = @AronowAudit.P039.maximumEffect := rfl


end SAP.P039.Bridge
