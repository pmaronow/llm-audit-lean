import SAP.P025a.Defs
import AronowAudit.P025.P025_Interval
import AronowAudit.P025.P025_PrintedRefutations
import AronowAudit.P025.Wave1.Gap.FidP025

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P025a.Bridge
open scoped BigOperators

/-! Definitional correspondences; the sampling witnesses use plain sample
maps and probability functions in place of the project's bundled data. -/

theorem populationMean_eq : @SAP.P025a.populationMean = @AronowAudit.P025.populationMean := rfl

theorem ratio_eq : @SAP.P025a.ratio = @AronowAudit.P025.ratio := rfl

theorem weightBox_eq : @SAP.P025a.weightBox = @AronowAudit.P025.weightBox := rfl

theorem normBox_eq : @SAP.P025a.normBox = @AronowAudit.P025.normBox := rfl

theorem lowerWeights_eq : @SAP.P025a.lowerWeights = @AronowAudit.P025.lowerWeights := rfl

theorem upperWeights_eq : @SAP.P025a.upperWeights = @AronowAudit.P025.upperWeights := rfl

theorem lowerValue_eq : @SAP.P025a.lowerValue = @AronowAudit.P025.lowerValue := rfl

theorem upperValue_eq : @SAP.P025a.upperValue = @AronowAudit.P025.upperValue := rfl

theorem lowerCut_eq : @SAP.P025a.lowerCut = @AronowAudit.P025.lowerCut := rfl

theorem upperCut_eq : @SAP.P025a.upperCut = @AronowAudit.P025.upperCut := rfl

theorem printedLowerCut_eq : @SAP.P025a.printedLowerCut = @AronowAudit.P025.printedLowerCut := rfl

theorem attainable_eq : @SAP.P025a.attainable = @AronowAudit.P025.attainable := rfl

theorem normAttainable_eq : @SAP.P025a.normAttainable = @AronowAudit.P025.normAttainable := rfl

theorem lowerEndpoint_eq : @SAP.P025a.lowerEndpoint = @AronowAudit.P025.lowerEndpoint := rfl

theorem upperEndpoint_eq : @SAP.P025a.upperEndpoint = @AronowAudit.P025.upperEndpoint := rfl

theorem separation_eq : @SAP.P025a.separation = @AronowAudit.P025.separation := rfl

theorem binaryTwo_eq : @SAP.P025a.binaryTwo = @AronowAudit.P025.binaryTwo := rfl

theorem twoPi_eq : @SAP.P025a.twoPi = @AronowAudit.P025.twoPi := rfl

theorem fourOutcomes_eq : @SAP.P025a.fourOutcomes = @AronowAudit.P025.fourOutcomes := rfl

theorem printedLowerExpression_eq : @SAP.P025a.printedLowerExpression = @AronowAudit.P025.printedLowerExpression := rfl

theorem sixTailOutcomes_eq : @SAP.P025a.sixTailOutcomes = @AronowAudit.P025.sixTailOutcomes := rfl

theorem sixTailClass_eq : @SAP.P025a.sixTailClass = @AronowAudit.P025.sixTailClass := rfl

theorem binaryLower_eq : @SAP.P025a.binaryLower = @AronowAudit.P025.binaryLower := rfl

theorem binaryUpper_eq : @SAP.P025a.binaryUpper = @AronowAudit.P025.binaryUpper := rfl

theorem binaryInterval_eq : @SAP.P025a.binaryInterval = @AronowAudit.P025.binaryInterval := rfl

theorem reweightedPrevalence_eq : @SAP.P025a.reweightedPrevalence = @AronowAudit.P025.reweightedPrevalence := rfl

theorem sampleOddsRatio_eq : @SAP.P025a.sampleOddsRatio = @AronowAudit.P025.sampleOddsRatio := rfl

theorem quotaDraws_eq : @SAP.P025a.quotaDraws = @AronowAudit.P025.quotaDraws := rfl

theorem quotaMarginal_eq : @SAP.P025a.quotaMarginal = @AronowAudit.P025.quotaMarginal := rfl

theorem pairObjective_eq : @SAP.P025a.pairObjective = @AronowAudit.P025.pairObjective := rfl

theorem threshold_lower {n : ℕ} (γ : ℝ) (k : ℕ) :
    (AronowAudit.P025.threshold γ 1 k : Fin n → ℝ) = lowerWeights γ k := rfl

theorem threshold_upper {n : ℕ} (γ : ℝ) (k : ℕ) :
    (AronowAudit.P025.threshold 1 γ k : Fin n → ℝ) = upperWeights γ k := rfl

 theorem twoSample_eq : twoSample = AronowAudit.P025.twoDesign.sample := rfl

 theorem twoProbability_eq : twoProbability = AronowAudit.P025.twoDesign.probability := rfl

 theorem twoInclusion_eq (i : Fin 2) :
     designInclusion twoSample twoProbability i =
       AronowAudit.P025.inclusion AronowAudit.P025.twoDesign i := rfl

 theorem twoEvent_eq :
     (∑ ω, twoProbability ω * (if twoSample ω = {0,1} then 1 else 0)) =
       AronowAudit.P025.designExpectation AronowAudit.P025.twoDesign
         (fun ω => if AronowAudit.P025.twoDesign.sample ω = {0,1} then 1 else 0) := rfl

 theorem fourClassSample_eq :
     fourClassSample = AronowAudit.P025.fourClassDesign.sample := rfl

 theorem fourClassProbability_eq :
     fourClassProbability = AronowAudit.P025.fourClassDesign.probability := rfl

 theorem fourClassInclusion_eq (i : Fin 6) :
     designInclusion fourClassSample fourClassProbability i =
       AronowAudit.P025.inclusion AronowAudit.P025.fourClassDesign i := rfl

 theorem fourClassTotal_eq (j : Fin 4) :
     designClassTotal fourClassSample fourClassProbability sixTailClass j =
       AronowAudit.P025.classTotal AronowAudit.P025.fourClassDesign
         AronowAudit.P025.sixTailClass j := rfl

end SAP.P025a.Bridge
