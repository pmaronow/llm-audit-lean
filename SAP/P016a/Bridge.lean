import SAP.P016a.Defs
import AronowAudit.P016.P016_Interference
import AronowAudit.P016.Wave1.Gap.GLP027P016P031P016B2
import AronowAudit.P016.Wave1.Gap.FidP016

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P016a.Bridge
open SAP.P016a
open scoped BigOperators

/-- Preserve the weights and both probability certificates. -/
def toLaw {Ω : Type} [Fintype Ω] (P : FiniteLaw Ω) : AronowAudit.P016.FiniteLaw Ω :=
  ⟨P.weight, P.nonneg, P.total⟩

def fromLaw {Ω : Type} [Fintype Ω] (P : AronowAudit.P016.FiniteLaw Ω) : FiniteLaw Ω :=
  ⟨P.weight, P.nonneg, P.total⟩

theorem toLaw_fromLaw {Ω : Type} [Fintype Ω] (P : AronowAudit.P016.FiniteLaw Ω) :
    toLaw (fromLaw P) = P := rfl

theorem fromLaw_toLaw {Ω : Type} [Fintype Ω] (P : FiniteLaw Ω) :
    fromLaw (toLaw P) = P := rfl

/-- All vector, regression and exposure notions have the same bodies. -/
theorem Outcome_eq : @Outcome = @AronowAudit.P016.Outcome := rfl
theorem Assignment_eq : @Assignment = @AronowAudit.P016.Assignment := rfl
theorem bit_eq : @bit = @AronowAudit.P016.bit := rfl
theorem groupSize_eq : @groupSize = @AronowAudit.P016.groupSize := rfl
theorem groupSum_eq : @groupSum = @AronowAudit.P016.groupSum := rfl
theorem groupMean_eq : @groupMean = @AronowAudit.P016.groupMean := rfl
theorem pooledMean_eq : @pooledMean = @AronowAudit.P016.pooledMean := rfl
theorem tss_eq : @tss = @AronowAudit.P016.tss := rfl
theorem rss_eq : @rss = @AronowAudit.P016.rss := rfl
theorem meanDifference_eq : @meanDifference = @AronowAudit.P016.meanDifference := rfl
theorem ecdf_eq : @ecdf = @AronowAudit.P016.ecdf := rfl
theorem ks_eq : @ks = @AronowAudit.P016.ks := rfl
theorem signedKS_eq : @signedKS = @AronowAudit.P016.signedKS := rfl
theorem additiveAdjust_eq : @additiveAdjust = @AronowAudit.P016.additiveAdjust := rfl
theorem additiveGenerate_eq : @additiveGenerate = @AronowAudit.P016.additiveGenerate := rfl
theorem doubledP_eq : @doubledP = @AronowAudit.P016.doubledP := rfl
theorem complete4_eq : @complete4 = @AronowAudit.P016.complete4 := rfl
theorem blocked4_eq : @blocked4 = @AronowAudit.P016.blocked4 := rfl
theorem u4_eq : @u4 = @AronowAudit.P016.u4 := rfl
theorem lsObjective_eq : @lsObjective = @AronowAudit.P016.lsObjective := rfl
theorem fitted_eq : @fitted = @AronowAudit.P016.fitted := rfl
theorem lsRSS_eq : @lsRSS = @AronowAudit.P016.lsRSS := rfl
theorem treatedNeighbors_eq : @treatedNeighbors = @AronowAudit.P016.treatedNeighbors := rfl
theorem degree_eq : @degree = @AronowAudit.P016.degree := rfl
theorem networkX_eq : @networkX = @AronowAudit.P016.networkX := rfl
theorem basicX_eq : @basicX = @AronowAudit.P016.basicX := rfl
theorem groupValues_eq : @groupValues = @AronowAudit.P016.groupValues := rfl
theorem sameMargins_eq : @sameMargins = @AronowAudit.P016.sameMargins := rfl
theorem pairedCovariance2_eq : @pairedCovariance2 = @AronowAudit.P016.pairedCovariance2 := rfl
theorem exposureSum_eq : @exposureSum = @AronowAudit.P016.exposureSum := rfl
theorem similarity_eq : @similarity = @AronowAudit.P016.similarity := rfl
theorem distance_eq : @distance = @AronowAudit.P016.distance := rfl
theorem conditionalMean_eq : @conditionalMean = @AronowAudit.P016.conditionalMean := rfl
theorem centeredExposure_eq : @centeredExposure = @AronowAudit.P016.centeredExposure := rfl
theorem sampleVariance_eq : @sampleVariance = @AronowAudit.P016.sampleVariance := rfl
theorem sampleSD_eq : @sampleSD = @AronowAudit.P016.sampleSD := rfl
theorem standardize_eq : @standardize = @AronowAudit.P016.standardize := rfl
theorem codedExposure_eq : @codedExposure = @AronowAudit.P016.codedExposure := rfl
theorem applicationAdjust_eq : @applicationAdjust = @AronowAudit.P016.applicationAdjust := rfl
theorem applicationX_eq : @applicationX = @AronowAudit.P016.applicationX := rfl
theorem printedReject_eq : @printedReject = @AronowAudit.P016.printedReject := rfl
theorem codedReject_eq : @codedReject = @AronowAudit.P016.codedReject := rfl
theorem matchedBank4_eq : @matchedBank4 = @AronowAudit.P016.matchedBank4 := rfl
theorem matchedBank6_eq : @matchedBank6 = @AronowAudit.P016.matchedBank6 := rfl
theorem scores4_eq : @scores4 = @AronowAudit.P016.scores4 := rfl
theorem scores6_eq : @scores6 = @AronowAudit.P016.scores6 := rfl
theorem IsDistanceMatrix_eq : @IsDistanceMatrix = @AronowAudit.P016.IsDistanceMatrix := rfl
theorem lowerCount_eq : @lowerCount = @AronowAudit.P016.lowerCount := rfl
theorem upperCount_eq : @upperCount = @AronowAudit.P016.upperCount := rfl
theorem rawP_eq : @rawP = @AronowAudit.P016.rawP := rfl
theorem Balanced_eq : @Balanced = @AronowAudit.P016.Balanced := rfl
theorem uniformMass_eq : @uniformMass = @AronowAudit.P016.uniformMass := rfl
theorem EffectIncreasing_eq : @EffectIncreasing = @AronowAudit.P016.EffectIncreasing := rfl

/-- The finite probability adapter preserves every event mass. -/
theorem mass_eq {Ω : Type} [Fintype Ω] (P : FiniteLaw Ω) (E : Ω → Prop) :
    mass P E = AronowAudit.P016.mass (toLaw P) E := rfl

theorem expectation_eq {Ω : Type} [Fintype Ω] (P : FiniteLaw Ω) (f : Ω → ℝ) :
    expectation P f = AronowAudit.P016.expectation (toLaw P) f := rfl

theorem covariance_eq {Ω : Type} [Fintype Ω] (P : FiniteLaw Ω) (f g : Ω → ℝ) :
    covariance P f g = AronowAudit.P016.covariance (toLaw P) f g := rfl

theorem variance_eq {Ω : Type} [Fintype Ω] (P : FiniteLaw Ω) (f : Ω → ℝ) :
    variance P f = AronowAudit.P016.variance (toLaw P) f := rfl

theorem upperP_eq {Ω : Type} [Fintype Ω] (P : FiniteLaw Ω) (s : Ω → ℝ) (z : Ω) :
    upperP P s z = AronowAudit.P016.upperP (toLaw P) s z := rfl

theorem lowerP_eq {Ω : Type} [Fintype Ω] (P : FiniteLaw Ω) (s : Ω → ℝ) (z : Ω) :
    lowerP P s z = AronowAudit.P016.lowerP (toLaw P) s z := rfl

theorem uniformLaw_eq (Ω : Type) [Fintype Ω] [Nonempty Ω] :
    toLaw (uniformLaw Ω) = AronowAudit.P016.uniformLaw Ω := rfl

end SAP.P016a.Bridge
