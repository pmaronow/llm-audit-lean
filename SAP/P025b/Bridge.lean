import SAP.P025b.Defs
import AronowAudit.P025.P025_Interval

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P025b.Bridge
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology

/-! All correspondences are definitional or preserve the four design fields. -/

theorem populationMean_eq : @SAP.P025b.populationMean = @AronowAudit.P025.populationMean := rfl

theorem ratio_eq : @SAP.P025b.ratio = @AronowAudit.P025.ratio := rfl

theorem weightBox_eq : @SAP.P025b.weightBox = @AronowAudit.P025.weightBox := rfl

theorem normBox_eq : @SAP.P025b.normBox = @AronowAudit.P025.normBox := rfl

theorem lowerWeights_eq : @SAP.P025b.lowerWeights = @AronowAudit.P025.lowerWeights := rfl

theorem upperWeights_eq : @SAP.P025b.upperWeights = @AronowAudit.P025.upperWeights := rfl

theorem lowerValue_eq : @SAP.P025b.lowerValue = @AronowAudit.P025.lowerValue := rfl

theorem upperValue_eq : @SAP.P025b.upperValue = @AronowAudit.P025.upperValue := rfl

theorem lowerCut_eq : @SAP.P025b.lowerCut = @AronowAudit.P025.lowerCut := rfl

theorem upperCut_eq : @SAP.P025b.upperCut = @AronowAudit.P025.upperCut := rfl

theorem attainable_eq : @SAP.P025b.attainable = @AronowAudit.P025.attainable := rfl

theorem lowerEndpoint_eq : @SAP.P025b.lowerEndpoint = @AronowAudit.P025.lowerEndpoint := rfl

theorem upperEndpoint_eq : @SAP.P025b.upperEndpoint = @AronowAudit.P025.upperEndpoint := rfl

theorem separation_eq : @SAP.P025b.separation = @AronowAudit.P025.separation := rfl

theorem binaryTwo_eq : @SAP.P025b.binaryTwo = @AronowAudit.P025.binaryTwo := rfl

theorem binaryLower_eq : @SAP.P025b.binaryLower = @AronowAudit.P025.binaryLower := rfl

theorem binaryUpper_eq : @SAP.P025b.binaryUpper = @AronowAudit.P025.binaryUpper := rfl

theorem normAttainable_eq : @SAP.P025b.normAttainable = @AronowAudit.P025.normAttainable := rfl

theorem roundsTenth_eq : @SAP.P025b.roundsTenth = @AronowAudit.P025.roundsTenth := rfl

theorem tableCells_eq : @SAP.P025b.tableCells = @AronowAudit.P025.tableCells := rfl

theorem cellPercent_eq : @SAP.P025b.cellPercent = @AronowAudit.P025.cellPercent := rfl

theorem absoluteCompatible_eq : @SAP.P025b.absoluteCompatible = @AronowAudit.P025.absoluteCompatible := rfl

theorem classMean_eq : @SAP.P025b.classMean = @AronowAudit.P025.classMean := rfl

theorem sharesCompatible_eq : @SAP.P025b.sharesCompatible = @AronowAudit.P025.sharesCompatible := rfl

theorem compatibleMeans_eq : @SAP.P025b.compatibleMeans = @AronowAudit.P025.compatibleMeans := rfl

theorem absoluteCompatibleMeans_eq : @SAP.P025b.absoluteCompatibleMeans = @AronowAudit.P025.absoluteCompatibleMeans := rfl

theorem knownSizeCompatibleMeans_eq : @SAP.P025b.knownSizeCompatibleMeans = @AronowAudit.P025.knownSizeCompatibleMeans := rfl

theorem proportionRegion_eq : @SAP.P025b.proportionRegion = @AronowAudit.P025.proportionRegion := rfl

theorem classProportions_eq : @SAP.P025b.classProportions = @AronowAudit.P025.classProportions := rfl

theorem weightProportions_eq : @SAP.P025b.weightProportions = @AronowAudit.P025.weightProportions := rfl

theorem rationalVector_eq : @SAP.P025b.rationalVector = @AronowAudit.P025.rationalVector := rfl

/-- Repackage the same sample map and finite probability weights. -/
def toAudit {ι κ : Type*} [Fintype κ] (d : SAP.P025b.FiniteDesign ι κ) :
    AronowAudit.P025.FiniteDesign ι κ where
  sample := d.sample
  probability := d.probability
  nonnegative := d.nonnegative
  total := d.total

theorem inclusion_eq {ι κ : Type*} [Fintype κ] (d : SAP.P025b.FiniteDesign ι κ) :
    SAP.P025b.inclusion d = AronowAudit.P025.inclusion (toAudit d) := rfl

theorem classTotal_eq {ι κ : Type*} [Fintype ι] [Fintype κ] {J : ℕ}
    (d : SAP.P025b.FiniteDesign ι κ) (cls : ι → Fin J) :
    SAP.P025b.classTotal d cls = AronowAudit.P025.classTotal (toAudit d) cls := rfl

theorem classCount_eq {ι κ : Type*} [Fintype ι] [Fintype κ] {J : ℕ}
    (d : SAP.P025b.FiniteDesign ι κ) (cls : ι → Fin J) :
    SAP.P025b.classCount d cls = AronowAudit.P025.classCount (toAudit d) cls := rfl

theorem designPMF_eq {ι κ : Type*} [Fintype κ] (d : SAP.P025b.FiniteDesign ι κ) :
    SAP.P025b.designPMF d = AronowAudit.P025.designPMF (toAudit d) := rfl

theorem jointLaw_eq {ι κ : Type*} [Fintype κ] [MeasurableSpace κ]
    (d : SAP.P025b.FiniteDesign ι κ) :
    SAP.P025b.jointLaw d = AronowAudit.P025.jointLaw (toAudit d) := rfl

theorem pooledIndicator_eq {ι κ : Type*} [Fintype κ]
    (d : SAP.P025b.FiniteDesign ι κ) (h : ℕ) (ω : ℕ → κ) :
    SAP.P025b.pooledIndicator d h ω =
      AronowAudit.P025.pooledIndicator (toAudit d) h ω := rfl

theorem pooledLower_eq {ι κ : Type*} [Fintype ι] [Fintype κ] {J : ℕ}
    (d : SAP.P025b.FiniteDesign ι κ) (cls : ι → Fin J) (y : Fin J → ℝ)
    (α β : ℝ) (h : ℕ) (ω : ℕ → κ) :
    SAP.P025b.pooledLower d cls y α β h ω =
      AronowAudit.P025.pooledLower (toAudit d) cls y α β h ω := rfl

theorem pooledUpper_eq {ι κ : Type*} [Fintype ι] [Fintype κ] {J : ℕ}
    (d : SAP.P025b.FiniteDesign ι κ) (cls : ι → Fin J) (y : Fin J → ℝ)
    (α β : ℝ) (h : ℕ) (ω : ℕ → κ) :
    SAP.P025b.pooledUpper d cls y α β h ω =
      AronowAudit.P025.pooledUpper (toAudit d) cls y α β h ω := rfl

theorem pooledNonempty_eq {ι κ : Type*} [Fintype κ]
    (d : SAP.P025b.FiniteDesign ι κ) (h : ℕ) (ω : ℕ → κ) :
    SAP.P025b.pooledNonempty d h ω ↔ AronowAudit.P025.pooledNonempty (toAudit d) h ω := Iff.rfl

theorem censusDesign_eq : toAudit SAP.P025b.censusDesign = AronowAudit.P025.censusDesign := rfl

theorem omitOneDesign_eq : toAudit SAP.P025b.omitOneDesign = AronowAudit.P025.omitOneDesign := rfl

theorem pairDesign_eq : toAudit SAP.P025b.pairDesign = AronowAudit.P025.pairDesign := rfl

theorem integralityOutcomes_eq : SAP.P025b.integralityOutcomes = AronowAudit.P025.integralityOutcomes := rfl

theorem integralityClass_eq : SAP.P025b.integralityClass = AronowAudit.P025.integralityClass := rfl

theorem threeOutcomes_eq : SAP.P025b.threeOutcomes = AronowAudit.P025.threeOutcomes := rfl

theorem pairChoice_eq : SAP.P025b.pairChoice = AronowAudit.P025.pairChoice := rfl

theorem convergence_eq {N J : ℕ} {κ : Type*} [Fintype κ] [MeasurableSpace κ]
    (d : SAP.P025b.FiniteDesign (Fin N) κ) (cls : Fin N → Fin J) (y : Fin J → ℝ) (α β : ℝ) :
    SAP.P025b.PooledConvergence d cls y α β ↔
    ∀ᵐ ω ∂AronowAudit.P025.jointLaw (toAudit d),
      (∀ᶠ h in atTop, AronowAudit.P025.pooledNonempty (toAudit d) h ω) ∧
      Tendsto (fun h => AronowAudit.P025.pooledLower (toAudit d) cls y α β h ω) atTop
        (nhds (AronowAudit.P025.lowerEndpoint y (AronowAudit.P025.classTotal (toAudit d) cls) α β)) ∧
      Tendsto (fun h => AronowAudit.P025.pooledUpper (toAudit d) cls y α β h ω) atTop
        (nhds (AronowAudit.P025.upperEndpoint y (AronowAudit.P025.classTotal (toAudit d) cls) α β)) := Iff.rfl

end SAP.P025b.Bridge
