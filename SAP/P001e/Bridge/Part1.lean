import SAP.P001e.Defs
import AronowAudit.P001.P001_Foundations
import AronowAudit.P001.Wave1.Gap.WP001dB3
import AronowAudit.P001.Wave1.Gap.GLP0014B4
import AronowAudit.P001.Wave1.Gap.GP0014B2b
import AronowAudit.P001.Wave1.Gap.GP0014B3

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal NNReal Topology Classical

namespace SAP.P001e.Bridge
universe u v w z
open AronowAudit.P001

theorem probability_eq : @SAP.P001e.probability.{u} = @AronowAudit.P001.prob.{u} := rfl

theorem expectation_eq : @SAP.P001e.expectation.{u} = @AronowAudit.P001.mean.{u} := rfl

theorem ConvergesInProbability_eq : @SAP.P001e.ConvergesInProbability.{u,v} = @AronowAudit.P001.CP.{u,v} := rfl

theorem IsIID_eq : @SAP.P001e.IsIID.{u,v} = @AronowAudit.P001.IID.{u,v} := rfl

theorem sampleAverage_eq : @SAP.P001e.sampleAverage.{u} = @AronowAudit.P001.sampleMean.{u} := rfl

theorem IsConditionalMean_eq : @SAP.P001e.IsConditionalMean.{u,v} = @AronowAudit.P001.IsCEF.{u,v} := rfl

theorem CondIndependent_eq : @SAP.P001e.CondIndependent.{u,v,w,z} = @AronowAudit.P001.CI.{u,v,w,z} := rfl

theorem residualSS_eq : @SAP.P001e.residualSS = @AronowAudit.P001.olsRSS := rfl

theorem leastSquaresCoef_eq : @SAP.P001e.leastSquaresCoef = @AronowAudit.P001.olsCoef := rfl

theorem gaussianLogLikelihood_eq : @SAP.P001e.gaussianLogLikelihood = @AronowAudit.P001.normalLogLikelihood := rfl

theorem fittedJointLaw_eq : @SAP.P001e.fittedJointLaw = @AronowAudit.P001.mlFittedLaw := rfl

theorem recordedOutcome_eq : @SAP.P001e.recordedOutcome = @AronowAudit.P001.censored := rfl

theorem completeMissing_eq : @SAP.P001e.completeMissing = @AronowAudit.P001.missingEndpoint := rfl

theorem realizedOutcome_eq : @SAP.P001e.realizedOutcome = @AronowAudit.P001.observedOutcome := rfl

theorem lowerEffect_eq : @SAP.P001e.lowerEffect = @AronowAudit.P001.ateLower := rfl

theorem upperEffect_eq : @SAP.P001e.upperEffect = @AronowAudit.P001.ateUpper := rfl

theorem cellMean_eq : @SAP.P001e.cellMean.{u,v} = @AronowAudit.P001.conditionalMeanAt.{u,v} := rfl

theorem spikeResponse_eq : @SAP.P001e.spikeResponse = @AronowAudit.P001.doseSpike := rfl

theorem exampleCoef_eq : @SAP.P001e.exampleCoef = @AronowAudit.P001.causalExampleBeta := rfl

theorem exampleY_eq : @SAP.P001e.exampleY = @AronowAudit.P001.causalExampleY := rfl

theorem exampleD_eq : @SAP.P001e.exampleD = @AronowAudit.P001.causalExampleD := rfl

theorem exampleX1_eq : @SAP.P001e.exampleX1 = @AronowAudit.P001.causalExampleX1 := rfl

theorem exampleX2_eq : @SAP.P001e.exampleX2 = @AronowAudit.P001.causalExampleX2 := rfl

theorem examplePrediction_eq : @SAP.P001e.examplePrediction = @AronowAudit.P001.causalPrediction := rfl

theorem partialImputation_eq : @SAP.P001e.partialImputation = @AronowAudit.P001.causalPartialImpute := rfl

theorem exampleDesign_eq : @SAP.P001e.exampleDesign = @AronowAudit.P001.causalDesign := rfl

theorem integratedModelMean_eq : @SAP.P001e.integratedModelMean = @AronowAudit.P001.modelConditionalMean := rfl

theorem fittedPotentialAverage_eq : @SAP.P001e.fittedPotentialAverage = @AronowAudit.P001.mlPotentialMean := rfl

theorem logisticProbability_eq : @SAP.P001e.logisticProbability = @AronowAudit.P001.logitProbability := rfl

theorem cellLogLikelihood_eq : @SAP.P001e.cellLogLikelihood = @AronowAudit.P001.groupedLogitLikelihood := rfl

theorem cellSize_eq : @SAP.P001e.cellSize = @AronowAudit.P001.missingCellSize := rfl

theorem cellResponses_eq : @SAP.P001e.cellResponses = @AronowAudit.P001.missingCellResponse := rfl

theorem cellOutcomeSum_eq : @SAP.P001e.cellOutcomeSum = @AronowAudit.P001.missingCellOutcomeSum := rfl

theorem boundsRecorded_eq : @SAP.P001e.boundsRecorded = @AronowAudit.P001.stableExampleYstar := rfl

theorem boundsResponse_eq : @SAP.P001e.boundsResponse = @AronowAudit.P001.stableExampleR := rfl

theorem postOutcome_eq : @SAP.P001e.postOutcome = @AronowAudit.P001.postY := rfl

theorem postCovariate_eq : @SAP.P001e.postCovariate = @AronowAudit.P001.postX := rfl

theorem postAssignment_eq : @SAP.P001e.postAssignment = @AronowAudit.P001.postD := rfl

theorem postCovariate0_eq : @SAP.P001e.postCovariate0 = @AronowAudit.P001.postPotentialX0 := rfl

theorem postCovariate1_eq : @SAP.P001e.postCovariate1 = @AronowAudit.P001.postPotentialX1 := rfl

theorem responseProbability_eq : @SAP.P001e.responseProbability.{u} = @AronowAudit.P001.kernelPropensity.{u} := rfl

theorem T77Statement_iff : SAP.P001e.T77Statement.{u} ↔
  (∀ {Ω : Type u} {τ : ℕ} (Θ : Set (Fin τ → ℝ)) (Y : Ω → ℝ)
   {K : ℕ} (X : Ω → Fin K → ℝ) (g : ℝ → (Fin K → ℝ) → (Fin τ → ℝ) → ℝ)
   (hg : ∀ y x t,t∈Θ → 0 ≤ g y x t),
  ∃ L : Ω → Θ → ℝ≥0, ∀ ω t,(L ω t : ℝ)=g (Y ω) (X ω) t.val) := Iff.rfl

theorem T78Statement_iff : SAP.P001e.T78Statement ↔
  (∀ {n K : ℕ} (hn : 0 < n) (X : Matrix (Fin n) (Fin (K+1)) ℝ) (Y : Fin n → ℝ)
   (bstar : Fin (K+1) → ℝ) (hmin : ∀ b,olsRSS X Y bstar ≤ olsRSS X Y b)
   (hQ : 0 < olsRSS X Y bstar),
  0 < Real.sqrt (olsRSS X Y bstar/(n : ℝ)) ∧
   (Real.sqrt (olsRSS X Y bstar/(n : ℝ)))^2=olsRSS X Y bstar/(n : ℝ) ∧
   ∀ b s,0 < s → normalLogLikelihood X Y b s  ≤ 
     normalLogLikelihood X Y bstar (Real.sqrt (olsRSS X Y bstar/(n : ℝ)))) := Iff.rfl

theorem T79Statement_iff : SAP.P001e.T79Statement ↔
  (∀ {n K : ℕ} (hn : 0 < n) (X : Fin n → Fin K → ℝ) (ν : Fin n → Measure ℝ)
   (hν : ∀ i,IsProbabilityMeasure (ν i)),
  IsProbabilityMeasure (mlFittedLaw X ν) ∧ ∀ y : ℝ, ∀ x : Fin K → ℝ,
     prob (mlFittedLaw X ν) {z | z.1 ≤ y ∧ ∀ k,z.2 k ≤ x k} =
       (∑ i,if (∀ k,X i k ≤ x k) then prob (ν i) (Set.Iic y) else 0)/(n : ℝ)) := Iff.rfl

theorem MissingBounds_iff : SAP.P001e.MissingBounds.{u} ↔
  (∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
   (Y R : Ω → ℝ) (hY : Measurable Y) (hR : Measurable R) (a b : ℝ)
   (hbound : ∀ ω,Y ω∈Set.Icc a b) (hbinary : ∀ ω,R ω=0 ∨ R ω=1),
  let L := mean μ (fun ω => missingEndpoint (censored (Y ω) (R ω)) (R ω) a)
   let U := mean μ (fun ω => missingEndpoint (censored (Y ω) (R ω)) (R ω) b)
   L ≤ mean μ Y ∧ mean μ Y ≤ U ∧ ∀ c : ℝ,c∈Set.Icc L U →
     ∃ Y' : Ω → ℝ, Measurable Y' ∧ (∀ ω,Y' ω∈Set.Icc a b) ∧ mean μ Y'=c ∧
       (fun ω => censored (Y' ω) (R ω))=(fun ω => censored (Y ω) (R ω))) := Iff.rfl

theorem BoundsExample_iff : SAP.P001e.BoundsExample ↔
  ((∑ i : Fin 6,missingEndpoint (stableExampleYstar i)
       (stableExampleR i) 0)/6=1/2 ∧
   (∑ i : Fin 6,missingEndpoint (stableExampleYstar i)
       (stableExampleR i) 1)/6=5/6) := Iff.rfl

theorem T82Core_iff : SAP.P001e.T82Core.{u,v} ↔
  (∀ {Ω : Type u} {E : Type v}
    [MeasurableSpace Ω] [MeasurableSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → E) (R : Ω → Bool)
    (hX : Measurable X) (hR : Measurable R)
    (hRpos : 0 < prob μ {ω | R ω = true} ∧ prob μ {ω | R ω = true} < 1),
  ∃ p : E → ℝ, ∃ κ : E → Measure Bool,
      Measurable p ∧ (∀ x, p x ∈ Set.Icc (0 : ℝ) 1) ∧
      (∀ x, IsProbabilityMeasure (κ x)) ∧
      (∀ B : Set Bool, MeasurableSet B → Measurable (fun x => κ x B)) ∧
      (∀ A : Set E, MeasurableSet A → ∀ B : Set Bool, MeasurableSet B →
        μ {ω | X ω ∈ A ∧ R ω ∈ B} = ∫⁻ x in A, κ x B ∂(μ.map X)) ∧
      (∀ x, kernelPropensity κ x = p x ∧
        mean (κ x) (fun r => if r then (1 : ℝ) else 0) = p x) ∧
      IsCEF μ X (fun ω => if R ω then (1 : ℝ) else 0) p ∧
      (∀ m : E → ℝ, IsCEF μ X (fun ω => if R ω then (1 : ℝ) else 0) m →
        (m ∘ X) =ᵐ[μ] (p ∘ X)) ∧
      (∀ q : ℝ, q ∉ Set.Icc (0 : ℝ) 1 ↔ 1 < q ∨ q < 0)) := Iff.rfl

theorem T83Statement_iff : SAP.P001e.T83Statement.{u,v} ↔
  (∀ {Ω : Type u} {E : Type v} [MeasurableSpace Ω] [MeasurableSpace E]
   (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → E) (hX : Measurable X)
   (Y R : Ω → ℝ) (hY : Measurable Y) (hR : Measurable R) (hYi : Integrable Y μ)
   (hbinary : ∀ ω,R ω=0 ∨ R ω=1) (p : E → ℝ) (hp : IsCEF μ X R p)
   (hpos : ∃ ε : ℝ,0 < ε ∧ ∀ ω,ε < p (X ω)) (hmar : CI μ X hX Y R),
  mean μ Y=mean μ (fun ω => censored (Y ω) (R ω)*R ω/p (X ω))) := Iff.rfl

theorem T84Core_iff : SAP.P001e.T84Core ↔
  ((∀ a b : ℝ,
    groupedLogitLikelihood missingCellSize missingCellResponse a b ≤ 
      groupedLogitLikelihood missingCellSize missingCellResponse (Real.log (7/5)) 0 ∧
    (groupedLogitLikelihood missingCellSize missingCellResponse a b=
      groupedLogitLikelihood missingCellSize missingCellResponse (Real.log (7/5)) 0 ↔
      a=Real.log (7/5) ∧ b=0)) ∧
   (∀ j : Fin 3,0 < missingCellResponse j ∧ missingCellResponse j < missingCellSize j ∧
      logitProbability (Real.log (7/5)) 0 ((![-1,0,1] : Fin 3 → ℝ) j)=7/12) ∧
   (∑ j,missingCellOutcomeSum j/
      logitProbability (Real.log (7/5)) 0 ((![-1,0,1] : Fin 3 → ℝ) j))/12=3/7 ∧
   (∑ j,missingCellSize j*missingCellOutcomeSum j/missingCellResponse j)/12=5/12 ∧
   (3/7 : ℝ)≠5/12) := Iff.rfl

theorem SaturatedCells_iff : SAP.P001e.SaturatedCells.{u} ↔
  (∀ {E : Type u} [Fintype E] (N r S : E → ℝ) (hN : ∀ x,0 < N x) (hr : ∀ x,0 < r x),
  (∑ x,S x/(r x/N x))=∑ x,N x*S x/r x) := Iff.rfl

theorem SaturationCriterion_iff : SAP.P001e.SaturationCriterion.{u} ↔
  (∀ {E : Type u} [Fintype E] [DecidableEq E] (N r q : E → ℝ)
   (hN : ∀ x,0 < N x) (hr : ∀ x,0 < r x) (hq : ∀ x,0 < q x),
  (∀ S : E → ℝ,(∑ x,S x/q x)=∑ x,N x*S x/r x) ↔ ∀ x,q x=r x/N x) := Iff.rfl

theorem T86Statement_iff : SAP.P001e.T86Statement.{u,v} ↔
  (∀ {Ω : Type u} {E : Type v} [MeasurableSpace Ω] [MeasurableSpace E]
   (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → E) (hX : Measurable X)
   (R : Ω → ℝ) (hR : Measurable R) (hbinary : ∀ ω,R ω=0 ∨ R ω=1)
   (p : E → ℝ) (hp : IsCEF μ X R p)
   (hpos : ∃ ε : ℝ,0 < ε ∧ ∀ ω,ε < p (X ω) ∧ p (X ω) ≤ 1),
  IsCEF μ X (fun ω => R ω/p (X ω)) (fun _ => 1) ∧
   mean μ (fun ω => R ω/p (X ω))=1 ∧
   1 ≤ mean μ (fun ω => 1/p (X ω)) ∧
   (mean μ (fun ω => 1/p (X ω))=1 ↔ ∀ᵐ ω ∂μ,p (X ω)=1)) := Iff.rfl

theorem RespondentMAR_iff : SAP.P001e.RespondentMAR.{u,v} ↔
  (∀ {Ω : Type u} {E : Type v} [MeasurableSpace Ω] [MeasurableSpace E]
   (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → E) (hX : Measurable X)
   (Y R : Ω → ℝ) (hY : Measurable Y) (hR : Measurable R) (hYi : Integrable Y μ)
   (hbinary : ∀ ω,R ω=0 ∨ R ω=1) (p m : E → ℝ) (hp : IsCEF μ X R p)
   (hpos : ∃ ε : ℝ,0 < ε ∧ ∀ ω,ε < p (X ω)) (hmar : CI μ X hX Y R)
   (hm : IsCEF (μ.restrict {ω | R ω=1}) X (fun ω => censored (Y ω) (R ω)) m)
   (hmi : Integrable (m ∘ X) μ),
  IsCEF μ X Y m) := Iff.rfl

theorem RespondentStable_iff : SAP.P001e.RespondentStable.{u,v} ↔
  (∀ {Ω : Type u} {E : Type v} [MeasurableSpace Ω] [MeasurableSpace E]
   (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → E) (hX : Measurable X)
   (Y R : Ω → ℝ) (hY : Measurable Y) (hR : Measurable R) (hYi : Integrable Y μ)
   (hbinary : ∀ ω,R ω=0 ∨ R ω=1) (hRpos : 0 < prob μ {ω | R ω=1} ∧ 0 < prob μ {ω | R ω=0}) (m : E → ℝ)
   (hm : IsCEF (μ.restrict {ω | R ω=1}) X Y m),
  IsCEF (μ.restrict {ω | R ω=1}) X (fun ω => censored (Y ω) (R ω)) m ∧
   IsCEF μ (fun ω => (R ω,X ω)) (fun ω => censored (Y ω) (R ω))
     (fun rx => if rx.1=1 then m rx.2 else -99)) := Iff.rfl

theorem T88Statement_iff : SAP.P001e.T88Statement.{u} ↔
  (∀ {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Y0 Y1 D : ℕ → Ω → ℝ)
    (h0 : ∀ i, Measurable (Y0 i)) (h1 : ∀ i, Measurable (Y1 i))
    (hD : ∀ i, Measurable (D i)) (a b : ℝ) (hab : a ≤ b)
    (hsupport : ∀ i, ∀ᵐ ω ∂μ,
      Y0 i ω ∈ Set.Icc a b ∧ Y1 i ω ∈ Set.Icc a b ∧ (D i ω = 0 ∨ D i ω = 1))
    (hpos : 0 < prob μ {ω | D 0 ω = 1} ∧ prob μ {ω | D 0 ω = 1} < 1)
    (hiid : IID μ (fun i ω => (observedOutcome (Y0 i ω) (Y1 i ω) (D i ω), D i ω))),
  let Y := fun i ω => observedOutcome (Y0 i ω) (Y1 i ω) (D i ω)
    let L := fun i ω => ateLower (Y i ω) (D i ω) a b
    let U := fun i ω => ateUpper (Y i ω) (D i ω) a b
    let p := prob μ {ω | D 0 ω = 1}
    let ℓ := conditionalMeanAt μ (D 0) (Y 0) 1*p + a*(1-p) -
      (conditionalMeanAt μ (D 0) (Y 0) 0*(1-p) + b*p)
    let u := conditionalMeanAt μ (D 0) (Y 0) 1*p + b*(1-p) -
      (conditionalMeanAt μ (D 0) (Y 0) 0*(1-p) + a*p)
    mean μ (L 0) = ℓ ∧ mean μ (U 0) = u ∧ u-ℓ = b-a ∧
    mean μ (fun ω => Y1 0 ω - Y0 0 ω) ∈ Set.Icc ℓ u ∧
    (∀ t ∈ Set.Icc ℓ u, ∃ A0 A1 : Ω → ℝ,
      Measurable A0 ∧ Measurable A1 ∧
      (∀ᵐ ω ∂μ, A0 ω ∈ Set.Icc a b ∧ A1 ω ∈ Set.Icc a b ∧
        observedOutcome (A0 ω) (A1 ω) (D 0 ω) = Y 0 ω) ∧
      mean μ (fun ω => A1 ω-A0 ω) = t) ∧
    (∀ n, 0 < n → mean μ (sampleMean L n) = ℓ ∧ mean μ (sampleMean U n) = u) ∧
    CP μ (sampleMean L) ℓ ∧ CP μ (sampleMean U) u) := Iff.rfl

theorem PositiveMassDose_iff : SAP.P001e.PositiveMassDose.{u,v} ↔
  (∀ {Ω : Type u} {E : Type v} [MeasurableSpace Ω] [MeasurableSpace E] [MeasurableSingletonClass E] [Countable E]
   (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → E) (D : Ω → ℝ)
   (hX : Measurable X) (hD : Measurable D) (Y : ℝ → Ω → ℝ)
   (hY : ∀ t,Measurable (Y t)) (hi : ∀ t,Integrable (Y t) μ)
   (hobs : Measurable (fun ω => Y (D ω) ω)) (hobsI : Integrable (fun ω => Y (D ω) ω) μ)
   (hind : CI μ X hX (fun ω t => Y t ω) D) (d : ℝ)
   (hpos : ∀ x,0 < prob μ {ω | X ω=x} → 0 < prob μ {ω | X ω=x ∧ D ω=d}),
  (∀ x,0 < prob μ {ω | X ω=x} →
     conditionalMeanAt μ X (Y d) x=
       conditionalMeanAt μ (fun ω => (X ω,D ω)) (fun ω => Y (D ω) ω) (x,d)) ∧
   mean μ (Y d)=∑' x : E,
     conditionalMeanAt μ (fun ω => (X ω,D ω)) (fun ω => Y (D ω) ω) (x,d)*prob μ {ω | X ω=x}) := Iff.rfl

end SAP.P001e.Bridge
