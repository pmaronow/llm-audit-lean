import SAP.P022.Defs
import SAP.P022.Bridge.Part1

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P022.Bridge
open SAP.P022 Filter MeasureTheory
open scoped BigOperators Topology ENNReal NNReal
noncomputable section

theorem finiteMean_eq {N : ℕ} (v : Fin N → ℝ) : AronowAudit.P022.finiteMean v = finiteMean v := rfl
theorem finiteVariance_eq {N : ℕ} (v : Fin N → ℝ) : AronowAudit.P022.finiteVariance v = finiteVariance v := rfl
theorem finiteCovariance_eq {N : ℕ} (v w : Fin N → ℝ) : AronowAudit.P022.finiteCovariance v w = finiteCovariance v w := rfl
theorem designExpectation_eq (d : Design) (f : Assignment d → ℝ) :
    AronowAudit.P022.designExpectation (toDesign d) f = designExpectation d f := rfl
theorem designProbability_eq (d : Design) (event : Assignment d → Prop) :
    AronowAudit.P022.designProbability (toDesign d) event = designProbability d event := rfl
theorem designVariance_eq (d : Design) (f : Assignment d → ℝ) :
    AronowAudit.P022.designVariance (toDesign d) f = designVariance d f := rfl
theorem observedTreatment_eq (d : Design) (y : Fin d.N → ℝ) (π : Assignment d) :
    AronowAudit.P022.observedTreatment (toDesign d) y π = observedTreatment d y π := rfl
theorem observedControl_eq (d : Design) (y : Fin d.N → ℝ) (π : Assignment d) :
    AronowAudit.P022.observedControl (toDesign d) y π = observedControl d y π := rfl
theorem averageEffect_eq (d : Design) (y1 y0 : Fin d.N → ℝ) :
    AronowAudit.P022.averageEffect (toDesign d) y1 y0 = averageEffect d y1 y0 := rfl
theorem estimatedEffect_eq (d : Design) (y1 y0 : Fin d.N → ℝ) :
    AronowAudit.P022.estimatedEffect (toDesign d) y1 y0 = estimatedEffect d y1 y0 := rfl
theorem trueVariance_eq (d : Design) (y1 y0 : Fin d.N → ℝ) :
    AronowAudit.P022.trueVariance (toDesign d) y1 y0 = trueVariance d y1 y0 := rfl
theorem varianceExpression_eq (N m k : ℕ) (v1 v0 cov : ℝ) :
    AronowAudit.P022.varianceExpression N m k v1 v0 cov = varianceExpression N m k v1 v0 cov := rfl
theorem empiricalCDF_eq {N : ℕ} (y : Fin N → ℝ) : AronowAudit.P022.empiricalCDF y = empiricalCDF y := rfl
theorem empiricalLeftCDF_eq {N : ℕ} (y : Fin N → ℝ) :
    AronowAudit.P022.empiricalLeftCDF y = empiricalLeftCDF y := rfl
theorem sortedOutcomes_eq {N : ℕ} (y : Fin N → ℝ) : AronowAudit.P022.sortedOutcomes y = sortedOutcomes y := rfl
theorem orderStatistic_eq {N : ℕ} (y : Fin N → ℝ) (r : ℕ) : AronowAudit.P022.orderStatistic y r = orderStatistic y r := rfl
theorem empiricalQuantile_eq {N : ℕ} (y : Fin N → ℝ) (u : ℝ) : AronowAudit.P022.empiricalQuantile y u = empiricalQuantile y u := rfl

/-- Endpoint formulas agree after the two-constructor conversion. -/
theorem sharpCovariance_eq {m k : ℕ} (a : Fin m → ℝ) (b : Fin k → ℝ) (B : AronowAudit.P022.BoundSide) :
    AronowAudit.P022.sharpCovariance a b B = sharpCovariance a b (fromSide B) := by cases B <;> rfl
theorem populationBound_eq (d : Design) (y1 y0 : Fin d.N → ℝ) (B : AronowAudit.P022.BoundSide) :
    AronowAudit.P022.populationBound (toDesign d) y1 y0 B = populationBound d y1 y0 (fromSide B) := by cases B <;> rfl
theorem sampleVariance_eq {s : ℕ} (y : Fin s → ℝ) : AronowAudit.P022.sampleVariance y = sampleVariance y := rfl
theorem marginalVarianceEstimate_eq {s : ℕ} (N : ℕ) (y : Fin s → ℝ) :
    AronowAudit.P022.marginalVarianceEstimate N y = marginalVarianceEstimate N y := rfl
theorem estimateBound_eq {m k : ℕ} (N : ℕ) (a : Fin m → ℝ) (b : Fin k → ℝ) (B : AronowAudit.P022.BoundSide) :
    AronowAudit.P022.estimateBound N a b B = estimateBound N a b (fromSide B) := by cases B <;> rfl
theorem estimatedVariance_eq (d : Design) (y1 y0 : Fin d.N → ℝ) (B : AronowAudit.P022.BoundSide) :
    AronowAudit.P022.estimatedVariance (toDesign d) y1 y0 B = estimatedVariance d y1 y0 (fromSide B) := by cases B <;> rfl
theorem conventionalEstimate_eq (d : Design) (y1 y0 : Fin d.N → ℝ) :
    AronowAudit.P022.conventionalEstimate (toDesign d) y1 y0 = conventionalEstimate d y1 y0 := rfl
theorem neymanEstimate_eq (d : Design) (y1 y0 : Fin d.N → ℝ) (B : AronowAudit.P022.BoundSide) :
    AronowAudit.P022.neymanEstimate (toDesign d) y1 y0 B = neymanEstimate d y1 y0 (fromSide B) := by cases B <;> rfl
theorem rowOutcomes_eq (S : ExperimentSequence) (t : Bool) (q : ℕ) :
    AronowAudit.P022.rowOutcomes (toSequence S) t q = rowOutcomes S t q := rfl
theorem lawCDF_eq (H : JointLaw) (t : Bool) : AronowAudit.P022.lawCDF H t = lawCDF H t := rfl
theorem lawLeftCDF_eq (H : JointLaw) (t : Bool) : AronowAudit.P022.lawLeftCDF H t = lawLeftCDF H t := rfl
theorem weakPopulationConvergence_eq (S : ExperimentSequence) (H : JointLaw) :
    AronowAudit.P022.weakPopulationConvergence (toSequence S) H = weakPopulationConvergence S H := rfl
theorem Conditions123_eq (S : ExperimentSequence) (H : JointLaw) (θ ρ : ℝ) :
    AronowAudit.P022.Conditions123 (toSequence S) H θ ρ = Conditions123 S H θ ρ := rfl
theorem UniformSquareIntegrability_eq (S : ExperimentSequence) :
    AronowAudit.P022.UniformSquareIntegrability (toSequence S) = UniformSquareIntegrability S := rfl
theorem AtomLeftConvergence_eq (S : ExperimentSequence) (H : JointLaw) :
    AronowAudit.P022.AtomLeftConvergence (toSequence S) H = AtomLeftConvergence S H := rfl
theorem cdfDistance_eq (A B : ℝ → ℝ) : AronowAudit.P022.cdfDistance A B = cdfDistance A B := rfl
theorem sampledCDF_eq (S : ExperimentSequence) (t : Bool) (q : ℕ) (π : Assignment (S.design q)) :
    AronowAudit.P022.sampledCDF (toSequence S) t q π = sampledCDF S t q π := rfl
theorem scaledProbabilityLimsup_eq (S : ExperimentSequence)
    (events : (q : ℕ) → Assignment (S.design q) → Prop) :
    AronowAudit.P022.scaledProbabilityLimsup (toSequence S) events = scaledProbabilityLimsup S events := rfl
theorem Lemma2Conclusions_eq (S : ExperimentSequence) (H : JointLaw) (θ ρ : ℝ) :
    AronowAudit.P022.Lemma2Conclusions (toSequence S) H θ ρ = Lemma2Conclusions S H θ ρ := rfl
theorem integratedCDFError_eq {N s : ℕ} (C : ℝ) (y : Fin N → ℝ) (a : Fin s → ℝ) :
    AronowAudit.P022.integratedCDFError C y a = integratedCDFError C y a := rfl
theorem midpointCovariance_eq {m k : ℕ} (a : Fin m → ℝ) (b : Fin k → ℝ) (B : AronowAudit.P022.BoundSide) :
    AronowAudit.P022.midpointCovariance a b B = midpointCovariance a b (fromSide B) := by cases B <;> rfl
theorem printedCodeBound_eq {m k : ℕ} (N : ℕ) (a : Fin m → ℝ) (b : Fin k → ℝ) (B : AronowAudit.P022.BoundSide) :
    AronowAudit.P022.printedCodeBound N a b B = printedCodeBound N a b (fromSide B) := by cases B <;> rfl
theorem limitingBound_eq (H : JointLaw) (θ ρ : ℝ) (B : AronowAudit.P022.BoundSide) :
    AronowAudit.P022.limitingBound H θ ρ B = limitingBound H θ ρ (fromSide B) := by cases B <;> rfl
theorem boundConsistency_eq (S : ExperimentSequence) : AronowAudit.P022.boundConsistency (toSequence S) = boundConsistency S := rfl
theorem BoundedThirdMoments_eq (S : ExperimentSequence) :
    AronowAudit.P022.BoundedThirdMoments (toSequence S) = BoundedThirdMoments S := rfl
theorem NonsingularLaw_eq (H : JointLaw) : AronowAudit.P022.NonsingularLaw H = NonsingularLaw H := rfl
theorem weakStandardNormal_eq (S : ExperimentSequence) (Z : (q : ℕ) → Assignment (S.design q) → ℝ) :
    AronowAudit.P022.weakStandardNormal (toSequence S) Z = weakStandardNormal S Z := rfl
theorem frechetCDF_eq (G F : ℝ → ℝ) (B : AronowAudit.P022.BoundSide) (x y : ℝ) :
    AronowAudit.P022.frechetCDF G F B x y = frechetCDF G F (fromSide B) x y := by cases B <;> rfl
theorem lastIntegralTerm_eq (d : Design) (y1 y0 : Fin d.N → ℝ) (C : ℝ) :
    AronowAudit.P022.lastIntegralTerm (toDesign d) y1 y0 C = lastIntegralTerm d y1 y0 C := rfl
theorem sevenTerms_eq (d : Design) (y1 y0 : Fin d.N → ℝ) (C : ℝ) :
    AronowAudit.P022.sevenTerms (toDesign d) y1 y0 C = sevenTerms d y1 y0 C := rfl
theorem displaysAs_iff (x p : ℝ) : AronowAudit.P022.displaysThree x p ↔ DisplaysAs x p := Iff.rfl
theorem halfWidth_eq (L U : ℝ) : AronowAudit.P022.halfWidth L U = halfWidth L U := rfl
theorem reductionPercent_eq (Va VH : ℝ) : AronowAudit.P022.reductionPercent Va VH = reductionPercent Va VH := rfl

theorem jointLaw_eq : AronowAudit.P022.JointLaw = JointLaw := rfl
theorem partitionKnots_eq (m k : ℕ) : AronowAudit.P022.partitionKnots m k = partitionKnots m k := rfl
theorem partitionPoint_eq (m k r : ℕ) : AronowAudit.P022.partitionPoint m k r = partitionPoint m k r := rfl
theorem partitionCells_eq (m k : ℕ) : AronowAudit.P022.partitionCells m k = partitionCells m k := rfl
theorem cellWidth_eq (m k r : ℕ) : AronowAudit.P022.cellWidth m k r = cellWidth m k r := rfl
theorem cellMidpoint_eq (m k r : ℕ) : AronowAudit.P022.cellMidpoint m k r = cellMidpoint m k r := rfl
theorem overlapWeight_eq (m k : ℕ) (i : Fin m) (j : Fin k) :
    AronowAudit.P022.overlapWeight m k i j = overlapWeight m k i j := rfl
theorem codeEpsilon_eq : AronowAudit.P022.codeEpsilon = codeEpsilon := rfl
theorem codePoint_eq (m k r : ℕ) : AronowAudit.P022.codePoint m k r = codePoint m k r := rfl
theorem sortedValues_eq {N : ℕ} (y : Fin N → ℝ) : AronowAudit.P022.sortedValues y = sortedValues y := rfl
theorem lawMean_eq (H : JointLaw) (t : Bool) : AronowAudit.P022.lawMean H t = lawMean H t := rfl
theorem lawVariance_eq (H : JointLaw) (t : Bool) : AronowAudit.P022.lawVariance H t = lawVariance H t := rfl
theorem lawCovariance_eq (H : JointLaw) : AronowAudit.P022.lawCovariance H = lawCovariance H := rfl
theorem compatibleLaws_eq (H : JointLaw) : AronowAudit.P022.compatibleLaws H = compatibleLaws H := rfl
theorem limitingTrueVariance_eq (H : JointLaw) (θ ρ : ℝ) :
    AronowAudit.P022.limitingTrueVariance H θ ρ = limitingTrueVariance H θ ρ := rfl
theorem gamma_eq (H : JointLaw) (θ ρ : ℝ) : AronowAudit.P022.gamma H θ ρ = gamma H θ ρ := rfl
theorem normalCDF_eq (x : ℝ) : AronowAudit.P022.normalCDF x = normalCDF x := rfl
theorem normalCritical_eq (α : ℝ) : AronowAudit.P022.normalCritical α = normalCritical α := rfl
theorem reciprocalThreshold_eq (q : ℕ) : AronowAudit.P022.reciprocalThreshold q = reciprocalThreshold q := rfl
theorem correctedPartitionInteger_eq (η : ℝ) :
    AronowAudit.P022.correctedPartitionInteger η = correctedPartitionInteger η := rfl
theorem sevenTotal_eq (T : Fin 7 → ℝ) : AronowAudit.P022.sevenTotal T = sevenTotal T := rfl
theorem correctedAllocation_eq (ν : Fin 8 → ℝ) (ε1 : ℝ) :
    AronowAudit.P022.correctedAllocation ν ε1 = correctedAllocation ν ε1 := rfl
theorem termRateCoefficient_eq (θ ρ : ℝ) : AronowAudit.P022.termRateCoefficient θ ρ = termRateCoefficient θ ρ := rfl
theorem zeroWitness_eq : AronowAudit.P022.zeroWitness = toSequence zeroWitness := rfl
theorem empiricalCompatibleLaws_eq {N : ℕ} (y1 y0 : Fin N → ℝ) :
    AronowAudit.P022.empiricalCompatibleLaws y1 y0 = empiricalCompatibleLaws y1 y0 := rfl

end
end SAP.P022.Bridge
