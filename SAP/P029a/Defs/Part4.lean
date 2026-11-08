import SAP.P029a.Defs.Part3

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables false

namespace SAP.P029a

open scoped BigOperators Classical Topology
open MeasureTheory ProbabilityTheory Filter Set

noncomputable section

def ConstantWeightEquivalence : Prop :=
  ∀ {I Θ : Type*} [Fintype I]
    (L : Θ → I → ℝ) (hL : ∀ θ i, 0 < L θ i) (k : ℝ) (hk : 0 < k) (θ : Θ),
    IsGlobalMinimum (fun t => insideLogObjective (L t) (fun _ => k)) θ ↔
      IsGlobalMinimum (fun t => observationWeightedObjective (L t) (fun _ => k)) θ

def ZeroAndUnitWeights : Prop :=
  ∀ {I : Type*} [Fintype I]
    (L : I → ℝ) (hL : ∀ i, L i ∈ Ioc (0 : ℝ) 1),
    (∀ i, (0 : ℝ) * Real.log (L i) = 0) ∧
    observationWeightedObjective L (fun _ => 1) = insideLogObjective L (fun _ => 1)

def IntegerWeightReplication : Prop :=
  ∀ {I : Type*} [Fintype I]
    (L : I → ℝ) (w : I → ℕ) (hL : ∀ i, 0 < L i),
    Real.exp (-observationWeightedObjective L (fun i => (w i : ℝ))) = ∏ i, (L i) ^ w i

def FreeCellUniqueMinimum : Prop :=
  ∀ {I C : Type*} [Fintype I] [Fintype C]
    (cell : I → C) (D : I → Bool) (w : I → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hS : ∀ c, 0 < successWeightTotal cell D w c)
    (hF : ∀ c, 0 < failureWeightTotal cell D w c),
    let qhat := fun c => successWeightTotal cell D w c /
      (successWeightTotal cell D w c + failureWeightTotal cell D w c)
    (∀ c, qhat c ∈ Ioo (0 : ℝ) 1) ∧
    ∀ q : C → ℝ, (∀ c, q c ∈ Ioo (0 : ℝ) 1) →
      observationWeightedObjective (fun i => bernoulliContribution (qhat (cell i)) (D i)) w ≤
        observationWeightedObjective (fun i => bernoulliContribution (q (cell i)) (D i)) w ∧
      (observationWeightedObjective (fun i => bernoulliContribution (qhat (cell i)) (D i)) w =
        observationWeightedObjective (fun i => bernoulliContribution (q (cell i)) (D i)) w ↔ q = qhat)

def CellStrictConcavity : Prop :=
  ∀ (S F : ℝ) (hS : 0 < S) (hF : 0 < F),
    StrictConcaveOn ℝ (Ioo (0 : ℝ) 1) (cellLogLikelihood S F)

def CellUniqueMaximum : Prop :=
  ∀ (S F : ℝ) (hS : 0 < S) (hF : 0 < F),
    (S / (S + F)) ∈ Ioo (0 : ℝ) 1 ∧
    ∀ q ∈ Ioo (0 : ℝ) 1,
      cellLogLikelihood S F q ≤ cellLogLikelihood S F (S / (S + F)) ∧
      (cellLogLikelihood S F q = cellLogLikelihood S F (S / (S + F)) ↔ q = S / (S + F))

def RecordedAssignmentSupport : Prop :=
  ∀ (e : ℝ) (he0 : 0 < e) (he1 : e < 1),
    0 < ∏ i : CanvassingRecord, (if recordedAssignment i then e else 1 - e)

def RaceCompletionFacts : Prop :=
  ∀ (Y : CanvassingRecord → ℝ),
    Fintype.card CanvassingRecord = 18933 ∧ IsFiniteLaw recordMass ∧
    PreservesRecordedRace raceCompletionA ∧ PreservesRecordedRace raceCompletionB ∧
    (∀ i, (recordPotentialResponse Y i).receivedTreatment (recordedAssignment i) = recordedContact i ∧
      (recordPotentialResponse Y i).observedOutcome (recordedAssignment i) = Y i ∧ ¬ (recordPotentialResponse Y i).isDefier) ∧
    finiteProbability recordMass (fun i => recordedContact i = true) = 2551/18933 ∧
    finiteProbability recordMass (fun i => raceCompletionA i = true) = 3884/18933 ∧
    finiteProbability recordMass (fun i => raceCompletionB i = true) = 18157/18933 ∧
    finiteProbability recordMass (fun i => raceCompletionA i = true ∧ recordedContact i = true) = 602/18933 ∧
    finiteProbability recordMass (fun i => raceCompletionB i = true ∧ recordedContact i = true) = 2391/18933 ∧
    (18933 * 602 - 2551 * 3884 : ℤ) = 1489582 ∧
    (18933 * 2391 - 2551 * 18157 : ℤ) = -1049704 ∧
    finiteConditionalMean recordMass (fun i => indicatorValue (recordedContact i)) (fun i => raceCompletionA i = true) -
      finiteConditionalMean recordMass (fun i => indicatorValue (recordedContact i)) (fun i => raceCompletionA i = false) =
        744791/29225158 ∧
    finiteConditionalMean recordMass (fun i => indicatorValue (recordedContact i)) (fun i => raceCompletionB i = true) -
      finiteConditionalMean recordMass (fun i => indicatorValue (recordedContact i)) (fun i => raceCompletionB i = false) =
        -131213/1761229 ∧
    (0 : ℝ) < 744791/29225158 ∧ (-131213/1761229 : ℝ) < 0

def RawRaceCodePreservation : Prop :=
  ∀ (R : CanvassingRecord → Option String)
    (hR : ∀ i code, R i = some code → recordedRace i = some (decide (code = "W"))),
    (∀ i, (completedRawRaceRecord R raceCompletionA i).1 = R i ∧
      (completedRawRaceRecord R raceCompletionB i).1 = R i) ∧
    (∀ i code, R i = some code →
      raceCompletionA i = decide (code = "W") ∧ raceCompletionB i = decide (code = "W"))

def GroupedCovarianceIdentity : Prop :=
  ∀ {n : ℕ} {G : Type*} [Fintype G]
    (s A : Fin (n+1) → ℝ) (group : Fin (n+1) → G),
    let p : Fin (n+1) → ℝ := fun _ => 1/(n+1)
    finiteCovariance p s A =
      finiteExpectation p (fun i => (s i - finiteGroupMean p s group (group i)) *
        (A i - finiteGroupMean p A group (group i))) +
      finiteExpectation p (fun i => (finiteGroupMean p s group (group i) - finiteExpectation p s) *
        (finiteGroupMean p A group (group i) - finiteExpectation p A)) ∧
    (∀ g, 0 < finiteProbability p (fun i => group i = g) → (∀ i, group i ≠ g → ∀ j, group j = group i → A j = A i) →
      finiteExpectation p (fun i => (s i - finiteGroupMean p s group (group i)) *
        (A i - finiteGroupMean p A group (group i))) =
      ((Finset.univ.filter (fun i => group i = g)).card : ℝ)/(n+1) *
        finiteConditionalMean p (fun i => (s i - finiteGroupMean p s group g) *
          (A i - finiteGroupMean p A group g)) (fun i => group i = g))

def BinaryPopulationSign : Prop :=
  ∀ {n : ℕ} (C W : Fin (n+1) → Bool)
    (hW : 0 < trueCount W) (hWN : trueCount W < n+1)
    (hC : 0 < trueCount C) (hCN : trueCount C < n+1),
    let N : ℝ := n+1
    let nW : ℝ := trueCount W
    let nC : ℝ := trueCount C
    let n11 : ℝ := jointTrueCount C W
    let p : Fin (n+1) → ℝ := fun _ => 1/N
    finiteCovariance p (fun i => indicatorValue (C i)) (fun i => indicatorValue (W i)) = (N*n11-nC*nW)/N^2 ∧
    finiteConditionalMean p (fun i => indicatorValue (C i)) (fun i => W i = true) -
      finiteConditionalMean p (fun i => indicatorValue (C i)) (fun i => W i = false) =
        (N*n11-nC*nW)/(nW*(N-nW)) ∧
    finiteConditionalMean p (fun i => indicatorValue (W i)) (fun i => C i = true) -
      finiteConditionalMean p (fun i => indicatorValue (W i)) (fun i => C i = false) =
        (N*n11-nC*nW)/(nC*(N-nC)) ∧
    (finiteConditionalMean p (fun i => indicatorValue (C i)) (fun i => W i = true) >
      finiteConditionalMean p (fun i => indicatorValue (C i)) (fun i => W i = false) ↔ nC*nW < N*n11) ∧
    (finiteConditionalMean p (fun i => indicatorValue (W i)) (fun i => C i = true) >
      finiteConditionalMean p (fun i => indicatorValue (W i)) (fun i => C i = false) ↔ nC*nW < N*n11)

def RaleighContactComparisons : Prop :=
    (602/1370 - 160/315 : ℝ) = -2957/43155 ∧
    (602/1370 - 155/308 : ℝ) = -13467/210980 ∧
    (602/1370 - 160/315 : ℝ) < 0 ∧ (602/1370 - 155/308 : ℝ) < 0

def SEMDefierFacts : Prop :=
    IsFiniteLaw semDefierWitnessMass ∧
    FiniteIndependent semDefierWitnessMass
      (fun i => ((semDefierResponse i.1).x, (semDefierResponse i.1).d0, (semDefierResponse i.1).d1,
        (semDefierResponse i.1).y0, (semDefierResponse i.1).y1)) Prod.snd ∧
    (∀ i : Bool × Bool, (semDefierResponse i.1).treatmentEffect = 1 ∧
      (semDefierResponse i.1).observedOutcome i.2 = indicatorValue ((semDefierResponse i.1).receivedTreatment i.2) +
        (semDefierResponse i.1).y0 ∧
      indicatorValue ((semDefierResponse i.1).receivedTreatment i.2) = 1/4 + indicatorValue i.2/2 + semDefierResidual i) ∧
    (∀ z, finiteConditionalMean semDefierWitnessMass semDefierResidual (fun i => i.2 = z) = 0) ∧
    finiteExpectation semDefierWitnessMass (fun i => indicatorValue i.2) = 1/4 ∧
    finiteVariance semDefierWitnessMass (fun i => indicatorValue i.2) = 3/16 ∧
    finiteExpectation semDefierWitnessMass (fun i => (semDefierResponse i.1).y0) = 0 ∧
    finiteVariance semDefierWitnessMass (fun i => (semDefierResponse i.1).y0) = 3/16 ∧
    finiteCovariance semDefierWitnessMass (fun i => indicatorValue i.2) (fun i => (semDefierResponse i.1).y0) = 0 ∧
    finiteCorrelation semDefierWitnessMass (fun i => indicatorValue i.2) (fun i => (semDefierResponse i.1).y0) = 0 ∧
    finiteCovariance semDefierWitnessMass (fun i => indicatorValue i.2)
      (fun i => indicatorValue ((semDefierResponse i.1).receivedTreatment i.2)) = 3/32 ∧
    finiteCovariance semDefierWitnessMass (fun i => indicatorValue ((semDefierResponse i.1).receivedTreatment i.2))
      (fun i => (semDefierResponse i.1).y0) = 3/32 ∧
    finiteProbability semDefierWitnessMass (fun i => (semDefierResponse i.1).isDefier) = 1/4

def SEMDependenceFacts : Prop :=
    IsFiniteLaw (fun _ : Fin 4 => (1/4 : ℝ)) ∧
    (∀ i, (semDependentResponse i).treatmentEffect = 1 ∧ (semDependentResponse i).observedOutcome (semDependentAssignment i) =
      indicatorValue ((semDependentResponse i).receivedTreatment (semDependentAssignment i)) + (semDependentResponse i).y0 ∧
      indicatorValue ((semDependentResponse i).receivedTreatment (semDependentAssignment i)) = 1/2 + indicatorValue (semDependentAssignment i)/2 + semDependentResidual i) ∧
    (∀ z, finiteConditionalMean (fun _ => 1/4) semDependentResidual (fun i => semDependentAssignment i = z) = 0 ∧
      finiteConditionalMean (fun _ => 1/4) (fun i => (semDependentResponse i).y0) (fun i => semDependentAssignment i = z) = 0) ∧
    finiteVariance (fun _ => 1/4) (fun i => indicatorValue (semDependentAssignment i)) = 1/4 ∧
    finiteVariance (fun _ => 1/4) (fun i => (semDependentResponse i).y0) = 5/2 ∧
    finiteCorrelation (fun _ => 1/4) (fun i => indicatorValue (semDependentAssignment i)) (fun i => (semDependentResponse i).y0) = 0 ∧
    finiteCovariance (fun _ => 1/4) (fun i => indicatorValue (semDependentAssignment i))
      (fun i => indicatorValue ((semDependentResponse i).receivedTreatment (semDependentAssignment i))) = 1/8 ∧
    finiteCovariance (fun _ => 1/4) (fun i => indicatorValue ((semDependentResponse i).receivedTreatment (semDependentAssignment i)))
      (fun i => (semDependentResponse i).y0) = 1/4 ∧
    finiteProbability (fun _ => 1/4) (fun i => (semDependentResponse i).isDefier) = 0 ∧
    ¬ FiniteIndependent (fun _ => 1/4) (fun i => (semDependentResponse i).y0) semDependentAssignment

def HeterogeneousIVFacts : Prop :=
    FiniteIVConditions (bernoulliProductMass (fun _ : Bool => 1/2) (1/2)) (assignResponse heterogeneousResponse) Prod.snd ∧
    (heterogeneousResponse false).treatmentEffect = 1 ∧ (heterogeneousResponse true).treatmentEffect = 2 ∧
    ¬ (∃ β : ℝ, ∀ h, (heterogeneousResponse h).treatmentEffect = β) ∧
    finiteExpectation (bernoulliProductMass (fun _ : Bool => 1/2) (1/2)) (fun i => (heterogeneousResponse i.1).treatmentEffect) = 3/2 ∧
    finiteWald (bernoulliProductMass (fun _ : Bool => 1/2) (1/2)) (assignResponse heterogeneousResponse) Prod.snd
      (fun _ => 1) = 3/2

def SEMConstantEffect : Prop :=
  ∀ {I K : Type*} [Fintype K]
    (Y0 Y1 u : I → ℝ) (Q : I → K → ℝ) (β0 β1 : ℝ) (coeff : K → ℝ)
    (h0 : ∀ i, Y0 i = β0 + (∑ k, coeff k * Q i k) + u i)
    (h1 : ∀ i, Y1 i = β0 + β1 + (∑ k, coeff k * Q i k) + u i),
    ∀ i, Y1 i - Y0 i = β1

def ConstantScorePopulationFacts : Prop :=
    FiniteIVConditions sixAtomMass (assignResponse constantResponse) Prod.snd ∧
    FiniteLatentIgnorability sixAtomMass (assignResponse constantResponse) ∧
    finiteComplianceScore sixAtomMass (assignResponse constantResponse) () = 1/2 ∧
    (1/4 : ℝ) < finiteComplianceScore sixAtomMass (assignResponse constantResponse) () ∧
    finiteExpectation sixAtomMass (fun i => (constantResponse i.1).treatmentEffect) = 1 ∧
    finiteWald sixAtomMass (assignResponse constantResponse) Prod.snd (fun _ => 2) = 1

def FivePerArmBiasFacts : Prop :=
    finiteExpectation (independentArmCountMass 5 5 (1/2) (3/10)) (empiricalPositiveScore 5 5) = 15659/64000 ∧
    (15659/64000 : ℝ) - 1/5 = 2859/64000 ∧
    finiteProbability (independentArmCountMass 5 5 (1/2) (3/10)) (fun k => k.1.val < k.2.val) = 257079/1600000

def SaturatedBiasWitnessFacts : Prop :=
    FiniteIVConditions sixAtomMass (assignResponse constantResponse) Prod.snd ∧
    FiniteLatentIgnorability sixAtomMass (assignResponse constantResponse) ∧
    finiteComplianceScore sixAtomMass (assignResponse constantResponse) () = 1/2 ∧
    (1/4 : ℝ) < finiteComplianceScore sixAtomMass (assignResponse constantResponse) () ∧
    finiteConditionalMean sixAtomMass (fun i => indicatorValue ((constantResponse i.1).receivedTreatment i.2)) (fun i => i.2 = true) = 3/4 ∧
    finiteConditionalMean sixAtomMass (fun i => indicatorValue ((constantResponse i.1).receivedTreatment i.2)) (fun i => i.2 = false) = 1/4 ∧
    IsFiniteLaw twoReceiptMass ∧
    (∀ d, twoReceiptFit d ∈ closedReceiptTriangle ∧
      ∀ v ∈ closedReceiptTriangle, twoReceiptLikelihood d v.1 v.2 ≤
        twoReceiptLikelihood d (twoReceiptFit d).1 (twoReceiptFit d).2) ∧
    finiteExpectation twoReceiptMass (fun d => (twoReceiptFit d).1-(twoReceiptFit d).2) = 9/16 ∧
    (9/16 : ℝ) ≠ finiteComplianceScore sixAtomMass (assignResponse constantResponse) ()

def SaturatedScoreBiasFacts : Prop :=
    IsFiniteLaw twoReceiptMass ∧
    (∀ d, (twoReceiptFit d).1 - (twoReceiptFit d).2 =
      if d.1 = true ∧ d.2 = false then 1 else 0) ∧
    finiteExpectation twoReceiptMass (fun d => (twoReceiptFit d).1 - (twoReceiptFit d).2) = 9/16 ∧
    finiteExpectation twoReceiptMass (fun d => indicatorValue d.1 - indicatorValue d.2) = 1/2 ∧
    (9/16 : ℝ) - 1/2 = 1/16 ∧ (9/16 : ℝ) ≠ 1/2 ∧
    nestedReceiptProbability (3/4) (1/3) true = 3/4 ∧ nestedReceiptProbability (3/4) (1/3) false = 1/4

end
end SAP.P029a
