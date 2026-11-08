import Mathlib
import SAP.P011a.Defs.Part4

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P011a

open MeasureTheory ProbabilityTheory Filter Finset
open scoped BigOperators Topology Classical Matrix NNReal ENNReal
noncomputable section
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false

def AlternatingMoments : Prop :=
  ∀ (k : ℕ),
  let n := k+1
    let m := alternatingModel n
    let t := alternatingWeight n
    1/2 ≤ t ∧ t ≤ 1 ∧ beta m=1 ∧
    (∀ i, covariance m i i=t^2 ∧
      delta m i=t*(if i.val%2=0 then 2 else 0)-1) ∧
    meanSpread m=alternatingSpread n ∧
    (∀ u : Fin n → Bool,
      sampleVariance (weighted m (alternatingOutcome n u)) = t^2+meanSpread m+
        2*t*(∑ i, delta m i*sign (u i))/(n : ℝ)-t^2*(∑ i, sign (u i))^2/(n : ℝ)^2) ∧
    expectation m (varianceRemainder m)=-t^2/(n : ℝ) ∧
    expectation m (fun y => varianceRemainder m y^2) =
      4*t^2*meanSpread m/(n : ℝ)+t^4*(3/(n : ℝ)^2-2/(n : ℝ)^3) ∧
    (Even n → t=1 ∧ meanSpread m=1 ∧
      expectation m (fun y => ((n : ℝ)*V2 m.G (weighted m y)-1-1)^2)=
        4/(n : ℝ)+3/(n : ℝ)^2-2/(n : ℝ)^3 ∧
      1-4*(4/(n : ℝ)+3/(n : ℝ)^2-2/(n : ℝ)^3) ≤
        probability m {y | |(n : ℝ)*V2 m.G (weighted m y)-1| > 1/2} ∧
      1-4*(4/(n : ℝ)+3/(n : ℝ)^2-2/(n : ℝ)^3) ≤
        probability m {y | |(n : ℝ)*V2 m.G (weighted m y)-1| < 3/2})

def HomoskedasticRepair : Prop :=
  ∀ (F : Family) (c1 c2 c3 c4 : ℝ)
    (h : Scaling F c1 c2 c3 c4) (hs : ∀ k, Homoskedastic (F.model k)),
  (∀ k,
      (∀ y, sampleVariance (weighted (F.model k) y) = U (F.model k) y-(betaHat (F.model k) y-beta (F.model k))^2) ∧
      expectation (F.model k) (U (F.model k)) = meanVariance (F.model k)+meanSpread (F.model k) ∧
      var (F.model k) (U (F.model k)) ≤ (1+c2)*c1^4/(F.size k : ℝ) ∧
      expectation (F.model k) (fun y => (betaHat (F.model k) y-beta (F.model k))^2) ≤ (1+c2)*c1^2/(F.size k : ℝ) ∧
      expectation (F.model k) (fun y => (betaHat (F.model k) y-beta (F.model k))^4) ≤ (1+c2)*c1^4/(F.size k : ℝ) ∧
      expectation (F.model k) (fun y => varianceRemainder (F.model k) y^2) ≤ 4*(1+c2)*c1^4/(F.size k : ℝ) ∧
      scaledTrue F k ≤ meanVariance (F.model k)*gFactor (F.model k) ∧
      1 ≤ gFactor (F.model k) ∧ gFactor (F.model k) ≤ 1+c2 ∧
      (∀ y, (F.size k : ℝ)*V2 (F.model k).G (weighted (F.model k) y) =
        gFactor (F.model k)*sampleVariance (weighted (F.model k) y) ∧
        scaledTrue F k-(F.size k : ℝ)*V2 (F.model k).G (weighted (F.model k) y) ≤
          (1+c2)*|varianceRemainder (F.model k) y|) ∧
      (∀ ε : ℝ, 0 < ε → probability (F.model k)
        {y | scaledTrue F k-(F.size k : ℝ)*V2 (F.model k).G (weighted (F.model k) y) > ε}
          ≤ 4*(1+c2)^3*c1^4/((F.size k : ℝ)*ε^2))) ∧
    Conservative F (fun k y => V2 (F.model k).G (weighted (F.model k) y))

def MatchingReduction : Prop :=
  ∀ {n : ℕ} (hn : 0 < n) (P : DegreeProblem n),
  ((∃ S, EdgeFeasible P S) ↔ ∀ i, edgeDegree P.forced i ≤ min (P.cap i) (n-1)) ∧
    ((∀ i, edgeDegree P.forced i ≤ min (P.cap i) (n-1)) →
      (∀ S, EdgeFeasible P S ↔ ∃ T : Finset (Edge n), T ⊆ optionalEdges P ∧
        (∀ i, edgeDegree T i ≤ remainingCap P i) ∧ S=P.forced ∪ T) ∧
      (∀ J : Finset (GadgetEdge P), IsMatching J →
        (∀ J' : Finset (GadgetEdge P), IsMatching J' →
          (∑ e ∈ J', gadgetWeight e) ≤ ∑ e ∈ J, gadgetWeight e) →
        EdgeFeasible P (P.forced ∪ decodeMatching P J) ∧
        (∀ S, EdgeFeasible P S → edgeObjective P S ≤ edgeObjective P (P.forced ∪ decodeMatching P J)) ∧
        edgeObjective P (P.forced ∪ decodeMatching P J) =
          edgeObjective P P.forced +
            ((∑ e ∈ J, gadgetWeight e : ℤ) - 4*gadgetM P*(optionalEdges P).card : ℚ)
              /(2*(denominatorLCM P : ℚ)))) ∧
    (2*(optionalEdges P).card+∑ i, remainingCap P i ≤ 2*n*(n-1)) ∧
    ((optionalEdges P).card+∑ e ∈ optionalEdges P,
      (remainingCap P e.val.1+remainingCap P e.val.2) ≤ (optionalEdges P).card*(2*n-1))

def MatchingCounts : Prop :=
  ∀ {n : ℕ} (P : DegreeProblem n),
  Nat.card (GadgetVertex P) = 2*(optionalEdges P).card+(∑ i, remainingCap P i) ∧
    Nat.card (GadgetEdge P) = (optionalEdges P).card+
      ∑ e ∈ optionalEdges P, (remainingCap P e.val.1 + remainingCap P e.val.2)

def MatchingInstances : Prop :=
  (∀ i, remainingCap (matchingWitness false) i = (![1,1,0,2] : Fin 4 → ℕ) i) ∧
    (∀ i, remainingCap (matchingWitness true) i = (![0,1,0,1] : Fin 4 → ℕ) i) ∧
    (∀ second, denominatorLCM (matchingWitness second)=4 ∧ gadgetM (matchingWitness second)=10) ∧
    (optionalEdges (matchingWitness false)).card=4 ∧
    (optionalEdges (matchingWitness true)).card=5 ∧
    (∀ second, EdgeFeasible (matchingWitness second) (matchingWitnessSolution second) ∧
      edgeObjective (matchingWitness second) (matchingWitnessSolution second) =
        (if second then -3/4 else 3/4) ∧
      (∀ T, EdgeFeasible (matchingWitness second) T →
        edgeObjective (matchingWitness second) T ≤
          edgeObjective (matchingWitness second) (matchingWitnessSolution second))) ∧
    (∀ second, ∃ J : Finset (GadgetEdge (matchingWitness second)), IsMatching J ∧
      (∑ e ∈ J, gadgetWeight e) = (if second then 200 else 166) ∧
      (∀ J' : Finset (GadgetEdge (matchingWitness second)), IsMatching J' →
        (∑ e ∈ J', gadgetWeight e) ≤ ∑ e ∈ J, gadgetWeight e))

def RelaxationUpperBound : Prop :=
  ∀ {n : ℕ} (hn : 0 < n) (R : Graph n) (d : Fin n → ℕ)
    (w : Edge n → ℝ) (U : ℝ)
    (hU : ∀ a, RelaxedFeasible R d a → relaxedObjective a w ≤ U),
  (∀ a : Edge n → Bool, Compatible R d (fromUpper a) → upperObjective a w ≤ U) ∧
    (∀ x a, Compatible R d (fromUpper a) →
      (∀ e, w e = centered x e.val.1*centered x e.val.2) →
      V1 (fromUpper a) x ≤ ((n : ℝ)*sampleVariance x+2*U)/(n : ℝ)^2) ∧
    ((∀ e, w e = 1) → ∀ x a, Compatible R d (fromUpper a) →
      V2 (fromUpper a) x ≤ sampleVariance x/n*(1+2*U/n))

def RelaxationGaps : Prop :=
  (let x : Fin 6 → ℝ := ![1,1,1,-1,-1,-1]
     let w : Edge 6 → ℝ := fun e => x e.val.1*x e.val.2
     let f : Edge 6 → ℝ := fun e => if x e.val.1=x e.val.2 then 1/2 else 0
     RelaxedFeasible (emptyGraph 6) (fun _ => 1) f ∧ relaxedObjective f w = 3 ∧
     (∀ a, RelaxedFeasible (emptyGraph 6) (fun _ => 1) a → relaxedObjective a w ≤ 3) ∧
     (∃ a : Edge 6 → Bool, Compatible (emptyGraph 6) (fun _ => 1) (fromUpper a) ∧
       upperObjective a w = 2 ∧ V1 (fromUpper a) x = 5/18) ∧
     (∀ a : Edge 6 → Bool, Compatible (emptyGraph 6) (fun _ => 1) (fromUpper a) → upperObjective a w ≤ 2) ∧
     ((6+2*3 : ℝ)/6^2=1/3)) ∧
    (RelaxedFeasible (emptyGraph 3) (fun _ => 1) (fun _ => 1/2) ∧
      relaxedObjective (fun _ => 1/2) (fun _ : Edge 3 => 1) = 3/2 ∧
      (∀ a, RelaxedFeasible (emptyGraph 3) (fun _ => 1) a → relaxedObjective a (fun _ => 1) ≤ 3/2) ∧
      (∃ A : Graph 3, Compatible (emptyGraph 3) (fun _ => 1) A ∧
        (∑ i, ∑ j, adjacency A i j) = 2) ∧
      (∀ A : Graph 3, Compatible (emptyGraph 3) (fun _ => 1) A →
        (∑ i, ∑ j, adjacency A i j) ≤ 2))

def ScaledQuadraticExpectation : Prop := ∀ (F : Family) (c1 c2 c3 c4 : ℝ),
  Scaling F c1 c2 c3 c4 → ∀ k (M : Matrix (Fin (F.size k)) (Fin (F.size k)) ℝ),
  (∀ i j, M i j = M j i) →
expectation (F.model k) (fun y => quadratic M (centered (weighted (F.model k) y))) =
      Matrix.trace (centeringMatrix (F.size k) * M * centeringMatrix (F.size k) * covariance (F.model k)) + quadratic M (delta (F.model k)) ∧
    expectation (F.model k) (fun y => quadratic M (centered (weighted (F.model k) y))) =
      Matrix.trace (M * covariance (F.model k)) + quadratic M (delta (F.model k)) -
      2/((F.size k) : ℝ)*(∑ i, ∑ j, (M * covariance (F.model k)) i j) +
      quadratic M (fun _ => 1)*var (F.model k) (betaHat (F.model k))

def correctedEdgeObjective {n : ℕ} (d : Fin n → ℕ) (x : Fin n → ℝ) (A : Graph n) : ℝ :=
  upperSum (fun i j => (centered x i*centered x j +
    (degreeCorrection d i*centered x i^2 + degreeCorrection d j*centered x j^2)/2) * adjacency A i j)

def CorrectedOptimal : Prop := ∀ {n : ℕ}, 0 < n →
  ∀ (R A : Graph n) (d : Fin n → ℕ) (x : Fin n → ℝ),
  Maximizes R d (fun B => V1plus d B x) A →
  (∀ B, Compatible R d B → correctedEdgeObjective d x B ≤ correctedEdgeObjective d x A) ∧
  (n : ℝ)^2 * V1plus d A x = (∑ i, centered x i^2) + 2*correctedEdgeObjective d x A

def DegreeOnlyBounds : Prop := ∀ {n : ℕ}, 0 < n →
  ∀ (d : Fin n → ℕ) (D : ℕ), (∀ i, truncatedDegree d i ≤ D) → ∀ x : Fin n → ℝ,
  (∀ A, Maximizes (emptyGraph n) d (fun B => V1 B x) A →
    0 ≤ (n : ℝ)*(VYoung d x-V1 A x) ∧
    (n : ℝ)*(VYoung d x-V1 A x) ≤
      (∑ r ∈ Finset.Icc 1 D, (3*(r : ℝ)^2+2*r))*maxAbs (centered x)^2/n) ∧
  (∀ Ap, Maximizes (emptyGraph n) d (fun B => V1plus d B x) Ap →
    0 ≤ (∑ i, max 1 (2*(truncatedDegree d i : ℝ))*centered x i^2)/n - (n : ℝ)*V1plus d Ap x ∧
    (∑ i, max 1 (2*(truncatedDegree d i : ℝ))*centered x i^2)/n - (n : ℝ)*V1plus d Ap x ≤
      maxAbs (centered x)^2/n*(∑ r ∈ Finset.Icc 1 D, (4*(r : ℝ)^2+r)))

def OracleSpecialCases : Prop := ∀ (F : Family) (c1 c2 c3 c4 : ℝ),
  Scaling F c1 c2 c3 c4 → Valid F →
  ((∀ k i, expectation (F.model k) (fun y => weighted (F.model k) y i) = beta (F.model k)) ∨
    (∀ k, CliqueUnion (F.model k).G)) →
  (Conservative F (fun k y => V1 (F.model k).G (weighted (F.model k) y)) ∧
    ConservativeCoverage F (fun k y => V1 (F.model k).G (weighted (F.model k) y))) ∧
  (∀ A : ∀ k, (Fin (F.size k) → ℝ) → Graph (F.size k),
    (∀ k y, Maximizes (F.model k).R (F.model k).d
      (fun B => V1 B (weighted (F.model k) y)) (A k y)) →
    Conservative F (fun k y => V1 (A k y) (weighted (F.model k) y)) ∧
    ConservativeCoverage F (fun k y => V1 (A k y) (weighted (F.model k) y)))

def SignWitnessFacts : Prop := Scaling signFamily 1 1 1 2 ∧ Valid signFamily ∧
  (∀ k, scaledTrue signFamily k = 1 ∧ beta (signFamily.model k) = 0)

def SpectralDifference : Prop := ∀ {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (hM : M.IsHermitian),
  positivePart M - M =
    (hM.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ) *
      Matrix.diagonal (fun i => max (hM.eigenvalues i) 0 - hM.eigenvalues i) *
      (hM.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ)ᵀ

def HomoskedasticIdentities : Prop := ∀ (F : Family) (c1 c2 c3 c4 : ℝ),
  Scaling F c1 c2 c3 c4 → (∀ k, Homoskedastic (F.model k)) → ∀ k,
  (∀ i, meanVariance (F.model k) = covariance (F.model k) i i) ∧
  0 ≤ meanSpread (F.model k) ∧
  scaledTrue F k = (∑ i, ∑ j, covariance (F.model k) i j)/(F.size k : ℝ) ∧
  (∀ y,
    scaledTrue F k - (F.size k : ℝ)*V2 (F.model k).G (weighted (F.model k) y) ≤
      gFactor (F.model k)*(meanVariance (F.model k)-sampleVariance (weighted (F.model k) y)) ∧
    gFactor (F.model k)*(meanVariance (F.model k)-sampleVariance (weighted (F.model k) y)) =
      -gFactor (F.model k)*(meanSpread (F.model k)+varianceRemainder (F.model k) y) ∧
    -gFactor (F.model k)*(meanSpread (F.model k)+varianceRemainder (F.model k) y) ≤
      (1+c2)*|varianceRemainder (F.model k) y|)

def RelaxationProgramValues : Prop :=
  let x : Fin 6 → ℝ := ![1,1,1,-1,-1,-1]
  let w : Edge 6 → ℝ := fun e => x e.val.1*x e.val.2
  let f : Edge 6 → ℝ := fun e => if x e.val.1=x e.val.2 then 1/2 else 0
  average x = 0 ∧ sampleVariance x = 1 ∧
  2*relaxedObjective f w = 6 ∧
  (∀ a, RelaxedFeasible (emptyGraph 6) (fun _ => 1) a → 2*relaxedObjective a w ≤ 6) ∧
  (∃ a : Edge 6 → Bool, Compatible (emptyGraph 6) (fun _ => 1) (fromUpper a) ∧
    2*upperObjective a w = 4 ∧ V1 (fromUpper a) x = 5/18) ∧
  (∀ a : Edge 6 → Bool, Compatible (emptyGraph 6) (fun _ => 1) (fromUpper a) → 2*upperObjective a w ≤ 4) ∧
  (6+2*relaxedObjective f w)/6^2 = 1/3 ∧
  2*relaxedObjective (fun _ => 1/2) (fun _ : Edge 3 => 1) = 3 ∧
  (∀ a, RelaxedFeasible (emptyGraph 3) (fun _ => 1) a →
    2*relaxedObjective a (fun _ => 1) ≤ 3) ∧
  (∃ a0 : Edge 6 → ℝ, RelaxedFeasible (emptyGraph 6) (fun _ => 1) a0 ∧
    ∃ a : Edge 6 → Bool, Compatible (emptyGraph 6) (fun _ => 1) (fromUpper a) ∧
      relaxedObjective a0 w < upperObjective a w)

def sixIntegerEdges : Edge 6 → Bool := fun e => decide (e.val = (0,1) ∨ e.val = (3,4))

def RelaxationNamedWitness : Prop :=
  let x : Fin 6 → ℝ := ![1,1,1,-1,-1,-1]
  let w : Edge 6 → ℝ := fun e => x e.val.1*x e.val.2
  Compatible (emptyGraph 6) (fun _ => 1) (fromUpper sixIntegerEdges) ∧
  upperObjective sixIntegerEdges w = 2 ∧ V1 (fromUpper sixIntegerEdges) x = 5/18

def PathOLS : Prop := ∀ t : ℝ, (t = 1 ∨ t = 2) → ∀ K : ℕ, 0 < K →
  let D : Matrix (Fin (3*K)) (Fin 2) ℝ := fun i j =>
    if j = 0 then 1 else (![t,-2*t,t] : Fin 3 → ℝ) (localIndex (by decide) i)
  MeanModel (pathModel t K) D (![0,1] : Fin 2 → ℝ) ∧
  (∀ y, ols D y 0 = average y)

def T1Statement : Prop := CycleCounterexample ∧
  (∀ a : ℝ,
    (let H : Matrix (Fin 4) (Fin 4) ℝ :=
      ![![1,0,0,1],![1,1,0,0],![0,1,1,0],![0,0,1,1]]
     H*Hᵀ = (2 : ℝ) • (1 : Matrix (Fin 4) (Fin 4) ℝ) + adjacency cycleGraph) ∧
    quadratic (oracleMatrix cycleGraph) (![a,-a,a,-a] : Fin 4 → ℝ) = -4*a^2 ∧
    (∑ i, ∑ j, ((2 : ℝ) • (1 : Matrix (Fin 4) (Fin 4) ℝ) + adjacency cycleGraph) i j) = 16) ∧
  average (![5,-1,5,-1] : Fin 4 → ℝ) = 2

def T2Statement : Prop := PathCounterexample ∧ PathMoments ∧ PathOLS

def T3Statement : Prop := OracleConvergence ∧ OracleExpectation ∧
  SampleVarianceConvergence ∧ OracleMeanConditions ∧ CliqueCharacterization

def T4Statement : Prop := DeterministicExpansion ∧ ScaledQuadraticExpectation ∧
  DataDependentFailure ∧ CliqueCharacterization ∧ SignWitnessFacts

def T5Statement : Prop := CorrectedFinite ∧ CorrectedMatrix ∧ CorrectedAsymptotic ∧ CorrectedOptimal

def T6Statement : Prop := PositivePartFinite ∧ PositivePartConservative ∧
  PositivePartUnique ∧ PositivePartCycle ∧ PositivePartNonaffine ∧ CycleSpectrum ∧
  (∀ x : Fin 4 → ℝ, quadratic (positivePart (oracleMatrix cycleGraph)) x =
    quadratic (oracleMatrix cycleGraph) x + (x 0-x 1+x 2-x 3)^2/4 ∧
    quadratic (positivePart (oracleMatrix cycleGraph)) x =
    3/4*(x 0+x 1+x 2+x 3)^2 + ((x 0-x 2)^2+(x 1-x 3)^2)/2) ∧
  (∀ k, scaledTrue (cycleFamily (3/2)) k = 4) ∧ SpectralDifference

end
end SAP.P011a
