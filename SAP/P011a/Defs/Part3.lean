import Mathlib
import SAP.P011a.Defs.Part2

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

def cycleEigenvectors : Matrix (Fin 4) (Fin 4) ℝ :=
  ![![1/2,1/2,1/2,1/2], ![1/2,1/2,-1/2,-1/2],
    ![1/2,-1/2,-1/2,1/2], ![1/2,-1/2,1/2,-1/2]]

def cycleClipped : Matrix (Fin 4) (Fin 4) ℝ :=
  cycleEigenvectors*Matrix.diagonal (![3,1,1,0] : Fin 4 → ℝ)*cycleEigenvectorsᵀ

def alternatingParity (n : ℕ) : ℕ := (n+1)/2-n/2

def alternatingSpread (n : ℕ) : ℝ :=
  alternatingWeight n^2*(1-(alternatingParity n : ℝ)^2/(n : ℝ)^2)

def matchingWitness (second : Bool) : DegreeProblem 4 where
  forced := if second then {⟨(0,2),by decide⟩} else
    {⟨(0,2),by decide⟩,⟨(2,3),by decide⟩}
  cap := if second then fun _ => 1 else ![2,1,2,7]
  weight := fun e =>
    (![3/2,1/2,-1/2,-3/2] : Fin 4 → ℚ) e.val.1 *
    (![3/2,1/2,-1/2,-3/2] : Fin 4 → ℚ) e.val.2

def matchingWitnessSolution (second : Bool) : Finset (Edge 4) :=
  if second then (matchingWitness true).forced else
    (matchingWitness false).forced ∪ {⟨(0,1),by decide⟩}

def CycleCounterexample : Prop :=
  Scaling (cycleFamily (3/2)) (7/2) 2 4 2 ∧ Valid (cycleFamily (3/2)) ∧
    (∀ k, Homoskedastic ((cycleFamily (3/2)).model k) ∧
      (∀ i, expectation ((cycleFamily (3/2)).model k) (fun y => y i) =
        (![3/2,-3/2,3/2,-3/2] : Fin 4 → ℝ) (localIndex (by decide) i)) ∧
      (∀ i j, covariance ((cycleFamily (3/2)).model k) i j =
        ((2 : ℝ) • (1 : Matrix (Fin ((cycleFamily (3/2)).size k))
          (Fin ((cycleFamily (3/2)).size k)) ℝ) + adjacency ((cycleFamily (3/2)).model k).G) i j)) ∧
    (∀ k, beta ((cycleFamily (3/2)).model k) = 0 ∧
      scaledTrue (cycleFamily (3/2)) k = 4 ∧
      meanBias ((cycleFamily (3/2)).model k) = -9/4 ∧
      (∀ A, Compatible ((cycleFamily (3/2)).model k).R ((cycleFamily (3/2)).model k).d A
        ↔ A = ((cycleFamily (3/2)).model k).G) ∧
      expectation ((cycleFamily (3/2)).model k) (scaledOracle (cycleFamily (3/2)) k) =
        7/4 - 12 / ((cycleFamily (3/2)).size k : ℝ) ∧
      var ((cycleFamily (3/2)).model k) (scaledOracle (cycleFamily (3/2)) k) =
        44 / ((cycleFamily (3/2)).size k : ℝ) - 96 / ((cycleFamily (3/2)).size k : ℝ)^2 -
        288 / ((cycleFamily (3/2)).size k : ℝ)^3) ∧
    InProbability (cycleFamily (3/2)) (scaledOracle (cycleFamily (3/2))) (fun _ => 7/4) ∧
    (∀ ε : ℝ, 0 < ε → ε < 9/4 →
      Tendsto (fun k => probability ((cycleFamily (3/2)).model k)
        {y | |scaledOracle (cycleFamily (3/2)) k y - 4| > ε}) atTop (𝓝 1) ∧
      Tendsto (fun k => probability ((cycleFamily (3/2)).model k)
        {y | 4 - scaledOracle (cycleFamily (3/2)) k y > ε}) atTop (𝓝 1)) ∧
    (∀ t : ℝ, Tendsto (fun k => probability ((cycleFamily (3/2)).model k)
      {y | Real.sqrt ((cycleFamily (3/2)).size k : ℝ)*betaHat ((cycleFamily (3/2)).model k) y ≤ t})
      atTop (𝓝 (Phi (t/2)))) ∧
    (∀ α : ℝ, 0 < α → α < 1 →
      Tendsto (fun k => coverage ((cycleFamily (3/2)).model k)
        (fun y => V1 ((cycleFamily (3/2)).model k).G (weighted ((cycleFamily (3/2)).model k) y)) α)
        atTop (𝓝 (2*Phi (normalQuantile α * Real.sqrt (7/16)) - 1)) ∧
      2*Phi (normalQuantile α * Real.sqrt (7/16)) - 1 < 1-α) ∧
    Scaling (cycleFamily 3) 5 2 4 2 ∧ Valid (cycleFamily 3) ∧
    (∀ k, Homoskedastic ((cycleFamily 3).model k) ∧ beta ((cycleFamily 3).model k)=0 ∧
      scaledTrue (cycleFamily 3) k=4) ∧
    InProbability (cycleFamily 3) (scaledOracle (cycleFamily 3)) (fun _ => -5) ∧
    probability (cycleModel 3 1) {y | y=(![5,-1,5,-1] : Fin 4 → ℝ)}=1/16 ∧
    V1 cycleGraph (![5,-1,5,-1] : Fin 4 → ℝ) = -9/4

def PathCounterexample : Prop :=
  ∀ (t : ℝ) (ht : t = 1 ∨ t = 2),
  Scaling (pathFamily t) 6 2 (29/15) 2 ∧ Valid (pathFamily t) ∧
    (∀ k, Homoskedastic ((pathFamily t).model k)) ∧
    (∀ k, beta ((pathFamily t).model k) = 0 ∧ scaledTrue (pathFamily t) k = 29/15 ∧
      (∀ A, Compatible ((pathFamily t).model k).R ((pathFamily t).model k).d A
        ↔ A = ((pathFamily t).model k).G) ∧
      expectation ((pathFamily t).model k) (scaledOracle (pathFamily t) k) =
        (29-10*t^2)/15 - 217/(135*((k+1 : ℕ) : ℝ))) ∧
    InProbability (pathFamily t) (scaledOracle (pathFamily t)) (fun _ => (29-10*t^2)/15) ∧
    (t = 1 → (∀ ε : ℝ, 0 < ε → ε < 2/3 →
      Tendsto (fun k => probability ((pathFamily t).model k)
        {y | |scaledOracle (pathFamily t) k y - 29/15| > ε}) atTop (𝓝 1) ∧
      Tendsto (fun k => probability ((pathFamily t).model k)
        {y | 29/15-scaledOracle (pathFamily t) k y > ε}) atTop (𝓝 1)) ∧
      (∀ α : ℝ, 0 < α → α < 1 →
        Tendsto (fun k => coverage ((pathFamily t).model k)
          (fun y => V1 ((pathFamily t).model k).G (weighted ((pathFamily t).model k) y)) α)
          atTop (𝓝 (2*Phi (normalQuantile α * Real.sqrt (19/29)) - 1)) ∧
        2*Phi (normalQuantile α * Real.sqrt (19/29)) - 1 < 1-α)) ∧
    (t = 2 → Tendsto (fun k => probability ((pathFamily t).model k)
      {y | V1 ((pathFamily t).model k).G (weighted ((pathFamily t).model k) y) < 0}) atTop (𝓝 1) ∧
      (∀ α : ℝ, 0 < α → α < 1 →
        Tendsto (fun k => coverage ((pathFamily t).model k)
          (fun y => V1 ((pathFamily t).model k).G (weighted ((pathFamily t).model k) y)) α)
          atTop (𝓝 0)))

def PathMoments : Prop :=
  ∀ (t : ℝ) (ht : t = 1 ∨ t = 2),
  (∀ i : Fin 3,
      pathMean (fun u v => pathBlock t u v i) =
        (![t, -2*t, t] : Fin 3 → ℝ) i) ∧
    (∀ i : Fin 3,
      expectation (pathModel t 1) (fun y => y i) =
        (![t, -2*t, t] : Fin 3 → ℝ) i) ∧
    covariance (pathModel t 1) =
      (![![1, 3/5, 0], ![3/5, 1, 4/5], ![0, 4/5, 1]] :
        Matrix (Fin 3) (Fin 3) ℝ) ∧
    quadratic (oracleMatrix pathGraph) (![t, -2*t, t] : Fin 3 → ℝ) = -2*t^2 ∧
    pathMean (fun u v => ∑ i, pathBlock t u v i) = 0 ∧
    pathMean (fun u v => (∑ i, pathBlock t u v i)^2) = 29/5 ∧
    pathMean (fun u v => quadratic (oracleMatrix pathGraph) (pathBlock t u v)) =
      29/5 - 2*t^2 ∧
    pathMean (fun u v =>
      (quadratic (oracleMatrix pathGraph) (pathBlock t u v) - (29/5 - 2*t^2))^2) =
      8*t^2 + 8836/625 ∧
    pathMean (fun u v => (∑ i, pathBlock t u v i) *
      (∑ i, ∑ j, oracleMatrix pathGraph i j * pathBlock t u v j)) = 14 ∧
    quadratic (oracleMatrix pathGraph) (fun _ => 1) = 7

def OracleConvergence : Prop :=
  ∀ (F : Family) (c1 c2 c3 c4 : ℝ)
    (h : Scaling F c1 c2 c3 c4),
  InProbability F
      (fun k y => (F.size k : ℝ) * V1 (F.model k).G (weighted (F.model k) y))
      (fun k => (F.size k : ℝ) * var (F.model k) (betaHat (F.model k)) + meanBias (F.model k))

def OracleExpectation : Prop :=
  ∀ (F : Family) (c1 c2 c3 c4 : ℝ)
    (h : Scaling F c1 c2 c3 c4) (k : ℕ),
  |expectation (F.model k) (scaledOracle F k) - scaledTrue F k - meanBias (F.model k)|
      ≤ 3*(1+c2)^2*c1^2/(F.size k : ℝ)

def SampleVarianceConvergence : Prop :=
  ∀ (F : Family) (c1 c2 c3 c4 : ℝ)
    (h : Scaling F c1 c2 c3 c4),
  InProbability F (fun k y => sampleVariance (weighted (F.model k) y))
      (fun k => meanVariance (F.model k) + meanSpread (F.model k))

def OracleMeanConditions : Prop :=
  ∀ (F : Family) (c1 c2 c3 c4 : ℝ)
    (h : Scaling F c1 c2 c3 c4),
  (InProbability F (scaledOracle F) (scaledTrue F) ↔
      Tendsto (fun k => meanBias (F.model k)) atTop (𝓝 0)) ∧
    (Conservative F (fun k y => V1 (F.model k).G (weighted (F.model k) y)) ↔
      0 ≤ Filter.liminf (fun k => meanBias (F.model k)) atTop) ∧
    ((∀ k i, delta (F.model k) i = 0) →
      InProbability F (scaledOracle F) (scaledTrue F)) ∧
    ((∀ k, PSD (oracleMatrix (F.model k).G)) →
      Conservative F (fun k y => V1 (F.model k).G (weighted (F.model k) y)))

def CliqueCharacterization : Prop :=
  ∀ {n : ℕ} (hn : 0 < n) (A : Graph n),
  (PSD (oracleMatrix A) ↔ CliqueUnion A) ∧
    (∀ C : Fin n → ℕ,
      (∀ i j, A.val i j = true ↔ i ≠ j ∧ C i = C j) →
      ∀ x : Fin n → ℝ, V1 A x =
        (∑ c ∈ Finset.univ.image C, (∑ i with C i = c, centered x i)^2) / (n : ℝ)^2)

def DeterministicExpansion : Prop :=
  ∀ (F : Family) (c1 c2 c3 c4 K : ℝ)
    (h : Scaling F c1 c2 c3 c4)
    (M : ∀ k, Matrix (Fin (F.size k)) (Fin (F.size k)) ℝ)
    (hM : ∀ k i j, M k i j = M k j i) (hK : ∀ k, operatorNorm (M k) ≤ K),
  (∃ B : ℝ, 0 ≤ B ∧ ∃ k0 : ℕ, ∀ k ≥ k0,
      var (F.model k) (fun y => quadratic (M k) (centered (weighted (F.model k) y)))
        ≤ B*(F.size k : ℝ)) ∧
    InProbability F
      (fun k y => (F.size k : ℝ)*varianceForm (M k) (weighted (F.model k) y) - scaledTrue F k)
      (fun k => (Matrix.trace ((M k - oracleMatrix (F.model k).G)*covariance (F.model k)) +
        quadratic (M k) (delta (F.model k))) / (F.size k : ℝ)) ∧
    ((∀ k, PSD (M k) ∧ PSD (M k - oracleMatrix (F.model k).G)) →
      (∀ k, 0 ≤ quadratic (M k) (delta (F.model k)) ∧
        0 ≤ Matrix.trace ((M k-oracleMatrix (F.model k).G)*covariance (F.model k))) ∧
      Conservative F (fun k y => varianceForm (M k) (weighted (F.model k) y)))

def QuadraticExpectation : Prop :=
  ∀ {n : ℕ} (hn : 0 < n) (m : Model n)
    (hL2 : ∀ i, MemLp (fun y => weighted m y i) 2 m.law)
    (M : Matrix (Fin n) (Fin n) ℝ) (hM : ∀ i j, M i j = M j i),
  expectation m (fun y => quadratic M (centered (weighted m y))) =
      Matrix.trace (centeringMatrix n * M * centeringMatrix n * covariance m) + quadratic M (delta m) ∧
    expectation m (fun y => quadratic M (centered (weighted m y))) =
      Matrix.trace (M * covariance m) + quadratic M (delta m) -
      2/(n : ℝ)*(∑ i, ∑ j, (M * covariance m) i j) +
      quadratic M (fun _ => 1)*var m (betaHat m)

def DataDependentFailure : Prop :=
  (∀ n (hn : 0 < n) (x : Fin n → ℝ), (∀ i, x i = 1 ∨ x i = -1) →
      operatorNorm (dataMatrix x) = 1 ∧ Matrix.trace (dataMatrix x) = 1 ∧
      (n : ℝ)*varianceForm (dataMatrix x) x = (1-average x^2)^2) ∧
    InProbability signFamily
      (fun k y => (k+1 : ℝ)*varianceForm (dataMatrix y) y - 1) (fun _ => 0) ∧
    InProbability signFamily
      (fun k y => Matrix.trace (dataMatrix y - 1)/(k+1 : ℝ)) (fun _ => -1)

def CorrectedFinite : Prop :=
  ∀ {n : ℕ} (hn : 0 < n) (R A : Graph n) (d : Fin n → ℕ)
    (hA : Compatible R d A) (x : Fin n → ℝ),
  (∀ i, degree A i ≤ truncatedDegree d i) ∧
    correctedMatrix d A = Matrix.diagonal (fun i => (degree A i : ℝ)) + adjacency A +
      Matrix.diagonal (fun i => 1 - if truncatedDegree d i = 0 then 0
        else (degree A i : ℝ)/(truncatedDegree d i : ℝ)) ∧
    (∀ z, quadratic (Matrix.diagonal (fun i => (degree A i : ℝ)) + adjacency A) z =
      upperSum (fun i j => adjacency A i j*(z i+z j)^2)) ∧
    PSD (correctedMatrix d A) ∧ 0 ≤ V1plus d A x ∧
    PSD (correctedMatrix d A - oracleMatrix A) ∧
    PSD (1 + Matrix.diagonal (fun i => (truncatedDegree d i : ℝ))) ∧
    PSD (Matrix.diagonal (fun i => (truncatedDegree d i : ℝ)) - adjacency A) ∧
    PSD (Matrix.diagonal (fun i => (truncatedDegree d i : ℝ)) -
      Matrix.diagonal (fun i => (degree A i : ℝ))) ∧
    PSD (Matrix.diagonal (fun i => (degree A i : ℝ)) - adjacency A) ∧
    (1 + Matrix.diagonal (fun i => (truncatedDegree d i : ℝ))) - oracleMatrix A =
      (Matrix.diagonal (fun i => (truncatedDegree d i : ℝ)) -
        Matrix.diagonal (fun i => (degree A i : ℝ))) +
      (Matrix.diagonal (fun i => (degree A i : ℝ)) - adjacency A) ∧
    (∀ z, quadratic (Matrix.diagonal (fun i => (degree A i : ℝ)) - adjacency A) z =
      upperSum (fun i j => adjacency A i j*(z i-z j)^2)) ∧
    V1 A x ≤ VYoung d x ∧
    ((n : ℝ)^2 * V1plus d A x = (∑ i, centered x i^2) +
      2*upperSum (fun i j => (centered x i*centered x j +
        (degreeCorrection d i*centered x i^2 + degreeCorrection d j*centered x j^2)/2)
        *adjacency A i j)) ∧
    (∀ D : ℕ, (∀ i, truncatedDegree d i = D) → VYoung d x = V2prime d x ∧
      V2prime d x = sampleVariance x*(1+(D : ℝ))/(n : ℝ)) ∧
    (∀ d0 D : ℕ, 1 ≤ D → (∀ i, degree A i = d0) →
      (∀ i, truncatedDegree d i = D) →
      V1plus d A x = V1 A x + (d0 : ℝ)*(1-1/(D : ℝ))*(∑ i, centered x i^2)/(n : ℝ)^2) ∧
    (∀ d0 : ℕ, 1 ≤ d0 → (∀ i, degree A i = d0) → (∀ i, truncatedDegree d i = d0) →
      V1plus d A x = V1 A x + ((d0 : ℝ)-1)*(∑ i, centered x i^2)/(n : ℝ)^2) ∧
    ((∀ i, degree A i = 0) → V1plus d A x = V1 A x)

end
end SAP.P011a
