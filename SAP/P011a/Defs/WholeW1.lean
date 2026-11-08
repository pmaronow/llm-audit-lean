import Mathlib
import SAP.P011a.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P011a

open MeasureTheory ProbabilityTheory Filter Finset
open scoped BigOperators Topology Classical Matrix NNReal ENNReal
noncomputable section

/-- Assumption 2 on the observed triangular array. The observed sizes are positive and
 tend to infinity by `Family`; no relation between different rows' observed graphs is imposed.
 This also covers nested full graphs with changing observed subsets. -/
structure WholeScaling (F : Family) (c1 c2 c3 c4 : ℝ) : Prop where
  c1_pos : 0 < c1
  c2_pos : 0 < c2
  c3_pos : 0 < c3
  c4_pos : 0 < c4
  dependency : ∀ k, Dependency (F.model k)
  bounded : ∀ k, ∀ᵐ y ∂(F.model k).law, ∀ i,
    |weighted (F.model k) y i - beta (F.model k)| ≤ c1
  degrees : ∀ k i, (degree (F.model k).G i : ℝ) ≤ c2
  variance_limit : Tendsto (scaledTrue F) atTop (𝓝 c3)
  coefficients : ∀ k i, |(F.model k).theta i| < c4

/-- The six finite identities and moment bounds in T12(i). -/
def WholeHomoskedasticMoments {n : ℕ} (m : Model n) (c d : ℝ) : Prop :=
  (∀ y, sampleVariance (weighted m y) = U m y - (betaHat m y - beta m)^2) ∧
  expectation m (U m) = meanVariance m + meanSpread m ∧
  var m (U m) ≤ (1+d)*c^4/(n : ℝ) ∧
  expectation m (fun y => (betaHat m y-beta m)^2) ≤ (1+d)*c^2/(n : ℝ) ∧
  expectation m (fun y => (betaHat m y-beta m)^4) ≤ (1+d)*c^4/(n : ℝ) ∧
  expectation m (fun y => varianceRemainder m y^2) ≤ 4*(1+d)*c^4/(n : ℝ)

/-- Common variance, nonnegative mean spread, and all equalities and inequalities
 in T12(ii),(iii). These are finite assertions; zero common variance is permitted. -/
def WholeHomoskedasticComparison {n : ℕ} (m : Model n) (d : ℝ) : Prop :=
  (∀ i, meanVariance m = covariance m i i) ∧ 0 ≤ meanSpread m ∧
  (n : ℝ)*var m (betaHat m) = (∑ i, ∑ j, covariance m i j)/(n : ℝ) ∧
  (n : ℝ)*var m (betaHat m) ≤ meanVariance m*gFactor m ∧
  1 ≤ gFactor m ∧ gFactor m ≤ 1+d ∧
  (∀ y,
    (n : ℝ)*V2 m.G (weighted m y) = gFactor m*sampleVariance (weighted m y) ∧
    (n : ℝ)*var m (betaHat m)-(n : ℝ)*V2 m.G (weighted m y) ≤
      gFactor m*(meanVariance m-sampleVariance (weighted m y)) ∧
    gFactor m*(meanVariance m-sampleVariance (weighted m y)) =
      -gFactor m*(meanSpread m+varianceRemainder m y) ∧
    -gFactor m*(meanSpread m+varianceRemainder m y) ≤ (1+d)*|varianceRemainder m y|)

/-- The explicit finite tail bound in T12(iv). -/
def WholeHomoskedasticTail {n : ℕ} (m : Model n) (c d : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → probability m
    {y | (n : ℝ)*var m (betaHat m)-(n : ℝ)*V2 m.G (weighted m y) > ε} ≤
      4*(1+d)^3*c^4/((n : ℝ)*ε^2)

/-- P011-T12; p. 2246 (PDF p. 9).
Under Assumptions 2 and 3, the homoskedastic oracle estimator satisfies the entire
finite moment, covariance and scalar gap chain, the explicit tail bound
4(1+c2)^3 c1^4/(n epsilon^2), and one-sided asymptotic conservativeness.
Unit means may differ, early common variances may vanish, and neither the mean
spread nor the common variance needs a limit. -/
def T12WholeStatement : Prop :=
  ∀ (F : Family) (c1 c2 c3 c4 : ℝ), WholeScaling F c1 c2 c3 c4 →
    (∀ k, Homoskedastic (F.model k)) →
    (∀ k, WholeHomoskedasticMoments (F.model k) c1 c2 ∧
      WholeHomoskedasticComparison (F.model k) c2 ∧
      WholeHomoskedasticTail (F.model k) c1 c2) ∧
    Conservative F (fun k y => V2 (F.model k).G (weighted (F.model k) y))

/-- A deterministic symmetric, uniformly bounded matrix sequence has an O(n)
quadratic-form variance bound. Used as an explicit input to the limit kernel. -/
def WholeQuadraticVariance (F : Family)
    (M : ∀ k, Matrix (Fin (F.size k)) (Fin (F.size k)) ℝ) : Prop :=
  ∃ B : ℝ, 0 ≤ B ∧ ∃ k0 : ℕ, ∀ k ≥ k0,
    var (F.model k) (fun y => quadratic (M k) (centered (weighted (F.model k) y))) ≤
      B*(F.size k : ℝ)

/-- The rowwise quadratic-form probability expansion and its PSD-majorant consequence.
The variance input can be obtained from the already proved finite concentration bound. -/
def WholeQuadraticLimit : Prop :=
  ∀ (F : Family) (c1 c2 c3 c4 K : ℝ), WholeScaling F c1 c2 c3 c4 →
    ∀ M : ∀ k, Matrix (Fin (F.size k)) (Fin (F.size k)) ℝ,
    (∀ k i j, M k i j = M k j i) → (∀ k, operatorNorm (M k) ≤ K) →
    WholeQuadraticVariance F M →
    InProbability F
      (fun k y => (F.size k : ℝ)*varianceForm (M k) (weighted (F.model k) y)-scaledTrue F k)
      (fun k => (Matrix.trace ((M k-oracleMatrix (F.model k).G)*covariance (F.model k)) +
        quadratic (M k) (delta (F.model k)))/(F.size k : ℝ)) ∧
    ((∀ k, PSD (M k) ∧ PSD (M k-oracleMatrix (F.model k).G)) →
      (∀ k, 0 ≤ quadratic (M k) (delta (F.model k)) ∧
        0 ≤ Matrix.trace ((M k-oracleMatrix (F.model k).G)*covariance (F.model k))) ∧
      Conservative F (fun k y => varianceForm (M k) (weighted (F.model k) y)))

/-- P011-T6; replaces the known-graph use of (3.1), p. 2242 (PDF p. 5).
Spectral clipping is a PSD majorant with the degree norm bound, dominates both the
oracle estimate and zero, and is asymptotically conservative under Assumption 2.
It is the unique nearest PSD matrix in Frobenius norm, but is neither a least
Loewner majorant nor affine in the adjacency entries. The four-cycle spectrum,
quadratic identities, alternative majorant, exact expectation 4-12/n and limit 4
are included. -/
def T6WholeStatement : Prop :=
  PositivePartFinite ∧
  (∀ (F : Family) (c1 c2 c3 c4 : ℝ), WholeScaling F c1 c2 c3 c4 →
    Conservative F (fun k y => VPositive (F.model k).G (weighted (F.model k) y))) ∧
  PositivePartUnique ∧ PositivePartCycle ∧ PositivePartNonaffine ∧ CycleSpectrum ∧
  (∀ x : Fin 4 → ℝ, quadratic (positivePart (oracleMatrix cycleGraph)) x =
    quadratic (oracleMatrix cycleGraph) x+(x 0-x 1+x 2-x 3)^2/4 ∧
    quadratic (positivePart (oracleMatrix cycleGraph)) x =
      3/4*(x 0+x 1+x 2+x 3)^2+((x 0-x 2)^2+(x 1-x 3)^2)/2) ∧
  (∀ k, scaledTrue (cycleFamily (3/2)) k = 4) ∧ SpectralDifference

/-- A standardized row statistic. At a zero-variance early row the quotient is
zero by the field convention; the positive limiting variance makes such rows
irrelevant to the CLT. -/
def wholeStandardized {n : ℕ} (m : Model n) (y : Fin n → ℝ) : ℝ :=
  (betaHat m y-beta m)/Real.sqrt (var m (betaHat m))

/-- The dependency-graph CLT without nesting of the observed rows. -/
def WholeCLT : Prop :=
  ∀ (F : Family) (c1 c2 c3 c4 : ℝ), WholeScaling F c1 c2 c3 c4 →
    ∀ t : ℝ, Tendsto
      (fun k => probability (F.model k) {y | wholeStandardized (F.model k) y ≤ t})
      atTop (𝓝 (Phi t))

/-- The clipped Wald consequence of the CLT and one-sided variance control. -/
def WholeWald : Prop :=
  ∀ (F : Family) (c1 c2 c3 c4 : ℝ), WholeScaling F c1 c2 c3 c4 →
    ∀ V : ∀ k, (Fin (F.size k) → ℝ) → ℝ,
    (∀ k, Measurable (V k)) → Conservative F V → ConservativeCoverage F V

/-- The degree-only maximum is conservative with arbitrary valid supplied caps. -/
def WholeDegreeOnlyConservative : Prop :=
  ∀ (F : Family) (c1 c2 c3 c4 : ℝ), WholeScaling F c1 c2 c3 c4 →
    Valid F → (∀ k, (F.model k).R = emptyGraph (F.size k)) →
    ∀ A : ∀ k, (Fin (F.size k) → ℝ) → Graph (F.size k),
    (∀ k y, Maximizes (F.model k).R (F.model k).d
      (fun B => V1 B (weighted (F.model k) y)) (A k y)) →
    Conservative F (fun k y => V1 (A k y) (weighted (F.model k) y))

/-- For a nonconstant sign sample with complete degree caps, every maximizing
graph is exactly the positive-residual clique and the negative-residual clique. -/
def WholeSignOptimizer : Prop :=
  ∀ {n : ℕ}, 0 < n → ∀ y : Fin n → ℝ,
    (∀ i, y i = 1 ∨ y i = -1) → average y ≠ 1 → average y ≠ -1 →
    ∀ A : Graph n,
    Maximizes (emptyGraph n) (fun _ => n-1) (fun B => V1 B y) A →
    ∀ i j, A.val i j = true ↔ i ≠ j ∧ 0 < centered y i*centered y j

/-- P011-T7; Corollary 1, p. 2245 (PDF p. 8), and the degree-only case on p. 2248
(PDF p. 11).
The degree identity and both fixed-cap finite comparisons hold. Under Assumption 2,
the degree-only maximum is conservative and has conservative clipped Wald coverage,
even for unbounded supplied caps; residuals are bounded by 2c1 almost surely.
For independent fair signs with caps n-1, every nonconstant sample has exactly the
two residual-sign cliques as optimizer, while the exact estimates converge unscaled
to 1/2 and 1, respectively. -/
def T7WholeStatement : Prop :=
  DegreeOnlyIdentity ∧ DegreeOnlyBounds ∧
  (∀ (F : Family) (c1 c2 c3 c4 : ℝ), WholeScaling F c1 c2 c3 c4 →
    Valid F → (∀ k, (F.model k).R = emptyGraph (F.size k)) →
    ∀ A : ∀ k, (Fin (F.size k) → ℝ) → Graph (F.size k),
    (∀ k y, Maximizes (F.model k).R (F.model k).d
      (fun B => V1 B (weighted (F.model k) y)) (A k y)) →
    Conservative F (fun k y => V1 (A k y) (weighted (F.model k) y)) ∧
    ConservativeCoverage F (fun k y => V1 (A k y) (weighted (F.model k) y)) ∧
    (∀ k, ∀ᵐ y ∂(F.model k).law, maxAbs (centered (weighted (F.model k) y)) ≤ 2*c1)) ∧
  UnboundedDegreeGap ∧ SignWitnessFacts ∧ WholeSignOptimizer

/-- Nonnegativity of every estimator in branches (1) and (2) of T8's list. -/
def WholeCorrectedNonnegative : Prop :=
  ∀ {n : ℕ}, 0 < n → ∀ (R G : Graph n) (d : Fin n → ℕ), Compatible R d G →
    ∀ (x : Fin n → ℝ) (A : Graph n),
    Maximizes R d (fun B => V1plus d B x) A →
    0 ≤ V1plus d G x ∧ 0 ≤ V1plus d A x ∧ 0 ≤ VYoung d x ∧
    0 ≤ min (V1plus d A x) (VYoung d x) ∧ 0 ≤ VPositive G x

/-- P011-T8; Corollary 1, p. 2245 (PDF p. 8), and Corollary 3, p. 2248 (PDF p. 11);
the homoskedasticity sentence on p. 2246 (PDF p. 9) is deleted.
Under Assumption 2, every estimator in the corrected list has one-sided asymptotic
variance control and conservative clipped Wald coverage: the four corrected/Young
estimators under valid constraints, spectral clipping, the degree-only original
maximum, and the oracle or original maximum when the mean-bias limit inferior is
nonnegative. Equal unit means and disjoint clique graphs imply that condition.
The first two branches are nonnegative in every sample. The homoskedastic cycle
and path counterexamples show why no such conclusion holds for the unrestricted
original estimator with known edges. -/
def T8WholeStatement : Prop :=
  (∀ (F : Family) (c1 c2 c3 c4 : ℝ), WholeScaling F c1 c2 c3 c4 →
    ∀ V : ∀ k, (Fin (F.size k) → ℝ) → ℝ, CorrectedClass F V →
      Conservative F V ∧ ConservativeCoverage F V) ∧
  (∀ (F : Family) (c1 c2 c3 c4 : ℝ), WholeScaling F c1 c2 c3 c4 →
    ((∀ k i, expectation (F.model k) (fun y => weighted (F.model k) y i) = beta (F.model k)) ∨
      (∀ k, CliqueUnion (F.model k).G)) →
      0 ≤ Filter.liminf (fun k => meanBias (F.model k)) atTop) ∧
  WholeCorrectedNonnegative ∧ CycleCounterexample ∧ PathCounterexample

end
end SAP.P011a
