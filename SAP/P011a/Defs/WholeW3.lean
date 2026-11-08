import Mathlib
import SAP.P011a.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P011a

open MeasureTheory ProbabilityTheory Filter Finset
open scoped BigOperators Topology Classical Matrix NNReal ENNReal
noncomputable section

/-- Assumption 2 on the observed rows. The positive sizes tend to infinity by
`Family`; no embeddings between observed graphs or monotonicity of sizes are assumed.
The bounded weighted outcomes imply the existence of every moment used below. -/
def WholeScaling_W3 (F : Family) (c1 c2 c3 c4 : ℝ) : Prop :=
  0 < c1 ∧ 0 < c2 ∧ 0 < c3 ∧ 0 < c4 ∧
  (∀ k, Dependency (F.model k)) ∧
  (∀ k, ∀ᵐ y ∂(F.model k).law, ∀ i,
    |weighted (F.model k) y i - beta (F.model k)| ≤ c1) ∧
  (∀ k i, (degree (F.model k).G i : ℝ) ≤ c2) ∧
  Tendsto (fun k => (F.size k : ℝ) * var (F.model k) (betaHat (F.model k)))
    atTop (𝓝 c3) ∧ (∀ k i, |(F.model k).theta i| < c4)

/-- A covariance is admissible for a graph if it comes from a square-integrable
weighted outcome vector with that dependency graph. Using models loses no laws:
one may take every weight to be one. No bound on the means is imposed here. -/
def AdmissibleCovariance {n : ℕ} (G : Graph n)
    (C : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∃ m : Model n, m.G = G ∧ Dependency m ∧
    (∀ i, MemLp (fun y => weighted m y i) 2 m.law) ∧ covariance m = C

/-- T4(i): both exact expectation identities, with all moments supplied by
Assumption 2 rather than added as hypotheses. -/
def WholeQuadraticExpectation : Prop :=
  ∀ (F : Family) (c1 c2 c3 c4 : ℝ), WholeScaling_W3 F c1 c2 c3 c4 →
  ∀ k (M : Matrix (Fin (F.size k)) (Fin (F.size k)) ℝ),
  (∀ i j, M i j = M j i) →
  expectation (F.model k) (fun y => quadratic M (centered (weighted (F.model k) y))) =
      Matrix.trace (centeringMatrix (F.size k) * M * centeringMatrix (F.size k) *
        covariance (F.model k)) + quadratic M (delta (F.model k)) ∧
    expectation (F.model k) (fun y => quadratic M (centered (weighted (F.model k) y))) =
      Matrix.trace (M * covariance (F.model k)) + quadratic M (delta (F.model k)) -
      2 / (F.size k : ℝ) * (∑ i, ∑ j, (M * covariance (F.model k)) i j) +
      quadratic M (fun _ => 1) * var (F.model k) (betaHat (F.model k))

/-- T4(ii)--(iv): linear variance growth, F1, and the two PSD sufficient
conditions. The variance bound holds in every row, which in particular is O(n). -/
def WholeDeterministicExpansion : Prop :=
  ∀ (F : Family) (c1 c2 c3 c4 K : ℝ), WholeScaling_W3 F c1 c2 c3 c4 →
  ∀ (M : ∀ k, Matrix (Fin (F.size k)) (Fin (F.size k)) ℝ),
  (∀ k i j, M k i j = M k j i) → (∀ k, operatorNorm (M k) ≤ K) →
  (∃ B : ℝ, 0 ≤ B ∧ ∀ k,
      var (F.model k) (fun y => quadratic (M k) (centered (weighted (F.model k) y)))
        ≤ B * (F.size k : ℝ)) ∧
    InProbability F
      (fun k y => (F.size k : ℝ) * varianceForm (M k) (weighted (F.model k) y) - scaledTrue F k)
      (fun k => (Matrix.trace ((M k - oracleMatrix (F.model k).G) * covariance (F.model k)) +
        quadratic (M k) (delta (F.model k))) / (F.size k : ℝ)) ∧
    ((∀ k, PSD (M k) ∧ PSD (M k - oracleMatrix (F.model k).G)) →
      (∀ k, 0 ≤ quadratic (M k) (delta (F.model k)) ∧
        0 ≤ Matrix.trace ((M k - oracleMatrix (F.model k).G) * covariance (F.model k))) ∧
      Conservative F (fun k y => varianceForm (M k) (weighted (F.model k) y)))

/-- T4(iv), weaker condition: the actual covariance trace suffices. Consequently
nonnegative traces against every admissible covariance suffice. -/
def WholeTraceCriterion : Prop :=
  ∀ (F : Family) (c1 c2 c3 c4 K : ℝ), WholeScaling_W3 F c1 c2 c3 c4 →
  ∀ (M : ∀ k, Matrix (Fin (F.size k)) (Fin (F.size k)) ℝ),
  (∀ k i j, M k i j = M k j i) → (∀ k, operatorNorm (M k) ≤ K) →
  (∀ k, PSD (M k)) →
  ((∀ k, 0 ≤ Matrix.trace ((M k - oracleMatrix (F.model k).G) * covariance (F.model k))) →
    (∀ k, 0 ≤ quadratic (M k) (delta (F.model k))) ∧
      Conservative F (fun k y => varianceForm (M k) (weighted (F.model k) y))) ∧
  ((∀ k C, AdmissibleCovariance (F.model k).G C →
      0 ≤ Matrix.trace ((M k - oracleMatrix (F.model k).G) * C)) →
    (∀ k, 0 ≤ quadratic (M k) (delta (F.model k)) ∧
      0 ≤ Matrix.trace ((M k - oracleMatrix (F.model k).G) * covariance (F.model k))) ∧
      Conservative F (fun k y => varianceForm (M k) (weighted (F.model k) y)))

/-- T4(iv), support observation: for every admissible covariance only diagonal
and true-edge entries of a symmetric matrix enter its covariance trace. -/
def WholeTraceSupport : Prop :=
  ∀ {n : ℕ} (G : Graph n) (C : Matrix (Fin n) (Fin n) ℝ),
  AdmissibleCovariance G C → ∀ N : Matrix (Fin n) (Fin n) ℝ,
  (∀ i j, N i j = N j i) →
  Matrix.trace (N * C) = (∑ i, N i i * C i i) +
    2 * upperSum (fun i j => adjacency G i j * N i j * C i j)

/-- The random-matrix F1 residual for the explicit independent-sign experiment. -/
def signExpansionResidual (k : ℕ) (y : Fin (signFamily.size k) → ℝ) : ℝ :=
  (signFamily.size k : ℝ) * varianceForm (dataMatrix y) y - scaledTrue signFamily k -
    Matrix.trace (dataMatrix y - 1) / (signFamily.size k : ℝ)

/-- T4(v): the fair independent signs have C=I and zero means. The bracket is
exactly (1-n)/n almost surely and tends to -1; the F1 residual tends to 1 and
does not tend to zero. The norm and finite quadratic identity are stated in
`DataDependentFailure`. Independence is the full disjoint-set condition on the
empty graph, rather than merely pairwise independence. -/
def WholeSignFailure : Prop :=
  WholeScaling_W3 signFamily 1 1 1 2 ∧ Valid signFamily ∧
  (∀ k, scaledTrue signFamily k = 1 ∧ beta (signFamily.model k) = 0 ∧
    Dependency (signFamily.model k) ∧
    covariance (signFamily.model k) = 1 ∧ delta (signFamily.model k) = 0 ∧
    (∀ i, probability (signFamily.model k) {y | y i = 1} = 1/2 ∧
      probability (signFamily.model k) {y | y i = -1} = 1/2) ∧
    (∀ᵐ y ∂(signFamily.model k).law,
      Matrix.trace (dataMatrix y - 1) / (signFamily.size k : ℝ) =
        (1 - (signFamily.size k : ℝ)) / (signFamily.size k : ℝ))) ∧
  InProbability signFamily
    (fun k y => (signFamily.size k : ℝ) * varianceForm (dataMatrix y) y) (fun _ => 1) ∧
  InProbability signFamily
    (fun k y => (signFamily.size k : ℝ) * varianceForm (dataMatrix y) y - scaledTrue signFamily k)
    (fun _ => 0) ∧
  Tendsto (fun k => (1 - (signFamily.size k : ℝ)) / (signFamily.size k : ℝ))
    atTop (𝓝 (-1)) ∧
  InProbability signFamily signExpansionResidual (fun _ => 1) ∧
  ¬ InProbability signFamily signExpansionResidual (fun _ => 0)

/-- P011-T4; Replaces the argument of the proof of Proposition 1,
pp. 2242–2244 (PDF pp. 5–7); not printed in the paper.
For deterministic symmetric matrices with uniformly bounded spectral norm,
Assumption 2 gives both exact expectations, linear variance growth, and F1.
PSD majorants give conservativeness for arbitrary unit means; nonnegative traces
against admissible covariances suffice in place of the PSD difference condition,
and only diagonal and true-edge entries enter those traces. The oracle matrix
is PSD exactly for unions of cliques. Independent fair signs give the stated
bounded-norm data-dependent counterexample. No nesting of observed graphs or
monotonicity of observed sizes is required. -/
def T4WholeStatement : Prop :=
  WholeQuadraticExpectation ∧ WholeDeterministicExpansion ∧ WholeTraceCriterion ∧
    WholeTraceSupport ∧
    (∀ {n : ℕ} (G : Graph n), oracleMatrix G - (1 + adjacency G) = 0) ∧
    CliqueCharacterization ∧ DataDependentFailure ∧ WholeSignFailure

/-- T5 finite supplements: the exact diagonal difference, nonnegativity of the
Young bound, existence of maximizers, oracle domination, and the finite norm bound.
Together with the existing finite and optimum identities these include (a)--(g).
The attained edge objective is the optimal value w*, so no empty supremum occurs. -/
def WholeCorrectedFinite : Prop :=
  ∀ {n : ℕ}, 0 < n → ∀ (R G : Graph n) (d : Fin n → ℕ), Compatible R d G →
  (correctedMatrix d G - oracleMatrix G =
    Matrix.diagonal (fun i => degreeCorrection d i * degree G i)) ∧
  (∀ x : Fin n → ℝ,
    VYoung d x = varianceForm (1 + Matrix.diagonal (fun i => (truncatedDegree d i : ℝ))) x ∧
    0 ≤ VYoung d x ∧
    (∃ A : Graph n, Maximizes R d (fun B => V1plus d B x) A) ∧
    (∀ A : Graph n, Maximizes R d (fun B => V1plus d B x) A →
      V1plus d G x ≤ V1plus d A x)) ∧
  (∀ c2 : ℝ, 0 ≤ c2 → (∀ i, (degree G i : ℝ) ≤ c2) →
    operatorNorm (correctedMatrix d G) ≤ 1 + 2*c2)

/-- T5(b),(c),(h),(i) without observed nesting. Only true graph degrees are
uniformly bounded; supplied caps and the constant common cap may grow by row.
The maximizing graph can depend arbitrarily on the sample. -/
def WholeCorrectedAsymptotic : Prop :=
  ∀ (F : Family) (c1 c2 c3 c4 : ℝ), WholeScaling_W3 F c1 c2 c3 c4 → Valid F →
  ∀ (A : ∀ k, (Fin (F.size k) → ℝ) → Graph (F.size k)),
  (∀ k y, Maximizes (F.model k).R (F.model k).d
    (fun B => V1plus (F.model k).d B (weighted (F.model k) y)) (A k y)) →
  (∀ k, operatorNorm (correctedMatrix (F.model k).d (F.model k).G) ≤ 1+2*c2) ∧
  (∀ k y, V1plus (F.model k).d (F.model k).G (weighted (F.model k) y) ≤
    V1plus (F.model k).d (A k y) (weighted (F.model k) y)) ∧
  Conservative F (fun k y => V1plus (F.model k).d (F.model k).G (weighted (F.model k) y)) ∧
  Conservative F (fun k y => V1plus (F.model k).d (A k y) (weighted (F.model k) y)) ∧
  Conservative F (fun k y => VYoung (F.model k).d (weighted (F.model k) y)) ∧
  Conservative F (fun k y => min
    (V1plus (F.model k).d (A k y) (weighted (F.model k) y))
    (VYoung (F.model k).d (weighted (F.model k) y))) ∧
  ((∀ k, ∃ D : ℕ, ∀ i, truncatedDegree (F.model k).d i = D) →
    Conservative F (fun k y => V2prime (F.model k).d (weighted (F.model k) y)))

/-- P011-T5; Replaces Corollary 1, p. 2245 (PDF p. 8), and the use of (3.1)
in programs (3.5)–(3.6), pp. 2244–2245 (PDF pp. 7–8); not printed in the paper.
The degree-corrected estimator and Young bound satisfy all finite decompositions,
PSD and nonnegativity conclusions, norm and oracle bounds, affine edge-objective
and attained-optimum identities, and the constant-cap and regular-graph formulas,
including zero degree. Under Assumption 2 and valid constraints the corrected
oracle, sample maximizer, Young bound, and their stated minimum are conservative
for arbitrary unit means, with no uniform bound on supplied degree caps. Common
caps give the same conclusion for (3.9), without homoskedasticity. No nesting of
observed graphs or monotonicity of observed sizes is required. -/
def T5WholeStatement : Prop :=
  CorrectedFinite ∧ CorrectedMatrix ∧ CorrectedOptimal ∧
    WholeCorrectedFinite ∧ WholeCorrectedAsymptotic

end
end SAP.P011a
