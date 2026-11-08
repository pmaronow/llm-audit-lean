import Mathlib.Tactic
import Mathlib.Probability.Independence.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.CDF
import Mathlib.Probability.Moments.Variance
import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Data.Nat.Bits

/-!
P011: Confidence Intervals for Linear Unbiased Estimators under Constrained Dependence.
Published EJS 12 (2018), pp. 2238–2252. Target numbering is from targets.json.
All declarations with `sorry` are drafts, including false printed claims.
No named mathematical axioms are introduced. Finite certificates are separate
from the asymptotic claims they support.
-/
namespace AronowAudit.P011

open MeasureTheory ProbabilityTheory Filter Finset
open scoped BigOperators Topology Classical Matrix NNReal ENNReal
attribute [-simp] Finset.sum_boole
noncomputable section
set_option maxHeartbeats 800000
set_option maxRecDepth 2000

/-- Definition 1, p. 2240: "a simple graph ... with no parallel edges or self-loops".
The Boolean adjacency function is symmetric and has zero diagonal. -/
abbrev Graph (n : ℕ) := { a : Fin n → Fin n → Bool //
  (∀ i j, a i j = a j i) ∧ (∀ i, a i i = false) }

/-- Section 3, p. 2241: "binary symmetric zero-diagonal adjacency matrix". -/
def adjacency {n : ℕ} (A : Graph n) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => if A.val i j then 1 else 0

/-- Assumption 1, p. 2240: "the degrees d₁,...,dₙ"; degree within the observed graph. -/
def degree {n : ℕ} (A : Graph n) (i : Fin n) : ℕ :=
  ∑ j, if A.val i j then 1 else 0

/-- Definition 4, p. 2241: forced recruitment edges and row sums at most dᵢ.
The supplied d may also be a valid upper bound (Discussion, p. 2248). -/
def Compatible {n : ℕ} (R : Graph n) (d : Fin n → ℕ) (A : Graph n) : Prop :=
  (∀ i j, R.val i j = true → A.val i j = true) ∧ ∀ i, degree A i ≤ d i

/-- Definition 3, p. 2240: "β̂ = (1/n) ∑ θᵢYᵢ"; x denotes θY. -/
def average {n : ℕ} (x : Fin n → ℝ) : ℝ := (∑ i, x i) / n

/-- Equation (3.1), p. 2242: the residual θᵢYᵢ − β̂. -/
def centered {n : ℕ} (x : Fin n → ℝ) : Fin n → ℝ := fun i => x i - average x

/-- Equation (3.1), p. 2242: "σ̂²_θ = n⁻¹ ∑ (θᵢYᵢ − β̂)²". -/
def sampleVariance {n : ℕ} (x : Fin n → ℝ) : ℝ := (∑ i, centered x i ^ 2) / n

/-- Audit notation S9: xᵀMx, with double sums over ordered pairs. -/
def quadratic {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) : ℝ :=
  ∑ i, ∑ j, M i j * x i * x j

/-- Audit notation S9: S = I + A. -/
def oracleMatrix {n : ℕ} (A : Graph n) : Matrix (Fin n) (Fin n) ℝ :=
  1 + adjacency A

/-- Correction (F1): V̂_M = n⁻² eᵀMe, e = θY − β̂1. -/
def varianceForm {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) : ℝ :=
  quadratic M (centered x) / (n : ℝ)^2

/-- Equation (3.1), p. 2242: V̂₁(A;Z) = n⁻²[∑ eᵢ² + ∑ Aᵢⱼeᵢeⱼ]. -/
def V1 {n : ℕ} (A : Graph n) (x : Fin n → ℝ) : ℝ :=
  ((∑ i, centered x i ^ 2) + quadratic (adjacency A) (centered x)) / (n : ℝ)^2

/-- Equation (3.7), p. 2246: V̂₂ = σ̂²_θ/n [1 + n⁻¹∑ᵢⱼ Aᵢⱼ]. -/
def V2 {n : ℕ} (A : Graph n) (x : Fin n → ℝ) : ℝ :=
  sampleVariance x / n * (1 + (∑ i, ∑ j, adjacency A i j) / n)

/-- Equation (3.9), pp. 2246–2247: "dᵢ′ = min{dᵢ,n−1}". -/
def truncatedDegree {n : ℕ} (d : Fin n → ℕ) (i : Fin n) : ℕ := min (d i) (n-1)

/-- Equation (3.9), p. 2247: V̂₂′ uses ∑ᵢdᵢ′ in place of ∑ᵢⱼAᵢⱼ. -/
def V2prime {n : ℕ} (d : Fin n → ℕ) (x : Fin n → ℝ) : ℝ :=
  sampleVariance x / n * (1 + (∑ i, (truncatedDegree d i : ℝ)) / n)

/-- Correction F2: tᵢ = 1 − 1/dᵢ′ for dᵢ′ > 0, and 0 at dᵢ′ = 0. -/
def degreeCorrection {n : ℕ} (d : Fin n → ℕ) (i : Fin n) : ℝ :=
  if truncatedDegree d i = 0 then 0 else 1 - 1 / (truncatedDegree d i : ℝ)

/-- Correction F2: M_A = I + A + diag(tᵢ dᵢᴬ). -/
def correctedMatrix {n : ℕ} (d : Fin n → ℕ) (A : Graph n) : Matrix (Fin n) (Fin n) ℝ :=
  oracleMatrix A + Matrix.diagonal (fun i => degreeCorrection d i * degree A i)

/-- Correction F2: V̂₁⁺ adds n⁻²∑tᵢdᵢᴬeᵢ² to (3.1). -/
def V1plus {n : ℕ} (d : Fin n → ℕ) (A : Graph n) (x : Fin n → ℝ) : ℝ :=
  V1 A x + (∑ i, degreeCorrection d i * degree A i * centered x i ^ 2) / (n : ℝ)^2

/-- Correction F3: V̂_Y′ = n⁻²∑(1+dᵢ′)eᵢ²; no homoskedasticity assumption. -/
def VYoung {n : ℕ} (d : Fin n → ℕ) (x : Fin n → ℝ) : ℝ :=
  (∑ i, (1 + (truncatedDegree d i : ℝ)) * centered x i ^ 2) / (n : ℝ)^2

/-- Definition 6, p. 2241: "V̂(A;Z) is maximized" over compatible A. -/
def Maximizes {n : ℕ} (R : Graph n) (d : Fin n → ℕ) (f : Graph n → ℝ)
    (A : Graph n) : Prop := Compatible R d A ∧ ∀ B, Compatible R d B → f B ≤ f A

/-- The observed part of the setting of Section 2 (pp. 2240–2241).
The law is the full joint law of raw outcomes on ℝⁿ, with probability mass 1.
G is the induced true graph; R and d are deterministic observed constraints.
Unobserved vertices enter these results only through the valid degree bounds. -/
structure Model (n : ℕ) where
  law : Measure (Fin n → ℝ)
  probability : IsProbabilityMeasure law
  theta : Fin n → ℝ
  G : Graph n
  R : Graph n
  d : Fin n → ℕ

/-- S9: "Xᵢ = θᵢYᵢ", with nonrandom coefficients from Assumption 1. -/
def weighted {n : ℕ} (m : Model n) (y : Fin n → ℝ) : Fin n → ℝ := fun i => m.theta i * y i

/-- Definition 3, p. 2240: the random linear estimator. -/
def betaHat {n : ℕ} (m : Model n) (y : Fin n → ℝ) : ℝ := average (weighted m y)

/-- S10(a): expectation with respect to the joint outcome law. -/
def expectation {n : ℕ} (m : Model n) (f : (Fin n → ℝ) → ℝ) : ℝ := ∫ y, f y ∂m.law

/-- Definition 3, p. 2240: "E[β̂] = β". The target may depend on n. -/
def beta {n : ℕ} (m : Model n) : ℝ := expectation m (betaHat m)

/-- Variance in Section 2, p. 2241, represented by E[(f−Ef)²].
All uses in bounded models have finite second moments. -/
def var {n : ℕ} (m : Model n) (f : (Fin n → ℝ) → ℝ) : ℝ :=
  expectation m (fun y => (f y - expectation m f)^2)

/-- S9: C is the covariance matrix of the weighted outcomes. -/
def covariance {n : ℕ} (m : Model n) : Matrix (Fin n) (Fin n) ℝ := fun i j =>
  expectation m (fun y =>
    (weighted m y i - expectation m (fun z => weighted m z i)) *
    (weighted m y j - expectation m (fun z => weighted m z j)))

/-- S9: "δᵢ = E[Xᵢ] − β"; unbiasedness only forces their sum to be zero. -/
def delta {n : ℕ} (m : Model n) : Fin n → ℝ :=
  fun i => expectation m (fun y => weighted m y i) - beta m

/-- The missing mean term in revised Proposition 1: bₙ = δᵀ(I+Aᴼ)δ/n. -/
def meanBias {n : ℕ} (m : Model n) : ℝ := quadratic (oracleMatrix m.G) (delta m) / n

/-- Between-unit mean variance Mₙ used in the repaired proof of Proposition 2. -/
def meanSpread {n : ℕ} (m : Model n) : ℝ := (∑ i, delta m i ^ 2) / n

/-- Definition 1, p. 2240: "for all disjoint sets ... with no edge ...
the set {Yᵢ} is independent from the set {Yⱼ}". This is vector independence,
not merely the vanishing of pairwise covariances. -/
def VariableDependency {Ω : Type} [MeasurableSpace Ω] {n : ℕ}
    (law : Measure Ω) (G : Graph n) (X : Fin n → Ω → ℝ) : Prop :=
  ∀ S T : Finset (Fin n), Disjoint S T →
    (∀ i ∈ S, ∀ j ∈ T, G.val i j = false) →
    IndepFun (fun y => fun i : {i // i ∈ S} => X i.val y)
      (fun y => fun j : {j // j ∈ T} => X j.val y) law

/-- Definition 1 for the raw outcome coordinates of the model (p. 2240). -/
def Dependency {n : ℕ} (m : Model n) : Prop :=
  VariableDependency m.law m.G (fun i y => y i)

/-- Assumption 3 corrected to the observed index set (p. 2246; T24). -/
def Homoskedastic {n : ℕ} (m : Model n) : Prop :=
  ∀ i j, covariance m i i = covariance m j j

/-- Sequences of observed populations in Assumption 2, p. 2242.
The sample size grows to infinity; this allows the block subsequences n=4m or 3m.
Nestedness of the induced true graphs is stated separately below. -/
structure Family where
  size : ℕ → ℕ
  positive : ∀ k, 0 < size k
  grows : Tendsto size atTop atTop
  model : ∀ k, Model (size k)

/-- Assumption 2's "nested graphs ... and observed data": observed vertices
embed and the induced true graphs are nested. Each n has its own joint law
(S10(a)); projective equality of the laws is not an added hypothesis. In
particular the triangular-array example T9(d) changes its raw outcomes with n. -/
def Nested (F : Family) : Prop := Monotone F.size ∧ ∀ k,
  ∃ e : Fin (F.size k) ↪ Fin (F.size (k+1)),
    ∀ i j, (F.model k).G.val i j = (F.model (k+1)).G.val (e i) (e j)

/-- Assumption 2, p. 2242: bounded weighted outcomes about β, bounded true
observed degree, n Var(β̂) → c₃ > 0, and |θᵢ| < c₄, with fixed positive constants. -/
def Scaling (F : Family) (c1 c2 c3 c4 : ℝ) : Prop :=
  Nested F ∧ 0 < c1 ∧ 0 < c2 ∧ 0 < c3 ∧ 0 < c4 ∧
  (∀ k, Dependency (F.model k)) ∧
  (∀ k, ∀ᵐ y ∂(F.model k).law, ∀ i,
    |weighted (F.model k) y i - beta (F.model k)| ≤ c1) ∧
  (∀ k i, (degree (F.model k).G i : ℝ) ≤ c2) ∧
  Tendsto (fun k => (F.size k : ℝ) * var (F.model k) (betaHat (F.model k)))
    atTop (𝓝 c3) ∧ (∀ k i, |(F.model k).theta i| < c4)

/-- S10(h): recruitment edges and supplied degree constraints are valid. -/
def Valid (F : Family) : Prop := ∀ k, Compatible (F.model k).R (F.model k).d (F.model k).G

/-- S10(a),(c): event probability under the joint law, as a real number. -/
def probability {n : ℕ} (m : Model n) (E : Set (Fin n → ℝ)) : ℝ := m.law.real E

/-- Convergence in probability, with a possibly varying deterministic centre. -/
def InProbability (F : Family) (T : ∀ k, (Fin (F.size k) → ℝ) → ℝ) (a : ℕ → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → Tendsto
    (fun k => probability (F.model k) {y | |T k y - a k| > ε}) atTop (𝓝 0)

/-- The n-scaled one-sided conservativeness of Corollaries 1 and 2. -/
def Conservative (F : Family) (V : ∀ k, (Fin (F.size k) → ℝ) → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → Tendsto
    (fun k => probability (F.model k) {y |
      (F.size k : ℝ) * (var (F.model k) (betaHat (F.model k)) - V k y) > ε})
    atTop (𝓝 0)

/-- Standard normal cdf Φ, Section 4, pp. 2247–2248. -/
def Phi (t : ℝ) : ℝ := ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1) t

/-- z_{1−α/2} = Φ⁻¹(1−α/2), Section 4; generalized inverse of the normal cdf. -/
def normalQuantile (α : ℝ) : ℝ := sInf {t : ℝ | 1 - α / 2 ≤ Phi t}

/-- Corrected S10(d) and T39: coverage of the well-defined clipped interval
β̂ ± z sqrt(max(V,0)). Printed V1 intervals use printedCoverage instead. -/
def coverage {n : ℕ} (m : Model n) (V : (Fin n → ℝ) → ℝ) (α : ℝ) : ℝ :=
  probability m {y | |betaHat m y - beta m| ≤ normalQuantile α * Real.sqrt (max (V y) 0)}

/-- Corrected S10(d) and conditional Proposition 3: "at least ... coverage ...
in large n", pp. 2247–2248, as liminf coverage of the clipped interval. -/
def ConservativeCoverage (F : Family) (V : ∀ k, (Fin (F.size k) → ℝ) → ℝ) : Prop :=
  ∀ α : ℝ, 0 < α → α < 1 →
    1 - α ≤ Filter.liminf (fun k => coverage (F.model k) (V k) α) atTop

/-- Corollary 3, p. 2248: "confidence intervals formed as" β̂ ± z sqrt(V1).
The printed interval is partial: it is defined only when V≥0. This event counts
undefined negative-estimate realizations as uncovered, rather than substituting
the corrected clipped interval or assuming that such realizations cannot occur. -/
def printedCoverage {n : ℕ} (m : Model n) (V : (Fin n → ℝ) → ℝ) (α : ℝ) : ℝ :=
  probability m {y | 0 ≤ V y ∧ |betaHat m y-beta m| ≤ normalQuantile α*Real.sqrt (V y)}

/-- Corollary 3, p. 2248: "at least ... coverage ... in large n", for the
printed interval whenever defined; undefined realizations are uncovered. -/
def PrintedConservativeCoverage (F : Family) (V : ∀ k, (Fin (F.size k) → ℝ) → ℝ) : Prop :=
  ∀ α : ℝ, 0 < α → α < 1 →
    1-α ≤ Filter.liminf (fun k => printedCoverage (F.model k) (V k) α) atTop

/-- Matrix positivity in the real setting: symmetric and nonnegative quadratic form.
This is the positive semidefinite condition used in corrections F1–F4. -/
def PSD {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  (∀ i j, M i j = M j i) ∧ ∀ x, 0 ≤ quadratic M x

/-- Euclidean vector norm in the residual correction. -/
def l2 {n : ℕ} (x : Fin n → ℝ) : ℝ := Real.sqrt (∑ i, x i ^ 2)

/-- Spectral operator norm, not the entrywise matrix norm, in correction F1. -/
def operatorNorm {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  ‖(Matrix.toEuclideanLin M).toContinuousLinearMap‖

/-- Correction F4: clip the eigenvalues of a symmetric matrix at zero.
Mathlib supplies the orthonormal eigenbasis. The zero fallback is used only
for nonsymmetric matrices, which are excluded in every F4 statement. -/
def positivePart {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  if h : M.IsHermitian then
    (h.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ) *
      Matrix.diagonal (fun i => max (h.eigenvalues i) 0) *
      (h.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ)ᵀ
  else 0

/-- Corrected known-graph estimator F4. -/
def VPositive {n : ℕ} (A : Graph n) (x : Fin n → ℝ) : ℝ :=
  varianceForm (positivePart (oracleMatrix A)) x

/- Revised Proposition 1, T3(i), p. 2242, with the previously omitted mean term.
This draft asserts the complete moving-target convergence under Assumption 2. -/
/- The unchanged revised_oracle_convergence contract is proved in P011_OracleCompletion.lean. -/


/-- A simple graph with no edges (used in T10, T11, T20 and T26). -/
def emptyGraph (n : ℕ) : Graph n := ⟨fun _ _ => false, by simp⟩

/-- T1: the printed correction's four-cycle 1–2–3–4–1. -/
def cycleGraph : Graph 4 :=
  ⟨![![false,true,false,true], ![true,false,true,false],
      ![false,true,false,true], ![true,false,true,false]], by
    constructor
    · intro i j; fin_cases i <;> fin_cases j <;> decide
    · intro i; fin_cases i <;> decide⟩

/-- T2 and T21: the path 1–2–3, with degrees (1,2,1). -/
def pathGraph : Graph 3 :=
  ⟨![![false,true,false], ![true,false,true], ![false,true,false]], by
    constructor
    · intro i j; fin_cases i <;> fin_cases j <;> decide
    · intro i; fin_cases i <;> decide⟩

/-- T15: the forced recruitment star with its centre in position 1. -/
def starGraph : Graph 4 :=
  ⟨![![false,true,true,true], ![true,false,false,false],
      ![true,false,false,false], ![true,false,false,false]], by
    constructor
    · intro i j; fin_cases i <;> fin_cases j <;> decide
    · intro i; fin_cases i <;> decide⟩

/-- Index a vertex by its position in a block, using 0-based Fin indices. -/
def localIndex {q blocks : ℕ} (hq : 0 < q) (i : Fin (q*blocks)) : Fin q :=
  ⟨i.val % q, Nat.mod_lt _ hq⟩

/-- Index the block containing a vertex. -/
def blockIndex {q blocks : ℕ} (hq : 0 < q) (i : Fin (q*blocks)) : Fin blocks :=
  ⟨i.val / q, (Nat.div_lt_iff_lt_mul hq).mpr (by simpa [Nat.mul_comm] using i.isLt)⟩

/-- T1, T2 and T15: independent blocks, with no edges between different blocks. -/
def blockGraph {q : ℕ} (hq : 0 < q) (A : Graph q) (blocks : ℕ) : Graph (q*blocks) :=
  ⟨fun i j => decide (i.val / q = j.val / q) && A.val (localIndex hq i) (localIndex hq j), by
    constructor
    · intro i j
      dsimp only
      rw [A.property.1 (localIndex hq i) (localIndex hq j)]
      simp only [eq_comm]
    · intro i
      simp [A.property.2]⟩

/-- T1,T2,T11,T20: a fair sign equals −1 or +1 with probability 1/2. -/
def sign (b : Bool) : ℝ := if b then 1 else -1

/-- Exact uniform finite law, pushed forward to the raw outcome vector.
The PMF has total mass one; it is never the zero measure. -/
def uniformLaw {Ω : Type} [Fintype Ω] [Nonempty Ω] {n : ℕ}
    (f : Ω → (Fin n → ℝ)) : Measure (Fin n → ℝ) :=
  ((PMF.uniformOfFintype Ω).map f).toMeasure

/-- T1: one cycle's outcomes a(1,−1,1,−1) + HU, as specified in the target. -/
def cycleBlock (a : ℝ) (u : Fin 4 → ℝ) : Fin 4 → ℝ :=
  ![a + u 0 + u 3, -a + u 0 + u 1, a + u 1 + u 2, -a + u 2 + u 3]

/-- T1: n=4m; coefficients 1, all true edges forced, degrees 2. -/
def cycleModel (a : ℝ) (blocks : ℕ) : Model (4*blocks) where
  law := uniformLaw (fun u : Fin blocks → Fin 4 → Bool => fun i =>
    cycleBlock a (fun r => sign (u (blockIndex (by decide) i) r)) (localIndex (by decide) i))
  probability := by dsimp [uniformLaw]; infer_instance
  theta := fun _ => 1
  G := blockGraph (by decide) cycleGraph blocks
  R := blockGraph (by decide) cycleGraph blocks
  d := fun _ => 2

/-- T1: appending cycles gives sample sizes 4,8,12,...; limits are along m→∞. -/
def cycleFamily (a : ℝ) : Family where
  size := fun k => 4*(k+1)
  positive := by intro k; omega
  grows := Filter.tendsto_atTop_mono (fun k => by change k ≤ _; omega) Filter.tendsto_id
  model := fun k => cycleModel a (k+1)

/-- T2: one path block (t+U, −2t+3U/5+4V/5, t+V). -/
def pathBlock (t U V : ℝ) : Fin 3 → ℝ := ![t+U, -2*t+3/5*U+4/5*V, t+V]

/-- T2: independent path blocks, all edges forced, degrees (1,2,1). -/
def pathModel (t : ℝ) (blocks : ℕ) : Model (3*blocks) where
  law := uniformLaw (fun u : Fin blocks → Fin 2 → Bool => fun i =>
    pathBlock t (sign (u (blockIndex (by decide) i) 0))
      (sign (u (blockIndex (by decide) i) 1)) (localIndex (by decide) i))
  probability := by dsimp [uniformLaw]; infer_instance
  theta := fun _ => 1
  G := blockGraph (by decide) pathGraph blocks
  R := blockGraph (by decide) pathGraph blocks
  d := fun i => degree pathGraph (localIndex (by decide) i)

/-- T2: appending path blocks, n=3K. -/
def pathFamily (t : ℝ) : Family where
  size := fun k => 3*(k+1)
  positive := by intro k; omega
  grows := Filter.tendsto_atTop_mono (fun k => by change k ≤ _; omega) Filter.tendsto_id
  model := fun k => pathModel t (k+1)

/-- T20: iid fair signs, θ=1, no dependency or recruitment edges, degrees zero. -/
def signModel (n : ℕ) : Model n where
  law := uniformLaw (fun u : Fin n → Bool => fun i => sign (u i))
  probability := by dsimp [uniformLaw]; infer_instance
  theta := fun _ => 1
  G := emptyGraph n
  R := emptyGraph n
  d := fun _ => 0

/-- T20: the complete positive-integer sample-size sequence. -/
def signFamily : Family where
  size := fun k => k+1
  positive := by intro k; omega
  grows := Filter.tendsto_atTop_mono (fun k => Nat.le_succ k) Filter.tendsto_id
  model := fun k => signModel (k+1)

/-- T11: tₙ=n/(2⌈n/2⌉), with raw means 2,0,2,0,... and β=1. -/
def alternatingWeight (n : ℕ) : ℝ := (n : ℝ) / (2 * (((n+1)/2 : ℕ) : ℝ))

/-- T11: Y_i = μ_i+ε_i, with μ_i=2 at odd printed indices and 0 otherwise. -/
def alternatingOutcome (n : ℕ) (u : Fin n → Bool) : Fin n → ℝ :=
  fun i => (if i.val % 2 = 0 then 2 else 0) + sign (u i)

/-- T11: raw outcomes μᵢ+εᵢ are nested; deterministic weights depend on n. -/
def alternatingModel (n : ℕ) : Model n where
  law := uniformLaw (alternatingOutcome n)
  probability := by dsimp [uniformLaw]; infer_instance
  theta := fun _ => alternatingWeight n
  G := emptyGraph n
  R := emptyGraph n
  d := fun _ => 0

/-- T11: the full sequence including odd sample sizes. -/
def alternatingFamily : Family where
  size := fun k => k+1
  positive := by intro k; omega
  grows := Filter.tendsto_atTop_mono (fun k => Nat.le_succ k) Filter.tendsto_id
  model := fun k => alternatingModel (k+1)

/-- T15: independent leaf Bernoulli probabilities, 1/4 each in the primary
model, and (3/4,1/4,1/2) in the comparison model. -/
def starLeaves (upper : Bool) (u : Fin 3 → Fin 4) : Fin 3 → ℝ :=
  fun j => if (u j).val < (if upper then (![3,1,2] : Fin 3 → ℕ) j else 1) then 1 else 0

/-- T15: centre probability 3/4+(∑(L−1/4))/12, or
1/2+(∑(L−EL))/12 in the comparison model. An independent uniform draw
on 48 values realizes these probabilities exactly (no rounding). -/
def starBlock (upper : Bool) (u : Fin 3 → Fin 4) (v : Fin 48) : Fin 4 → ℝ :=
  let count : ℕ := ∑ j, if starLeaves upper u j = 1 then 1 else 0
  ![if v.val < (if upper then 18 else 33) + 4*count then 1 else 0,
    starLeaves upper u 0, starLeaves upper u 1, starLeaves upper u 2]

/-- T15: binary outcomes on saturated recruitment stars, θ=1. -/
def starModel (upper : Bool) (blocks : ℕ) : Model (4*blocks) where
  law := uniformLaw (fun u : Fin blocks → ((Fin 3 → Fin 4) × Fin 48) => fun i =>
    starBlock upper (u (blockIndex (by decide) i)).1
      (u (blockIndex (by decide) i)).2 (localIndex (by decide) i))
  probability := by dsimp [uniformLaw]; infer_instance
  theta := fun _ => 1
  G := blockGraph (by decide) starGraph blocks
  R := blockGraph (by decide) starGraph blocks
  d := fun i => degree starGraph (localIndex (by decide) i)

/-- T15: growing nested saturated stars. -/
def starFamily (upper : Bool) : Family where
  size := fun k => 4*(k+1)
  positive := by intro k; omega
  grows := Filter.tendsto_atTop_mono (fun k => by change k ≤ _; omega) Filter.tendsto_id
  model := fun k => starModel upper (k+1)

/-- The scaled true variance n Var(β̂), common notation in all limit statements. -/
def scaledTrue (F : Family) (k : ℕ) : ℝ := (F.size k : ℝ) * var (F.model k) (betaHat (F.model k))

/-- The scaled oracle estimate n V̂₁(Aᴼ;Z). -/
def scaledOracle (F : Family) (k : ℕ) (y : Fin (F.size k) → ℝ) : ℝ :=
  (F.size k : ℝ) * V1 (F.model k).G (weighted (F.model k) y)

/-- T1(a)–(g): the complete concrete four-cycle counterexample, including every
standing hypothesis, singleton compatibility, exact moments, failure probabilities,
coverage loss, and the a=3 negative-estimate variant. Not claimed proved. -/
theorem cycle_counterexample :
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
    V1 cycleGraph (![5,-1,5,-1] : Fin 4 → ℝ) = -9/4 := by
  sorry

/-- T2(a)–(g): concrete path counterexample for t=1,2, including Assumptions 2,3,
single compatible graph, exact expectation, limiting underestimate or negativity,
and limiting undercoverage. Its regression representation is stated in path_ols below. -/
theorem path_counterexample (t : ℝ) (ht : t = 1 ∨ t = 2) :
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
          atTop (𝓝 0))) := by
  sorry

/-- T11(a)–(f): the alternating-means counterexample to both readings of the
auxiliary consistency step, with positive-integer sample sizes including odd n.
The finite residual moments are separately stated below. -/
theorem alternating_counterexample :
    Scaling alternatingFamily 2 1 1 2 ∧ Valid alternatingFamily ∧
    (∀ k, Homoskedastic (alternatingFamily.model k) ∧ beta (alternatingFamily.model k) = 1 ∧
      scaledTrue alternatingFamily k = alternatingWeight (k+1)^2) ∧
    InProbability alternatingFamily
      (fun k y => (k+1 : ℝ)*V2 (alternatingFamily.model k).G (weighted (alternatingFamily.model k) y)
        - scaledTrue alternatingFamily k) (fun _ => 1) ∧
    Tendsto (fun k => probability (alternatingFamily.model k)
      {y | |(k+1 : ℝ)*V2 (alternatingFamily.model k).G (weighted (alternatingFamily.model k) y)
        - scaledTrue alternatingFamily k| > 1/2}) atTop (𝓝 1) ∧
    Tendsto (fun k => probability (alternatingFamily.model k)
      {y | |(k+1 : ℝ)*V2 (alternatingFamily.model k).G (weighted (alternatingFamily.model k) y)
        - scaledTrue alternatingFamily k| < 3/2}) atTop (𝓝 1) ∧
    Conservative alternatingFamily
      (fun k y => V2 (alternatingFamily.model k).G (weighted (alternatingFamily.model k) y)) := by
  sorry

/-- T15(a)–(f): saturated-star OLS intercept counterexample. The joint law is
the exact conditional Bernoulli law in the target, realized by finite uniform draws.
The comparison law shows the bias may also be positive. -/
theorem star_counterexample :
    Scaling (starFamily false) 1 3 (27/128) 2 ∧ Valid (starFamily false) ∧
    (∀ k, Homoskedastic ((starFamily false).model k) ∧
      (∀ᵐ y ∂((starFamily false).model k).law, ∀ i, y i=0 ∨ y i=1) ∧
      (∀ i, expectation ((starFamily false).model k) (fun y => y i) =
        (![3/4,1/4,1/4,1/4] : Fin 4 → ℝ) (localIndex (by decide) i)) ∧
      (∀ i j, covariance ((starFamily false).model k) i j =
        ((3/16 : ℝ) • (1 : Matrix (Fin ((starFamily false).size k))
          (Fin ((starFamily false).size k)) ℝ) + (1/64 : ℝ) • adjacency ((starFamily false).model k).G) i j)) ∧
    (∀ k, beta ((starFamily false).model k) = 3/8 ∧ scaledTrue (starFamily false) k = 27/128 ∧
      meanBias ((starFamily false).model k) = -3/128 ∧
      (∀ A, Compatible ((starFamily false).model k).R ((starFamily false).model k).d A
        ↔ A = ((starFamily false).model k).G) ∧
      expectation ((starFamily false).model k) (scaledOracle (starFamily false) k) =
        3*(64*((k+1 : ℕ) : ℝ)-47)/(1024*((k+1 : ℕ) : ℝ))) ∧
    InProbability (starFamily false) (scaledOracle (starFamily false)) (fun _ => 3/16) ∧
    Tendsto (fun k => probability ((starFamily false).model k)
      {y | 27/128 - scaledOracle (starFamily false) k y > 3/256}) atTop (𝓝 1) ∧
    (∀ α : ℝ, 0 < α → α < 1 →
      Tendsto (fun k => coverage ((starFamily false).model k)
        (fun y => V1 ((starFamily false).model k).G (weighted ((starFamily false).model k) y)) α)
        atTop (𝓝 (2*Phi (normalQuantile α * Real.sqrt (8/9)) - 1)) ∧
      2*Phi (normalQuantile α * Real.sqrt (8/9)) - 1 < 1-α) ∧
    Scaling (starFamily true) 1 3 (47/192) 2 ∧ Valid (starFamily true) ∧
    (∀ k, beta ((starFamily true).model k) = 1/2 ∧ scaledTrue (starFamily true) k = 47/192) ∧
    InProbability (starFamily true) (scaledOracle (starFamily true)) (fun _ => 53/192) ∧
    (∀ upper : Bool,
      InProbability (starFamily upper)
        (fun k y => quadratic (oracleMatrix ((starFamily upper).model k).G)
          (fun i => y i - (if upper then (![1/2,3/4,1/4,1/2] : Fin 4 → ℝ)
            (localIndex (by decide) i) else (![3/4,1/4,1/4,1/4] : Fin 4 → ℝ)
            (localIndex (by decide) i))) / ((starFamily upper).size k : ℝ))
        (fun _ => if upper then 47/192 else 27/128)) := by
  sorry

/- T20(a)–(c): iid fair signs refute the printed '< ε ... → 0' display.
Every standing hypothesis holds; the displayed probability actually tends to one. -/
/- The unchanged printed_sign_counterexample contract is proved in P011_SignCompletion.lean. -/


/-- Audit notation: population-average marginal variance (not sample variance). -/
def meanVariance {n : ℕ} (m : Model n) : ℝ := (∑ i, covariance m i i) / n

/- T3(ii): the explicit O(1/n) expectation bound replacing the printed
"asymptotic unbiasedness" step, with the mean term retained. -/
/- The unchanged revised_oracle_expectation contract is proved in P011_ExpectationCompletion.lean. -/

/- T3(iii): the plug-in sample variance concentrates about average marginal
variance plus the between-unit mean variance, not about marginal variance alone. -/
/- The unchanged revised_sample_variance contract is proved in P011_SampleCompletion.lean. -/

/- T3(iv),(v): consistency iff bₙ→0; one-sided conservativeness of the oracle
iff liminf bₙ≥0. Neither equivalence is asserted for the data-selected maximum. -/
/- The unchanged oracle_mean_conditions contract is proved in P011_MeanCompletion.lean. -/

/-- T3(vi): "a disjoint union of cliques" means that equality-or-adjacency is
transitive; it is already reflexive and symmetric. Singleton cliques are included. -/
def CliqueUnion {n : ℕ} (A : Graph n) : Prop :=
  ∀ i j k, (i=j ∨ A.val i j = true) → (j=k ∨ A.val j k = true) →
    i=k ∨ A.val i k = true

/- T3(vi): The unchanged clique_characterization statement is proved in
P011_FiniteCompletion.lean, including the within-clique sum-of-squares identity. -/

/-- Correction F1: P = I − 11ᵀ/n is the sample-centering projection. -/
def centeringMatrix (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  1 - (1/(n : ℝ)) • (fun _ _ => 1)

/- T4(i): The unchanged quadratic_expectation contract is proved in
P011_QuadraticCompletion.lean from weighted L2 moments, covariance bilinearity
and finite centering/trace identities. -/

/- T4(ii)–(iv): the unchanged deterministic_quadratic_expansion contract is proved
in P011_DenseVarianceCompletion.lean, including the actual dense variance bound. -/

/-- T4(v): the sample-dependent rank-one matrix XXᵀ/n of iid signs. -/
def dataMatrix {n : ℕ} (x : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => x i*x j/n

/- T4(v): bounded norm does not permit substitution of a data-dependent matrix
into F1. The stochastic difference tends to 0, while its alleged bracket tends to −1. -/
/- The unchanged data_dependent_expansion_failure contract is proved in P011_DataMatrixCompletion.lean. -/

/-- Ordered representation of an unordered-edge sum, each edge counted once. -/
def upperSum {n : ℕ} (f : Fin n → Fin n → ℝ) : ℝ := ∑ i, ∑ j with i < j, f i j

/-- Maximum absolute entry, including the harmless empty-vector convention 0. -/
def maxAbs {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  (Finset.univ.sup (fun i => (⟨|x i|, abs_nonneg (x i)⟩ : ℝ≥0)) : ℝ≥0)


/- T5(b),(c),(h),(i): Assumption 2 and valid constraints suffice even when
supplied degree bounds grow. All four repaired estimators are nonnegative and
n-scaled conservative; constant degree caps make V̂_Y′ equal the paper's V̂₂′. -/
/- The unchanged corrected_asymptotic contract is proved in P011_CorrectedAsymptoticCompletion.lean. -/

/-- Frobenius squared norm used only for the nearest-PSD statement in T6. -/
def frobeniusSq {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) : ℝ := ∑ i, ∑ j, M i j^2

/- T6(a)–(c): the positive part is a PSD majorant of I+A, bounded in spectral
norm, and nearest in Frobenius norm; this does not assert a least Loewner majorant. -/
/- The unchanged positive_part_finite contract is proved in P011_SpectralCompletion.lean. -/

/- T6(b): known-graph spectral clipping is n-scaled conservative under exactly
Assumption 2, without a condition on the unit means. -/
/- The unchanged positive_part_conservative contract is proved in P011_SpectralCompletion.lean. -/

/-- T6(d): cycle positive-part quadratic identity, exact for every real vector.
The right side is a sum of squares, exposing the finite positivity argument. -/
theorem cycle_positive_identity (x : Fin 4 → ℝ) :
    quadratic (oracleMatrix cycleGraph) x + (x 0-x 1+x 2-x 3)^2/4 =
      3/4*(x 0+x 1+x 2+x 3)^2 + ((x 0-x 2)^2+(x 1-x 3)^2)/2 := by
  norm_num [quadratic, oracleMatrix, adjacency, cycleGraph, Fin.sum_univ_succ,
    Matrix.add_apply, Matrix.of_apply, Pi.add_apply, Pi.sub_apply, Matrix.one_apply]
  <;> ring

/-- T6(c): the exact alternative majorant specified by the correction. -/
def cycleMajorantDifference : Matrix (Fin 4) (Fin 4) ℝ :=
  ![![17/20,-1/4,1/4,-17/20], ![-1/4,3/20,-3/20,1/4],
    ![1/4,-3/20,3/20,-1/4], ![-17/20,1/4,-1/4,17/20]]

/-- T6(c),(d): the explicit majorant has δᵀMδ=3/5 while spectral clipping gives
1 at δ=(0,1,−1,0); cycle F4 has expectation 4−12/n and tends to the true value 4. -/
theorem positive_part_cycle_claims :
    PSD (oracleMatrix cycleGraph + cycleMajorantDifference) ∧ PSD cycleMajorantDifference ∧
    quadratic (oracleMatrix cycleGraph + cycleMajorantDifference) (![0,1,-1,0] : Fin 4 → ℝ) = 3/5 ∧
    quadratic (positivePart (oracleMatrix cycleGraph)) (![0,1,-1,0] : Fin 4 → ℝ) = 1 ∧
    (∀ k, expectation ((cycleFamily (3/2)).model k)
      (fun y => ((cycleFamily (3/2)).size k : ℝ)*VPositive ((cycleFamily (3/2)).model k).G
        (weighted ((cycleFamily (3/2)).model k) y)) = 4-12/((cycleFamily (3/2)).size k : ℝ)) ∧
    InProbability (cycleFamily (3/2))
      (fun k y => ((cycleFamily (3/2)).size k : ℝ)*VPositive ((cycleFamily (3/2)).model k).G
        (weighted ((cycleFamily (3/2)).model k) y)) (fun _ => 4) := by
  sorry

/-- T7(a),(b),(e): degree-only finite comparison bounds, with the correction's
explicit constants. B is max |eᵢ| and D bounds the supplied truncated degrees. -/
theorem degree_only_finite {n : ℕ} (hn : 0 < n) (d : Fin n → ℕ) (D : ℕ)
    (hd : ∀ i, truncatedDegree d i ≤ D) (x : Fin n → ℝ) (A Ap : Graph n)
    (hm : Maximizes (emptyGraph n) d (fun B => V1 B x) A)
    (hp : Maximizes (emptyGraph n) d (fun B => V1plus d B x) Ap) :
    (∀ (B : Graph n) (z : Fin n → ℝ), quadratic (adjacency B) z =
      (∑ i, (degree B i : ℝ)*z i^2) - upperSum (fun i j => adjacency B i j*(z i-z j)^2)) ∧
    (0 ≤ (n : ℝ)*(VYoung d x-V1 A x) ∧
      (n : ℝ)*(VYoung d x-V1 A x) ≤
        (∑ r ∈ Finset.Icc 1 D, (3*(r : ℝ)^2+2*r))*maxAbs (centered x)^2/n) ∧
    (0 ≤ (∑ i, max 1 (2*(truncatedDegree d i : ℝ))*centered x i^2)/n - (n : ℝ)*V1plus d Ap x ∧
      (∑ i, max 1 (2*(truncatedDegree d i : ℝ))*centered x i^2)/n - (n : ℝ)*V1plus d Ap x ≤
        maxAbs (centered x)^2/n*(∑ r ∈ Finset.Icc 1 D, (4*(r : ℝ)^2+r))) := by
  sorry

/-- T7(c): the original maximum is conservative when no recruitment edges are
known. Only the true dependency degree must be bounded; supplied caps may grow. -/
theorem degree_only_conservative (F : Family) (c1 c2 c3 c4 : ℝ)
    (h : Scaling F c1 c2 c3 c4) (hv : Valid F) (hr : ∀ k, (F.model k).R = emptyGraph (F.size k))
    (A : ∀ k, (Fin (F.size k) → ℝ) → Graph (F.size k))
    (hm : ∀ k y, Maximizes (F.model k).R (F.model k).d
      (fun B => V1 B (weighted (F.model k) y)) (A k y)) :
    Conservative F (fun k y => V1 (A k y) (weighted (F.model k) y)) := by
  sorry

/-- T7(d): unbounded supplied caps break equivalence of the original maximum and
Young bound even without scaling. For fair signs they tend to 1/2 and 1. -/
theorem unbounded_caps_gap (A : ∀ k, (Fin (k+1) → ℝ) → Graph (k+1))
    (hm : ∀ k y, Maximizes (emptyGraph (k+1)) (fun _ => k)
      (fun B => V1 B y) (A k y)) :
    (∀ k y, (∀ i, y i = 1 ∨ y i = -1) →
      V1 (A k y) y = (1-average y^2)^2/2 ∧
      VYoung (fun _ => k) y = 1-average y^2) ∧
    InProbability signFamily (fun k y => V1 (A k y) y) (fun _ => 1/2) ∧
    InProbability signFamily (fun k y => VYoung (fun _ => k) y) (fun _ => 1) := by
  sorry

/-- T8: membership in the revised list C, with the condition for each estimator.
Every selected matrix is an actual maximizer; data dependence is handled by
samplewise domination, not by the deterministic F1 expansion. -/
def CorrectedClass (F : Family) (V : ∀ k, (Fin (F.size k) → ℝ) → ℝ) : Prop :=
  (Valid F ∧ ((V = fun k y => V1plus (F.model k).d (F.model k).G (weighted (F.model k) y)) ∨
    (V = fun k y => VYoung (F.model k).d (weighted (F.model k) y)) ∨
    (∃ A : ∀ k, (Fin (F.size k) → ℝ) → Graph (F.size k),
      (∀ k y, Maximizes (F.model k).R (F.model k).d
        (fun B => V1plus (F.model k).d B (weighted (F.model k) y)) (A k y)) ∧
      ((V = fun k y => V1plus (F.model k).d (A k y) (weighted (F.model k) y)) ∨
       (V = fun k y => min (V1plus (F.model k).d (A k y) (weighted (F.model k) y))
         (VYoung (F.model k).d (weighted (F.model k) y))))))) ∨
  (V = fun k y => VPositive (F.model k).G (weighted (F.model k) y)) ∨
  (Valid F ∧ (∀ k, (F.model k).R = emptyGraph (F.size k)) ∧
    ∃ A : ∀ k, (Fin (F.size k) → ℝ) → Graph (F.size k),
      (∀ k y, Maximizes (F.model k).R (F.model k).d
        (fun B => V1 B (weighted (F.model k) y)) (A k y)) ∧
      V = fun k y => V1 (A k y) (weighted (F.model k) y)) ∨
  (Valid F ∧ 0 ≤ Filter.liminf (fun k => meanBias (F.model k)) atTop ∧
    ((V = fun k y => V1 (F.model k).G (weighted (F.model k) y)) ∨
      (∃ A : ∀ k, (Fin (F.size k) → ℝ) → Graph (F.size k),
        (∀ k y, Maximizes (F.model k).R (F.model k).d
          (fun B => V1 B (weighted (F.model k) y)) (A k y)) ∧
        V = fun k y => V1 (A k y) (weighted (F.model k) y))))

/-- T8: revised Corollaries 1 and 3 for every estimator in C. Coverage clips a
possibly negative V1 at zero; homoskedasticity alone is not an admissibility condition. -/
theorem revised_corollaries (F : Family) (c1 c2 c3 c4 : ℝ)
    (h : Scaling F c1 c2 c3 c4) (V : ∀ k, (Fin (F.size k) → ℝ) → ℝ)
    (hV : CorrectedClass F V) : Conservative F V ∧ ConservativeCoverage F V := by
  sorry

/-- The probability-theoretic meaning of O_p(1): eventual tightness. -/
def Tight (F : Family) (T : ∀ k, (Fin (F.size k) → ℝ) → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, 0 < B ∧ ∃ k0 : ℕ, ∀ k ≥ k0,
    probability (F.model k) {y | |T k y| > B} ≤ ε

/-- Corrections T9 and T16: fixed finite-dimensional covariate mean model. -/
def MeanModel {n p : ℕ} (m : Model n) (D : Matrix (Fin n) (Fin p) ℝ) (γ : Fin p → ℝ) : Prop :=
  (∀ i, Integrable (fun y => y i) m.law) ∧
  ∀ i, expectation m (fun y => y i) = (D *ᵥ γ) i

/-- T9: true weighted errors zᵢ=θᵢ(Yᵢ−xᵢᵀγ). -/
def trueResidual {n p : ℕ} (m : Model n) (D : Matrix (Fin n) (Fin p) ℝ)
    (γ : Fin p → ℝ) (y : Fin n → ℝ) : Fin n → ℝ := fun i => m.theta i*(y i-(D *ᵥ γ) i)

/-- T9: fitted weighted residuals use γ̂(y), without further sample recentering. -/
def fittedResidual {n p : ℕ} (m : Model n) (D : Matrix (Fin n) (Fin p) ℝ)
    (γhat : (Fin n → ℝ) → (Fin p → ℝ)) (y : Fin n → ℝ) : Fin n → ℝ :=
  fun i => m.theta i*(y i-(D *ᵥ (γhat y)) i)

/-- T9,T16: V̂₁^res = rᵀ(I+A)r/n², a different objective from raw centering. -/
def VResidual {n : ℕ} (A : Graph n) (r : Fin n → ℝ) : ℝ := quadratic (oracleMatrix A) r/(n : ℝ)^2

/-- T9(b): the finite perturbation bound for every symmetric matrix in Euclidean norm. -/
theorem residual_perturbation {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    (hM : ∀ i j, M i j = M j i) (r z : Fin n → ℝ) :
    |quadratic M r-quadratic M z| ≤ operatorNorm M*l2 (r-z)*(2*l2 z+l2 (r-z)) := by
  let B (a b : Fin n → ℝ) : ℝ := ∑ i, ∑ j, M i j*a i*b j
  let L : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
    (Matrix.toEuclideanLin M).toContinuousLinearMap
  have hn (a : Fin n → ℝ) : ‖WithLp.toLp 2 a‖=l2 a := by
    simp [EuclideanSpace.norm_eq,l2,Real.norm_eq_abs,sq_abs]
  have hi (a b : Fin n → ℝ) : B a b =
      inner ℝ (WithLp.toLp 2 a) (L (WithLp.toLp 2 b)) := by
    change B a b=inner ℝ (WithLp.toLp 2 a)
      ((Matrix.toEuclideanLin M) (WithLp.toLp 2 b))
    simp [Matrix.toEuclideanLin,Matrix.toLpLin_toLp,EuclideanSpace.inner_toLp_toLp,
      dotProduct,Matrix.mulVec,B,Finset.mul_sum,Finset.sum_mul,mul_comm,mul_left_comm,mul_assoc]
  have hs : B z r=B r z := by
    dsimp [B]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    rw [hM j i]
    ring
  have he : B (r-z) (r+z)=quadratic M r+B r z-(B z r+quadratic M z) := by
    have hpoint (i j : Fin n) : M i j*(r i-z i)*(r j+z j)=
        M i j*r i*r j+M i j*r i*z j-(M i j*z i*r j+M i j*z i*z j) := by ring
    change (∑ i, ∑ j, M i j*(r i-z i)*(r j+z j)) =
      (∑ i, ∑ j, M i j*r i*r j)+(∑ i, ∑ j, M i j*r i*z j)-
        ((∑ i, ∑ j, M i j*z i*r j)+(∑ i, ∑ j, M i j*z i*z j))
    simp_rw [hpoint,Finset.sum_sub_distrib,Finset.sum_add_distrib]
  have hd : quadratic M r-quadratic M z=B (r-z) (r+z) := by
    rw [he,hs]
    ring
  have hv : WithLp.toLp 2 (r+z)=WithLp.toLp 2 (r-z)+(2 : ℝ) • WithLp.toLp 2 z := by
    ext i
    simp only [PiLp.toLp_apply,Pi.add_apply,Pi.sub_apply,PiLp.add_apply,PiLp.smul_apply,smul_eq_mul]
    ring
  have hb : ‖WithLp.toLp 2 (r+z)‖ ≤ ‖WithLp.toLp 2 (r-z)‖+2*‖WithLp.toLp 2 z‖ := by
    rw [hv]
    simpa [norm_smul] using norm_add_le (WithLp.toLp 2 (r-z)) ((2 : ℝ) • WithLp.toLp 2 z)
  calc
    |quadratic M r-quadratic M z| = |B (r-z) (r+z)| := by rw [hd]
    _ = ‖inner ℝ (WithLp.toLp 2 (r-z)) (L (WithLp.toLp 2 (r+z)))‖ := by rw [hi,Real.norm_eq_abs]
    _ ≤ ‖WithLp.toLp 2 (r-z)‖*‖L (WithLp.toLp 2 (r+z))‖ := norm_inner_le_norm _ _
    _ ≤ ‖WithLp.toLp 2 (r-z)‖*(‖L‖*‖WithLp.toLp 2 (r+z)‖) :=
      mul_le_mul_of_nonneg_left (L.le_opNorm _) (norm_nonneg _)
    _ ≤ ‖WithLp.toLp 2 (r-z)‖*(‖L‖*(‖WithLp.toLp 2 (r-z)‖+2*‖WithLp.toLp 2 z‖)) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hb (norm_nonneg _)) (norm_nonneg _)
    _ = _ := by simp only [hn]; dsimp [L,operatorNorm]; ring

/-- T9(a),(c): bounded fixed-p covariates and root-n parameter consistency imply
oracle residual consistency and conservative maximization under valid constraints. -/
theorem residual_root_n (F : Family) (c1 c2 c3 c4 : ℝ) (h : Scaling F c1 c2 c3 c4)
    (p : ℕ) (D : ∀ k, Matrix (Fin (F.size k)) (Fin p) ℝ) (γ : Fin p → ℝ)
    (γhat : ∀ k, (Fin (F.size k) → ℝ) → (Fin p → ℝ))
    (hmeas : ∀ k, Measurable (γhat k))
    (hmean : ∀ k, MeanModel (F.model k) (D k) γ)
    (hbound : ∃ B : ℝ, ∀ k i, l2 (D k i) ≤ B)
    (hrate : Tight F (fun k y => Real.sqrt (F.size k : ℝ)*l2 (γhat k y-γ)))
    (A : ∀ k, (Fin (F.size k) → ℝ) → Graph (F.size k)) (hv : Valid F)
    (hm : ∀ k y, Maximizes (F.model k).R (F.model k).d
      (fun B => VResidual B (fittedResidual (F.model k) (D k) (γhat k) y)) (A k y)) :
    (∀ k i, expectation (F.model k) (fun y => trueResidual (F.model k) (D k) γ y i) = 0) ∧
    (∀ k i j, expectation (F.model k) (fun y =>
      trueResidual (F.model k) (D k) γ y i*trueResidual (F.model k) (D k) γ y j) =
      covariance (F.model k) i j) ∧
    Tight F (fun k y => Real.sqrt (F.size k : ℝ)*maxAbs
      (fittedResidual (F.model k) (D k) (γhat k) y-trueResidual (F.model k) (D k) γ y)) ∧
    Tight F (fun k y => l2
      (fittedResidual (F.model k) (D k) (γhat k) y-trueResidual (F.model k) (D k) γ y)) ∧
    Tight F (fun k y => l2 (trueResidual (F.model k) (D k) γ y)/Real.sqrt (F.size k : ℝ)) ∧
    InProbability F
      (fun k y => (F.size k : ℝ)*VResidual (F.model k).G
        (fittedResidual (F.model k) (D k) (γhat k) y)) (scaledTrue F) ∧
    Conservative F (fun k y => VResidual (A k y)
      (fittedResidual (F.model k) (D k) (γhat k) y)) := by
  sorry

/-- T9(c), weaker regularity: weighted prediction error o_p(√n) and bounded
limiting residual summands suffice; no root-n estimator is inserted as an extra premise. -/
theorem residual_prediction_stability (F : Family) (c1 c2 c3 c4 : ℝ)
    (h : Scaling F c1 c2 c3 c4) (p : ℕ)
    (D : ∀ k, Matrix (Fin (F.size k)) (Fin p) ℝ) (γ : Fin p → ℝ)
    (γhat : ∀ k, (Fin (F.size k) → ℝ) → (Fin p → ℝ))
    (hmeas : ∀ k, Measurable (γhat k))
    (hmean : ∀ k, MeanModel (F.model k) (D k) γ)
    (hz : ∃ B : ℝ, ∀ k, ∀ᵐ y ∂(F.model k).law, ∀ i, |trueResidual (F.model k) (D k) γ y i| ≤ B)
    (herr : InProbability F (fun k y => l2
      (fittedResidual (F.model k) (D k) (γhat k) y-trueResidual (F.model k) (D k) γ y)
        /Real.sqrt (F.size k : ℝ)) (fun _ => 0))
    (A : ∀ k, (Fin (F.size k) → ℝ) → Graph (F.size k)) (hv : Valid F)
    (hm : ∀ k y, Maximizes (F.model k).R (F.model k).d
      (fun B => VResidual B (fittedResidual (F.model k) (D k) (γhat k) y)) (A k y)) :
    InProbability F (fun k y => (F.size k : ℝ)*VResidual (F.model k).G
      (fittedResidual (F.model k) (D k) (γhat k) y)) (scaledTrue F) ∧
    Conservative F (fun k y => VResidual (A k y) (fittedResidual (F.model k) (D k) (γhat k) y)) := by
  sorry

/-- T9(e): a wrong mean model retains the deterministic mean quadratic term;
residuals here are not additionally sample-centered. -/
theorem misspecified_residual_limit (F : Family) (c1 c2 c3 c4 : ℝ)
    (h : Scaling F c1 c2 c3 c4) (p : ℕ)
    (D : ∀ k, Matrix (Fin (F.size k)) (Fin p) ℝ) (γstar : Fin p → ℝ)
    (γhat : ∀ k, (Fin (F.size k) → ℝ) → (Fin p → ℝ))
    (hmeas : ∀ k, Measurable (γhat k))
    (hz : ∃ B : ℝ, ∀ k, ∀ᵐ y ∂(F.model k).law, ∀ i, |trueResidual (F.model k) (D k) γstar y i| ≤ B)
    (herr : InProbability F (fun k y => l2
      (fittedResidual (F.model k) (D k) (γhat k) y-trueResidual (F.model k) (D k) γstar y)
        /Real.sqrt (F.size k : ℝ)) (fun _ => 0)) :
    InProbability F
      (fun k y => (F.size k : ℝ)*VResidual (F.model k).G
        (fittedResidual (F.model k) (D k) (γhat k) y)-scaledTrue F k)
      (fun k => quadratic (oracleMatrix (F.model k).G)
        (fun i => expectation (F.model k) (fun y => weighted (F.model k) y i)
          -(F.model k).theta i*(D k *ᵥ γstar) i) / (F.size k : ℝ)) := by
  sorry

/-- T12: Uₙ=n⁻¹∑(Xᵢ−β)² used in the direct repaired proof of Proposition 2. -/
def U {n : ℕ} (m : Model n) (y : Fin n → ℝ) : ℝ :=
  (∑ i, (weighted m y i-beta m)^2)/n

/-- T12: gₙ=1+n⁻¹∑Aᴼᵢⱼ and σ²ₙ equal to a marginal variance.
The sum/card definition avoids a choice of vertex at n=0. -/
def gFactor {n : ℕ} (m : Model n) : ℝ := 1+(∑ i, ∑ j, adjacency m.G i j)/n

/-- T12: Rₙ=σ̂²_θ−(σ²ₙ+Mₙ); σ²ₙ is meanVariance under homoskedasticity. -/
def varianceRemainder {n : ℕ} (m : Model n) (y : Fin n → ℝ) : ℝ :=
  sampleVariance (weighted m y)-meanVariance m-meanSpread m

/- T12(i)–(iv): the complete finite rate proof and unchanged Proposition 2.
No auxiliary correlations, equal means, or separate variance/mean-spread limit is assumed. -/
/- The unchanged homoskedastic_repair contract is proved in P011_HomoskedasticCompletion.lean. -/


/-- Section 2, p. 2240: fixed-design OLS β̂=(XᵀX)⁻¹XᵀY. -/
def ols {n p : ℕ} (D : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ) : Fin p → ℝ :=
  (Dᵀ*D)⁻¹ *ᵥ (Dᵀ *ᵥ y)

/-- Section 2, p. 2241: "Θ = n(X′X)⁻¹X′" (different from diag(θ) in Section 3). -/
def olsTheta {n p : ℕ} (D : Matrix (Fin n) (Fin p) ℝ) : Matrix (Fin p) (Fin n) ℝ :=
  (n : ℝ) • ((Dᵀ*D)⁻¹*Dᵀ)

/-- T16(i),(ii),(iii): raw OLS mean term, exact residual shift invariance,
and consistency of fitted residual products under fixed p, bounded rows and outcomes,
and a uniform lower eigenvalue bound on the normalized Gram matrix. -/
theorem ols_repair (F : Family) (c1 c2 c3 c4 : ℝ) (h : Scaling F c1 c2 c3 c4)
    (p : ℕ) (j : Fin p) (D : ∀ k, Matrix (Fin (F.size k)) (Fin p) ℝ) (b : Fin p → ℝ)
    (hrank : ∀ k, ((D k)ᵀ*D k).det ≠ 0)
    (hmean : ∀ k, MeanModel (F.model k) (D k) b)
    (hθ : ∀ k i, (F.model k).theta i = olsTheta (D k) j i) :
    (∀ k i, delta (F.model k) i = olsTheta (D k) j i*(D k*ᵥb) i-b j) ∧
    InProbability F (fun k y => scaledOracle F k y-scaledTrue F k)
      (fun k => meanBias (F.model k)) ∧
    (∀ k y c, fittedResidual (F.model k) (D k) (ols (D k)) (y+D k*ᵥc) =
      fittedResidual (F.model k) (D k) (ols (D k)) y ∧
      centered (weighted (F.model k) (y+D k*ᵥc)) =
        centered (weighted (F.model k) y) +
          (fun i => (F.model k).theta i*(D k*ᵥc) i-c j)) ∧
    ((∃ Bx By lambdaMin : ℝ, 0 < lambdaMin ∧ (∀ k i, l2 (D k i) ≤ Bx) ∧
      (∀ k, ∀ᵐ y ∂(F.model k).law, ∀ i, |y i| ≤ By) ∧
      (∀ k z, lambdaMin*l2 z^2 ≤ quadratic ((1/(F.size k : ℝ)) • ((D k)ᵀ*D k)) z)) →
      Tight F (fun k y => Real.sqrt (F.size k : ℝ)*l2 (ols (D k) y-b)) ∧
      InProbability F (fun k y => (F.size k : ℝ)*VResidual (F.model k).G
        (fittedResidual (F.model k) (D k) (ols (D k)) y)) (scaledTrue F) ∧
      (∀ A : ∀ k, (Fin (F.size k) → ℝ) → Graph (F.size k), Valid F →
        (∀ k y, Maximizes (F.model k).R (F.model k).d
          (fun B => VResidual B (fittedResidual (F.model k) (D k) (ols (D k)) y)) (A k y)) →
        Conservative F (fun k y => VResidual (A k y)
          (fittedResidual (F.model k) (D k) (ols (D k)) y)))) := by
  sorry

/- The unchanged block_ols_representations contract is proved in P011_BlockOLSCompletion.lean. -/


/-- T9(d): covariates (1,w), w=(1,0,−1,0), with high-variance observations
at zero slope-weight. This is permitted by the paper's bound on θY. -/
def unstableModel (blocks : ℕ) : Model (4*blocks) where
  law := uniformLaw (fun u : Fin (4*blocks) → Bool => fun i =>
    (if i.val%2=0 then 1 else (4*blocks : ℝ))*sign (u i))
  probability := by dsimp [uniformLaw]; infer_instance
  theta := fun i => 2*(![1,0,-1,0] : Fin 4 → ℝ) (localIndex (by decide) i)
  G := emptyGraph (4*blocks)
  R := emptyGraph (4*blocks)
  d := fun _ => 0

/-- T9(d): the complete-block unstable OLS sequence. -/
def unstableFamily : Family where
  size := fun k => 4*(k+1)
  positive := by intro k; omega
  grows := Filter.tendsto_atTop_mono (fun k => by change k ≤ _; omega) Filter.tendsto_id
  model := fun k => unstableModel (k+1)

/-- T9(d): exact finite expectation n+2−7/n and lack of residual consistency.
No inference of inconsistency from diverging expectations alone is made. -/
theorem residual_missing_regularity :
    Scaling unstableFamily 2 1 2 3 ∧
    (∀ k, let D : Matrix (Fin (4*(k+1))) (Fin 2) ℝ := fun i j =>
      if j=0 then 1 else (![1,0,-1,0] : Fin 4 → ℝ) (localIndex (by decide) i)
      MeanModel (unstableFamily.model k) D 0 ∧
      var (unstableFamily.model k) (fun y => ols D y 0) =
        (unstableFamily.size k : ℝ)/2+1/(2*(unstableFamily.size k : ℝ)) ∧
      expectation (unstableFamily.model k) (fun y => (unstableFamily.size k : ℝ)*
        VResidual (unstableFamily.model k).G
          (fittedResidual (unstableFamily.model k) D (ols D) y)) =
        (unstableFamily.size k : ℝ)+2-7/(unstableFamily.size k : ℝ)) ∧
    ¬ InProbability unstableFamily
      (fun k y => let D : Matrix (Fin (4*(k+1))) (Fin 2) ℝ := fun i j =>
        if j=0 then 1 else (![1,0,-1,0] : Fin 4 → ℝ) (localIndex (by decide) i)
        (unstableFamily.size k : ℝ)*VResidual (unstableFamily.model k).G
          (fittedResidual (unstableFamily.model k) D (ols D) y)) (fun _ => 2) := by
  sorry

/-- T10: P_s has deterministic infinite mean pattern s, not an n-dependent
finite pattern. This quantifier is essential to the bounded-convergence argument. -/
def fixedMeanModel (a b : ℝ) (s : ℕ → Bool) (n : ℕ) : Model n where
  law := uniformLaw (fun u : Fin n → Bool => fun i => a*sign (s i.val)+b*sign (u i))
  probability := by dsimp [uniformLaw]; infer_instance
  theta := fun _ => 1
  G := emptyGraph n
  R := emptyGraph n
  d := fun _ => 0

/-- T10: the mixture has iid independent random mean signs and error signs. -/
def mixtureModel (a b : ℝ) (n : ℕ) : Model n where
  law := uniformLaw (fun u : (Fin n → Bool) × (Fin n → Bool) =>
    fun i => a*sign (u.1 i)+b*sign (u.2 i))
  probability := by dsimp [uniformLaw]; infer_instance
  theta := fun _ => 1
  G := emptyGraph n
  R := emptyGraph n
  d := fun _ => 0

/-- T10: fixed-mean positive-integer sample sequence. -/
def fixedMeanFamily (a b : ℝ) (s : ℕ → Bool) : Family where
  size := fun k => k+1
  positive := by intro k; omega
  grows := Filter.tendsto_atTop_mono (fun k => Nat.le_succ k) Filter.tendsto_id
  model := fun k => fixedMeanModel a b s (k+1)

/-- T10: unconditional mixture sample sequence. -/
def mixtureFamily (a b : ℝ) : Family where
  size := fun k => k+1
  positive := by intro k; omega
  grows := Filter.tendsto_atTop_mono (fun k => Nat.le_succ k) Filter.tendsto_id
  model := fun k => mixtureModel a b (k+1)

/-- T10(i)–(iii): exact finite mixture identity and impossibility of n-scaled
consistency over every deterministic infinite mean pattern and the mixture.
The statistic is the same measurable function of observations in all models. -/
theorem universal_consistency_impossible (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    (∀ s : ℕ → Bool, Scaling (fixedMeanFamily a b s) (2*a+b) 1 (b^2) 2) ∧
    Scaling (mixtureFamily a b) (a+b) 1 (a^2+b^2) 2 ∧
    (∀ n, (mixtureModel a b n).law =
      ∑ s : (Fin n → Bool), ((2 : ℝ≥0∞)^n)⁻¹ •
        (fixedMeanModel a b (fun i => if hi : i < n then s ⟨i,hi⟩ else false) n).law) ∧
    ¬ (∃ T : ∀ n, (Fin (n+1) → ℝ) → ℝ,
      (∀ n, Measurable (T n)) ∧
      (∀ s : ℕ → Bool, InProbability (fixedMeanFamily a b s) T (fun _ => b^2)) ∧
      InProbability (mixtureFamily a b) T (fun _ => a^2+b^2)) ∧
    (∀ T : ∀ n, (Fin (n+1) → ℝ) → ℝ, (∀ n, Measurable (T n)) →
      (∀ ε : ℝ, 0 < ε → Tendsto (fun k => probability (mixtureModel a b (k+1))
        {y | a^2+b^2-T k y > ε}) atTop (𝓝 0)) →
      ¬ (∀ s : ℕ → Bool, InProbability (fixedMeanFamily a b s) T (fun _ => b^2))) := by
  sorry

/-- T13: an unordered edge is represented exactly once by i<j. -/
abbrev Edge (n : ℕ) := {ij : Fin n × Fin n // ij.1 < ij.2}

/-- T13: (P), with rational weights and mandatory edges, exactly as in the validator. -/
structure DegreeProblem (n : ℕ) where
  forced : Finset (Edge n)
  cap : Fin n → ℕ
  weight : Edge n → ℚ

/-- T13: degree of a vertex in an unordered edge set. -/
def edgeDegree {n : ℕ} (S : Finset (Edge n)) (i : Fin n) : ℕ :=
  (S.filter (fun e => e.val.1=i ∨ e.val.2=i)).card

/-- T13: the paper's graph-program feasible set. -/
def EdgeFeasible {n : ℕ} (P : DegreeProblem n) (S : Finset (Edge n)) : Prop :=
  P.forced ⊆ S ∧ ∀ i, edgeDegree S i ≤ P.cap i

/-- T13: signed edge objective, including negative mandatory weights. -/
def edgeObjective {n : ℕ} (P : DegreeProblem n) (S : Finset (Edge n)) : ℚ := ∑ e ∈ S, P.weight e

/-- T13(b): subtract incidences of mandatory edges from truncated capacities. -/
def remainingCap {n : ℕ} (P : DegreeProblem n) (i : Fin n) : ℕ :=
  min (P.cap i) (n-1)-edgeDegree P.forced i

/-- T13(c): optional edges E=K\F. -/
def optionalEdges {n : ℕ} (P : DegreeProblem n) : Finset (Edge n) := Finset.univ \ P.forced

/-- T13(c): L is the lcm of optional rational denominators (empty lcm = 1). -/
def denominatorLCM {n : ℕ} (P : DegreeProblem n) : ℕ :=
  (optionalEdges P).lcm (fun e => (P.weight e).den)

/-- T13(c): exact integer W_e = L w_e. -/
def integerWeight {n : ℕ} (P : DegreeProblem n) (e : Edge n) : ℤ :=
  (denominatorLCM P : ℤ)*(P.weight e).num/(P.weight e).den

/-- T13(c): M = 1+max |W_e|, empty maximum 0. -/
def gadgetM {n : ℕ} (P : DegreeProblem n) : ℤ :=
  1 + (((optionalEdges P).sup (fun e => (integerWeight P e).natAbs) : ℕ) : ℤ)

/-- T13(c): graph H has slot vertices and two gadget vertices per optional edge. -/
abbrev GadgetVertex {n : ℕ} (P : DegreeProblem n) :=
  (Σ i : Fin n, Fin (remainingCap P i)) ⊕ ({e // e ∈ optionalEdges P} × Bool)

/-- An optional edge's endpoint corresponding to its left/right gadget vertex. -/
def endpoint {n : ℕ} (e : Edge n) (side : Bool) : Fin n := if side then e.val.2 else e.val.1

/-- T13(c): every edge of H is internal or connects a gadget endpoint to a slot.
The tagged edge type has no duplicate orientations or self-loops. -/
inductive GadgetEdge {n : ℕ} (P : DegreeProblem n)
  | internal (e : {e // e ∈ optionalEdges P})
  | external (e : {e // e ∈ optionalEdges P}) (side : Bool)
      (slot : Fin (remainingCap P (endpoint e.val side)))

/-- Endpoints of H's edges; ordinary matching forbids sharing either endpoint. -/
def gadgetEnds {n : ℕ} {P : DegreeProblem n} : GadgetEdge P → GadgetVertex P × GadgetVertex P
  | .internal e => (.inr (e,false), .inr (e,true))
  | .external e side slot => (.inr (e,side), .inl ⟨endpoint e.val side,slot⟩)

/-- T13(c): internal weight 4M, external weight 2M+W_e. -/
def gadgetWeight {n : ℕ} {P : DegreeProblem n} : GadgetEdge P → ℤ
  | .internal _ => 4*gadgetM P
  | .external e _ _ => 2*gadgetM P+integerWeight P e.val

/-- T13: the usual matching condition, no two selected edges sharing a vertex. -/
def IsMatching {n : ℕ} {P : DegreeProblem n} (J : Finset (GadgetEdge P)) : Prop :=
  ∀ e ∈ J, ∀ f ∈ J, e ≠ f →
    (gadgetEnds e).1 ≠ (gadgetEnds f).1 ∧ (gadgetEnds e).1 ≠ (gadgetEnds f).2 ∧
    (gadgetEnds e).2 ≠ (gadgetEnds f).1 ∧ (gadgetEnds e).2 ≠ (gadgetEnds f).2

/-- T13(c): decode edges whose gadget vertices are both matched to slots. -/
def decodeMatching {n : ℕ} (P : DegreeProblem n) (J : Finset (GadgetEdge P)) : Finset (Edge n) :=
  (optionalEdges P).filter (fun e => ∃ he : e ∈ optionalEdges P,
    (∃ s, GadgetEdge.external (P:=P) ⟨e,he⟩ false s ∈ J) ∧
    (∃ s, GadgetEdge.external (P:=P) ⟨e,he⟩ true s ∈ J))

/-- T13(b)–(d): exact reduction to ordinary maximum-weight matching, including
feasibility, objective recovery, and polynomial vertex/edge count bounds.
The external algorithmic theorem about bit complexity is not formalized here. -/
theorem matching_reduction {n : ℕ} (hn : 0 < n) (P : DegreeProblem n) :
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
      (remainingCap P e.val.1+remainingCap P e.val.2) ≤ (optionalEdges P).card*(2*n-1)) := by
  sorry

/-- T22: candidate edges, not nonzero empirical covariances, are the decision variables. -/
def fromUpper {n : ℕ} (a : Edge n → Bool) : Graph n :=
  ⟨fun (i j : Fin n) => if h : i < j then a ⟨(i,j),h⟩ else if h' : j < i then a ⟨(j,i),h'⟩ else false, by
    constructor
    · intro i j
      by_cases h : i < j
      · have h' : ¬ (j < i) := by omega
        simp [h,h']
      · by_cases h' : j < i
        · simp [h,h']
        · simp [h,h']
    · intro i; simp⟩

/-- T22: coordinates of an adjacency matrix in its upper triangular part. -/
def toUpper {n : ℕ} (A : Graph n) : Edge n → Bool := fun e => A.val e.val.1 e.val.2

/-- T22: upper-triangular objective of program (3.6), each unordered pair once. -/
def upperObjective {n : ℕ} (a : Edge n → Bool) (w : Edge n → ℝ) : ℝ :=
  ∑ e, if a e then w e else 0

/-- T22: program (3.6) degrees are the numbers of selected edges incident to i. -/
def upperDegree {n : ℕ} (a : Edge n → Bool) (i : Fin n) : ℕ :=
  ∑ e, if a e && decide (e.val.1=i ∨ e.val.2=i) then 1 else 0

/- T22: The unchanged upper_program_equivalence contract is proved in
P011_FiniteCompletion.lean from the actual graph/edge-vector bijection. -/

/-- T14: LP relaxation of (3.6), preserving mandatory edges and vertex degrees. -/
def RelaxedFeasible {n : ℕ} (R : Graph n) (d : Fin n → ℕ) (a : Edge n → ℝ) : Prop :=
  (∀ e, 0 ≤ a e ∧ a e ≤ 1) ∧ (∀ e, toUpper R e = true → a e = 1) ∧
  ∀ i, (∑ e, if e.val.1=i ∨ e.val.2=i then a e else 0) ≤ d i

/-- T14: real-valued objective of the relaxation. -/
def relaxedObjective {n : ℕ} (a w : Edge n → ℝ) : ℝ := ∑ e, w e*a e

/- T14(a): The unchanged relaxation_upper_bound statement is proved in
P011_FiniteCompletion.lean using a Boolean feasible embedding and exact objectives. -/

/- T14(b),(c): The unchanged relaxation_gaps contract is proved in
P011_FiniteCompletion.lean with explicit fractional and integer witnesses. -/


/-- Covariance expressed as E[fg]−E[f]E[g], for integrable mixed moments (T17).
On the L² functions in these statements this equals centred covariance. -/
def covOf {n : ℕ} (m : Model n) (f g : (Fin n → ℝ) → ℝ) : ℝ :=
  expectation m (fun y => f y*g y)-expectation m f*expectation m g

/-- T17: corrected second-moment block Qᵢⱼ, including both weighted factors. -/
def pairMoment {Ω : Type} (E : (Ω → ℝ) → ℝ) (yi yj B : Ω → ℝ) (ti tj : ℝ) : ℝ :=
  ti*tj*E (fun y => yi y*yj y)-ti*E (fun y => yi y*B y)-
    tj*E (fun y => yj y*B y)+E (fun y => B y^2)

/-- T17: the 16 terms of the corrected fourth-moment block, grouped by power
of β̂. Xi here is the full θᵢYi, including the formerly missing θⱼ. -/
def fourthMoment {Ω : Type} (E : (Ω → ℝ) → ℝ) (Xi Xj Xk Xl B : Ω → ℝ) : ℝ :=
  E (fun y => Xi y*Xj y*Xk y*Xl y) -
  E (fun y => B y*(Xi y*Xj y*Xk y+Xi y*Xj y*Xl y+Xi y*Xk y*Xl y+Xj y*Xk y*Xl y)) +
  E (fun y => B y^2*(Xi y*Xj y+Xi y*Xk y+Xi y*Xl y+Xj y*Xk y+Xj y*Xl y+Xk y*Xl y)) -
  E (fun y => B y^3*(Xi y+Xj y+Xk y+Xl y)) + E (fun y => B y^4)

/- T17(i)-(iii): The unchanged corrected_covariance_expansion contract is
proved in P011_CovarianceCompletion.lean with explicit L4 integrability
and covariance bilinearity. The asymptotic remainder is outside this target. -/

/-- T17 finite polynomial behind the 16 fourth-moment monomials, for all values.
Taking any linear expectation preserves this identity when the moments exist. -/
theorem fourth_polynomial (a b c d B : ℝ) :
    (a-B)*(b-B)*(c-B)*(d-B) = a*b*c*d -
      B*(a*b*c+a*b*d+a*c*d+b*c*d) +
      B^2*(a*b+a*c+a*d+b*c+b*d+c*d)-B^3*(a+b+c+d)+B^4 := by ring

/-- T18: exactly the erroneous printed bracket of (3.3); its leading term
has no weights, the θ_i before E[Yi β̂]E[YkYl] is missing, and a four-weight
factor multiplies the entire bracket externally. -/
def printedBracket {Ω : Type} (E : (Ω → ℝ) → ℝ) (yi yj yk yl B : Ω → ℝ)
    (ti tj tk tl : ℝ) : ℝ :=
  E (fun y => yi y*yj y)*E (fun y => yk y*yl y) -
  ti*tj*tk*E (fun y => yi y*yj y)*E (fun y => yk y*B y) -
  ti*tj*tl*E (fun y => yi y*yj y)*E (fun y => yl y*B y) +
  ti*tj*E (fun y => yi y*yj y)*E (fun y => B y^2) -
  tk*tl*E (fun y => yi y*B y)*E (fun y => yk y*yl y) +
  ti*tl*E (fun y => yi y*B y)*E (fun y => yl y*B y) +
  ti*tk*E (fun y => yi y*B y)*E (fun y => yk y*B y) -
  ti*E (fun y => yi y*B y)*E (fun y => B y^2) -
  tj*tk*tl*E (fun y => yj y*B y)*E (fun y => yk y*yl y) +
  tj*tl*E (fun y => yj y*B y)*E (fun y => yl y*B y) +
  tj*tk*E (fun y => yj y*B y)*E (fun y => yk y*B y) -
  tj*E (fun y => yj y*B y)*E (fun y => B y^2) +
  tk*tl*E (fun y => B y^2)*E (fun y => yk y*yl y) -
  tk*E (fun y => B y^2)*E (fun y => yk y*B y) -
  tl*E (fun y => B y^2)*E (fun y => yl y*B y) +
  E (fun y => B y^2)*E (fun y => B y^2)

/-- T18: degenerate probability-one outcomes, not a zero measure. -/
def constantWitness : Model 4 where
  law := Measure.dirac (fun _ => (1 : ℝ))
  probability := by infer_instance
  theta := ![2,3,4,5]
  G := emptyGraph 4
  R := emptyGraph 4
  d := fun _ => 0

/-- T18, (3.3), p. 2243: true covariance at the explicit Dirac witness. -/
def cwTrueCovariance : ℝ :=
  covOf constantWitness
      (fun y => (2*y 0-betaHat constantWitness y)*(3*y 1-betaHat constantWitness y))
      (fun y => (4*y 2-betaHat constantWitness y)*(5*y 3-betaHat constantWitness y))

/-- T18, first line of (3.3), p. 2243: the literal printed right side at that witness. -/
def cwPrintedFirst : ℝ :=
  (expectation constantWitness (fun y => (2*y 0-betaHat constantWitness y)*
      (y 1-betaHat constantWitness y)*(4*y 2-betaHat constantWitness y)*(5*y 3-betaHat constantWitness y)) -
      expectation constantWitness (fun y => (2*y 0-betaHat constantWitness y)*(3*y 1-betaHat constantWitness y))*
      expectation constantWitness (fun y => (4*y 2-betaHat constantWitness y)*(5*y 3-betaHat constantWitness y)))

/-- T18, final line of (3.3), pp. 2243–2244: the literal printed value at that witness. -/
def cwPrintedLast : ℝ :=
  (fourthMoment (expectation constantWitness) (fun y => 2*y 0) (fun y => 3*y 1)
      (fun y => 4*y 2) (fun y => 5*y 3) (betaHat constantWitness) -
      120*printedBracket (expectation constantWitness) (fun y => y 0) (fun y => y 1)
        (fun y => y 2) (fun y => y 3) (betaHat constantWitness) 2 3 4 5)

/-- T18(a)–(e): the exact constant-distribution refutation of both printed
lines and the bracket-only repair. The fully literal final line is 93009/16,
not the double-counted value in one validator file. -/
theorem printed_expansion_counterexample :
    beta constantWitness = 7/2 ∧
    cwTrueCovariance = 0 ∧
    cwPrintedFirst = 9/4 ∧
    cwPrintedLast = 93009/16 ∧
    (9/16 - (9/16 + 140-70) : ℝ) = -70 ∧
    (fourthMoment (expectation constantWitness) (fun y => 2*y 0) (fun y => 3*y 1)
      (fun y => 4*y 2) (fun y => 5*y 3) (betaHat constantWitness) -
      pairMoment (expectation constantWitness) (fun y => y 0) (fun y => y 1) (betaHat constantWitness) 2 3 *
      pairMoment (expectation constantWitness) (fun y => y 2) (fun y => y 3) (betaHat constantWitness) 4 5) = 0 ∧
    cwTrueCovariance ≠ cwPrintedFirst ∧ cwTrueCovariance ≠ cwPrintedLast ∧
    cwTrueCovariance ≠ -70 := by
  norm_num [beta, betaHat, weighted, average, expectation, covOf, fourthMoment,
    pairMoment, printedBracket, constantWitness, cwTrueCovariance, cwPrintedFirst,
    cwPrintedLast, Fin.sum_univ_succ]

/-- T21: pairwise correlations; at common variance zero the convention is 0. -/
def rho {n : ℕ} (m : Model n) (i j : Fin n) : ℝ :=
  if meanVariance m = 0 then 0 else covariance m i j/meanVariance m

/-- T19,T21: the auxiliary oracle of the proof of Proposition 2, with ρ_ij. -/
def V2star {n : ℕ} (m : Model n) (y : Fin n → ℝ) : ℝ :=
  sampleVariance (weighted m y)/n * (1+(∑ i, ∑ j, adjacency m.G i j*rho m i j)/n)

/- T21(i),(ii): exact correlation-weighted variance identity, all ρ_ij≤1,
and samplewise V̂₂*≤V̂₂, including the zero-variance convention. -/
/- The unchanged pairwise_correlation_repair contract is proved in P011_CorrelationCompletion.lean. -/

/- T19(i)–(iii): correcting '<' to '>' gives auxiliary consistency only with
a vanishing between-unit mean variance; sign repair alone is insufficient. -/
/- The unchanged auxiliary_corrected_display contract is proved in P011_AuxiliaryCompletion.lean. -/

/-- T23: the invalid printed rule selects all nonzero pair products. -/
def nonzeroRule {n : ℕ} (x : Fin n → ℝ) : Graph n :=
  fromUpper (fun e => decide (centered x e.val.1*centered x e.val.2 ≠ 0))

/-- A complete graph, used in the finite counterexamples T23 and T26. -/
def completeGraph (n : ℕ) : Graph n :=
  ⟨fun i j => decide (i ≠ j), by constructor <;> intros <;> simp [ne_comm]⟩

/-- T26(b): one edge {1,2} and an isolated third vertex. -/
def edge12 : Graph 3 :=
  ⟨![![false,true,false], ![true,false,false], ![false,false,false]], by
    constructor
    · intro i j; fin_cases i <;> fin_cases j <;> decide
    · intro i; fin_cases i <;> decide⟩

/-- T23(c): the unique optimum is the single edge {2,3}. -/
def edge23 : Graph 3 :=
  ⟨![![false,false,false], ![false,false,true], ![false,true,false]], by
    constructor
    · intro i j; fin_cases i <;> fin_cases j <;> decide
    · intro i; fin_cases i <;> decide⟩

/-- T23(a),(b),(d): explicit nonzero products force an infeasible triangle;
zero product on a mandatory edge forces its exclusion. All observations and
bounds are explicit, and the refuted conclusion is program feasibility. -/
theorem printed_variables_counterexample :
    average (![-2,1/2,3/2] : Fin 3 → ℝ) = 0 ∧
    (centered (![-2,1/2,3/2] : Fin 3 → ℝ) 0 * centered (![-2,1/2,3/2] : Fin 3 → ℝ) 1 = -1) ∧
    (centered (![-2,1/2,3/2] : Fin 3 → ℝ) 0 * centered (![-2,1/2,3/2] : Fin 3 → ℝ) 2 = -3) ∧
    (centered (![-2,1/2,3/2] : Fin 3 → ℝ) 1 * centered (![-2,1/2,3/2] : Fin 3 → ℝ) 2 = 3/4) ∧
    ¬ Compatible (emptyGraph 3) (fun _ => 1) (nonzeroRule (![-2,1/2,3/2] : Fin 3 → ℝ)) ∧
    Compatible (emptyGraph 3) (fun _ => 1) edge23 ∧
    upperSum (fun i j => centered (![-2,1/2,3/2] : Fin 3 → ℝ) i*
      centered (![-2,1/2,3/2] : Fin 3 → ℝ) j*adjacency edge23 i j) = 3/4 ∧
    ¬ Compatible edge12 (fun _ => 2) (nonzeroRule (![0,1,-1] : Fin 3 → ℝ)) := by
  norm_num [average, centered, Compatible, degree, adjacency, emptyGraph,
    nonzeroRule, fromUpper, edge12, edge23, upperSum, Finset.sum_filter, Fin.sum_univ_succ, Fin.forall_fin_succ]

/-- Definition 1, p. 2240: auxiliary enumeration of every three-vertex simple
graph by its three independent unordered-edge bits. -/
def threeGraph (b01 b02 b12 : Bool) : Graph 3 :=
  ⟨![![false,b01,b02],![b01,false,b12],![b02,b12,false]], by
    constructor
    · intro i j; fin_cases i <;> fin_cases j <;> rfl
    · intro i; fin_cases i <;> rfl⟩

/-- T23 finite graph certificate: the three upper edge bits determine the
whole symmetric zero-diagonal three-by-three adjacency matrix. -/
theorem graph_three_cases (A : Graph 3) :
    A=threeGraph (A.val 0 1) (A.val 0 2) (A.val 1 2) := by
  apply Subtype.ext
  funext i j
  fin_cases i <;> fin_cases j <;> simp [threeGraph,A.property.2] <;> exact A.property.1 _ _

/-- T23(c): the single-edge solution is the unique optimum of (3.6).
This additional optimization claim is separate from the proved infeasibility witness. -/
theorem printed_variables_optimum (A : Graph 3) (hA : Compatible (emptyGraph 3) (fun _ => 1) A) :
    upperSum (fun i j => centered (![-2,1/2,3/2] : Fin 3 → ℝ) i*
      centered (![-2,1/2,3/2] : Fin 3 → ℝ) j*adjacency A i j) ≤ 3/4 ∧
    (upperSum (fun i j => centered (![-2,1/2,3/2] : Fin 3 → ℝ) i*
      centered (![-2,1/2,3/2] : Fin 3 → ℝ) j*adjacency A i j) = 3/4 → A=edge23) := by
  rw [graph_three_cases A] at hA ⊢
  cases h01 : A.val 0 1 <;> cases h02 : A.val 0 2 <;> cases h12 : A.val 1 2
  all_goals norm_num [threeGraph,Compatible,degree,adjacency,emptyGraph,average,
    centered,upperSum,edge23,Finset.sum_filter,Fin.sum_univ_succ,Fin.forall_fin_succ,h01,h02,h12] at hA
  all_goals norm_num [threeGraph,Compatible,degree,adjacency,emptyGraph,average,
    centered,upperSum,edge23,Finset.sum_filter,Fin.sum_univ_succ,Fin.forall_fin_succ,h01,h02,h12]

/-- T24: program (3.5)/(3.8) uses element-wise ≤ and ≥. -/
def ProgramFeasible {n : ℕ} (R : Graph n) (d : Fin n → ℕ) (A : Graph n) : Prop :=
  (∀ i, (∑ j, adjacency A i j) ≤ d i) ∧ (∀ i j, adjacency R i j ≤ adjacency A i j)


/-- Finite row-sum identity used in Definition 4 and Lemma 1. -/
theorem degree_row_sum {n : ℕ} (A : Graph n) (i : Fin n) :
    (degree A i : ℝ)=∑ j, adjacency A i j := by
  simp [degree, adjacency, Nat.cast_sum]

/-- Every simple graph on n vertices has observed degree at most n−1. -/
theorem simple_degree_bound {n : ℕ} (A : Graph n) (i : Fin n) : degree A i ≤ n-1 := by
  classical
  let f : Fin n → ℕ := fun j => if A.val i j then 1 else 0
  have hf : f i=0 := by simp [f,A.property.2]
  have he := Finset.sum_erase_add (s:=Finset.univ) f (Finset.mem_univ i)
  have hsum : degree A i=∑ j ∈ Finset.univ.erase i, f j := by
    simpa [hf,degree,f] using he.symm
  rw [hsum]
  calc
    _ ≤ ∑ j ∈ Finset.univ.erase i, 1 := Finset.sum_le_sum (fun j hj => by
      dsimp [f]; split <;> omega)
    _ = n-1 := by simp

/-- Valid candidate degrees are at most the truncated supplied caps. -/
theorem compatible_truncated_degree {n : ℕ} (R A : Graph n) (d : Fin n → ℕ)
    (hA : Compatible R d A) (i : Fin n) : degree A i ≤ truncatedDegree d i := by
  exact le_min (hA.2 i) (simple_degree_bound A i)

/-- T24(i): the corrected numeric feasibility condition is exactly Definition 4
and contains the true observed adjacency matrix under valid constraints. -/
theorem corrected_notation {n : ℕ} (R G : Graph n) (d : Fin n → ℕ)
    (hv : Compatible R d G) :
    (∀ A, ProgramFeasible R d A ↔ Compatible R d A) ∧ ProgramFeasible R d G := by
  have hiff (A : Graph n) : ProgramFeasible R d A ↔ Compatible R d A := by
    constructor
    · rintro ⟨hrow,hforce⟩
      constructor
      · intro i j hR
        have hh := hforce i j
        cases hA : A.val i j
        · norm_num [adjacency,hR,hA] at hh
        · rfl
      · intro i
        have hh := hrow i
        rw [← degree_row_sum] at hh
        exact_mod_cast hh
    · rintro ⟨hforce,hrow⟩
      constructor
      · intro i
        rw [← degree_row_sum]
        exact_mod_cast hrow i
      · intro i j
        cases hR : R.val i j
        · cases hA : A.val i j <;> norm_num [adjacency,hR,hA]
        · have hA := hforce i j hR
          norm_num [adjacency,hR,hA]
  exact ⟨hiff,(hiff G).mpr hv⟩

/-- T25: the staged V1 helper uses R's n−1 sample-variance divisor on the
first term only (R/depvar.r line 11), retaining the paper's edge term. -/
def V1R {n : ℕ} (A : Graph n) (x : Fin n → ℝ) : ℝ :=
  (∑ i, centered x i^2)/((n : ℝ)*((n : ℝ)-1)) + quadratic (adjacency A) (centered x)/(n : ℝ)^2

/-- T25: staged V2 helper (line 19), rescaling all of equation (3.7). -/
def V2R {n : ℕ} (A : Graph n) (x : Fin n → ℝ) : ℝ :=
  (∑ i, centered x i^2)/((n : ℝ)*((n : ℝ)-1))*(1+(∑ i, ∑ j, adjacency A i j)/n)

/-- T25: staged V2′ helper (line 27), rescaling all of equation (3.9). -/
def V2primeR {n : ℕ} (d : Fin n → ℕ) (x : Fin n → ℝ) : ℝ :=
  (∑ i, centered x i^2)/((n : ℝ)*((n : ℝ)-1))*(1+(∑ i, (truncatedDegree d i : ℝ))/n)

/-- T25(i),(ii): exact general denominator identities. -/
theorem helper_denominators {n : ℕ} (hn : 1 < n) (A : Graph n) (d : Fin n → ℕ) (x : Fin n → ℝ) :
    V1R A x-V1 A x = (∑ i, centered x i^2)/((n : ℝ)^2*((n : ℝ)-1)) ∧
    V1R A x-V1 A x = sampleVariance x/((n : ℝ)*((n : ℝ)-1)) ∧
    V2R A x = (n : ℝ)/((n : ℝ)-1)*V2 A x ∧ V2primeR d x = (n : ℝ)/((n : ℝ)-1)*V2prime d x := by
  have h0 : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have h1 : (n : ℝ)-1 ≠ 0 := by
    have hlt : (1 : ℝ)<n := by exact_mod_cast hn
    linarith
  dsimp [V1R, V1, V2R, V2, V2primeR, V2prime, sampleVariance]
  constructor
  · field_simp [h0,h1]; ring
  constructor
  · field_simp [h0,h1]; ring
  constructor <;> field_simp [h0,h1] <;> ring

/-- T26(a)–(c): exact helper-versus-paper numerical counterexamples. The graph
constraints are satisfied on each explicitly given observation vector. -/
theorem helper_counterexamples :
    (let x : Fin 3 → ℝ := ![0,1,2]
     Compatible (emptyGraph 3) (fun _ => 0) (emptyGraph 3) ∧
     average x=1 ∧ (∑ i, centered x i^2)=2 ∧
     V1 (emptyGraph 3) x=2/9 ∧ V2 (emptyGraph 3) x=2/9 ∧ V2prime (fun _ => 0) x=2/9 ∧
     V1R (emptyGraph 3) x=1/3 ∧ V2R (emptyGraph 3) x=1/3 ∧ V2primeR (fun _ => 0) x=1/3 ∧
     V1 (emptyGraph 3) x ≠ V1R (emptyGraph 3) x ∧
     V2 (emptyGraph 3) x ≠ V2R (emptyGraph 3) x ∧
     V2prime (fun _ => 0) x ≠ V2primeR (fun _ => 0) x) ∧
    (let x : Fin 3 → ℝ := ![0,0,3]
     let d : Fin 3 → ℕ := ![1,1,0]
     Compatible (emptyGraph 3) d edge12 ∧ average x=1 ∧ (∑ i, centered x i^2)=6 ∧
     V1 edge12 x=8/9 ∧ V2 edge12 x=10/9 ∧ V2prime d x=10/9 ∧
     V1R edge12 x=11/9 ∧ V2R edge12 x=5/3 ∧ V2primeR d x=5/3 ∧
     V1 edge12 x ≠ V1R edge12 x ∧ V2 edge12 x ≠ V2R edge12 x ∧
     V2prime d x ≠ V2primeR d x) ∧
    (let x : Fin 3 → ℝ := ![0,1,2]
     Compatible (emptyGraph 3) (fun _ => 2) (completeGraph 3) ∧
     V1 (completeGraph 3) x=0 ∧ V1R (completeGraph 3) x=1/9 ∧
     V1 (completeGraph 3) x ≠ V1R (completeGraph 3) x) := by
  norm_num [V1, V2, V2prime, V1R, V2R, V2primeR, sampleVariance, centered, average,
    quadratic, adjacency, degree, truncatedDegree, Compatible, emptyGraph, edge12,
    completeGraph, Fin.sum_univ_succ, Fin.forall_fin_succ]

/-- T26(d): independent raw outcomes uniform on {0,1,2}, θ=1, edgeless graph. -/
def threePointModel (n : ℕ) : Model n where
  law := uniformLaw (fun u : Fin n → Fin 3 => fun i => ((u i).val : ℝ))
  probability := by dsimp [uniformLaw]; infer_instance
  theta := fun _ => 1
  G := emptyGraph n
  R := emptyGraph n
  d := fun _ => 0

/- T26(d): the witness triple has positive probability 1/27 under a model with
β=1 and n Var(β̂)=2/3, so it is admissible statistical data. -/
/- The unchanged helper_witness_law contract is proved in P011_ThreePointCompletion.lean. -/


/-- T27(a),(b): a maximum exists over the finite nonempty compatible family;
it dominates the oracle sharply, with equality when the oracle also maximizes.
The result bounds the oracle statistic, not the true variance. -/
theorem oracle_sharp_bound {n : ℕ} (R G : Graph n) (d : Fin n → ℕ)
    (hv : Compatible R d G) (f : Graph n → ℝ) :
    (∃ A, Maximizes R d f A) ∧
    (∀ A, Maximizes R d f A → f G ≤ f A ∧ (Maximizes R d f G → f G=f A)) := by
  classical
  let S : Finset (Graph n) := Finset.univ.filter (Compatible R d)
  have hS : S.Nonempty := ⟨G, by simp [S,hv]⟩
  obtain ⟨A,hA,hmax⟩ := Finset.exists_max_image S f hS
  constructor
  · refine ⟨A, ?_, ?_⟩
    · simpa [S] using hA
    · intro B hB
      exact hmax B (by simp [S,hB])
  · intro A hA
    exact ⟨hA.2 G hv, fun hG => le_antisymm (hA.2 G hv) (hG.2 A hA.1)⟩

/-- T28: Lemma 1, p. 2247; its oracle ≤ maximum ≤ closed bound, with equality
when every truncated degree is attained. No asymptotics or homoskedasticity premise. -/
theorem lemma_one {n : ℕ} (hn : 0 < n) (R G A : Graph n) (d : Fin n → ℕ)
    (hv : Compatible R d G) (x : Fin n → ℝ)
    (hm : Maximizes R d (fun B => V2 B x) A) :
    V2 G x ≤ V2 A x ∧ V2 A x ≤ V2prime d x ∧
    ((∀ i, degree A i = truncatedDegree d i) → V2 A x=V2prime d x) := by
  have hσ : 0 ≤ sampleVariance x := by unfold sampleVariance; positivity
  have hcoeff : 0 ≤ sampleVariance x/(n : ℝ) := div_nonneg hσ (Nat.cast_nonneg _)
  have hsum : (∑ i, ∑ j, adjacency A i j) ≤ ∑ i, (truncatedDegree d i : ℝ) := by
    apply Finset.sum_le_sum
    intro i hi
    rw [← degree_row_sum]
    exact_mod_cast compatible_truncated_degree R A d hm.1 i
  refine ⟨hm.2 G hv, ?_, ?_⟩
  · unfold V2 V2prime
    exact mul_le_mul_of_nonneg_left
      (add_le_add_right (div_le_div_of_nonneg_right hsum (Nat.cast_nonneg n)) 1) hcoeff
  · intro hdeg
    have heq : (∑ i, ∑ j, adjacency A i j)=∑ i, (truncatedDegree d i : ℝ) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [← degree_row_sum,hdeg i]
    unfold V2 V2prime
    rw [heq]

/-- T29(c): exact variance of any linear estimator, with fixed coefficients
and finite second moments. Covariances are of raw outcomes and double sums ordered. -/
theorem linear_variance_identity {n : ℕ} (hn : 0 < n) (m : Model n)
    (hL2 : ∀ i, MemLp (fun y => y i) 2 m.law) :
    var m (betaHat m) = (∑ i, ∑ j, m.theta i*m.theta j*
      covOf m (fun y => y i) (fun y => y j))/(n : ℝ)^2 := by
  letI : IsProbabilityMeasure m.law := m.probability
  have hx (i : Fin n) : MemLp (fun y => m.theta i*y i) 2 m.law :=
    (hL2 i).const_mul (m.theta i)
  have hsum : MemLp (fun y => ∑ i, m.theta i*y i) 2 m.law :=
    by simpa using memLp_finsetSum Finset.univ (fun i hi => hx i)
  have hb : MemLp (betaHat m) 2 m.law := by
    change MemLp (fun y => (∑ i, m.theta i*y i)/(n : ℝ)) 2 m.law
    simpa only [div_eq_mul_inv,mul_comm] using hsum.const_mul (n : ℝ)⁻¹
  unfold var expectation
  rw [← ProbabilityTheory.variance_eq_integral hb.aemeasurable]
  change ProbabilityTheory.variance (fun y => (∑ i, m.theta i*y i)/(n : ℝ)) m.law = _
  simp only [div_eq_mul_inv]
  rw [ProbabilityTheory.variance_mul_const, ProbabilityTheory.variance_fun_sum hx]
  have hc (i j : Fin n) : ProbabilityTheory.covariance (fun y => y i) (fun y => y j) m.law =
      covOf m (fun y => y i) (fun y => y j) := by
    exact ProbabilityTheory.covariance_eq_sub (hL2 i) (hL2 j)
  simp only [ProbabilityTheory.covariance_const_mul_left,
    ProbabilityTheory.covariance_const_mul_right, hc, inv_pow]
  simp only [mul_assoc,mul_left_comm,mul_comm]

/-- T29(a),(b): OLS coefficients have the paper's linear representation and
are unbiased under E[Y]=Xb, independently of identical distribution or independence. -/
theorem ols_linear_unbiased {n p : ℕ} (hn : 0 < n) (m : Model n)
    (D : Matrix (Fin n) (Fin p) ℝ) (b : Fin p → ℝ) (hrank : (Dᵀ*D).det ≠ 0)
    (hmean : MeanModel m D b) :
    (∀ j y, ols D y j = (∑ i, olsTheta D j i*y i)/(n : ℝ)) ∧
    (∀ j, expectation m (fun y => ols D y j) = b j) := by
  let C := (Dᵀ*D)⁻¹*Dᵀ
  have h0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hc (j : Fin p) (y : Fin n → ℝ) : ols D y j=∑ i, C j i*y i := by
    change (((Dᵀ*D)⁻¹ *ᵥ (Dᵀ*ᵥy)) j)=(C*ᵥy) j
    rw [Matrix.mulVec_mulVec]
  constructor
  · intro j y
    rw [hc]
    simp only [olsTheta,Matrix.smul_apply,smul_eq_mul]
    simp_rw [mul_assoc,← Finset.mul_sum]
    change (∑ i, C j i*y i)=(n : ℝ)*(∑ i, C j i*y i)/(n : ℝ)
    field_simp [h0] <;> ring
  · intro j
    unfold expectation
    simp_rw [hc]
    rw [integral_finsetSum Finset.univ (fun i hi => (hmean.1 i).const_mul (C j i))]
    simp_rw [integral_const_mul]
    have he (i : Fin n) : (∫ y, y i ∂m.law)=(D*ᵥb) i := hmean.2 i
    simp_rw [he]
    change (C*ᵥ(D*ᵥb)) j=b j
    rw [Matrix.mulVec_mulVec]
    have hCD : C*D=1 := by
      dsimp [C]
      rw [Matrix.mul_assoc]
      exact Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hrank)
    rw [hCD,Matrix.one_mulVec]

/-- T31: Proposition 1 exactly as printed, without a unit-mean condition.
This is a false claim retained as an unproved draft, not an axiom or a correction. -/
theorem printed_proposition_one (F : Family) (c1 c2 c3 c4 : ℝ) (h : Scaling F c1 c2 c3 c4) :
    InProbability F (scaledOracle F) (scaledTrue F) := by
  sorry

/-- T32: printed Corollary 1 and its homoskedastic specialization on p. 2246.
Both are false under these hypotheses; no mean condition or empty-edge condition
is inserted into the printed statement. -/
theorem printed_corollary_one (F : Family) (c1 c2 c3 c4 : ℝ) (h : Scaling F c1 c2 c3 c4)
    (hv : Valid F) (A : ∀ k, (Fin (F.size k) → ℝ) → Graph (F.size k))
    (hm : ∀ k y, Maximizes (F.model k).R (F.model k).d
      (fun B => V1 B (weighted (F.model k) y)) (A k y)) :
    Conservative F (fun k y => V1 (A k y) (weighted (F.model k) y)) ∧
    ((∀ k, Homoskedastic (F.model k)) → Conservative F
      (fun k y => V1 (A k y) (weighted (F.model k) y))) := by
  sorry

/-- T32 finite step (A.1): domination gives the event inclusion, regardless
of whether the oracle has a correct statistical limit. -/
theorem underestimation_event_inclusion {Ω : Type} (a n ε : ℝ) (hn : 0 ≤ n)
    (V W : Ω → ℝ) (hVW : ∀ y, V y ≤ W y) :
    {y | n*(a-W y)>ε} ⊆ {y | n*(a-V y)>ε} := by
  intro y hy
  have h := mul_le_mul_of_nonneg_left (hVW y) hn
  dsimp at *
  nlinarith

/-- T33: printed Corollary 3, without additional hypotheses on means or known
edges. The printed interval must be defined to cover β; negative-estimate
realizations are explicitly undefined and uncovered, without clipping V1. -/
theorem printed_corollary_three (F : Family) (c1 c2 c3 c4 : ℝ) (h : Scaling F c1 c2 c3 c4)
    (hv : Valid F) (A : ∀ k, (Fin (F.size k) → ℝ) → Graph (F.size k))
    (hm : ∀ k y, Maximizes (F.model k).R (F.model k).d
      (fun B => V1 B (weighted (F.model k) y)) (A k y)) :
    PrintedConservativeCoverage F (fun k y => V1 (A k y) (weighted (F.model k) y)) := by
  sorry

/-- T34(P3): the unambiguous printed proof step "By Assumption 2,
1 ≤ 1 + n⁻¹∑ Aᵒ_ij ≤ 1+c₂", p. 2246. The undefined rho_i and the
unspecified mean-square centre of the other proof steps are not substituted. -/
theorem printed_auxiliary_degree_bound (F : Family) (c1 c2 c3 c4 : ℝ)
    (h : Scaling F c1 c2 c3 c4) (k : ℕ) :
    1 ≤ gFactor (F.model k) ∧ gFactor (F.model k) ≤ 1+c2 := by
  rcases h with ⟨hnest,h1,h2,h3,h4,hdep,hbound,hdeg,hlim,hθ⟩
  have hn : (0 : ℝ)<F.size k := by exact_mod_cast F.positive k
  have ha (i j : Fin (F.size k)) : 0 ≤ adjacency (F.model k).G i j := by
    unfold adjacency; split <;> norm_num
  have hs : (∑ i, ∑ j, adjacency (F.model k).G i j) ≤ (F.size k : ℝ)*c2 := by
    calc
      _ ≤ ∑ i : Fin (F.size k), c2 := Finset.sum_le_sum (fun i hi => by
        rw [← degree_row_sum]
        exact hdeg k i)
      _ = _ := by simp [nsmul_eq_mul]
  unfold gFactor
  constructor
  · have hsum : 0 ≤ ∑ i, ∑ j, adjacency (F.model k).G i j :=
      Finset.sum_nonneg (fun i hi => Finset.sum_nonneg (fun j hj => ha i j))
    have hd := div_nonneg hsum hn.le
    linarith
  · have hd : (∑ i, ∑ j, adjacency (F.model k).G i j)/(F.size k : ℝ) ≤ c2 :=
      (div_le_iff₀ hn).mpr (by simpa [mul_comm] using hs)
    linarith

/-- T35: the package's formal generic OLS guarantee, under exactly the paper's
Assumption 2 and a correctly specified linear mean model. False as asserted. -/
theorem printed_package_ols_guarantee (F : Family) (c1 c2 c3 c4 : ℝ)
    (h : Scaling F c1 c2 c3 c4) (hv : Valid F) (p : ℕ) (j : Fin p)
    (D : ∀ k, Matrix (Fin (F.size k)) (Fin p) ℝ) (b : Fin p → ℝ)
    (hrank : ∀ k, ((D k)ᵀ*D k).det ≠ 0) (hmean : ∀ k, MeanModel (F.model k) (D k) b)
    (hθ : ∀ k i, (F.model k).theta i=olsTheta (D k) j i)
    (A : ∀ k, (Fin (F.size k) → ℝ) → Graph (F.size k))
    (hm : ∀ k y, Maximizes (F.model k).R (F.model k).d
      (fun B => V1 B (weighted (F.model k) y)) (A k y)) :
    Conservative F (fun k y => V1 (A k y) (weighted (F.model k) y)) ∧
    PrintedConservativeCoverage F (fun k y => V1 (A k y) (weighted (F.model k) y)) := by
  sorry

/- T36: Proposition 2 as printed, p. 2246. The finite-rate repaired proof is
homoskedastic_repair (T12); its unproved dependency remains visible in the axioms. -/
/- The unchanged proposition_two contract is proved in P011_HomoskedasticCompletion.lean. -/

/- T37: Corollary 2 exactly as printed, p. 2247. Supplied degree bounds are
not required to be bounded; valid constraints and maximality suffice. -/
/- The unchanged corollary_two contract is proved in P011_CorollariesCompletion.lean. -/

/-- T38: the standardized estimator of Lemma 2. Zero-variance early terms use
Lean's division convention; Assumption 2 makes the denominator eventually positive. -/
def standardized {n : ℕ} (m : Model n) (y : Fin n → ℝ) : ℝ :=
  (betaHat m y-beta m)/Real.sqrt (var m (betaHat m))

/- T38: The unchanged dependency_graph_clt contract is proved in
P011_ProbabilityCompletion.lean by an audited dependency-graph CLT. -/

/-- T38 finite normalized summands ζᵢ use each unit's own mean. -/
def zeta {n : ℕ} (m : Model n) (i : Fin n) (y : Fin n → ℝ) : ℝ :=
  (weighted m y i-expectation m (fun z => weighted m z i))/
    ((n : ℝ)*Real.sqrt (var m (betaHat m)))

/- T38: The unchanged clt_finite_normalization contract is proved in
P011_ProbabilityCompletion.lean from finite integrals and affine independence. -/

/- T39: The unchanged conditional_wald_coverage contract is proved in
P011_CoverageCompletion.lean using the proved CLT, varying-law CDF squeeze,
variance-limit algebra and the original truncation argument. -/

/-- T39 finite step: U=min(V,v) has n-scaled absolute discrepancy equal to
the positive part of the n-scaled underestimation; V≥U in every realization. -/
theorem truncation_identity (n v V : ℝ) (hn : 0 ≤ n) :
    |n*min V v-n*v|=max (n*v-n*V) 0 ∧ min V v ≤ V := by
  by_cases h : V ≤ v
  · rw [min_eq_left h, abs_of_nonpos (by nlinarith), max_eq_left (by nlinarith)]
    constructor <;> linarith
  · have h' : v ≤ V := le_of_not_ge h
    rw [min_eq_right h']
    simp only [sub_self, abs_zero]
    rw [max_eq_right (by nlinarith)]
    exact ⟨rfl,h'⟩

/-- T8,T39: the well-defined comparison U=min(max(T,0),c) satisfies
0≤c−U≤(c−T)_+ for c≥0, exactly the repaired coverage argument. -/
theorem clipped_truncation (c T : ℝ) (hc : 0 ≤ c) :
    0 ≤ c-min (max T 0) c ∧ c-min (max T 0) c ≤ max (c-T) 0 := by
  constructor
  · exact sub_nonneg.mpr (min_le_right _ _)
  · by_cases hT : T ≤ 0
    · rw [max_eq_right hT, min_eq_left hc, max_eq_left (by linarith)]
      linarith
    · rw [max_eq_left (le_of_not_ge hT)]
      by_cases h : T ≤ c
      · rw [min_eq_left h, max_eq_left (by linarith)]
      · rw [min_eq_right (le_of_not_ge h), max_eq_right (by linarith)]
        simp

/-- T39 finite interval containment: larger nonnegative variance gives a wider
Wald interval, for any nonnegative normal critical value. -/
theorem interval_containment (a z U V : ℝ) (hz : 0 ≤ z) (hUV : U ≤ V)
    (ha : |a| ≤ z*Real.sqrt (max U 0)) : |a| ≤ z*Real.sqrt (max V 0) := by
  exact ha.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (max_le_max hUV le_rfl)) hz)

/- T40: Corollary 4, p. 2248, for the maximized V2 and the closed degree bound,
under exactly Assumptions 2 and 3 and valid constraints. -/
/- The unchanged corollary_four contract is proved in P011_CorollariesCompletion.lean. -/


/-- T1 finite enumeration: 16 equally likely states of the four independent
edge signs; bit r represents the sign on edge r. -/
def cycleSigns (u : Fin 16) (r : Fin 4) : ℝ :=
  if (u.val/2^r.val)%2=0 then -1 else 1

/-- T1 finite expectation is a weighted finite sum with weights 1/16. -/
def cycleMean (f : (Fin 4 → ℝ) → ℝ) : ℝ := (∑ u : Fin 16, f (cycleSigns u))/16

/-- T1 finite certificate: H Hᵀ=2I+A_cycle and the mean-direction quadratic
form is −4a². The covariance entries sum to 16. -/
theorem cycle_covariance_algebra (a : ℝ) :
    (let H : Matrix (Fin 4) (Fin 4) ℝ :=
      ![![1,0,0,1], ![1,1,0,0], ![0,1,1,0], ![0,0,1,1]]
     H*Hᵀ = (2 : ℝ) • (1 : Matrix (Fin 4) (Fin 4) ℝ)+adjacency cycleGraph) ∧
    quadratic (oracleMatrix cycleGraph) (![a,-a,a,-a] : Fin 4 → ℝ) = -4*a^2 ∧
    (∑ i, ∑ j, ((2 : ℝ) • (1 : Matrix (Fin 4) (Fin 4) ℝ)+adjacency cycleGraph) i j)=16 := by
  constructor
  · let H : Matrix (Fin 4) (Fin 4) ℝ :=
      ![![1,0,0,1], ![1,1,0,0], ![0,1,1,0], ![0,0,1,1]]
    change H*Hᵀ=(2 : ℝ) • (1 : Matrix (Fin 4) (Fin 4) ℝ)+adjacency cycleGraph
    ext i j
    change (∑ k : Fin 4, H i k*H j k)=2*(if i=j then 1 else 0)+adjacency cycleGraph i j
    fin_cases i <;> fin_cases j <;> norm_num [H,adjacency,cycleGraph,Fin.sum_univ_succ]
  constructor
  · norm_num [quadratic, oracleMatrix, adjacency, cycleGraph, Fin.sum_univ_succ,
      Matrix.add_apply, Matrix.of_apply, Pi.add_apply, Pi.sub_apply, Matrix.one_apply]
    <;> ring
  · norm_num [adjacency, cycleGraph, Fin.sum_univ_succ, Matrix.add_apply, Matrix.of_apply, Pi.add_apply, Pi.sub_apply, Matrix.one_apply]

/-- T1 finite certificate: E[q]=16−4a², Var(q)=176 at a=3/2, and the second
and fourth moments of a block's four shocks are 4 and 40. These are normalized
finite probability calculations, not assumed moment values. -/
theorem cycle_block_moments (a : ℝ) :
    cycleMean (fun u => quadratic (oracleMatrix cycleGraph) (cycleBlock a u)) = 16-4*a^2 ∧
    cycleMean (fun u => (quadratic (oracleMatrix cycleGraph) (cycleBlock (3/2) u)-7)^2)=176 ∧
    cycleMean (fun u => (∑ i, u i)^2)=4 ∧ cycleMean (fun u => (∑ i, u i)^4)=40 ∧
    cycleMean (fun u => quadratic (oracleMatrix cycleGraph) (cycleBlock (3/2) u)*(∑ i, u i)^2)=92 := by
  repeat' constructor
  all_goals (norm_num [cycleMean, cycleSigns, cycleBlock, quadratic, oracleMatrix, adjacency,
    cycleGraph, Matrix.add_apply, Matrix.of_apply, Pi.add_apply, Pi.sub_apply, Matrix.one_apply, Fin.sum_univ_succ] <;> ring)

/-- T1(g): the all-positive shock realization gives β̂=2, V̂₁=−9/4 at a=3.
It is one of the 16 equiprobable states in cycleMean. -/
theorem cycle_negative_realization :
    cycleBlock 3 (fun _ => 1)=(![5,-1,5,-1] : Fin 4 → ℝ) ∧
    average (![5,-1,5,-1] : Fin 4 → ℝ)=2 ∧
    V1 cycleGraph (![5,-1,5,-1] : Fin 4 → ℝ)=-9/4 := by
  norm_num [cycleBlock, average, V1, quadratic, centered, adjacency, cycleGraph, Fin.sum_univ_succ]

/-- T2 finite enumeration: four equiprobable independent (U,V) sign states. -/
def pathMean (f : ℝ → ℝ → ℝ) : ℝ := (f (-1) (-1)+f (-1) 1+f 1 (-1)+f 1 1)/4

/-- T2 finite block identities, with the covariance matrix and all moments of
S, L and Q specified in the target. No asymptotic or probability premise is assumed. -/
theorem path_block_moments (t : ℝ) :
    quadratic (oracleMatrix pathGraph) (![t,-2*t,t] : Fin 3 → ℝ)=-2*t^2 ∧
    pathMean (fun u v => ∑ i, pathBlock t u v i)=0 ∧
    pathMean (fun u v => (∑ i, pathBlock t u v i)^2)=29/5 ∧
    pathMean (fun u v => quadratic (oracleMatrix pathGraph) (pathBlock t u v))=29/5-2*t^2 ∧
    pathMean (fun u v => (quadratic (oracleMatrix pathGraph) (pathBlock t u v)-(29/5-2*t^2))^2)=
      8*t^2+8836/625 ∧
    pathMean (fun u v => (∑ i, pathBlock t u v i)*
      (∑ i, ∑ j, oracleMatrix pathGraph i j*pathBlock t u v j))=14 ∧
    quadratic (oracleMatrix pathGraph) (fun _ => 1)=7 := by
  repeat' constructor
  all_goals (norm_num [pathMean, pathBlock, quadratic, oracleMatrix, adjacency, pathGraph,
    Matrix.add_apply, Matrix.of_apply, Pi.add_apply, Pi.sub_apply, Matrix.one_apply, Fin.sum_univ_succ] <;> ring)

/-- T15(c),(e): exact mean quadratic terms on the forced stars; their signs
exhibit why the raw-outcome bias can point in either direction. -/
theorem star_mean_terms :
    quadratic (oracleMatrix starGraph) (![3/8,-1/8,-1/8,-1/8] : Fin 4 → ℝ)=-3/32 ∧
    quadratic (oracleMatrix starGraph) (![0,1/4,-1/4,0] : Fin 4 → ℝ)=1/8 := by
  norm_num [quadratic, oracleMatrix, adjacency, starGraph, Matrix.add_apply,
    Matrix.one_apply, Fin.sum_univ_succ]

/-- T6(d): the four-cycle has an explicit rational orthonormal eigenbasis.
Clipping only the eigenvalue −1 gives the displayed PSD candidate. -/
def cycleEigenvectors : Matrix (Fin 4) (Fin 4) ℝ :=
  ![![1/2,1/2,1/2,1/2], ![1/2,1/2,-1/2,-1/2],
    ![1/2,-1/2,-1/2,1/2], ![1/2,-1/2,1/2,-1/2]]

/-- T6(d): clipped cycle matrix computed from the explicit orthonormal basis. -/
def cycleClipped : Matrix (Fin 4) (Fin 4) ℝ :=
  cycleEigenvectors*Matrix.diagonal (![3,1,1,0] : Fin 4 → ℝ)*cycleEigenvectorsᵀ

/-- T6(d): the clipped cycle's exact entries, obtained by ordinary matrix
multiplication in its displayed orthonormal eigenbasis. -/
theorem cycle_clipped_entries (i j : Fin 4) :
    cycleClipped i j =
      (∑ k : Fin 4, (∑ l : Fin 4, cycleEigenvectors i l *
        (if l=k then (![3,1,1,0] : Fin 4 → ℝ) l else 0))*cycleEigenvectors j k) := by
  rfl

/-- T6(d): exact spectral decomposition certificates, using rational entries. -/
theorem cycle_spectral_certificate :
    cycleEigenvectorsᵀ*cycleEigenvectors=1 ∧
    oracleMatrix cycleGraph=cycleEigenvectors*Matrix.diagonal (![3,1,1,-1] : Fin 4 → ℝ)*cycleEigenvectorsᵀ ∧
    (∀ x, quadratic cycleClipped x=quadratic (oracleMatrix cycleGraph) x+(x 0-x 1+x 2-x 3)^2/4) := by
  constructor
  · ext i j
    change (∑ k : Fin 4, cycleEigenvectors k i*cycleEigenvectors k j)=(if i=j then 1 else 0)
    fin_cases i <;> fin_cases j <;> norm_num [cycleEigenvectors,Fin.sum_univ_succ]
  constructor
  · ext i j
    change (if i=j then 1 else 0)+adjacency cycleGraph i j =
      ∑ k : Fin 4, (∑ l : Fin 4, cycleEigenvectors i l *
        (if l=k then (![3,1,1,-1] : Fin 4 → ℝ) l else 0))*cycleEigenvectors j k
    fin_cases i <;> fin_cases j <;> norm_num [cycleEigenvectors,adjacency,cycleGraph,Fin.sum_univ_succ]
  · intro x
    have hS (i j : Fin 4) : oracleMatrix cycleGraph i j=
        (if i=j then 1 else 0)+adjacency cycleGraph i j := rfl
    simp only [quadratic,cycle_clipped_entries,hS]
    norm_num [cycleEigenvectors,adjacency,cycleGraph,Fin.sum_univ_succ]
    <;> ring

/-- T6(c): PSD majorants are not ordered by the clipped matrix. Both M and M−S
are PSD, yet at δ=(0,1,−1,0) the quadratic value is 3/5 versus clipping's 1.
Identifying this candidate with Mathlib's positivePart remains a separate draft. -/
theorem cycle_majorant_certificate :
    PSD cycleMajorantDifference ∧ PSD (oracleMatrix cycleGraph+cycleMajorantDifference) ∧
    quadratic (oracleMatrix cycleGraph+cycleMajorantDifference) (![0,1,-1,0] : Fin 4 → ℝ)=3/5 ∧
    quadratic cycleClipped (![0,1,-1,0] : Fin 4 → ℝ)=1 := by
  have hm (i j : Fin 4) : (oracleMatrix cycleGraph+cycleMajorantDifference) i j=
      (if i=j then 1 else 0)+adjacency cycleGraph i j+cycleMajorantDifference i j := rfl
  have hN (x : Fin 4 → ℝ) : quadratic cycleMajorantDifference x =
      17/20*((x 0-x 3)-5/17*(x 1-x 2))^2+13/170*(x 1-x 2)^2 := by
    norm_num [quadratic, cycleMajorantDifference, Fin.sum_univ_succ]
    <;> ring
  have hM (x : Fin 4 → ℝ) : quadratic (oracleMatrix cycleGraph+cycleMajorantDifference) x =
      3/4*(x 0+x 1+x 2+x 3)^2+1/4*(x 0-x 1-x 2+x 3)^2+
      17/20*((x 0-x 3)+5/17*(x 1-x 2))^2+13/170*(x 1-x 2)^2 := by
    simp only [quadratic,hm]
    norm_num [cycleMajorantDifference,adjacency,cycleGraph,Fin.sum_univ_succ]
    <;> ring
  constructor
  · constructor
    · intro i j; fin_cases i <;> fin_cases j <;> norm_num [cycleMajorantDifference]
    · intro x; rw [hN]; positivity
  constructor
  · constructor
    · intro i j; fin_cases i <;> fin_cases j <;>
        (simp only [hm] <;> norm_num [adjacency,cycleGraph,cycleMajorantDifference])
    · intro x; rw [hM]; positivity
  constructor
  · simp only [quadratic,hm]
    norm_num [adjacency,cycleGraph,cycleMajorantDifference,Fin.sum_univ_succ]
  · simp only [quadratic,cycle_clipped_entries]
    norm_num [cycleEigenvectors,Fin.sum_univ_succ]

/-- T12(iii): purely finite one-sided step of the repaired Proposition 2 proof.
A nonnegative mean-spread term helps the bound instead of being omitted. -/
theorem one_sided_algebra (v σ M R g c : ℝ) (hM : 0 ≤ M) (hg : 0 ≤ g)
    (hgc : g ≤ 1+c) (hv : v ≤ g*σ) : v-g*(σ+M+R) ≤ (1+c)*|R| := by
  have h1 : 0 ≤ g*M := mul_nonneg hg hM
  have h2 : -R ≤ |R| := neg_le_abs R
  have h3 := mul_le_mul_of_nonneg_left h2 hg
  have h4 := mul_le_mul_of_nonneg_right hgc (abs_nonneg R)
  nlinarith

/-- Equation (3.1): empirical variance is nonnegative for every observation. -/
theorem sample_variance_nonnegative {n : ℕ} (x : Fin n → ℝ) : 0 ≤ sampleVariance x := by
  unfold sampleVariance
  positivity

/-- T40 finite lemma: the homoskedastic estimators (3.7),(3.9) are always
nonnegative, so their printed square roots need no additional condition. -/
theorem homoskedastic_estimators_nonnegative {n : ℕ} (A : Graph n) (d : Fin n → ℕ) (x : Fin n → ℝ) :
    0 ≤ V2 A x ∧ 0 ≤ V2prime d x := by
  have ha : ∀ i j, 0 ≤ adjacency A i j := by intro i j; unfold adjacency; split <;> norm_num
  have hs := sample_variance_nonnegative x
  have hsum : 0 ≤ ∑ i, ∑ j, adjacency A i j :=
    Finset.sum_nonneg (fun i hi => Finset.sum_nonneg (fun j hj => ha i j))
  unfold V2 V2prime
  constructor <;> apply mul_nonneg (div_nonneg hs (Nat.cast_nonneg n))
  · exact add_nonneg (by norm_num) (div_nonneg hsum (Nat.cast_nonneg n))
  · positivity


/-- T30(C1): the valid multidimensional-knapsack encoding has one resource
coordinate per vertex and incidence 1 at precisely the two endpoints. This
encoding alone says nothing about the hardness of this special case. -/
def KnapsackEncoded {n : ℕ} (P : DegreeProblem n) (S : Finset (Edge n)) : Prop :=
  P.forced ⊆ S ∧ ∀ i, (∑ e ∈ S, if e.val.1=i ∨ e.val.2=i then (1 : ℕ) else 0) ≤ P.cap i

/-- T30(C1): the two-endpoint incidence knapsack encoding is exact. -/
theorem knapsack_encoding {n : ℕ} (P : DegreeProblem n) (S : Finset (Edge n)) :
    KnapsackEncoded P S ↔ EdgeFeasible P S := by
  simp [KnapsackEncoded,EdgeFeasible,edgeDegree,Finset.sum_boole]


/-- T17 finite expectation algebra: the complete corrected (3.3) for any linear
expectation on its moment functions. It applies in particular to every weighted
finite probability space; no special distribution or equal means are assumed. -/
theorem covariance_expansion_linear {Ω : Type} (E : (Ω → ℝ) →ₗ[ℝ] ℝ)
    (yi yj yk yl B : Ω → ℝ) (ti tj tk tl : ℝ) :
    E (fun y => ((ti*yi y-B y)*(tj*yj y-B y))*((tk*yk y-B y)*(tl*yl y-B y))) -
      E (fun y => (ti*yi y-B y)*(tj*yj y-B y))*E (fun y => (tk*yk y-B y)*(tl*yl y-B y)) =
      fourthMoment E (fun y => ti*yi y) (fun y => tj*yj y) (fun y => tk*yk y) (fun y => tl*yl y) B -
        pairMoment E yi yj B ti tj*pairMoment E yk yl B tk tl := by
  have hp (f g : Ω → ℝ) (a b : ℝ) :
      E (fun y => (a*f y-B y)*(b*g y-B y))=pairMoment E f g B a b := by
    have hh : (fun y => (a*f y-B y)*(b*g y-B y)) =
        (a*b) • (fun y => f y*g y) - a • (fun y => f y*B y) -
        b • (fun y => g y*B y)+(fun y => B y^2) := by
      ext y
      simp only [Pi.sub_apply,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
      ring
    rw [hh]
    simp only [map_add,map_sub,map_smul,smul_eq_mul]
    rfl
  have hq : (fun y => ((ti*yi y-B y)*(tj*yj y-B y))*((tk*yk y-B y)*(tl*yl y-B y))) =
      (fun y => ti*yi y*(tj*yj y)*(tk*yk y)*(tl*yl y)) -
      (fun y => B y*(ti*yi y*(tj*yj y)*(tk*yk y)+ti*yi y*(tj*yj y)*(tl*yl y)+
        ti*yi y*(tk*yk y)*(tl*yl y)+tj*yj y*(tk*yk y)*(tl*yl y))) +
      (fun y => B y^2*(ti*yi y*(tj*yj y)+ti*yi y*(tk*yk y)+ti*yi y*(tl*yl y)+
        tj*yj y*(tk*yk y)+tj*yj y*(tl*yl y)+tk*yk y*(tl*yl y))) -
      (fun y => B y^3*(ti*yi y+tj*yj y+tk*yk y+tl*yl y))+(fun y => B y^4) := by
    ext y
    simp only [Pi.sub_apply,Pi.add_apply]
    ring
  rw [hq,hp,hp]
  simp only [map_add,map_sub]
  rfl

/-- T1 finite variance algebra: the exact moment combination (D4) simplifies
to 44/n−96/n²−288/n³ at every positive n. The block moment inputs themselves
are separately proved in cycle_block_moments, not assumed by this algebra lemma. -/
theorem cycle_variance_formula (n : ℝ) (hn : n ≠ 0) :
    176*(n/4)/n^2 + 9*(32/n^2-32/n^3)-6*(64/n^2) = 44/n-96/n^2-288/n^3 := by
  field_simp [hn]
  ring


/-- T5,T7 finite graph bound: the absolute adjacency quadratic form is bounded
by the degree-weighted sum of squares. It needs no outcome distribution. -/
theorem adjacency_quadratic_bound {n : ℕ} (A : Graph n) (x : Fin n → ℝ) :
    |quadratic (adjacency A) x| ≤ ∑ i, (degree A i : ℝ)*x i^2 := by
  have ha (i j : Fin n) : 0 ≤ adjacency A i j := by
    unfold adjacency; split <;> norm_num
  have hs (i j : Fin n) : adjacency A i j=adjacency A j i := by
    unfold adjacency; rw [A.property.1 i j]
  have hr (i : Fin n) : (∑ j, adjacency A i j)=(degree A i : ℝ) :=
    (degree_row_sum A i).symm
  have hc (j : Fin n) : (∑ i, adjacency A i j)=(degree A j : ℝ) := by
    calc
      _ = ∑ i, adjacency A j i := Finset.sum_congr rfl (fun i hi => hs i j)
      _ = _ := hr j
  have h1 : (∑ i, ∑ j, adjacency A i j*x i^2)=∑ i, (degree A i : ℝ)*x i^2 := by
    simp_rw [← Finset.sum_mul,hr]
  have h2 : (∑ i, ∑ j, adjacency A i j*x j^2)=∑ i, (degree A i : ℝ)*x i^2 := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul,hc]
  have he : (∑ i, ∑ j, adjacency A i j*(x i^2+x j^2)/2)=
      ∑ i, (degree A i : ℝ)*x i^2 := by
    simp_rw [mul_add,add_div,Finset.sum_add_distrib,← Finset.sum_div]
    rw [h1,h2]
    ring
  apply abs_le.mpr
  constructor
  · have hh : (∑ i, ∑ j, -(adjacency A i j*(x i^2+x j^2)/2)) ≤
        quadratic (adjacency A) x := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      have hp := mul_nonneg (ha i j) (sq_nonneg (x i+x j))
      nlinarith
    simp only [Finset.sum_neg_distrib] at hh
    rwa [he] at hh
  · calc
      quadratic (adjacency A) x ≤ ∑ i, ∑ j, adjacency A i j*(x i^2+x j^2)/2 := by
        apply Finset.sum_le_sum
        intro i hi
        apply Finset.sum_le_sum
        intro j hj
        have hp := mul_nonneg (ha i j) (sq_nonneg (x i-x j))
        nlinarith
      _ = _ := he

/-- T5(a),(e): the Young degree bound dominates the printed quadratic estimate
for every compatible graph, including zero degrees and loose caps. -/
theorem young_bound_finite {n : ℕ} (R A : Graph n) (d : Fin n → ℕ)
    (hA : Compatible R d A) (x : Fin n → ℝ) : V1 A x ≤ VYoung d x := by
  have hq := (abs_le.mp (adjacency_quadratic_bound A (centered x))).2
  have hd : (∑ i, (degree A i : ℝ)*centered x i^2) ≤
      ∑ i, (truncatedDegree d i : ℝ)*centered x i^2 := by
    apply Finset.sum_le_sum
    intro i hi
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    exact_mod_cast compatible_truncated_degree R A d hA i
  unfold V1 VYoung
  apply div_le_div_of_nonneg_right _ (sq_nonneg _)
  simp only [add_mul,one_mul,Finset.sum_add_distrib]
  linarith


/-- T4,T5 finite algebra: quadratic forms distribute over matrix addition. -/
theorem quadratic_add {n : ℕ} (M N : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) :
    quadratic (M+N) x=quadratic M x+quadratic N x := by
  simp [quadratic,Matrix.add_apply,add_mul,Finset.sum_add_distrib]

/-- T4,T5 finite algebra: the quadratic form of a diagonal matrix is a
weighted sum of coordinate squares. -/
theorem quadratic_diagonal {n : ℕ} (v x : Fin n → ℝ) :
    quadratic (Matrix.diagonal v) x=∑ i, v i*x i^2 := by
  simp [quadratic,Matrix.diagonal,ite_mul,pow_two,mul_assoc]

/-- T5 finite scalar inequalities: t_i is nonnegative, and the corrected
diagonal dominates the candidate degree, even when the supplied cap is loose. -/
theorem corrected_diagonal_bounds {n : ℕ} (R A : Graph n) (d : Fin n → ℕ)
    (hA : Compatible R d A) (i : Fin n) :
    0 ≤ degreeCorrection d i ∧ (degree A i : ℝ) ≤ 1+degreeCorrection d i*degree A i := by
  have hd := compatible_truncated_degree R A d hA i
  by_cases hz : truncatedDegree d i=0
  · have he : degree A i=0 := by omega
    simp [degreeCorrection,hz,he]
  · have hp : (0 : ℝ)<truncatedDegree d i := by
      exact_mod_cast Nat.pos_of_ne_zero hz
    have h1 : (1 : ℝ)≤truncatedDegree d i := by
      exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hz)
    have hf : (degree A i : ℝ)/(truncatedDegree d i : ℝ)≤1 := by
      apply (div_le_one hp).mpr
      exact_mod_cast hd
    have hi : 1/(truncatedDegree d i : ℝ)≤1 := (div_le_one hp).mpr h1
    simp only [degreeCorrection,if_neg hz]
    simp only [div_eq_mul_inv,one_mul] at hf hi ⊢
    constructor <;> nlinarith

/-- T5 finite PSD repair: M_A and its difference from I+A are positive
semidefinite, and V1plus is its nonnegative centered quadratic estimate. This
is a finite component of corrected_finite, independent of limit arguments. -/
theorem corrected_matrix_majorant {n : ℕ} (R A : Graph n) (d : Fin n → ℕ)
    (hA : Compatible R d A) (x : Fin n → ℝ) :
    PSD (correctedMatrix d A) ∧ PSD (correctedMatrix d A-oracleMatrix A) ∧
    V1plus d A x=varianceForm (correctedMatrix d A) x ∧ 0 ≤ V1plus d A x := by
  have hsym (i j : Fin n) : adjacency A i j=adjacency A j i := by
    unfold adjacency; rw [A.property.1 i j]
  have hf (z : Fin n → ℝ) : quadratic (correctedMatrix d A) z=
      (∑ i, (1+degreeCorrection d i*degree A i)*z i^2)+quadratic (adjacency A) z := by
    unfold correctedMatrix oracleMatrix
    rw [quadratic_add,quadratic_add]
    have hI : (1 : Matrix (Fin n) (Fin n) ℝ)=Matrix.diagonal (fun _ => 1) := by
      ext i j; simp [Matrix.one_apply,Matrix.diagonal_apply]
    rw [hI,quadratic_diagonal,quadratic_diagonal]
    simp only [one_mul,add_mul,Finset.sum_add_distrib]
    ring
  have hp : PSD (correctedMatrix d A) := by
    constructor
    · intro i j
      simp only [correctedMatrix,oracleMatrix,Matrix.add_apply,Matrix.diagonal_apply,
        Matrix.one_apply]
      by_cases hij : i=j
      · subst j; rfl
      · simp [hij,Ne.symm hij,hsym i j]
    · intro z
      rw [hf]
      have hb := (abs_le.mp (adjacency_quadratic_bound A z)).1
      have hd : (∑ i, (degree A i : ℝ)*z i^2) ≤
          ∑ i, (1+degreeCorrection d i*degree A i)*z i^2 := by
        exact Finset.sum_le_sum (fun i hi => mul_le_mul_of_nonneg_right
          (corrected_diagonal_bounds R A d hA i).2 (sq_nonneg _))
      linarith
  have hdiff : correctedMatrix d A-oracleMatrix A=
      Matrix.diagonal (fun i => degreeCorrection d i*degree A i) := by
    unfold correctedMatrix
    abel
  have hdp : PSD (correctedMatrix d A-oracleMatrix A) := by
    rw [hdiff]
    constructor
    · intro i j
      simp only [Matrix.diagonal_apply]
      by_cases h : i=j
      · subst j; rfl
      · simp [h,Ne.symm h]
    · intro z
      rw [quadratic_diagonal]
      apply Finset.sum_nonneg
      intro i hi
      exact mul_nonneg (mul_nonneg (corrected_diagonal_bounds R A d hA i).1
        (Nat.cast_nonneg _)) (sq_nonneg _)
  have he : V1plus d A x=varianceForm (correctedMatrix d A) x := by
    unfold V1plus V1 varianceForm
    rw [hf]
    simp only [add_mul,one_mul,Finset.sum_add_distrib]
    ring
  refine ⟨hp,hdp,he,?_⟩
  rw [he]
  exact div_nonneg (hp.2 _) (sq_nonneg _)


/- The unchanged mixture_finite_moments contract is proved in P011_FiniteLawCompletion.lean. -/


/-- T11(c): r=ceil(n/2)−floor(n/2), the parity imbalance (0 or 1). -/
def alternatingParity (n : ℕ) : ℕ := (n+1)/2-n/2

/-- T11(c): the exact deterministic between-unit mean variance M_n. -/
def alternatingSpread (n : ℕ) : ℝ :=
  alternatingWeight n^2*(1-(alternatingParity n : ℝ)^2/(n : ℝ)^2)

/-- T11(a)–(e): exact finite decomposition and remainder moments, including the
odd sizes; the even-size specialization gives the validator's Chebyshev witnesses. -/
theorem alternating_finite_moments (k : ℕ) :
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
        probability m {y | |(n : ℝ)*V2 m.G (weighted m y)-1| < 3/2}) := by
  sorry

/- The unchanged path_correlation_instance contract is proved in P011_PathFiniteCompletion.lean. -/


/-- T26(d): the complete iid uniform-three-point sample sequence. -/
def threePointFamily : Family where
  size := fun k => k+1
  positive := by intro k; omega
  grows := Filter.tendsto_atTop_mono (fun k => Nat.le_succ k) Filter.tendsto_id
  model := fun k => threePointModel (k+1)

/- T26(d): the numerical helper witness occurs in a full model satisfying
Assumptions 2 and 3, with beta=1 and n Var(betaHat)=2/3 at every sample size. -/
/- The unchanged helper_witness_scaling contract is proved in P011_ThreePointCompletion.lean. -/


/-- Finite-law bridge for T1,T2,T10,T11,T15,T20,T21,T26: expectation under
the defined uniform pushforward law is exactly the normalized finite sum.
This checks that the real probability laws and the block enumerations agree. -/
theorem uniform_integral {Ω : Type} [Fintype Ω] [Nonempty Ω]
    [MeasurableSpace Ω] [MeasurableSingletonClass Ω] {n : ℕ}
    (f : Ω → (Fin n → ℝ)) (hf : Measurable f)
    (g : (Fin n → ℝ) → ℝ) (hg : Measurable g) :
    (∫ y, g y ∂uniformLaw f)=(∑ u, g (f u))/(Fintype.card Ω : ℝ) := by
  unfold uniformLaw
  rw [← PMF.toMeasure_map f (PMF.uniformOfFintype Ω) hf]
  rw [integral_map hf.aemeasurable hg.aestronglyMeasurable, PMF.integral_eq_sum]
  simp only [PMF.uniformOfFintype_apply,ENNReal.toReal_inv,ENNReal.toReal_natCast,smul_eq_mul]
  rw [← Finset.mul_sum]
  simp only [div_eq_mul_inv,mul_comm]


/-- T11(b),T20: with no edges the correlation-weighted auxiliary estimator
is exactly the printed V2 estimator, for every realization. -/
theorem auxiliary_empty_identity {n : ℕ} (m : Model n) (hG : m.G=emptyGraph n) (y : Fin n → ℝ) :
    V2star m y=V2 m.G (weighted m y) := by
  simp [V2star,V2,hG,emptyGraph,adjacency]

/-- T1(c),T2(c),T15(b): forcing every true edge and setting each cap to its
actual observed degree leaves exactly the true graph as a feasible candidate.
This finite constraint lemma holds for every simple graph, including all blocks. -/
theorem saturated_graph_singleton {n : ℕ} (G A : Graph n) :
    Compatible G (degree G) A ↔ A=G := by
  constructor
  · intro hA
    apply Subtype.ext
    funext i j
    by_cases h : G.val i j=true
    · exact (hA.1 i j h).trans h.symm
    · have hg : G.val i j=false := by cases hh : G.val i j <;> simp_all
      cases ha : A.val i j
      · exact hg.symm
      · have hs : degree G i < degree A i := by
          apply Finset.sum_lt_sum
          · intro v hv
            cases hvG : G.val i v
            · simp [hvG]
            · have hvA := hA.1 i v hvG
              simp [hvG,hvA]
          · exact ⟨j,Finset.mem_univ j,by simp [hg,ha]⟩
        exact False.elim (Nat.not_lt_of_ge (hA.2 i) hs)
  · intro h
    subst A
    exact ⟨fun i j h => h,fun i => le_rfl⟩

/-- Definition 3 and T3: unbiasedness implies that the weighted unit-mean
contrasts sum to zero. It imposes no individual equal-mean restriction. -/
theorem delta_sum_zero {n : ℕ} (hn : 0 < n) (m : Model n)
    (hL1 : ∀ i, Integrable (fun y => weighted m y i) m.law) :
    (∑ i, delta m i)=0 := by
  have hb : beta m=(∑ i, expectation m (fun y => weighted m y i))/(n : ℝ) := by
    unfold beta expectation betaHat average
    rw [integral_div,integral_finsetSum Finset.univ (fun i hi => hL1 i)]
  have h0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  unfold delta
  simp only [Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,
    Fintype.card_fin,nsmul_eq_mul]
  rw [hb]
  field_simp [h0] <;> ring

/-- Equation (3.1) and T12(i): the empirical residuals sum to zero for each
fixed positive sample size, independently of the outcome law. -/
theorem centered_sum_zero {n : ℕ} (hn : 0 < n) (x : Fin n → ℝ) :
    (∑ i, centered x i)=0 := by
  have h0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  unfold centered average
  simp only [Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,
    Fintype.card_fin,nsmul_eq_mul]
  field_simp [h0] <;> ring

/-- T12(i): the exact fixed-sample centering identity
σ̂² = n⁻¹∑(x_i−b)² − (x̄−b)². No common-unit-mean premise is used. -/
theorem sample_variance_centering {n : ℕ} (hn : 0 < n) (x : Fin n → ℝ) (b : ℝ) :
    sampleVariance x=(∑ i, (x i-b)^2)/(n : ℝ)-(average x-b)^2 := by
  have h0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hs : (∑ i, (x i-b)^2)=(∑ i, centered x i^2)+(n : ℝ)*(average x-b)^2 := by
    calc
      _ = ∑ i, (centered x i^2+2*(average x-b)*centered x i+(average x-b)^2) := by
        apply Finset.sum_congr rfl
        intro i hi
        dsimp [centered]
        ring
      _ = _ := by
        simp only [Finset.sum_add_distrib,← Finset.mul_sum,centered_sum_zero hn x,
          mul_zero,add_zero,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  unfold sampleVariance
  rw [hs]
  field_simp [h0]
  <;> ring

/- T15(b): The unchanged star_relaxation_singleton contract is proved in
P011_StarCompletion.lean from saturated fractional capacities and exact block degrees. -/

/-- Definition 4 and programs (3.5),(3.8), pp. 2241,2244,2246: the numeric
row and mandatory-edge inequalities are exactly graph compatibility. -/
theorem program_feasible_iff {n : ℕ} (R A : Graph n) (d : Fin n → ℕ) :
    ProgramFeasible R d A ↔ Compatible R d A := by
  constructor
  · rintro ⟨hrow,hforce⟩
    constructor
    · intro i j hR
      have hh := hforce i j
      cases hA : A.val i j
      · norm_num [adjacency,hR,hA] at hh
      · rfl
    · intro i
      have hh := hrow i
      rw [← degree_row_sum] at hh
      exact_mod_cast hh
  · rintro ⟨hforce,hrow⟩
    constructor
    · intro i
      rw [← degree_row_sum]
      exact_mod_cast hrow i
    · intro i j
      cases hR : R.val i j
      · cases hA : A.val i j <;> norm_num [adjacency,hR,hA]
      · have hA := hforce i j hR
        norm_num [adjacency,hR,hA]

/-- T27(c)–(e): programs (3.5) and (3.8) select the stated maximal estimators;
the converse for V2 requires positive empirical variance. Program (3.6)'s
edge bijection and decision-variable count are upper_program_equivalence (T22). -/
theorem integer_program_estimators {n : ℕ} (hn : 0 < n) (R : Graph n) (d : Fin n → ℕ) (x : Fin n → ℝ) :
    (∀ A, ProgramFeasible R d A ↔ Compatible R d A) ∧
    (∀ A, Maximizes R d (fun B => quadratic (adjacency B) (centered x)) A ↔
      Maximizes R d (fun B => V1 B x) A) ∧
    (∀ A, (n : ℝ)^2*V1 A x = (n : ℝ)*sampleVariance x+quadratic (adjacency A) (centered x)) ∧
    (∀ A, Maximizes R d (fun B => ∑ i, ∑ j, adjacency B i j) A → Maximizes R d (fun B => V2 B x) A) ∧
    (0 < sampleVariance x → ∀ A, Maximizes R d (fun B => V2 B x) A →
      Maximizes R d (fun B => ∑ i, ∑ j, adjacency B i j) A) := by
  have hnR : (0 : ℝ)<n := by exact_mod_cast hn
  have hn2 : 0 < (n : ℝ)^2 := sq_pos_of_pos hnR
  have h0 : (n : ℝ) ≠ 0 := ne_of_gt hnR
  have hσ := sample_variance_nonnegative x
  have hcoeff : 0 ≤ sampleVariance x/(n : ℝ) := div_nonneg hσ hnR.le
  refine ⟨fun A => program_feasible_iff R A d, ?_, ?_, ?_, ?_⟩
  · intro A
    constructor
    · rintro ⟨hA,hmax⟩
      refine ⟨hA,fun B hB => ?_⟩
      unfold V1
      apply (div_le_div_iff_of_pos_right hn2).mpr
      have hh := hmax B hB
      linarith
    · rintro ⟨hA,hmax⟩
      refine ⟨hA,fun B hB => ?_⟩
      have hh := hmax B hB
      unfold V1 at hh
      have hh' := (div_le_div_iff_of_pos_right hn2).mp hh
      linarith
  · intro A
    unfold V1 sampleVariance
    field_simp [h0] <;> ring
  · intro A hA
    refine ⟨hA.1,fun B hB => ?_⟩
    unfold V2
    apply mul_le_mul_of_nonneg_left _ hcoeff
    have hh := div_le_div_of_nonneg_right (hA.2 B hB) hnR.le
    linarith
  · intro hpos A hA
    refine ⟨hA.1,fun B hB => ?_⟩
    have hh := hA.2 B hB
    unfold V2 at hh
    have hp : 0 < sampleVariance x/(n : ℝ) := div_pos hpos hnR
    have hh' := (mul_le_mul_iff_of_pos_left hp).mp hh
    have hdiv : (∑ i, ∑ j, adjacency B i j)/(n : ℝ) ≤
        (∑ i, ∑ j, adjacency A i j)/(n : ℝ) := by linarith
    exact (div_le_div_iff_of_pos_right hnR).mp hdiv


/-- T25(iii),(iv),(v): upward difference, unchanged maximizers, the n-scale bound,
and correcting the helper divisor to n restores all three printed formulas. -/
theorem helper_correction {n : ℕ} (hn : 1 < n) (R : Graph n) (d : Fin n → ℕ) (x : Fin n → ℝ) :
    (∀ A, V1 A x ≤ V1R A x ∧ V2 A x ≤ V2R A x) ∧ V2prime d x ≤ V2primeR d x ∧
    ((0 < ∑ i, centered x i^2) →
      (∀ A, V1 A x < V1R A x ∧ V2 A x < V2R A x) ∧ V2prime d x < V2primeR d x) ∧
    (∀ A, (Maximizes R d (fun B => V1R B x) A ↔ Maximizes R d (fun B => V1 B x) A) ∧
      (Maximizes R d (fun B => V2R B x) A ↔ Maximizes R d (fun B => V2 B x) A)) ∧
    (∀ β c : ℝ, (∀ i, |x i-β| ≤ c) → ∀ A,
      0 ≤ (n : ℝ)*(V1R A x-V1 A x) ∧ (n : ℝ)*(V1R A x-V1 A x) ≤ 4*c^2/((n : ℝ)-1)) ∧
    (∀ A, ((∑ i, centered x i^2)/(n : ℝ)^2+quadratic (adjacency A) (centered x)/(n : ℝ)^2) = V1 A x ∧
      ((∑ i, centered x i^2)/(n : ℝ)^2*(1+(∑ i, ∑ j, adjacency A i j)/n)) = V2 A x) ∧
    ((∑ i, centered x i^2)/(n : ℝ)^2*(1+(∑ i, (truncatedDegree d i : ℝ))/n)) = V2prime d x := by
  have hnN : 0 < n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hnN
  have hn1 : (0 : ℝ) < (n : ℝ)-1 := by
    have hh : (1 : ℝ) < n := by exact_mod_cast hn
    linarith
  have h0 : (n : ℝ) ≠ 0 := ne_of_gt hnR
  have h1 : (n : ℝ)-1 ≠ 0 := ne_of_gt hn1
  have hn2 : 0 < (n : ℝ)^2 := sq_pos_of_pos hnR
  let S : ℝ := ∑ i, centered x i^2
  let Δ : ℝ := S/((n : ℝ)^2*((n : ℝ)-1))
  let q : ℝ := (n : ℝ)/((n : ℝ)-1)
  have hS : 0 ≤ S := Finset.sum_nonneg (fun i hi => sq_nonneg _)
  have hΔ : 0 ≤ Δ := div_nonneg hS (mul_nonneg hn2.le hn1.le)
  have hq : 1 < q := by
    apply (lt_div_iff₀ hn1).mpr
    linarith
  have hqp : 0 < q := lt_trans (by norm_num) hq
  have hd (A : Graph n) := helper_denominators hn A d x
  have hAffine (A : Graph n) : V1R A x = V1 A x+Δ := by
    have hh := (hd A).1
    change V1R A x-V1 A x=Δ at hh
    linarith
  have hScale (A : Graph n) : V2R A x=q*V2 A x := (hd A).2.2.1
  have hScalePrime : V2primeR d x=q*V2prime d x := (hd R).2.2.2
  have hnonneg (A : Graph n) := homoskedastic_estimators_nonnegative A d x
  have hfac (A : Graph n) : 0 < 1+(∑ i, ∑ j, adjacency A i j)/(n : ℝ) := by
    have ha : ∀ i j, 0 ≤ adjacency A i j := by
      intro i j
      unfold adjacency
      split <;> norm_num
    have hs : 0 ≤ ∑ i, ∑ j, adjacency A i j :=
      Finset.sum_nonneg (fun i hi => Finset.sum_nonneg (fun j hj => ha i j))
    have hh := div_nonneg hs hnR.le
    linarith
  have hfacPrime : 0 < 1+(∑ i, (truncatedDegree d i : ℝ))/(n : ℝ) := by
    have hs : 0 ≤ ∑ i, (truncatedDegree d i : ℝ) := by positivity
    have hh := div_nonneg hs hnR.le
    linarith
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro A
    rw [hAffine A,hScale A]
    constructor
    · linarith
    · simpa only [one_mul] using mul_le_mul_of_nonneg_right hq.le (hnonneg A).1
  · rw [hScalePrime]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hq.le (hnonneg R).2
  · intro hpos
    have hSp : 0 < S := hpos
    have hΔp : 0 < Δ := div_pos hSp (mul_pos hn2 hn1)
    have hσp : 0 < sampleVariance x := div_pos hSp hnR
    have hV2 (A : Graph n) : 0 < V2 A x := mul_pos (div_pos hσp hnR) (hfac A)
    have hV2prime : 0 < V2prime d x := mul_pos (div_pos hσp hnR) hfacPrime
    constructor
    · intro A
      rw [hAffine A,hScale A]
      constructor
      · linarith
      · simpa only [one_mul] using mul_lt_mul_of_pos_right hq (hV2 A)
    · rw [hScalePrime]
      simpa only [one_mul] using mul_lt_mul_of_pos_right hq hV2prime
  · intro A
    constructor
    · constructor
      · rintro ⟨hA,hmax⟩
        refine ⟨hA,fun B hB => ?_⟩
        have hh := hmax B hB
        dsimp only at hh
        rw [hAffine B,hAffine A] at hh
        linarith
      · rintro ⟨hA,hmax⟩
        refine ⟨hA,fun B hB => ?_⟩
        dsimp only
        rw [hAffine B,hAffine A]
        have hh := hmax B hB
        dsimp only at hh
        linarith
    · constructor
      · rintro ⟨hA,hmax⟩
        refine ⟨hA,fun B hB => ?_⟩
        have hh := hmax B hB
        dsimp only at hh
        rw [hScale B,hScale A] at hh
        exact (mul_le_mul_iff_of_pos_left hqp).mp hh
      · rintro ⟨hA,hmax⟩
        refine ⟨hA,fun B hB => ?_⟩
        dsimp only
        rw [hScale B,hScale A]
        exact (mul_le_mul_iff_of_pos_left hqp).mpr (hmax B hB)
  · intro β c hx A
    have hterm (i : Fin n) : (x i-β)^2 ≤ c^2 := by
      have hh := mul_self_le_mul_self (abs_nonneg (x i-β)) (hx i)
      simpa only [← pow_two,sq_abs] using hh
    have hsum : (∑ i, (x i-β)^2) ≤ (n : ℝ)*c^2 := by
      calc
        _ ≤ ∑ i : Fin n, c^2 := Finset.sum_le_sum (fun i hi => hterm i)
        _ = _ := by simp
    have hσbound : sampleVariance x ≤ c^2 := by
      rw [sample_variance_centering hnN x β]
      have hh : (∑ i, (x i-β)^2)/(n : ℝ) ≤ c^2 :=
        (div_le_iff₀ hnR).mpr (by simpa only [mul_comm] using hsum)
      nlinarith [sq_nonneg (average x-β)]
    have hnerror : (n : ℝ)*(V1R A x-V1 A x)=sampleVariance x/((n : ℝ)-1) := by
      rw [(hd A).2.1]
      field_simp [h0,h1]
    rw [hnerror]
    constructor
    · exact div_nonneg (sample_variance_nonnegative x) hn1.le
    · have h4 : c^2 ≤ 4*c^2 := by nlinarith [sq_nonneg c]
      exact div_le_div_of_nonneg_right (hσbound.trans h4) hn1.le
  · intro A
    constructor <;> dsimp only [V1,V2,sampleVariance] <;> ring
  · unfold V2prime sampleVariance
    ring


/-- T33,T35,T39 finite comparison: when every estimate is nonnegative, the
printed interval and the corrected clipped interval have identical coverage.
No nonnegativity hypothesis is inserted into the printed asymptotic claims. -/
theorem printed_coverage_eq_of_nonnegative {n : ℕ} (m : Model n)
    (V : (Fin n → ℝ) → ℝ) (hV : ∀ y, 0 ≤ V y) (α : ℝ) :
    printedCoverage m V α=coverage m V α := by
  unfold printedCoverage coverage
  congr 1
  ext y
  simp [hV y,max_eq_left (hV y)]




/-- T5 and T7: split an ordered sum with zero diagonal into its two orientations. -/
theorem ordered_pair_sum {n : ℕ} (f : Fin n → Fin n → ℝ)
    (hdiag : ∀ i, f i i = 0) :
    (∑ i, ∑ j, f i j) = upperSum (fun i j => f i j + f j i) := by
  have hp (i j : Fin n) : f i j =
      (if i < j then f i j else 0) + (if j < i then f i j else 0) := by
    rcases lt_trichotomy i j with h | h | h
    · simp [h, not_lt_of_gt h]
    · subst j; simp [hdiag]
    · simp [h, not_lt_of_gt h]
  calc
    (∑ i, ∑ j, f i j) =
        (∑ i, ∑ j, if i < j then f i j else 0) +
          (∑ i, ∑ j, if j < i then f i j else 0) := by
      calc
        (∑ i, ∑ j, f i j) = ∑ i, ∑ j,
            ((if i < j then f i j else 0) + (if j < i then f i j else 0)) := by
          apply Finset.sum_congr rfl
          intro i hi; apply Finset.sum_congr rfl
          intro j hj; exact hp i j
        _ = _ := by simp only [Finset.sum_add_distrib]
    _ = upperSum f + upperSum (fun i j => f j i) := by
      congr 1
      · simp [upperSum, Finset.sum_filter]
      · rw [Finset.sum_comm]; simp [upperSum, Finset.sum_filter]
    _ = upperSum (fun i j => f i j + f j i) := by
      simp [upperSum, Finset.sum_add_distrib]

/-- T5(a),(d) and T7(a): signless and ordinary graph Laplacians are sums of
one squared sum or difference per unordered edge, exactly at fixed n. -/
theorem graph_laplacian_identity {n : ℕ} (A : Graph n) (z : Fin n → ℝ) :
    quadratic (Matrix.diagonal (fun i => (degree A i : ℝ)) + adjacency A) z =
      upperSum (fun i j => adjacency A i j * (z i + z j)^2) ∧
    quadratic (Matrix.diagonal (fun i => (degree A i : ℝ)) - adjacency A) z =
      upperSum (fun i j => adjacency A i j * (z i - z j)^2) := by
  have hs (i j : Fin n) : adjacency A i j = adjacency A j i := by
    unfold adjacency; rw [A.property.1 i j]
  have hd : (∑ i, (degree A i : ℝ) * z i^2) =
      ∑ i, ∑ j, adjacency A i j * z i^2 := by
    simp_rw [degree_row_sum, Finset.sum_mul]
  have hplus : quadratic (Matrix.diagonal (fun i => (degree A i : ℝ)) + adjacency A) z =
      ∑ i, ∑ j, adjacency A i j * (z i^2 + z i*z j) := by
    rw [quadratic_add, quadratic_diagonal, hd]
    simp only [quadratic, mul_add, Finset.sum_add_distrib, mul_assoc]
  have hminus : quadratic (Matrix.diagonal (fun i => (degree A i : ℝ)) - adjacency A) z =
      ∑ i, ∑ j, adjacency A i j * (z i^2 - z i*z j) := by
    have hsub : quadratic (Matrix.diagonal (fun i => (degree A i : ℝ)) - adjacency A) z =
        quadratic (Matrix.diagonal (fun i => (degree A i : ℝ))) z - quadratic (adjacency A) z := by
      simp [quadratic, Matrix.sub_apply, sub_mul, Finset.sum_sub_distrib]
    rw [hsub, quadratic_diagonal, hd]
    simp only [quadratic, mul_sub, Finset.sum_sub_distrib, mul_assoc]
  constructor
  · rw [hplus, ordered_pair_sum (fun i j => adjacency A i j * (z i^2 + z i*z j))
        (by intro i; simp [adjacency, A.property.2 i])]
    unfold upperSum
    apply Finset.sum_congr rfl
    intro i hi; apply Finset.sum_congr rfl
    intro j hj
    change adjacency A i j * (z i^2 + z i*z j) +
      adjacency A j i * (z j^2 + z j*z i) = adjacency A i j * (z i+z j)^2
    rw [← hs i j]; ring
  · rw [hminus, ordered_pair_sum (fun i j => adjacency A i j * (z i^2 - z i*z j))
        (by intro i; simp [adjacency, A.property.2 i])]
    unfold upperSum
    apply Finset.sum_congr rfl
    intro i hi; apply Finset.sum_congr rfl
    intro j hj
    change adjacency A i j * (z i^2 - z i*z j) +
      adjacency A j i * (z j^2 - z j*z i) = adjacency A i j * (z i-z j)^2
    rw [← hs i j]; ring

/-- T7(a): the degree identity for an arbitrary graph and arbitrary empirical
residuals; it is not an asymptotic or bounded-cap statement. -/
theorem degree_only_edge_identity {n : ℕ} (A : Graph n) (x : Fin n → ℝ) :
    quadratic (adjacency A) (centered x) =
      (∑ i, (degree A i : ℝ) * centered x i^2) -
        upperSum (fun i j => adjacency A i j * (centered x i-centered x j)^2) := by
  have hh := (graph_laplacian_identity A (centered x)).2
  have hsub : quadratic (Matrix.diagonal (fun i => (degree A i : ℝ)) - adjacency A) (centered x) =
      (∑ i, (degree A i : ℝ) * centered x i^2) - quadratic (adjacency A) (centered x) := by
    simp [quadratic, Matrix.sub_apply, Matrix.diagonal_apply, sub_mul,
      Finset.sum_sub_distrib, pow_two, mul_assoc]
  rw [hsub] at hh
  linarith

/-- T5: an ordered adjacency quadratic equals twice the unordered edge objective. -/
theorem adjacency_upper_quadratic {n : ℕ} (A : Graph n) (z : Fin n → ℝ) :
    quadratic (adjacency A) z = 2*upperSum (fun i j => adjacency A i j*z i*z j) := by
  unfold quadratic
  rw [ordered_pair_sum (fun i j => adjacency A i j*z i*z j)
    (by intro i; simp [adjacency,A.property.2 i])]
  have hs (i j : Fin n) : adjacency A j i=adjacency A i j := by
    unfold adjacency; rw [A.property.1 j i]
  simp only [upperSum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi; apply Finset.sum_congr rfl
  intro j hj
  rw [hs]; ring

/-- T5: summing a vertex quantity against degrees counts its two endpoints once
per unordered edge. This identity includes arbitrary signed vertex quantities. -/
theorem degree_weight_sum {n : ℕ} (A : Graph n) (f : Fin n → ℝ) :
    (∑ i, (degree A i : ℝ)*f i) =
      upperSum (fun i j => adjacency A i j*(f i+f j)) := by
  simp_rw [degree_row_sum,Finset.sum_mul]
  rw [ordered_pair_sum (fun i j => adjacency A i j*f i)
    (by intro i; simp [adjacency,A.property.2 i])]
  have hs (i j : Fin n) : adjacency A j i=adjacency A i j := by
    unfold adjacency; rw [A.property.1 j i]
  unfold upperSum
  apply Finset.sum_congr rfl
  intro i hi; apply Finset.sum_congr rfl
  intro j hj
  dsimp only; rw [hs]; ring

/-- T5: a diagonal matrix with nonnegative diagonal is positive semidefinite. -/
theorem psd_diagonal {n : ℕ} (f : Fin n → ℝ) (hf : ∀ i, 0 ≤ f i) :
    PSD (Matrix.diagonal f) := by
  constructor
  · intro i j; by_cases hij : i=j
    · subst j; rfl
    · simp [Matrix.diagonal_apply,hij,Ne.symm hij]
  · intro z; rw [quadratic_diagonal]
    exact Finset.sum_nonneg (fun i hi => mul_nonneg (hf i) (sq_nonneg _))

/-- T5: sums of positive semidefinite matrices are positive semidefinite. -/
theorem psd_add {n : ℕ} (M N : Matrix (Fin n) (Fin n) ℝ)
    (hM : PSD M) (hN : PSD N) : PSD (M+N) := by
  constructor
  · intro i j; simp only [Matrix.add_apply,hM.1 i j,hN.1 i j]
  · intro z; rw [quadratic_add]; exact add_nonneg (hM.2 z) (hN.2 z)

/-- T5(d): the graph Laplacian is positive semidefinite, at each finite size. -/
theorem graph_laplacian_psd {n : ℕ} (A : Graph n) :
    PSD (Matrix.diagonal (fun i => (degree A i : ℝ))-adjacency A) := by
  constructor
  · intro i j
    have hs : adjacency A i j=adjacency A j i := by
      unfold adjacency; rw [A.property.1 i j]
    simp only [Matrix.sub_apply,Matrix.diagonal_apply]
    by_cases hij : i=j
    · subst j; rfl
    · simp [hij,Ne.symm hij,hs]
  · intro z; rw [(graph_laplacian_identity A z).2]
    unfold upperSum
    apply Finset.sum_nonneg
    intro i hi; apply Finset.sum_nonneg
    intro j hj
    exact mul_nonneg (by simp [adjacency]; split <;> norm_num) (sq_nonneg _)

/-- T5(a)–(g): finite matrix identities and inequalities for the degree correction
and Young bound, with zero degree and loose supplied bounds handled explicitly. -/
theorem corrected_finite {n : ℕ} (hn : 0 < n) (R A : Graph n) (d : Fin n → ℕ)
    (hA : Compatible R d A) (x : Fin n → ℝ) :
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
    ((∀ i, degree A i = 0) → V1plus d A x = V1 A x) := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hc := compatible_truncated_degree R A d hA
  have hm := corrected_matrix_majorant R A d hA x
  have hI : (1 : Matrix (Fin n) (Fin n) ℝ)=Matrix.diagonal (fun _ => 1) := by
    ext i j; simp [Matrix.one_apply,Matrix.diagonal_apply]
  have hgap : PSD (Matrix.diagonal (fun i => (truncatedDegree d i : ℝ)) -
      Matrix.diagonal (fun i => (degree A i : ℝ))) := by
    have he : Matrix.diagonal (fun i => (truncatedDegree d i : ℝ)) -
        Matrix.diagonal (fun i => (degree A i : ℝ)) =
        Matrix.diagonal (fun i => (truncatedDegree d i : ℝ)-(degree A i : ℝ)) := by
      ext i j; by_cases h : i=j <;> simp [Matrix.diagonal_apply,h]
    rw [he]
    apply psd_diagonal
    intro i; exact sub_nonneg.mpr (by exact_mod_cast hc i)
  have hlap := graph_laplacian_psd A
  have hdecomp : (1 + Matrix.diagonal (fun i => (truncatedDegree d i : ℝ))) - oracleMatrix A =
      (Matrix.diagonal (fun i => (truncatedDegree d i : ℝ)) -
        Matrix.diagonal (fun i => (degree A i : ℝ))) +
      (Matrix.diagonal (fun i => (degree A i : ℝ)) - adjacency A) := by
    unfold oracleMatrix
    abel
  have hyoung : PSD (1+Matrix.diagonal (fun i => (truncatedDegree d i : ℝ))) := by
    rw [hI]
    exact psd_add _ _ (psd_diagonal _ (by intro i; norm_num))
      (psd_diagonal _ (by intro i; positivity))
  have hbound : PSD (Matrix.diagonal (fun i => (truncatedDegree d i : ℝ))-adjacency A) := by
    have he : Matrix.diagonal (fun i => (truncatedDegree d i : ℝ))-adjacency A =
        (Matrix.diagonal (fun i => (truncatedDegree d i : ℝ)) -
          Matrix.diagonal (fun i => (degree A i : ℝ))) +
        (Matrix.diagonal (fun i => (degree A i : ℝ))-adjacency A) := by abel
    rw [he]; exact psd_add _ _ hgap hlap
  refine ⟨hc, ?_, fun z => (graph_laplacian_identity A z).1, hm.1, hm.2.2.2,
    hm.2.1, hyoung, hbound, hgap, hlap, hdecomp,
    fun z => (graph_laplacian_identity A z).2, young_bound_finite R A d hA x,
    ?_, ?_, ?_, ?_, ?_⟩
  · ext i j
    by_cases hij : i=j
    · subst j
      by_cases hz : truncatedDegree d i=0
      · have hd : degree A i=0 := by have h := hc i; rw [hz] at h; omega
        simp [correctedMatrix,oracleMatrix,degreeCorrection,Matrix.diagonal_apply,
          Matrix.add_apply,Matrix.one_apply,hz,hd] <;> ring
      · have hD : (truncatedDegree d i : ℝ) ≠ 0 := by exact_mod_cast hz
        simp only [correctedMatrix,oracleMatrix,degreeCorrection,Matrix.diagonal_apply,
          Matrix.add_apply,Matrix.one_apply,ite_true,if_neg hz]
        field_simp [hD] <;> ring
    · simp [correctedMatrix,oracleMatrix,Matrix.diagonal_apply,Matrix.add_apply,
        Matrix.one_apply,hij]
  · have hq := adjacency_upper_quadratic A (centered x)
    have hd := degree_weight_sum A (fun i => degreeCorrection d i*centered x i^2)
    have hd' : (∑ i, degreeCorrection d i*degree A i*centered x i^2) =
        upperSum (fun i j => adjacency A i j*
          (degreeCorrection d i*centered x i^2+degreeCorrection d j*centered x j^2)) := by
      convert hd using 1 <;> apply Finset.sum_congr rfl
      intro i hi; ring
    have he : 2*upperSum (fun i j => adjacency A i j*centered x i*centered x j) +
        upperSum (fun i j => adjacency A i j*
          (degreeCorrection d i*centered x i^2+degreeCorrection d j*centered x j^2)) =
        2*upperSum (fun i j => (centered x i*centered x j+
          (degreeCorrection d i*centered x i^2+degreeCorrection d j*centered x j^2)/2)*
          adjacency A i j) := by
      simp only [upperSum,Finset.mul_sum,← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i hi; apply Finset.sum_congr rfl
      intro j hj; ring
    unfold V1plus V1
    rw [hq,hd']
    calc
      (n : ℝ)^2 * (((∑ i, centered x i^2)+
          2*upperSum (fun i j => adjacency A i j*centered x i*centered x j))/(n : ℝ)^2+
          upperSum (fun i j => adjacency A i j*
            (degreeCorrection d i*centered x i^2+degreeCorrection d j*centered x j^2))/(n : ℝ)^2) =
          (∑ i, centered x i^2)+(2*upperSum (fun i j => adjacency A i j*centered x i*centered x j)+
          upperSum (fun i j => adjacency A i j*
            (degreeCorrection d i*centered x i^2+degreeCorrection d j*centered x j^2))) := by
        field_simp [hn0] <;> ring
      _ = _ := by rw [he]

  · intro D hD
    have hys : VYoung d x=sampleVariance x*(1+(D : ℝ))/(n : ℝ) := by
      unfold VYoung sampleVariance
      simp_rw [hD]
      rw [← Finset.mul_sum]
      field_simp [hn0] <;> ring
    have hvs : V2prime d x=sampleVariance x*(1+(D : ℝ))/(n : ℝ) := by
      unfold V2prime
      simp_rw [hD]
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
      field_simp [hn0] <;> ring
    exact ⟨hys.trans hvs.symm,hvs⟩
  · intro d0 D hD hd0 hd
    have hDz : D ≠ 0 := by omega
    unfold V1plus
    simp_rw [degreeCorrection,hd,if_neg hDz,hd0]
    simp only [← Finset.mul_sum]
    ring
  · intro d0 hd0 hdeg hcap
    have hz : d0 ≠ 0 := by omega
    have hzR : (d0 : ℝ) ≠ 0 := by exact_mod_cast hz
    unfold V1plus
    simp_rw [degreeCorrection,hcap,if_neg hz,hdeg]
    simp only [← Finset.mul_sum]
    field_simp [hzR] <;> ring
  · intro hd0
    simp [V1plus,hd0]

/-- Counterexample laws T1, T2, T11, T20 and T26: the uniform law on a finite
function space is the product of its uniform coordinate laws, with total mass 1. -/
theorem uniform_function_product (I A : Type) [Fintype I] [Fintype A] [Nonempty A]
    [MeasurableSpace A] [MeasurableSingletonClass A] :
    (PMF.uniformOfFintype (I → A)).toMeasure =
      Measure.pi (fun _ : I => (PMF.uniformOfFintype A).toMeasure) := by
  apply Measure.ext_of_singleton
  intro u
  simp [Measure.pi_singleton,PMF.toMeasure_apply_singleton,
    PMF.uniformOfFintype_apply,Fintype.card_fun,ENNReal.inv_pow]

set_option backward.isDefEq.respectTransparency false in
/-- T11, T20, T26: mutually independent finite uniform coordinates remain
independent after applying a separate outcome function to each coordinate. -/
theorem uniform_coordinate_dependency {n : ℕ} (A : Type) [Fintype A] [Nonempty A]
    [MeasurableSpace A] [MeasurableSingletonClass A]
    (f : Fin n → A → ℝ) (hf : ∀ i, Measurable (f i)) :
    VariableDependency (uniformLaw (fun u : Fin n → A => fun i => f i (u i)))
      (⟨fun _ _ => false,by simp⟩ : Graph n) (fun i y => y i) := by
  let g : (Fin n → A) → (Fin n → ℝ) := fun u i => f i (u i)
  have hg : Measurable g := measurable_pi_lambda (fun i =>
    (hf i).comp (measurable_pi_apply i))
  have hind : iIndepFun (fun i (u : Fin n → A) => f i (u i))
      (PMF.uniformOfFintype (Fin n → A)).toMeasure := by
    have he : (PMF.uniformOfFintype (Fin n → A)).toMeasure =
        Measure.pi (fun _ : Fin n => (PMF.uniformOfFintype A).toMeasure) :=
      by
        apply Measure.ext_of_singleton
        intro u
        simp [Measure.pi_singleton,PMF.uniformOfFintype_apply,ENNReal.inv_pow]
    have hpi : iIndepFun (fun i (u : Fin n → A) => f i (u i))
        (Measure.pi (fun _ : Fin n => (PMF.uniformOfFintype A).toMeasure)) :=
      iIndepFun_pi (μ := fun _ : Fin n => (PMF.uniformOfFintype A).toMeasure)
        (X := f) (fun i => (hf i).aemeasurable)
    exact he.symm ▸ hpi
  intro S T hST _
  have hi := iIndepFun.indepFun_finset S T hST hind
    (fun i => (hf i).comp (measurable_pi_apply i))
  change IndepFun (fun y => fun i : {i // i ∈ S} => y i.val)
    (fun y => fun j : {j // j ∈ T} => y j.val) (uniformLaw g)
  unfold uniformLaw
  rw [← PMF.toMeasure_map g (PMF.uniformOfFintype (Fin n → A)) hg]
  apply indepFun_iff_measure_inter_preimage_eq_mul.mpr
  intro s t hs ht
  have hS : MeasurableSet ((fun y : Fin n → ℝ => fun i : {i // i ∈ S} => y i.val) ⁻¹' s) :=
    hs.preimage (by fun_prop)
  have hT : MeasurableSet ((fun y : Fin n → ℝ => fun j : {j // j ∈ T} => y j.val) ⁻¹' t) :=
    ht.preimage (by fun_prop)
  rw [Measure.map_apply hg (hS.inter hT),Measure.map_apply hg hS,Measure.map_apply hg hT]
  simpa only [Set.preimage_inter,Set.preimage_preimage,Function.comp_def] using
    hi.measure_inter_preimage_eq_mul s t hs ht


/-- T1(g): the actual normalized uniform four-cycle law gives the explicit
negative-variance realization probability 1/16; the estimator there is -9/4.
This is a finite law certificate, not the unproved full asymptotic refutation. -/
theorem cycle_negative_probability :
    probability (cycleModel 3 1) {y | y=(![5,-1,5,-1] : Fin 4 → ℝ)}=1/16 ∧
    V1 cycleGraph (![5,-1,5,-1] : Fin 4 → ℝ) = -9/4 := by
  let f : (Fin 1 → Fin 4 → Bool) → (Fin 4 → ℝ) :=
    fun u => cycleBlock 3 (fun r => sign (u 0 r))
  have hf : Measurable f := measurable_of_finite _
  have hlaw : (cycleModel 3 1).law=uniformLaw f := by
    change uniformLaw (fun u : Fin 1 → Fin 4 → Bool => fun i =>
      cycleBlock 3 (fun r => sign (u (blockIndex (by decide) i) r))
        (localIndex (by decide) i)) = uniformLaw f
    congr 1
    funext u i; fin_cases i <;> rfl
  have hpre : f ⁻¹' {(![5,-1,5,-1] : Fin 4 → ℝ)} =
      {(fun _ _ => true : Fin 1 → Fin 4 → Bool)} := by
    ext u
    change f u=(![5,-1,5,-1] : Fin 4 → ℝ) ↔ u=(fun _ _ => true)
    constructor
    · intro hu
      have h0 := congrFun hu 0
      have h1 := congrFun hu 1
      have h2 := congrFun hu 2
      have h3 := congrFun hu 3
      have huall : ∀ b : Fin 1, b = 0 := fun b => Subsingleton.elim _ _
      cases hu0 : u 0 0 <;> cases hu1 : u 0 1 <;> cases hu2 : u 0 2 <;> cases hu3 : u 0 3 <;>
        simp_all [f,cycleBlock,sign,funext_iff,Fin.forall_fin_succ] <;> norm_num at *
    · intro hu; subst u
      funext i; fin_cases i <;> norm_num [f,cycleBlock,sign]
  constructor
  · unfold probability
    rw [hlaw]
    change (uniformLaw f).real {(![5,-1,5,-1] : Fin 4 → ℝ)}=1/16
    rw [Measure.real,uniformLaw,← PMF.toMeasure_map f
      (PMF.uniformOfFintype (Fin 1 → Fin 4 → Bool)) hf,
      Measure.map_apply hf (measurableSet_singleton _),hpre]
    simp [PMF.uniformOfFintype_apply,ENNReal.toReal_inv]
  · norm_num [V1,centered,average,quadratic,adjacency,cycleGraph,Fin.sum_univ_succ]

/-- T13(e), validator §4: an input is the finite rational-weight degree problem,
including its number of observed vertices, mandatory edges and degree caps. -/
abbrev DegreeInput := Σ n : ℕ, DegreeProblem n

/-- T13(e): binary words are the input/output alphabet of the finite Turing
machines used to give a precise bit-complexity statement. -/
abbrev BitWord := List Bool

/-- Self-delimiting binary encoding: a unary bit-length prefix, a separator,
and the little-endian binary digits. This costs twice the bit length plus one,
not unary time in the value of a degree or rational numerator. -/
def encodeNatBits (n : ℕ) : BitWord :=
  List.replicate n.bits.length false ++ [true] ++ n.bits

/-- T13(e): signed integers are a sign bit followed by the absolute value. -/
def encodeIntBits (z : ℤ) : BitWord := [decide (z < 0)] ++ encodeNatBits z.natAbs

/-- T13(e): rationals use their canonical reduced signed numerator and positive
denominator. Arithmetic data are counted in bits. -/
def encodeRatBits (q : ℚ) : BitWord := encodeIntBits q.num ++ encodeNatBits q.den

/-- T13(e): list all i<j in lexicographic order. Each possible unordered edge
appears once; there is no oracle for an optimal solution in this encoding. -/
def edgeList (n : ℕ) : List (Edge n) :=
  (List.finRange n).flatMap (fun i => (List.finRange n).flatMap (fun j =>
    if h : i < j then [⟨(i,j),h⟩] else []))

/-- T13(e): serialize n, the n degree caps, then the mandatory flag and rational
weight of each possible edge. This is the usual explicit dense input encoding. -/
def encodeDegreeInput (I : DegreeInput) : BitWord :=
  encodeNatBits I.1 ++
  (List.ofFn (fun i : Fin I.1 => encodeNatBits (I.2.cap i))).flatten ++
  ((edgeList I.1).map (fun e => [decide (e ∈ I.2.forced)] ++ encodeRatBits (I.2.weight e))).flatten

/-- T13(e): an output graph is n followed by its upper-triangular edge flags. -/
def encodeEdgeSolution (S : Σ n : ℕ, Finset (Edge n)) : BitWord :=
  encodeNatBits S.1 ++ (edgeList S.1).map (fun e => decide (e ∈ S.2))

/-- T13(e): none reports infeasibility; some reports an ordinary edge set. -/
def encodeOptionalSolution (S : Option (Σ n : ℕ, Finset (Edge n))) : BitWord :=
  match S with
  | none => [false]
  | some S => [true] ++ encodeEdgeSolution S

/-- T13(e): an exact solver must detect infeasibility and return a feasible
maximizer on every feasible input, including negative mandatory weights. -/
def ExactDegreeSolver (s : ∀ I : DegreeInput, Option (Finset (Edge I.1))) : Prop :=
  ∀ I, (s I = none ↔ ¬ ∃ S, EdgeFeasible I.2 S) ∧
    ∀ S, s I = some S → EdgeFeasible I.2 S ∧
      ∀ T, EdgeFeasible I.2 T → edgeObjective I.2 T ≤ edgeObjective I.2 S

/-- T13(e): a genuine finite Turing machine computes the exact solver within
a fixed polynomial in the length of the above binary input. -/
def PolyDegreeSolver (s : ∀ I : DegreeInput, Option (Finset (Edge I.1))) : Prop :=
  ExactDegreeSolver s ∧ Nonempty (Turing.TM2ComputableInPolyTime
    encodeDegreeInput encodeOptionalSolution
    (fun I => (s I).map (fun S => (⟨I.1,S⟩ : Σ n : ℕ, Finset (Edge n)))))

/-- T13(e): ordinary weighted matching has an explicitly supplied simple graph
and integer edge weights; no mandatory edges or vertex capacities other than 1. -/
structure WeightedMatchingData (n : ℕ) where
  present : Finset (Edge n)
  weight : Edge n → ℤ

/-- T13(e): matching input with its vertex count. -/
abbrev MatchingInput := Σ n : ℕ, WeightedMatchingData n

/-- T13(e): the explicit bit encoding of an ordinary weighted matching input. -/
def encodeMatchingInput (I : MatchingInput) : BitWord :=
  encodeNatBits I.1 ++ ((edgeList I.1).map (fun e =>
    [decide (e ∈ I.2.present)] ++ encodeIntBits (I.2.weight e))).flatten

/-- T13(e): polynomial-time maximum-weight matching, with the usual matching
constraint and exact optimality, represented by a finite Turing machine. -/
def PolyMatchingSolver (s : ∀ I : MatchingInput, Finset (Edge I.1)) : Prop :=
  (∀ I, s I ⊆ I.2.present ∧ (∀ i, edgeDegree (s I) i ≤ 1) ∧
    ∀ T, T ⊆ I.2.present → (∀ i, edgeDegree T i ≤ 1) →
      (∑ e ∈ T, I.2.weight e) ≤ ∑ e ∈ s I, I.2.weight e) ∧
  Nonempty (Turing.TM2ComputableInPolyTime encodeMatchingInput encodeEdgeSolution
    (fun I => (⟨I.1,s I⟩ : Σ n : ℕ, Finset (Edge n))))

/-- T13(e), T30(C2): class P on binary languages, with polynomial time measured
by Mathlib's finite TM2 model and the length of the input word. -/
def BitP (L : Set BitWord) : Prop :=
  ∃ d : BitWord → Bool,
    Nonempty (Turing.TM2ComputableInPolyTime id (fun b : Bool => [b]) d) ∧
    ∀ x, x ∈ L ↔ d x = true

/-- A length prefix separates an input word from its nondeterministic witness. -/
def encodeWordPair (p : BitWord × BitWord) : BitWord :=
  encodeNatBits p.1.length ++ p.1 ++ p.2

/-- T13(e), T30(C2): NP means acceptance by a polynomial-time verifier with a
polynomially bounded binary witness. This is the usual language definition. -/
def BitNP (L : Set BitWord) : Prop :=
  ∃ v : BitWord × BitWord → Bool,
    Nonempty (Turing.TM2ComputableInPolyTime encodeWordPair (fun b : Bool => [b]) v) ∧
    ∃ C k : ℕ, ∀ x, x ∈ L ↔
      ∃ w : BitWord, w.length ≤ C*(x.length+1)^k ∧ v (x,w) = true

/-- T13(e), T30(C2): polynomial-time many-one reductions and NP-hardness. -/
def BitNPHard (L : Set BitWord) : Prop :=
  ∀ K : Set BitWord, BitNP K → ∃ r : BitWord → BitWord,
    Nonempty (Turing.TM2ComputableInPolyTime id id r) ∧ ∀ x, x ∈ K ↔ r x ∈ L

/-- T13(e): P = NP as equality of their binary language classes. -/
def BitPEqualsNP : Prop := ∀ L : Set BitWord, BitP L ↔ BitNP L

/-- T13(e): the decision version asks whether a feasible graph has objective
at least the rational threshold. Invalid binary encodings are rejected. -/
def degreeDecisionLanguage : Set BitWord :=
  {x | ∃ I : DegreeInput, ∃ q : ℚ, x = encodeDegreeInput I ++ encodeRatBits q ∧
    ∃ S, EdgeFeasible I.2 S ∧ q ≤ edgeObjective I.2 S}

/-- T13(e): the corrected bit-complexity consequence. An exact polynomial solver
exists; any polynomial matching algorithm suffices via the stated reduction;
the decision version belongs to P, and its NP-hardness would imply P = NP.
This is a faithful draft, not a certificate of the algorithmic theorem. -/
theorem corrected_polynomial_complexity :
    (∃ s, PolyDegreeSolver s) ∧
    (∀ s, PolyMatchingSolver s → ∃ t, PolyDegreeSolver t) ∧
    BitP degreeDecisionLanguage ∧
    (BitNPHard degreeDecisionLanguage → BitPEqualsNP) := by
  sorry

/-- T30: actual rational residual data for program (3.5), rather than arbitrary
unstructured knapsack weights. The graph constraints are exactly Definition 4. -/
structure ProgramData (n : ℕ) where
  x : Fin n → ℚ
  forced : Finset (Edge n)
  cap : Fin n → ℕ

/-- T30: construct the rank-one weights r_i r_j after empirical centering. -/
def programDegreeProblem {n : ℕ} (P : ProgramData n) : DegreeProblem n where
  forced := P.forced
  cap := P.cap
  weight := fun e =>
    (P.x e.val.1 - (∑ i, P.x i)/(n : ℚ)) * (P.x e.val.2 - (∑ i, P.x i)/(n : ℚ))

/-- T30: serialize the rational observations and exact graph constraints. -/
def encodeProgramInput (I : Σ n : ℕ, ProgramData n) : BitWord :=
  encodeNatBits I.1 ++ (List.ofFn (fun i : Fin I.1 => encodeRatBits (I.2.x i))).flatten ++
    (List.ofFn (fun i : Fin I.1 => encodeNatBits (I.2.cap i))).flatten ++
    (edgeList I.1).map (fun e => decide (e ∈ I.2.forced))

/-- T30(C2): the threshold decision language of (3.5), equivalently (3.6). -/
def programDecisionLanguage : Set BitWord :=
  {x | ∃ I : (Σ n : ℕ, ProgramData n), ∃ q : ℚ,
    x = encodeProgramInput I ++ encodeRatBits q ∧
    ∃ S, EdgeFeasible (programDegreeProblem I.2) S ∧
      q ≤ edgeObjective (programDegreeProblem I.2) S}

/-- T30(C2), printed p. 2245: the paper's NP-hardness assertion, preserved
as an unproved statement about its own degree-incidence, rank-one program. -/
theorem printed_program_np_hard : BitNPHard programDecisionLanguage := by
  sorry

/- T6(c): the nearest PSD matrix in Frobenius norm is unique. This fills the
uniqueness clause omitted from positive_part_finite without altering its type. -/
/- The unchanged positive_part_nearest_unique contract is proved in P011_SpectralCompletion.lean. -/


/-- T6(a): the spectral positive part is positive semidefinite; the fallback
for nonsymmetric matrices is zero and is also positive semidefinite. -/
theorem positive_part_psd {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) : PSD (positivePart M) := by
  have hp : (positivePart M).PosSemidef := by
    unfold positivePart
    split
    · rename_i h
      simpa using (Matrix.PosSemidef.diagonal (fun i => le_max_right (h.eigenvalues i) 0)).mul_mul_conjTranspose_same
        (h.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ)
    · exact Matrix.PosSemidef.zero
  constructor
  · intro i j
    have hh := congr_fun (congr_fun hp.1 j) i
    simpa using hh
  · intro x
    simpa [quadratic,dotProduct,Matrix.mulVec,Finset.mul_sum,mul_assoc,mul_comm,mul_left_comm] using
      hp.dotProduct_mulVec_nonneg x

/-- T6: clipping does nothing to a positive semidefinite matrix. -/
theorem positive_part_of_psd {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (hM : PSD M) :
    positivePart M = M := by
  have hp : M.PosSemidef := by
    apply Matrix.posSemidef_iff_dotProduct_mulVec.mpr
    constructor
    · ext i j; simpa using hM.1 j i
    · intro x
      simpa [quadratic,dotProduct,Matrix.mulVec,Finset.mul_sum,mul_assoc,mul_comm,mul_left_comm] using hM.2 x
  rw [positivePart,dif_pos hp.1]
  have he : Matrix.diagonal (fun i => max (hp.1.eigenvalues i) 0) =
      Matrix.diagonal (fun i => hp.1.eigenvalues i) := by
    congr 1; funext i; exact max_eq_left (hp.eigenvalues_nonneg i)
  rw [he]
  simpa [Unitary.conjStarAlgAut_apply,Matrix.star_eq_conjTranspose,Matrix.conjTranspose_eq_transpose_of_trivial,Function.comp_def] using hp.1.spectral_theorem.symm

/-- T6: the quadratic-form notation for I+A equals the printed V1 formula. -/
theorem variance_form_oracle {n : ℕ} (A : Graph n) (x : Fin n → ℝ) :
    varianceForm (oracleMatrix A) x=V1 A x := by
  have hI : (1 : Matrix (Fin n) (Fin n) ℝ)=Matrix.diagonal (fun _ => 1) := by
    ext i j; simp [Matrix.one_apply,Matrix.diagonal_apply]
  unfold varianceForm oracleMatrix V1
  rw [quadratic_add,hI,quadratic_diagonal]
  simp only [one_mul]

/-- T6(c): already at three observations, positive-part variance estimation
does not admit an affine objective in the adjacency entries, for fixed data. -/
theorem positive_part_objective_nonaffine :
    ¬ ∃ c : ℝ, ∃ w : Fin 3 → Fin 3 → ℝ, ∀ A : Graph 3,
      VPositive A (![1,-2,1] : Fin 3 → ℝ) =
        c + upperSum (fun i j => w i j*adjacency A i j) := by
  have hempty : PSD (oracleMatrix (emptyGraph 3)) := by
    constructor
    · intro i j; simp [oracleMatrix,adjacency,emptyGraph,Matrix.one_apply,eq_comm]
    · intro z
      norm_num [quadratic,oracleMatrix,adjacency,emptyGraph,Fin.sum_univ_succ,Matrix.one_apply]
      nlinarith [sq_nonneg (z 0),sq_nonneg (z 1),sq_nonneg (z 2)]
  have h12 : PSD (oracleMatrix edge12) := by
    constructor
    · intro i j; fin_cases i <;> fin_cases j <;>
        norm_num [oracleMatrix,adjacency,edge12,Matrix.one_apply]
    · intro z
      norm_num [quadratic,oracleMatrix,adjacency,edge12,Fin.sum_univ_succ,Matrix.one_apply]
      nlinarith [sq_nonneg (z 0+z 1),sq_nonneg (z 2)]
  have h23 : PSD (oracleMatrix edge23) := by
    constructor
    · intro i j; fin_cases i <;> fin_cases j <;>
        norm_num [oracleMatrix,adjacency,edge23,Matrix.one_apply]
    · intro z
      norm_num [quadratic,oracleMatrix,adjacency,edge23,Fin.sum_univ_succ,Matrix.one_apply]
      nlinarith [sq_nonneg (z 1+z 2),sq_nonneg (z 0)]
  have he (A : Graph 3) (hA : PSD (oracleMatrix A)) :
      VPositive A (![1,-2,1] : Fin 3 → ℝ)=V1 A (![1,-2,1] : Fin 3 → ℝ) := by
    unfold VPositive
    rw [positive_part_of_psd _ hA,variance_form_oracle]
  rintro ⟨c,w,hw⟩
  have h0 := hw (emptyGraph 3)
  have h1 := hw edge12
  have h2 := hw edge23
  have h3 := hw pathGraph
  rw [he _ hempty] at h0
  rw [he _ h12] at h1
  rw [he _ h23] at h2
  have hpos : 0 ≤ VPositive pathGraph (![1,-2,1] : Fin 3 → ℝ) :=
    div_nonneg ((positive_part_psd (oracleMatrix pathGraph)).2 _) (sq_nonneg _)
  norm_num [V1,quadratic,centered,average,oracleMatrix,adjacency,emptyGraph,
    edge12,edge23,upperSum,pathGraph,Fin.sum_univ_succ,Finset.sum_filter,Matrix.one_apply] at h0 h1 h2 h3
  dsimp only [pathGraph] at hpos
  linarith


/-- T13(d): the gadget edge type is exactly its internal edges plus its
endpoint-to-slot edges; this is an equivalence of finite combinatorial objects. -/
def gadgetEdgeEquiv {n : ℕ} (P : DegreeProblem n) : GadgetEdge P ≃
    ({e // e ∈ optionalEdges P} ⊕
      (Σ e : {e // e ∈ optionalEdges P}, Σ side : Bool,
        Fin (remainingCap P (endpoint e.val side)))) where
  toFun
    | .internal e => .inl e
    | .external e side slot => .inr ⟨e,side,slot⟩
  invFun
    | .inl e => .internal e
    | .inr ⟨e,side,slot⟩ => .external e side slot
  left_inv := by intro e; cases e <;> rfl
  right_inv := by intro e; rcases e with e | ⟨e,side,slot⟩ <;> rfl

/-- T13(d): the exact vertex and edge counts of the matching gadget, in addition
to the polynomial inequalities already stated in matching_reduction. -/
theorem matching_gadget_exact_counts {n : ℕ} (P : DegreeProblem n) :
    Nat.card (GadgetVertex P) = 2*(optionalEdges P).card+(∑ i, remainingCap P i) ∧
    Nat.card (GadgetEdge P) = (optionalEdges P).card+
      ∑ e ∈ optionalEdges P, (remainingCap P e.val.1 + remainingCap P e.val.2) := by
  constructor
  · simp [GadgetVertex,Nat.card_eq_fintype_card,Fintype.card_sigma]
    ring
  · rw [Nat.card_congr (gadgetEdgeEquiv P)]
    simp [Nat.card_eq_fintype_card,Fintype.card_sum,Fintype.card_sigma,
      Fintype.card_coe,Fintype.sum_bool,endpoint,Finset.sum_coe_sort,Finset.sum_attach,Nat.add_comm]
    exact Finset.sum_attach (optionalEdges P) (fun e => remainingCap P e.val.1 + remainingCap P e.val.2)

/-- T13(f): the two exact four-vertex validator inputs, with centered data
(3/2,1/2,-1/2,-3/2), rational weights and the listed mandatory edges. -/
def matchingWitness (second : Bool) : DegreeProblem 4 where
  forced := if second then {⟨(0,2),by decide⟩} else
    {⟨(0,2),by decide⟩,⟨(2,3),by decide⟩}
  cap := if second then fun _ => 1 else ![2,1,2,7]
  weight := fun e =>
    (![3/2,1/2,-1/2,-3/2] : Fin 4 → ℚ) e.val.1 *
    (![3/2,1/2,-1/2,-3/2] : Fin 4 → ℚ) e.val.2

/-- T13(f), validator exact instances: the attaining sets are
"{{1,2},{1,3},{3,4}}" and "F alone", respectively (one-based paper indices). -/
def matchingWitnessSolution (second : Bool) : Finset (Edge 4) :=
  if second then (matchingWitness true).forced else
    (matchingWitness false).forced ∪ {⟨(0,1),by decide⟩}

/-- T13(f): capacities, denominator, integer weight bound and both exact graph
and matching optima of the validator's instances. No numeric certificate is
silently substituted for the general reduction or its complexity conclusion. -/
theorem matching_exact_instances :
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
        (∑ e ∈ J', gadgetWeight e) ≤ ∑ e ∈ J, gadgetWeight e)) := by
  sorry

end
end AronowAudit.P011

#print axioms AronowAudit.P011.cycle_counterexample
#print axioms AronowAudit.P011.path_counterexample
#print axioms AronowAudit.P011.alternating_counterexample
#print axioms AronowAudit.P011.star_counterexample
#print axioms AronowAudit.P011.corrected_finite


#print axioms AronowAudit.P011.cycle_positive_identity
#print axioms AronowAudit.P011.positive_part_cycle_claims
#print axioms AronowAudit.P011.degree_only_finite
#print axioms AronowAudit.P011.degree_only_conservative
#print axioms AronowAudit.P011.unbounded_caps_gap
#print axioms AronowAudit.P011.revised_corollaries
#print axioms AronowAudit.P011.residual_perturbation
#print axioms AronowAudit.P011.residual_root_n
#print axioms AronowAudit.P011.residual_prediction_stability
#print axioms AronowAudit.P011.misspecified_residual_limit
#print axioms AronowAudit.P011.ols_repair
#print axioms AronowAudit.P011.residual_missing_regularity
#print axioms AronowAudit.P011.universal_consistency_impossible
#print axioms AronowAudit.P011.matching_reduction
#print axioms AronowAudit.P011.fourth_polynomial
#print axioms AronowAudit.P011.printed_expansion_counterexample
#print axioms AronowAudit.P011.printed_variables_counterexample
#print axioms AronowAudit.P011.printed_variables_optimum
#print axioms AronowAudit.P011.degree_row_sum
#print axioms AronowAudit.P011.simple_degree_bound
#print axioms AronowAudit.P011.compatible_truncated_degree
#print axioms AronowAudit.P011.corrected_notation
#print axioms AronowAudit.P011.helper_denominators
#print axioms AronowAudit.P011.helper_correction
#print axioms AronowAudit.P011.helper_counterexamples
#print axioms AronowAudit.P011.oracle_sharp_bound
#print axioms AronowAudit.P011.integer_program_estimators
#print axioms AronowAudit.P011.lemma_one
#print axioms AronowAudit.P011.linear_variance_identity
#print axioms AronowAudit.P011.ols_linear_unbiased
#print axioms AronowAudit.P011.printed_proposition_one
#print axioms AronowAudit.P011.printed_corollary_one
#print axioms AronowAudit.P011.underestimation_event_inclusion
#print axioms AronowAudit.P011.printed_corollary_three
#print axioms AronowAudit.P011.printed_auxiliary_degree_bound
#print axioms AronowAudit.P011.printed_package_ols_guarantee
#print axioms AronowAudit.P011.truncation_identity
#print axioms AronowAudit.P011.clipped_truncation
#print axioms AronowAudit.P011.interval_containment
#print axioms AronowAudit.P011.cycle_covariance_algebra
#print axioms AronowAudit.P011.cycle_block_moments
#print axioms AronowAudit.P011.cycle_negative_realization
#print axioms AronowAudit.P011.path_block_moments
#print axioms AronowAudit.P011.star_mean_terms
#print axioms AronowAudit.P011.cycle_spectral_certificate
#print axioms AronowAudit.P011.cycle_majorant_certificate
#print axioms AronowAudit.P011.one_sided_algebra
#print axioms AronowAudit.P011.sample_variance_nonnegative
#print axioms AronowAudit.P011.homoskedastic_estimators_nonnegative
#print axioms AronowAudit.P011.knapsack_encoding
#print axioms AronowAudit.P011.covariance_expansion_linear
#print axioms AronowAudit.P011.cycle_variance_formula
#print axioms AronowAudit.P011.adjacency_quadratic_bound
#print axioms AronowAudit.P011.young_bound_finite
#print axioms AronowAudit.P011.quadratic_add
#print axioms AronowAudit.P011.quadratic_diagonal
#print axioms AronowAudit.P011.corrected_diagonal_bounds
#print axioms AronowAudit.P011.corrected_matrix_majorant
#print axioms AronowAudit.P011.alternating_finite_moments
#print axioms AronowAudit.P011.uniform_integral
#print axioms AronowAudit.P011.graph_three_cases
#print axioms AronowAudit.P011.auxiliary_empty_identity
#print axioms AronowAudit.P011.saturated_graph_singleton
#print axioms AronowAudit.P011.delta_sum_zero
#print axioms AronowAudit.P011.centered_sum_zero
#print axioms AronowAudit.P011.sample_variance_centering
#print axioms AronowAudit.P011.cycle_clipped_entries
#print axioms AronowAudit.P011.program_feasible_iff
#print axioms AronowAudit.P011.printed_coverage_eq_of_nonnegative
#print axioms AronowAudit.P011.ordered_pair_sum
#print axioms AronowAudit.P011.graph_laplacian_identity
#print axioms AronowAudit.P011.degree_only_edge_identity
#print axioms AronowAudit.P011.adjacency_upper_quadratic
#print axioms AronowAudit.P011.degree_weight_sum
#print axioms AronowAudit.P011.psd_diagonal
#print axioms AronowAudit.P011.psd_add
#print axioms AronowAudit.P011.graph_laplacian_psd
#print axioms AronowAudit.P011.uniform_function_product
#print axioms AronowAudit.P011.uniform_coordinate_dependency
#print axioms AronowAudit.P011.corrected_polynomial_complexity
#print axioms AronowAudit.P011.printed_program_np_hard

#print axioms AronowAudit.P011.positive_part_objective_nonaffine
#print axioms AronowAudit.P011.matching_gadget_exact_counts
#print axioms AronowAudit.P011.matching_exact_instances
#print axioms AronowAudit.P011.cycle_negative_probability
#print axioms AronowAudit.P011.positive_part_psd
#print axioms AronowAudit.P011.positive_part_of_psd
#print axioms AronowAudit.P011.variance_form_oracle
