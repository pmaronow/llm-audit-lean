import Mathlib

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

abbrev Graph (n : ℕ) := { a : Fin n → Fin n → Bool //
  (∀ i j, a i j = a j i) ∧ (∀ i, a i i = false) }

def adjacency {n : ℕ} (A : Graph n) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => if A.val i j then 1 else 0

def degree {n : ℕ} (A : Graph n) (i : Fin n) : ℕ :=
  ∑ j, if A.val i j then 1 else 0

def Compatible {n : ℕ} (R : Graph n) (d : Fin n → ℕ) (A : Graph n) : Prop :=
  (∀ i j, R.val i j = true → A.val i j = true) ∧ ∀ i, degree A i ≤ d i

def average {n : ℕ} (x : Fin n → ℝ) : ℝ := (∑ i, x i) / n

def centered {n : ℕ} (x : Fin n → ℝ) : Fin n → ℝ := fun i => x i - average x

def sampleVariance {n : ℕ} (x : Fin n → ℝ) : ℝ := (∑ i, centered x i ^ 2) / n

def quadratic {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) : ℝ :=
  ∑ i, ∑ j, M i j * x i * x j

def oracleMatrix {n : ℕ} (A : Graph n) : Matrix (Fin n) (Fin n) ℝ :=
  1 + adjacency A

def varianceForm {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) : ℝ :=
  quadratic M (centered x) / (n : ℝ)^2

def V1 {n : ℕ} (A : Graph n) (x : Fin n → ℝ) : ℝ :=
  ((∑ i, centered x i ^ 2) + quadratic (adjacency A) (centered x)) / (n : ℝ)^2

def V2 {n : ℕ} (A : Graph n) (x : Fin n → ℝ) : ℝ :=
  sampleVariance x / n * (1 + (∑ i, ∑ j, adjacency A i j) / n)

def truncatedDegree {n : ℕ} (d : Fin n → ℕ) (i : Fin n) : ℕ := min (d i) (n-1)

def V2prime {n : ℕ} (d : Fin n → ℕ) (x : Fin n → ℝ) : ℝ :=
  sampleVariance x / n * (1 + (∑ i, (truncatedDegree d i : ℝ)) / n)

def degreeCorrection {n : ℕ} (d : Fin n → ℕ) (i : Fin n) : ℝ :=
  if truncatedDegree d i = 0 then 0 else 1 - 1 / (truncatedDegree d i : ℝ)

def correctedMatrix {n : ℕ} (d : Fin n → ℕ) (A : Graph n) : Matrix (Fin n) (Fin n) ℝ :=
  oracleMatrix A + Matrix.diagonal (fun i => degreeCorrection d i * degree A i)

def V1plus {n : ℕ} (d : Fin n → ℕ) (A : Graph n) (x : Fin n → ℝ) : ℝ :=
  V1 A x + (∑ i, degreeCorrection d i * degree A i * centered x i ^ 2) / (n : ℝ)^2

def VYoung {n : ℕ} (d : Fin n → ℕ) (x : Fin n → ℝ) : ℝ :=
  (∑ i, (1 + (truncatedDegree d i : ℝ)) * centered x i ^ 2) / (n : ℝ)^2

def Maximizes {n : ℕ} (R : Graph n) (d : Fin n → ℕ) (f : Graph n → ℝ)
    (A : Graph n) : Prop := Compatible R d A ∧ ∀ B, Compatible R d B → f B ≤ f A

structure Model (n : ℕ) where
  law : Measure (Fin n → ℝ)
  probability : IsProbabilityMeasure law
  theta : Fin n → ℝ
  G : Graph n
  R : Graph n
  d : Fin n → ℕ

def weighted {n : ℕ} (m : Model n) (y : Fin n → ℝ) : Fin n → ℝ := fun i => m.theta i * y i

def betaHat {n : ℕ} (m : Model n) (y : Fin n → ℝ) : ℝ := average (weighted m y)

def expectation {n : ℕ} (m : Model n) (f : (Fin n → ℝ) → ℝ) : ℝ := ∫ y, f y ∂m.law

def beta {n : ℕ} (m : Model n) : ℝ := expectation m (betaHat m)

def var {n : ℕ} (m : Model n) (f : (Fin n → ℝ) → ℝ) : ℝ :=
  expectation m (fun y => (f y - expectation m f)^2)

def covariance {n : ℕ} (m : Model n) : Matrix (Fin n) (Fin n) ℝ := fun i j =>
  expectation m (fun y =>
    (weighted m y i - expectation m (fun z => weighted m z i)) *
    (weighted m y j - expectation m (fun z => weighted m z j)))

def delta {n : ℕ} (m : Model n) : Fin n → ℝ :=
  fun i => expectation m (fun y => weighted m y i) - beta m

def meanBias {n : ℕ} (m : Model n) : ℝ := quadratic (oracleMatrix m.G) (delta m) / n

def meanSpread {n : ℕ} (m : Model n) : ℝ := (∑ i, delta m i ^ 2) / n

def VariableDependency {Ω : Type} [MeasurableSpace Ω] {n : ℕ}
    (law : Measure Ω) (G : Graph n) (X : Fin n → Ω → ℝ) : Prop :=
  ∀ S T : Finset (Fin n), Disjoint S T →
    (∀ i ∈ S, ∀ j ∈ T, G.val i j = false) →
    IndepFun (fun y => fun i : {i // i ∈ S} => X i.val y)
      (fun y => fun j : {j // j ∈ T} => X j.val y) law

def Dependency {n : ℕ} (m : Model n) : Prop :=
  VariableDependency m.law m.G (fun i y => y i)

def Homoskedastic {n : ℕ} (m : Model n) : Prop :=
  ∀ i j, covariance m i i = covariance m j j

structure Family where
  size : ℕ → ℕ
  positive : ∀ k, 0 < size k
  grows : Tendsto size atTop atTop
  model : ∀ k, Model (size k)

def Nested (F : Family) : Prop := Monotone F.size ∧ ∀ k,
  ∃ e : Fin (F.size k) ↪ Fin (F.size (k+1)),
    ∀ i j, (F.model k).G.val i j = (F.model (k+1)).G.val (e i) (e j)

def Scaling (F : Family) (c1 c2 c3 c4 : ℝ) : Prop :=
  Nested F ∧ 0 < c1 ∧ 0 < c2 ∧ 0 < c3 ∧ 0 < c4 ∧
  (∀ k, Dependency (F.model k)) ∧
  (∀ k, ∀ᵐ y ∂(F.model k).law, ∀ i,
    |weighted (F.model k) y i - beta (F.model k)| ≤ c1) ∧
  (∀ k i, (degree (F.model k).G i : ℝ) ≤ c2) ∧
  Tendsto (fun k => (F.size k : ℝ) * var (F.model k) (betaHat (F.model k)))
    atTop (𝓝 c3) ∧ (∀ k i, |(F.model k).theta i| < c4)

def Valid (F : Family) : Prop := ∀ k, Compatible (F.model k).R (F.model k).d (F.model k).G

def probability {n : ℕ} (m : Model n) (E : Set (Fin n → ℝ)) : ℝ := m.law.real E

def InProbability (F : Family) (T : ∀ k, (Fin (F.size k) → ℝ) → ℝ) (a : ℕ → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → Tendsto
    (fun k => probability (F.model k) {y | |T k y - a k| > ε}) atTop (𝓝 0)

def Conservative (F : Family) (V : ∀ k, (Fin (F.size k) → ℝ) → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → Tendsto
    (fun k => probability (F.model k) {y |
      (F.size k : ℝ) * (var (F.model k) (betaHat (F.model k)) - V k y) > ε})
    atTop (𝓝 0)

def Phi (t : ℝ) : ℝ := ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1) t

def normalQuantile (α : ℝ) : ℝ := sInf {t : ℝ | 1 - α / 2 ≤ Phi t}

def coverage {n : ℕ} (m : Model n) (V : (Fin n → ℝ) → ℝ) (α : ℝ) : ℝ :=
  probability m {y | |betaHat m y - beta m| ≤ normalQuantile α * Real.sqrt (max (V y) 0)}

def ConservativeCoverage (F : Family) (V : ∀ k, (Fin (F.size k) → ℝ) → ℝ) : Prop :=
  ∀ α : ℝ, 0 < α → α < 1 →
    1 - α ≤ Filter.liminf (fun k => coverage (F.model k) (V k) α) atTop

def PSD {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  (∀ i j, M i j = M j i) ∧ ∀ x, 0 ≤ quadratic M x

def l2 {n : ℕ} (x : Fin n → ℝ) : ℝ := Real.sqrt (∑ i, x i ^ 2)

def operatorNorm {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  ‖(Matrix.toEuclideanLin M).toContinuousLinearMap‖

def positivePart {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  if h : M.IsHermitian then
    (h.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ) *
      Matrix.diagonal (fun i => max (h.eigenvalues i) 0) *
      (h.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ)ᵀ
  else 0

def VPositive {n : ℕ} (A : Graph n) (x : Fin n → ℝ) : ℝ :=
  varianceForm (positivePart (oracleMatrix A)) x

def emptyGraph (n : ℕ) : Graph n := ⟨fun _ _ => false, by simp⟩

def cycleGraph : Graph 4 :=
  ⟨![![false,true,false,true], ![true,false,true,false],
      ![false,true,false,true], ![true,false,true,false]], by
    constructor
    · intro i j; fin_cases i <;> fin_cases j <;> decide
    · intro i; fin_cases i <;> decide⟩

def pathGraph : Graph 3 :=
  ⟨![![false,true,false], ![true,false,true], ![false,true,false]], by
    constructor
    · intro i j; fin_cases i <;> fin_cases j <;> decide
    · intro i; fin_cases i <;> decide⟩

def localIndex {q blocks : ℕ} (hq : 0 < q) (i : Fin (q*blocks)) : Fin q :=
  ⟨i.val % q, Nat.mod_lt _ hq⟩

def blockIndex {q blocks : ℕ} (hq : 0 < q) (i : Fin (q*blocks)) : Fin blocks :=
  ⟨i.val / q, (Nat.div_lt_iff_lt_mul hq).mpr (by simpa [Nat.mul_comm] using i.isLt)⟩

def blockGraph {q : ℕ} (hq : 0 < q) (A : Graph q) (blocks : ℕ) : Graph (q*blocks) :=
  ⟨fun i j => decide (i.val / q = j.val / q) && A.val (localIndex hq i) (localIndex hq j), by
    constructor
    · intro i j
      dsimp only
      rw [A.property.1 (localIndex hq i) (localIndex hq j)]
      simp only [eq_comm]
    · intro i
      simp [A.property.2]⟩

def sign (b : Bool) : ℝ := if b then 1 else -1

def uniformLaw {Ω : Type} [Fintype Ω] [Nonempty Ω] {n : ℕ}
    (f : Ω → (Fin n → ℝ)) : Measure (Fin n → ℝ) :=
  ((PMF.uniformOfFintype Ω).map f).toMeasure

def cycleBlock (a : ℝ) (u : Fin 4 → ℝ) : Fin 4 → ℝ :=
  ![a + u 0 + u 3, -a + u 0 + u 1, a + u 1 + u 2, -a + u 2 + u 3]

def cycleModel (a : ℝ) (blocks : ℕ) : Model (4*blocks) where
  law := uniformLaw (fun u : Fin blocks → Fin 4 → Bool => fun i =>
    cycleBlock a (fun r => sign (u (blockIndex (by decide) i) r)) (localIndex (by decide) i))
  probability := by dsimp [uniformLaw]; infer_instance
  theta := fun _ => 1
  G := blockGraph (by decide) cycleGraph blocks
  R := blockGraph (by decide) cycleGraph blocks
  d := fun _ => 2

def cycleFamily (a : ℝ) : Family where
  size := fun k => 4*(k+1)
  positive := by intro k; omega
  grows := Filter.tendsto_atTop_mono (fun k => by change k ≤ _; omega) Filter.tendsto_id
  model := fun k => cycleModel a (k+1)

def pathBlock (t U V : ℝ) : Fin 3 → ℝ := ![t+U, -2*t+3/5*U+4/5*V, t+V]

def pathModel (t : ℝ) (blocks : ℕ) : Model (3*blocks) where
  law := uniformLaw (fun u : Fin blocks → Fin 2 → Bool => fun i =>
    pathBlock t (sign (u (blockIndex (by decide) i) 0))
      (sign (u (blockIndex (by decide) i) 1)) (localIndex (by decide) i))
  probability := by dsimp [uniformLaw]; infer_instance
  theta := fun _ => 1
  G := blockGraph (by decide) pathGraph blocks
  R := blockGraph (by decide) pathGraph blocks
  d := fun i => degree pathGraph (localIndex (by decide) i)

def pathFamily (t : ℝ) : Family where
  size := fun k => 3*(k+1)
  positive := by intro k; omega
  grows := Filter.tendsto_atTop_mono (fun k => by change k ≤ _; omega) Filter.tendsto_id
  model := fun k => pathModel t (k+1)

def signModel (n : ℕ) : Model n where
  law := uniformLaw (fun u : Fin n → Bool => fun i => sign (u i))
  probability := by dsimp [uniformLaw]; infer_instance
  theta := fun _ => 1
  G := emptyGraph n
  R := emptyGraph n
  d := fun _ => 0

end
end SAP.P011a
