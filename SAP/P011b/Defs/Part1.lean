import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P011b

open MeasureTheory ProbabilityTheory Filter Finset
open scoped BigOperators Topology Classical Matrix NNReal ENNReal

noncomputable section

/-! Finite observed graphs and the three paper estimators.
All statistical statements below require a positive sample size. -/

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

def V1 {n : ℕ} (A : Graph n) (x : Fin n → ℝ) : ℝ :=
  ((∑ i, centered x i ^ 2) + quadratic (adjacency A) (centered x)) / (n : ℝ)^2

def V2 {n : ℕ} (A : Graph n) (x : Fin n → ℝ) : ℝ :=
  sampleVariance x / n * (1 + (∑ i, ∑ j, adjacency A i j) / n)

def truncatedDegree {n : ℕ} (d : Fin n → ℕ) (i : Fin n) : ℕ := min (d i) (n-1)

def V2prime {n : ℕ} (d : Fin n → ℕ) (x : Fin n → ℝ) : ℝ :=
  sampleVariance x / n * (1 + (∑ i, (truncatedDegree d i : ℝ)) / n)

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

end
end SAP.P011b
