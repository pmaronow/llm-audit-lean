import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P011c

open MeasureTheory ProbabilityTheory Filter Finset
open scoped BigOperators Topology Classical Matrix NNReal ENNReal

noncomputable section

/-- A finite simple undirected graph, represented by Boolean adjacency. -/
abbrev Graph (n : ℕ) := { a : Fin n → Fin n → Bool //
  (∀ i j, a i j = a j i) ∧ (∀ i, a i i = false) }

def adjacency {n : ℕ} (A : Graph n) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => if A.val i j then 1 else 0

def degree {n : ℕ} (A : Graph n) (i : Fin n) : ℕ :=
  ∑ j, if A.val i j then 1 else 0

/-- Mandatory known edges and upper bounds on observed degrees. -/
def Compatible {n : ℕ} (R : Graph n) (d : Fin n → ℕ) (A : Graph n) : Prop :=
  (∀ i j, R.val i j = true → A.val i j = true) ∧ ∀ i, degree A i ≤ d i

def average {n : ℕ} (x : Fin n → ℝ) : ℝ := (∑ i, x i) / n

def centered {n : ℕ} (x : Fin n → ℝ) : Fin n → ℝ := fun i => x i - average x

def sampleVariance {n : ℕ} (x : Fin n → ℝ) : ℝ := (∑ i, centered x i ^ 2) / n

/-- Double sums are over ordered pairs. -/
def quadratic {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) : ℝ :=
  ∑ i, ∑ j, M i j * x i * x j

def oracleMatrix {n : ℕ} (A : Graph n) : Matrix (Fin n) (Fin n) ℝ :=
  1 + adjacency A

/-- The general variance estimator (3.1). -/
def V1 {n : ℕ} (A : Graph n) (x : Fin n → ℝ) : ℝ :=
  ((∑ i, centered x i ^ 2) + quadratic (adjacency A) (centered x)) / (n : ℝ)^2

/-- The homoskedastic variance estimator (3.7). -/
def V2 {n : ℕ} (A : Graph n) (x : Fin n → ℝ) : ℝ :=
  sampleVariance x / n * (1 + (∑ i, ∑ j, adjacency A i j) / n)

def truncatedDegree {n : ℕ} (d : Fin n → ℕ) (i : Fin n) : ℕ := min (d i) (n-1)

/-- The degree-only variance estimator (3.9). -/
def V2prime {n : ℕ} (d : Fin n → ℕ) (x : Fin n → ℝ) : ℝ :=
  sampleVariance x / n * (1 + (∑ i, (truncatedDegree d i : ℝ)) / n)

def Maximizes {n : ℕ} (R : Graph n) (d : Fin n → ℕ) (f : Graph n → ℝ)
    (A : Graph n) : Prop := Compatible R d A ∧ ∀ B, Compatible R d B → f B ≤ f A

/-- A raw joint outcome law and the fixed data of Section 2.
The graph G is the true induced graph on the observed vertices, not the full graph. -/
structure Model (n : ℕ) where
  law : Measure (Fin n → ℝ)
  probability : IsProbabilityMeasure law
  theta : Fin n → ℝ
  G : Graph n
  R : Graph n
  d : Fin n → ℕ

def weighted {n : ℕ} (m : Model n) (y : Fin n → ℝ) : Fin n → ℝ :=
  fun i => m.theta i * y i

def betaHat {n : ℕ} (m : Model n) (y : Fin n → ℝ) : ℝ := average (weighted m y)

def expectation {n : ℕ} (m : Model n) (f : (Fin n → ℝ) → ℝ) : ℝ :=
  ∫ y, f y ∂m.law

def beta {n : ℕ} (m : Model n) : ℝ := expectation m (betaHat m)

/-- Centered second moment; all statistical uses have finite second moments. -/
def var {n : ℕ} (m : Model n) (f : (Fin n → ℝ) → ℝ) : ℝ :=
  expectation m (fun y => (f y - expectation m f)^2)

def covariance {n : ℕ} (m : Model n) : Matrix (Fin n) (Fin n) ℝ := fun i j =>
  expectation m (fun y =>
    (weighted m y i - expectation m (fun z => weighted m z i)) *
    (weighted m y j - expectation m (fun z => weighted m z j)))

/-- Covariance of raw outcomes, used only under finite second moments. -/
def covOf {n : ℕ} (m : Model n) (f g : (Fin n → ℝ) → ℝ) : ℝ :=
  expectation m (fun y => f y*g y)-expectation m f*expectation m g

/-- Independence of every two disjoint, unconnected vertex sets. -/
def VariableDependency {Ω : Type} [MeasurableSpace Ω] {n : ℕ}
    (law : Measure Ω) (G : Graph n) (X : Fin n → Ω → ℝ) : Prop :=
  ∀ S T : Finset (Fin n), Disjoint S T →
    (∀ i ∈ S, ∀ j ∈ T, G.val i j = false) →
    IndepFun (fun y => fun i : {i // i ∈ S} => X i.val y)
      (fun y => fun j : {j // j ∈ T} => X j.val y) law

def Dependency {n : ℕ} (m : Model n) : Prop :=
  VariableDependency m.law m.G (fun i y => y i)

/-- Equal variances of the weighted observed outcomes. -/
def Homoskedastic {n : ℕ} (m : Model n) : Prop :=
  ∀ i j, covariance m i i = covariance m j j

end
end SAP.P011c
