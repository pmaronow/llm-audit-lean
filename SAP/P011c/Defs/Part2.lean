import Mathlib
import SAP.P011c.Defs.Part1

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P011c

open MeasureTheory ProbabilityTheory Filter Finset
open scoped BigOperators Topology Classical Matrix NNReal ENNReal

noncomputable section

/-- Positive sample sizes tending to infinity; each row has its own joint law. -/
structure Family where
  size : ℕ → ℕ
  positive : ∀ k, 0 < size k
  grows : Tendsto size atTop atTop
  model : ∀ k, Model (size k)

/-- Additional scope condition: nondecreasing sample sizes and induced embeddings
between successive observed dependency graphs. Printed Assumption 2 nests the full
graphs and does not impose this condition on their observed induced subgraphs. -/
def Nested (F : Family) : Prop := Monotone F.size ∧ ∀ k,
  ∃ e : Fin (F.size k) ↪ Fin (F.size (k+1)),
    ∀ i j, (F.model k).G.val i j = (F.model (k+1)).G.val (e i) (e j)

/-- Assumption 2's numerical and dependency conditions, strengthened by `Nested`
on the observed induced graphs rather than just nesting of the full graphs.
The almost-everywhere bound implies finite second moments of weighted outcomes. -/
def Scaling (F : Family) (c1 c2 c3 c4 : ℝ) : Prop :=
  Nested F ∧ 0 < c1 ∧ 0 < c2 ∧ 0 < c3 ∧ 0 < c4 ∧
  (∀ k, Dependency (F.model k)) ∧
  (∀ k, ∀ᵐ y ∂(F.model k).law, ∀ i,
    |weighted (F.model k) y i - beta (F.model k)| ≤ c1) ∧
  (∀ k i, (degree (F.model k).G i : ℝ) ≤ c2) ∧
  Tendsto (fun k => (F.size k : ℝ) * var (F.model k) (betaHat (F.model k)))
    atTop (𝓝 c3) ∧ (∀ k i, |(F.model k).theta i| < c4)

def Valid (F : Family) : Prop :=
  ∀ k, Compatible (F.model k).R (F.model k).d (F.model k).G

def probability {n : ℕ} (m : Model n) (E : Set (Fin n → ℝ)) : ℝ := m.law.real E

def InProbability (F : Family) (T : ∀ k, (Fin (F.size k) → ℝ) → ℝ)
    (a : ℕ → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → Tendsto
    (fun k => probability (F.model k) {y | |T k y - a k| > ε}) atTop (𝓝 0)

/-- Vanishing probability of underestimation by more than ε after scaling by n. -/
def Conservative (F : Family) (V : ∀ k, (Fin (F.size k) → ℝ) → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → Tendsto
    (fun k => probability (F.model k) {y |
      (F.size k : ℝ) * (var (F.model k) (betaHat (F.model k)) - V k y) > ε})
    atTop (𝓝 0)

def scaledTrue (F : Family) (k : ℕ) : ℝ :=
  (F.size k : ℝ) * var (F.model k) (betaHat (F.model k))

def scaledOracle (F : Family) (k : ℕ) (y : Fin (F.size k) → ℝ) : ℝ :=
  (F.size k : ℝ) * V1 (F.model k).G (weighted (F.model k) y)

def Phi (t : ℝ) : ℝ := ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1) t

/-- Normal critical value; every coverage assertion restricts 0 < α < 1. -/
def normalQuantile (α : ℝ) : ℝ := sInf {t : ℝ | 1 - α / 2 ≤ Phi t}

/-- Coverage with the corrected nonnegative clipping. -/
def coverage {n : ℕ} (m : Model n) (V : (Fin n → ℝ) → ℝ) (α : ℝ) : ℝ :=
  probability m {y | |betaHat m y - beta m| ≤ normalQuantile α * Real.sqrt (max (V y) 0)}

def ConservativeCoverage (F : Family) (V : ∀ k, (Fin (F.size k) → ℝ) → ℝ) : Prop :=
  ∀ α : ℝ, 0 < α → α < 1 →
    1 - α ≤ Filter.liminf (fun k => coverage (F.model k) (V k) α) atTop

/-- Coverage of the printed interval: a negative estimate is undefined and uncovered. -/
def printedCoverage {n : ℕ} (m : Model n) (V : (Fin n → ℝ) → ℝ) (α : ℝ) : ℝ :=
  probability m {y | 0 ≤ V y ∧ |betaHat m y-beta m| ≤ normalQuantile α*Real.sqrt (V y)}

def PrintedConservativeCoverage (F : Family)
    (V : ∀ k, (Fin (F.size k) → ℝ) → ℝ) : Prop :=
  ∀ α : ℝ, 0 < α → α < 1 →
    1-α ≤ Filter.liminf (fun k => printedCoverage (F.model k) (V k) α) atTop

/-- Standardization used only in the CLT, with explicitly eventual positive variance. -/
def standardized {n : ℕ} (m : Model n) (y : Fin n → ℝ) : ℝ :=
  (betaHat m y-beta m)/Real.sqrt (var m (betaHat m))

/-- A linear mean model requires ordinary, finite coordinate expectations. -/
def MeanModel {n p : ℕ} (m : Model n) (D : Matrix (Fin n) (Fin p) ℝ)
    (b : Fin p → ℝ) : Prop :=
  (∀ i, Integrable (fun y => y i) m.law) ∧
    ∀ i, expectation m (fun y => y i) = (D *ᵥ b) i

def ols {n p : ℕ} (D : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ) : Fin p → ℝ :=
  (Dᵀ*D)⁻¹ *ᵥ (Dᵀ *ᵥ y)

def olsTheta {n p : ℕ} (D : Matrix (Fin n) (Fin p) ℝ) : Matrix (Fin p) (Fin n) ℝ :=
  (n : ℝ) • ((Dᵀ*D)⁻¹*Dᵀ)

def gFactor {n : ℕ} (m : Model n) : ℝ :=
  1+(∑ i, ∑ j, adjacency m.G i j)/n

/-- Symmetry and nonnegativity of every real quadratic form. -/
def PSD {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  (∀ i j, M i j = M j i) ∧ ∀ x, 0 ≤ quadratic M x

/-- The capacity matrix uses real subtraction. -/
def recruitmentCapacityMatrix {n : ℕ} (R : Graph n) (h : Fin n → ℕ) :
    Matrix (Fin n) (Fin n) ℝ :=
  oracleMatrix R + Matrix.diagonal (fun i => (h i : ℝ) - (degree R i : ℝ))

end
end SAP.P011c
