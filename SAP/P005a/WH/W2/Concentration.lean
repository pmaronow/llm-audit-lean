import SAP.P005a.Defs.WholeW2
import SAP.P005a.Bridge
import AronowAudit.P005.Wave1.Cond.CondP005T8T9Proofs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P005a.WH.W2
noncomputable section
open Finset Filter
open scoped BigOperators Matrix Topology Matrix.Norms.Operator

/-- Real symmetric matrices are viewed inside the full finite matrix space. -/
def hermitianSet (k : ℕ) : Set (Matrix (Fin k) (Fin k) ℝ) := {A | A.IsHermitian}

def quadratic {k : ℕ} (A : Matrix (Fin k) (Fin k) ℝ) (v : Fin k → ℝ) : ℝ :=
  dot v (A *ᵥ v)

def unitVector {k : ℕ} (v : Fin k → ℝ) : Prop := dot v v = 1

def matrixLE {k : ℕ} (A B : Matrix (Fin k) (Fin k) ℝ) : Prop := (B-A).PosSemidef

def traceExp {k : ℕ} (A : Matrix (Fin k) (Fin k) ℝ) : ℝ := Matrix.trace (NormedSpace.exp A)

def subsetSum {N k : ℕ} (X : Fin N → Matrix (Fin k) (Fin k) ℝ)
    (S : Finset (Fin N)) : Matrix (Fin k) (Fin k) ℝ := ∑ i ∈ S, X i

def drawSum {N k s : ℕ} (X : Fin N → Matrix (Fin k) (Fin k) ℝ)
    (f : Fin s → Fin N) : Matrix (Fin k) (Fin k) ℝ := ∑ j, X (f j)

/-- A finite product-uniform average, with no measure or integrability conventions. -/
def iidAverage (N s : ℕ) (f : (Fin s → Fin N) → ℝ) : ℝ :=
  (∑ w, f w) / (N : ℝ)^s

/-- Hoeffding's labelled coupling: first draw with replacement, then choose a
uniform size-s superset of the labels observed. All substantive uses have s <= N. -/
def samplingWeight (N s : ℕ) (S : Finset (Fin N)) (f : Fin s → Fin N) : ℝ := by
  classical
  let D := univ.image f
  exact if S ∈ design N s ∧ D ⊆ S then
    1 / ((N : ℝ)^s * ((N-D.card).choose (s-D.card) : ℝ)) else 0

/-- Spectral positivity and the finite trace-exponential test for a large eigenvalue. -/
def spectralTraceTest : Prop :=
  ∀ (k : ℕ) (A : Matrix (Fin k) (Fin k) ℝ), A.IsHermitian →
    (NormedSpace.exp A).PosSemidef ∧
    ∀ a θ : ℝ, 0 < θ →
      (∃ v : Fin k → ℝ, unitVector v ∧ a < quadratic A v) →
      Real.exp (θ*a) ≤ traceExp (θ • A)

/-- Peierls' scalar Jensen inequality in an eigenbasis. -/
def peierls : Prop :=
  ∀ (k : ℕ) (A : Matrix (Fin k) (Fin k) ℝ), A.IsHermitian →
    ∀ v : Fin k → ℝ, unitVector v →
      Real.exp (quadratic A v) ≤ quadratic (NormedSpace.exp A) v

def traceExpConvex : Prop :=
  ∀ k : ℕ, ConvexOn ℝ (hermitianSet k) (@traceExp k)

/-- Golden--Thompson in real finite dimension. -/
def goldenThompson : Prop :=
  ∀ (k : ℕ) (A B : Matrix (Fin k) (Fin k) ℝ),
    A.IsHermitian → B.IsHermitian →
    traceExp (A+B) ≤ Matrix.trace (NormedSpace.exp A * NormedSpace.exp B)

/-- Hoeffding convex comparison for labelled sampling, allowing repeated matrix values. -/
def convexSampling : Prop :=
  ∀ (N k s : ℕ), 0 < N → s ≤ N →
    ∀ X : Fin N → Matrix (Fin k) (Fin k) ℝ, (∀ i, (X i).IsHermitian) →
    ∀ f : Matrix (Fin k) (Fin k) ℝ → ℝ, ConvexOn ℝ (hermitianSet k) f →
      expectation s (fun S => f (subsetSum X S)) ≤
        iidAverage N s (fun w => f (drawSum X w))

/-- The scalar-mean exponential chord bound for one PSD draw in [0,I]. -/
def exponentialChord : Prop :=
  ∀ (N k : ℕ), 0 < N → ∀ X : Fin N → Matrix (Fin k) (Fin k) ℝ,
    (∀ i, (X i).PosSemidef ∧ matrixLE (X i) 1) →
    ∀ μ : ℝ, 0 ≤ μ → μ ≤ 1 → (N : ℝ)⁻¹ • (∑ i, X i) = μ • (1 : Matrix (Fin k) (Fin k) ℝ) →
    ∀ θ : ℝ, matrixLE ((N : ℝ)⁻¹ • (∑ i, NormedSpace.exp (θ • X i)))
      ((1+μ*(Real.exp θ-1)) • (1 : Matrix (Fin k) (Fin k) ℝ))

/-- Independent trace MGF; scalar isotropy makes the Golden--Thompson recursion sufficient. -/
def independentTraceMGF : Prop :=
  ∀ (N k s : ℕ), 0 < N → ∀ X : Fin N → Matrix (Fin k) (Fin k) ℝ,
    (∀ i, (X i).PosSemidef ∧ matrixLE (X i) 1) →
    ∀ μ : ℝ, 0 ≤ μ → μ ≤ 1 → (N : ℝ)⁻¹ • (∑ i, X i) = μ • (1 : Matrix (Fin k) (Fin k) ℝ) →
    ∀ θ : ℝ, iidAverage N s (fun w => traceExp (θ • drawSum X w)) ≤
      (k : ℝ)*(1+μ*(Real.exp θ-1))^s

/-- Only the fixed two-sided Chernoff bound needed by this campaign.
The absolute constants are deliberately loose; no full literature theorem is assumed. -/
def fixedChernoff : Prop :=
  ∀ (N k s : ℕ), 0 < N → 0 < k → s ≤ N →
    ∀ X : Fin N → Matrix (Fin k) (Fin k) ℝ,
    (∀ i, (X i).PosSemidef ∧ matrixLE (X i) 1) →
    ∀ μ : ℝ, 0 < μ → μ ≤ 1 → (N : ℝ)⁻¹ • (∑ i, X i) = μ • (1 : Matrix (Fin k) (Fin k) ℝ) →
    probability s (fun S => ∃ v : Fin k → ℝ, unitVector v ∧
      (quadratic (subsetSum X S) v < (s : ℝ)*μ/2 ∨
        2*(s : ℝ)*μ < quadratic (subsetSum X S) v)) ≤
      2*(k : ℝ)*Real.exp (-((s : ℝ)*μ)/8)

/-- Finite, dimension-uniform Gram control used by the existing expansion proof. -/
def finiteGramControl : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ A : ℝ, 0 < A ∧
    ∀ {n d s : ℕ} (P : Population n d),
      0 < n → 1 ≤ d → standardized P → s ≤ n →
      A*(2*n*kappa P)*Real.log (d+1 : ℕ) ≤ (s : ℝ) →
      probability s (AronowAudit.P005.Wave1.CondT8T9_bad
        (SAP.P005a.Bridge.toPopulation P) s) < ε

end
end SAP.P005a.WH.W2
