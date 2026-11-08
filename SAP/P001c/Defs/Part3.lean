import Mathlib
import SAP.P001c.Defs.Part2

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P001c

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology Classical
noncomputable section

def hadamardDerivative {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (D H : Set E) (T : E → ℝ) (F : E) (L : E →L[ℝ] ℝ) : Prop :=
  ∀ h ∈ H, ∀ t : ℕ → ℝ, ∀ hn : ℕ → E,
    (∀ n, 0 < t n) → Tendsto t atTop (nhds 0) → Tendsto hn atTop (nhds h) →
    (∀ n, F + t n • hn n ∈ D) →
    Tendsto (fun n => (T (F+t n • hn n)-T F)/t n) atTop (nhds (L h))

/-- Used only on bounded functions and bounded differences of directions. -/
def supNorm (h : ℝ → ℝ) : ℝ := sSup (Set.range (fun x => |h x|))

def isCDF (F : ℝ → ℝ) : Prop :=
  (∀ x, 0 ≤ F x ∧ F x ≤ 1) ∧ Monotone F ∧
  (∀ x, Tendsto F (nhdsWithin x (Set.Ici x)) (nhds (F x))) ∧
  Tendsto F atBot (nhds 0) ∧ Tendsto F atTop (nhds 1)

def cdfHadamard (T : (ℝ → ℝ) → ℝ) (F : ℝ → ℝ) : Prop :=
  ∃ L : (ℝ → ℝ) → ℝ,
    (∀ f g, L (fun x => f x+g x)=L f+L g) ∧
    (∀ a f, L (fun x => a*f x)=a*L f) ∧
    (∃ C : ℝ, 0 ≤ C ∧ ∀ h, BddAbove (Set.range (fun x => |h x|)) → |L h| ≤ C*supNorm h) ∧
    ∀ h : ℝ → ℝ, BddAbove (Set.range (fun x => |h x|)) →
      ∀ t : ℕ → ℝ, ∀ hn : ℕ → ℝ → ℝ, (∀ n, 0 < t n) →
        (∀ n, BddAbove (Set.range (fun x => |hn n x|))) → Tendsto t atTop (nhds 0) →
        Tendsto (fun n => supNorm (fun x => hn n x-h x)) atTop (nhds 0) →
        (∀ n, isCDF (fun x => F x+t n*hn n x)) →
        Tendsto (fun n => (T (fun x => F x+t n*hn n x)-T F)/t n) atTop (nhds (L h))

abbrev CDFSpace := lp (fun _ : ℝ => ℝ) ∞

/-- All uses below embed bounded CDFs, including the zero empirical measure at n=0. -/
def embedCDF (f : ℝ → ℝ) : CDFSpace :=
  if hf : Memℓp f ∞ then ⟨f, hf⟩ else 0

def cdfSet : Set CDFSpace := {f | isCDF (fun x => f x)}

def empiricalCDF {Ω : Type*} [MeasurableSpace Ω]
    (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : CDFSpace :=
  embedCDF (cdfAt (empiricalLaw X n ω) id)

def cdfTangent (F : ℝ → ℝ) : Set CDFSpace :=
  {h | (∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ x y : ℝ,
    |F x-F y| < δ → |h x-h y| < ε) ∧ (∀ x, F x=0 ∨ F x=1 → h x=0)}

def isCDFBridge [MeasurableSpace CDFSpace] (F : ℝ → ℝ) (ν : Measure CDFSpace) : Prop :=
  ν (cdfTangent F)ᶜ=0 ∧ ∀ r : ℕ, ∀ x a : Fin r → ℝ,
    let v := ∑ j, ∑ k, a j*(min (F (x j)) (F (x k))-F (x j)*F (x k))*a k
    0 ≤ v ∧ ν.map (fun h => ∑ j, a j*h (x j)) =
      gaussianReal 0 ⟨max v 0, le_max_right _ _⟩

/-- Bounded tests on a probability space have integrable constant majorants. -/
def upperExpectation {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (Z : Ω → ℝ) : ℝ :=
  sInf {r | ∃ g : Ω → ℝ, Measurable g ∧ Integrable g μ ∧
    (∀ ω, Z ω ≤ g ω) ∧ expectation μ g=r}

def outerWeakConvergence {Ω E : Type*} [MeasurableSpace Ω]
    [TopologicalSpace E] [MeasurableSpace E]
    (μ : Measure Ω) (Z : ℕ → Ω → E) (ν : Measure E) : Prop :=
  ∀ f : E → ℝ, Continuous f → (∃ C : ℝ, ∀ x, |f x| ≤ C) →
    Tendsto (fun n => upperExpectation μ (fun ω => f (Z n ω))) atTop (nhds (expectation ν f)) ∧
    Tendsto (fun n => -upperExpectation μ (fun ω => -f (Z n ω))) atTop (nhds (expectation ν f))

def quadraticFunctional (G : ℝ → ℝ) : ℝ := (G 0-1/2)^2

end
end SAP.P001c
