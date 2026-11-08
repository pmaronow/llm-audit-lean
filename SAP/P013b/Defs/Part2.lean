import Mathlib
import SAP.P013b.Defs.Part1

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables false

namespace SAP.P013b
open scoped BigOperators Topology NNReal ENNReal
open Filter Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {Ω : Type*} [Fintype Ω]

def VectorIndependent {N K : ℕ} (P : Design Ω) (D : Ω → Fin N → Fin K)
    (A B : Finset (Fin N)) : Prop :=
  ∀ a b : Fin N → Fin K,
    probability P (fun z => (∀ i ∈ A, D z i = a i) ∧ (∀ j ∈ B, D z j = b j)) =
      probability P (fun z => ∀ i ∈ A, D z i = a i) *
      probability P (fun z => ∀ j ∈ B, D z j = b j)

def PrintedNoEdge {N : ℕ} (h : Fin N → Fin N → Bool) (A B : Finset (Fin N)) : Prop :=
  ¬ ∃ i j, h i j = true ∧
    ((i ∈ A ∧ j ∉ B) ∨ (j ∈ A ∧ i ∉ B) ∨
      (i ∉ A ∧ j ∈ B) ∨ (j ∉ A ∧ i ∈ B))

def PrintedDependency {N K : ℕ} (P : Design Ω) (D : Ω → Fin N → Fin K)
    (h : Fin N → Fin N → Bool) : Prop :=
  ∀ A B, Disjoint A B → PrintedNoEdge h A B → VectorIndependent P D A B

def RowBound {N : ℕ} (h : Fin N → Fin N → Bool) (m : ℕ) : Prop :=
  ∀ i, ∑ j, (if h i j = true then 1 else 0 : ℕ) ≤ m

def PairIndependent {N K : ℕ} {P : Design Ω} (F : Population P N K) (i j : Fin N) : Prop :=
  ∀ d e, jointPi F i j d e = pi F i d * pi F j e

def ConvergesInProbability {L : ℕ → Type*} [∀ n : ℕ, Fintype (L n)]
    (P : ∀ n : ℕ, Design (L n)) (X : ∀ n : ℕ, L n → ℝ) (a : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → Tendsto (fun n : ℕ => probability (P n) (fun z => ε < |X n z-a|)) atTop (𝓝 0)

def normalCDF (x : ℝ) : ℝ := ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1) x

/-- Standard Gaussian critical value; coverage clauses restrict the level to 0 < α < 1. -/
def normalCritical (α : ℝ) : ℝ := sInf {x : ℝ | 1-α/2 ≤ normalCDF x}

structure Experiment (N : ℕ) where
  supportSize : ℕ
  exposureSize : ℕ
  design : Design (Fin supportSize)
  population : Population design N exposureSize

structure ExperimentSequence where
  experiment : ∀ n : ℕ, Experiment (n+1)
  treated : ∀ n : ℕ, Fin (experiment n).exposureSize
  control : ∀ n : ℕ, Fin (experiment n).exposureSize
  distinct : ∀ n : ℕ, treated n ≠ control n
  positiveTreated : ∀ n : ℕ, Positivity (experiment n).population (treated n)
  positiveControl : ∀ n : ℕ, Positivity (experiment n).population (control n)

def NestedPopulationSetup (S : ExperimentSequence) : Prop :=
  ∃ labels : ∀ n, Fin (S.experiment n).exposureSize ↪ ℕ,
    ∃ d e : ℕ, ∃ outcomes : ℕ → ℕ → ℝ, d ≠ e ∧
      (∀ n, labels n (S.treated n) = d ∧ labels n (S.control n) = e) ∧
      (∀ n (i : Fin (n+1)) a,
        (S.experiment n).population.outcome i a = outcomes i.val (labels n a))

abbrev seqLaw (S : ExperimentSequence) (n : ℕ) := (S.experiment n).design

abbrev seqPopulation (S : ExperimentSequence) (n : ℕ) := (S.experiment n).population

abbrev seqEstimate (S : ExperimentSequence) (n : ℕ) :=
  htEffect (seqPopulation S n) (S.treated n) (S.control n)

abbrev seqTarget (S : ExperimentSequence) (n : ℕ) :=
  causalEffect (seqPopulation S n) (S.treated n) (S.control n)

abbrev seqTrueVariance (S : ExperimentSequence) (n : ℕ) := variance (seqLaw S n) (seqEstimate S n)

abbrev seqVarianceEstimate (S : ExperimentSequence) (n : ℕ) :=
  effectVariance (seqPopulation S n) (S.treated n) (S.control n)

def StandingPositivity (S : ExperimentSequence) : Prop :=
  ∀ n d, Positivity (seqPopulation S n) d

def Condition3 (S : ExperimentSequence) : Prop :=
  ∃ c1 c2 : ℝ, 0 ≤ c1 ∧ 0 < c2 ∧ ∀ n i d,
    |(seqPopulation S n).outcome i d| ≤ c1 ∧
    |1 / pi (seqPopulation S n) i d| ≤ c2

def Condition4 (S : ExperimentSequence) : Prop :=
  ∃ g : ∀ n : ℕ, Fin (n+1) → Fin (n+1) → Bool,
    (∀ n i j, g n i j = false → PairIndependent (seqPopulation S n) i j) ∧
    Tendsto (fun n : ℕ => (∑ i, ∑ j, (if g n i j = true then 1 else 0 : ℝ)) / (n+1 : ℝ)^2)
      atTop (𝓝 0)

def Condition5Printed (S : ExperimentSequence) : Prop :=
  ∃ m : ℕ, ∃ h : ∀ n : ℕ, Fin (n+1) → Fin (n+1) → Bool, ∀ n : ℕ,
    PrintedDependency (seqLaw S n) (seqPopulation S n).exposure (h n) ∧ RowBound (h n) m

def Condition6 (S : ExperimentSequence) : Prop :=
  ∃ c : ℝ, 0 < c ∧ Tendsto (fun n : ℕ => (n+1 : ℝ)*seqTrueVariance S n) atTop (𝓝 c)

/-- Defined Wald intervals: a negative estimated variance gives no coverage event. -/
def seqCoverage (S : ExperimentSequence) (α : ℝ) (n : ℕ) :=
  probability (seqLaw S n) (fun z => 0 ≤ seqVarianceEstimate S n z ∧
    |seqEstimate S n z-seqTarget S n| ≤ normalCritical α * Real.sqrt (seqVarianceEstimate S n z))

end
end SAP.P013b
