import SAP.P013a.Defs.Part2

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P013a

open scoped BigOperators Topology NNReal ENNReal
open Filter Finset
noncomputable section

variable {Ω Ξ : Type*} [Fintype Ω] [Fintype Ξ]

def ConvergesInProbability {L : ℕ → Type*} [∀ n : ℕ, Fintype (L n)]
    (P : ∀ n : ℕ, Design (L n)) (X : ∀ n : ℕ, L n → ℝ) (a : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → Tendsto (fun n : ℕ => probability (P n) (fun z => ε < |X n z-a|)) atTop (𝓝 0)

def normalCDF (x : ℝ) : ℝ := ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1) x

def normalCritical (α : ℝ) : ℝ := sInf {x : ℝ | 1-α/2 ≤ normalCDF x}

def TendsNormal {L : ℕ → Type*} [∀ n : ℕ, Fintype (L n)]
    (P : ∀ n : ℕ, Design (L n)) (X : ∀ n : ℕ, L n → ℝ) (μ : ℝ) (v : ℝ≥0) : Prop :=
  ∀ x : ℝ, Tendsto (fun n : ℕ => probability (P n) (fun z => X n z ≤ x)) atTop
    (𝓝 (ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal μ v) x))

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

def ComparisonBounded (S : ExperimentSequence) : Prop :=
  ∃ c1 c2 : ℝ, 0 ≤ c1 ∧ 0 < c2 ∧ ∀ n i,
    |(seqPopulation S n).outcome i (S.treated n)| ≤ c1 ∧
    |(seqPopulation S n).outcome i (S.control n)| ≤ c1 ∧
    |1 / pi (seqPopulation S n) i (S.treated n)| ≤ c2 ∧
    |1 / pi (seqPopulation S n) i (S.control n)| ≤ c2

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

def Condition5Genuine (S : ExperimentSequence) : Prop :=
  ∃ m : ℕ, ∃ h : ∀ n : ℕ, Fin (n+1) → Fin (n+1) → Bool, ∀ n : ℕ,
    (∀ i j, h n i j = h n j i) ∧
    GenuineDependency (seqLaw S n) (seqPopulation S n).exposure (h n) ∧ RowBound (h n) m

def Condition6 (S : ExperimentSequence) : Prop :=
  ∃ c : ℝ, 0 < c ∧ Tendsto (fun n : ℕ => (n+1 : ℝ)*seqTrueVariance S n) atTop (𝓝 c)

def LowerTailCondition (S : ExperimentSequence) : Prop :=
  ∀ δ : ℝ, 0 < δ → Tendsto (fun n : ℕ => probability (seqLaw S n)
    (fun z => (n+1 : ℝ)*seqVarianceEstimate S n z < (n+1 : ℝ)*seqTrueVariance S n-δ))
      atTop (𝓝 0)

def seqCoverage (S : ExperimentSequence) (α : ℝ) (n : ℕ) :=
  probability (seqLaw S n) (fun z => 0 ≤ seqVarianceEstimate S n z ∧
    |seqEstimate S n z-seqTarget S n| ≤ normalCritical α * Real.sqrt (seqVarianceEstimate S n z))

def JointLowerBound (S : ExperimentSequence) (b : ℝ) : Prop :=
  ∀ n i j, i ≠ j →
    (jointPi (seqPopulation S n) i j (S.treated n) (S.treated n) = 0 ∨
      b ≤ jointPi (seqPopulation S n) i j (S.treated n) (S.treated n)) ∧
    (jointPi (seqPopulation S n) i j (S.control n) (S.control n) = 0 ∨
      b ≤ jointPi (seqPopulation S n) i j (S.control n) (S.control n)) ∧
    (jointPi (seqPopulation S n) i j (S.treated n) (S.control n) = 0 ∨
      b ≤ jointPi (seqPopulation S n) i j (S.treated n) (S.control n))

def PositiveJointDomain (S : ExperimentSequence) (n : ℕ) : Prop :=
  ∃ i j : Fin (n+1), i ≠ j ∧
    (0 < jointPi (seqPopulation S n) i j (S.treated n) (S.treated n) ∨
     0 < jointPi (seqPopulation S n) i j (S.control n) (S.control n) ∨
     0 < jointPi (seqPopulation S n) i j (S.treated n) (S.control n))

def IsMinimumPositiveJoint (S : ExperimentSequence) (n : ℕ) (b : ℝ) : Prop :=
  0 < b ∧
  (∃ i j : Fin (n+1), i ≠ j ∧
    (b = jointPi (seqPopulation S n) i j (S.treated n) (S.treated n) ∨
     b = jointPi (seqPopulation S n) i j (S.control n) (S.control n) ∨
     b = jointPi (seqPopulation S n) i j (S.treated n) (S.control n))) ∧
  (∀ i j : Fin (n+1), i ≠ j →
    (0 < jointPi (seqPopulation S n) i j (S.treated n) (S.treated n) →
      b ≤ jointPi (seqPopulation S n) i j (S.treated n) (S.treated n)) ∧
    (0 < jointPi (seqPopulation S n) i j (S.control n) (S.control n) →
      b ≤ jointPi (seqPopulation S n) i j (S.control n) (S.control n)) ∧
    (0 < jointPi (seqPopulation S n) i j (S.treated n) (S.control n) →
      b ≤ jointPi (seqPopulation S n) i j (S.treated n) (S.control n)))
end
end SAP.P013a
