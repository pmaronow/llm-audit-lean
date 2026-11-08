import Mathlib
import SAP.P001g.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P001g

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology

noncomputable section
universe u

/-- The fixed first component, on the three outcomes 0, 1, 2. -/
def circleBaseW2 : Fin 3 → ℝ :=
  ![Real.sqrt 2 / 4, Real.sqrt 2 / 4, 1 - Real.sqrt 2 / 2]

/-- The closed Euclidean unit disc, written in ordinary real coordinates. -/
def circleDiscW2 : Set (Fin 2 → ℝ) := {z | z 0 ^ 2 + z 1 ^ 2 ≤ 1}

/-- The unit circle of admissible parameters for the second component. -/
def circleBoundaryW2 : Set (Fin 2 → ℝ) := {b | b 0 ^ 2 + b 1 ^ 2 = 1}

/-- The affine PMF map A on the disc; its restriction to the circle is g₂. -/
def circleAffineW2 (z : Fin 2 → ℝ) : Fin 3 → ℝ :=
  ![Real.sqrt 2 / 4 + z 0 / 10,
    Real.sqrt 2 / 4 + (z 1 - z 0) / 10,
    1 - Real.sqrt 2 / 2 - z 1 / 10]

/-- The second component g₂, indexed by a point of the unit circle. -/
def circleSecondW2 (b : Fin 2 → ℝ) : Fin 3 → ℝ := circleAffineW2 b

/-- The full parameter vector (p,b₁,b₂) lies in [0,1] × S¹. -/
def circleThetaW2 : Set (Fin 3 → ℝ) :=
  {t | t 0 ∈ Set.Icc (0 : ℝ) 1 ∧ t 1 ^ 2 + t 2 ^ 2 = 1}

/-- The two-component mixture, with weight p on the fixed first component. -/
def circleMixW2 (t : Fin 3 → ℝ) (y : Fin 3) : ℝ :=
  t 0 * circleBaseW2 y +
    (1 - t 0) * circleSecondW2 (![t 1, t 2] : Fin 2 → ℝ) y

/-- The disc coordinate (1-p)b of a full parameter vector. -/
def circleProjectionW2 (t : Fin 3 → ℝ) : Fin 2 → ℝ :=
  ![(1 - t 0) * t 1, (1 - t 0) * t 2]

/-- Every (1,b) is a true full vector when the first component alone is the law. -/
def circleTruthW2 (b : Fin 2 → ℝ) : Fin 3 → ℝ := ![1, b 0, b 1]

/-- The sample likelihood over the full parameter space. The empty product is
used only to choose an arbitrary value of the estimator at sample size zero. -/
def circleLikeW2 {n : ℕ} (s : Fin n → Fin 3) (t : Fin 3 → ℝ) : ℝ :=
  ∏ i, circleMixW2 t (s i)

/-- The same sample likelihood in disc coordinates. -/
def circleDiscLikeW2 {n : ℕ} (s : Fin n → Fin 3) (z : Fin 2 → ℝ) : ℝ :=
  ∏ i, circleAffineW2 z (s i)

/-- Outcome counts in a finite sample, including outcomes not observed. -/
def circleCountW2 {n : ℕ} (s : Fin n → Fin 3) (y : Fin 3) : ℕ :=
  (Finset.univ.filter fun i => s i = y).card

/-- The book's unique arg max estimator: every sample of every positive size
has exactly one maximizing full vector. At zero only attainment is required.
Every statistic here is measurable because its sample domain is finite. -/
def CircleMLEW2 (that : ∀ n : ℕ, (Fin n → Fin 3) → Fin 3 → ℝ) : Prop :=
  ∀ n s, that n s ∈ circleThetaW2 ∧
    IsMaxOn (circleLikeW2 s) circleThetaW2 (that n s) ∧
    (0 < n → ∀ t ∈ circleThetaW2,
      circleLikeW2 s t = circleLikeW2 s (that n s) → t = that n s)

/-- P001-T121. Location: Section 5.2.5, p. 199 (PDF p. 217), second paragraph;
Definitions 5.1.1 and 5.2.2; unique arg max convention, Glossary p. 285.
The printed claim is false: in this compact two-component mixture on three
outcomes, the sample likelihood has a unique maximizer for every sample of
every positive size, so the book's unique arg max estimator is defined
everywhere. The first component alone characterizes the true law, but this
estimator cannot be consistent for every true full vector (1,b), where the
unused component's parameter b ranges over the unit circle. The refuted
assertion does not assume identification of the full vector. Failure of
consistency refutes the consistency-and-asymptotic-efficiency conjunction;
no separate definition or refutation of efficiency is needed. The usual
measure-theoretic conditions are assumed; all sample statistics are measurable. -/
def T121WholeStatement : Prop :=
  ¬ (∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → Fin 3), IID μ X →
    ∀ b : Fin 2 → ℝ, b ∈ circleBoundaryW2 →
    μ.map (X 0) = ∑ y : Fin 3,
      ENNReal.ofReal (circleMixW2 (circleTruthW2 b) y) • Measure.dirac y →
    ∀ that : ∀ n : ℕ, (Fin n → Fin 3) → Fin 3 → ℝ,
      CircleMLEW2 that →
      CP μ (fun n ω => that n (firstSample X n ω)) (circleTruthW2 b))

end
end SAP.P001g
