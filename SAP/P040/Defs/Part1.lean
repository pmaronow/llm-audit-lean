import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P040
open scoped BigOperators
open MeasureTheory
noncomputable section

abbrev DetectionCount := Fin 16

def binomialMass (p : ℝ) (k : DetectionCount) : ℝ :=
  (Nat.choose 15 k.val : ℝ) * p ^ k.val * (1 - p) ^ (15 - k.val)

def countProbability (p : ℝ) (E : DetectionCount → Prop) : ℝ := by
  classical
  exact ∑ k, if E k then binomialMass p k else 0

def intervalCoverage (p : ℝ) (I : DetectionCount → Set ℝ) : ℝ :=
  countProbability p (fun k => p ∈ I k)

def roundsTwo (x w : ℝ) : Prop := w - 1 / 200 ≤ x ∧ x < w + 1 / 200

def detectionProportion (k : DetectionCount) : ℝ := (k.val : ℝ) / 15

def waldRadius (z : ℝ) (k : DetectionCount) : ℝ :=
  z * Real.sqrt (detectionProportion k * (1 - detectionProportion k) / 15)

def waldInterval (z : ℝ) (k : DetectionCount) : Set ℝ :=
  Set.Icc (detectionProportion k - waldRadius z k)
    (detectionProportion k + waldRadius z k)

def upperDetectionTail (p : ℝ) (k : DetectionCount) : ℝ :=
  countProbability p (fun j => k ≤ j)

def lowerDetectionTail (p : ℝ) (k : DetectionCount) : ℝ :=
  countProbability p (fun j => j ≤ k)

def exactDetectionInterval (k : DetectionCount) : Set ℝ :=
  {p | p ∈ Set.Icc (0 : ℝ) 1 ∧
    (1 : ℝ) / 40 ≤ upperDetectionTail p k ∧ (1 : ℝ) / 40 ≤ lowerDetectionTail p k}

def exactDetectionLowerSet (k : DetectionCount) : Set ℝ :=
  {p | p ∈ Set.Icc (0 : ℝ) 1 ∧ (1 : ℝ) / 20 ≤ upperDetectionTail p k}

def observedUpperPolynomial (p : ℝ) : ℝ := p ^ 14 * (15 - 14 * p)

/-- Rounding at six decimal places, with the same half-open convention as roundsTwo. -/
def roundsSix (x w : ℝ) : Prop := w - 1 / 2000000 ≤ x ∧ x < w + 1 / 2000000

/-- The reconstructed interval arithmetic shared by T1 and T3. -/
def printedWaldArithmetic : Prop :=
    detectionProportion 14 = (14 : ℝ) / 15 ∧
    detectionProportion 14 * (1 - detectionProportion 14) / 15 = (14 : ℝ) / 3375 ∧
    waldRadius (49 / 25) 14 ^ 2 = (33614 : ℝ) / 2109375 ∧
    (8070 / 10000 : ℝ) < detectionProportion 14 - waldRadius (49 / 25) 14 ∧
    detectionProportion 14 - waldRadius (49 / 25) 14 < (8071 / 10000 : ℝ) ∧
    (10595 / 10000 : ℝ) < detectionProportion 14 + waldRadius (49 / 25) 14 ∧
    detectionProportion 14 + waldRadius (49 / 25) 14 < (10596 / 10000 : ℝ) ∧
    roundsTwo (detectionProportion 14 - waldRadius (49 / 25) 14) (81 / 100) ∧
    roundsTwo (detectionProportion 14 + waldRadius (49 / 25) 14) (106 / 100) ∧
    (1 : ℝ) < detectionProportion 14 + waldRadius (49 / 25) 14 ∧
    (4 / 5 : ℝ) ∉ waldInterval (49 / 25) 14

/-- The finite-calibration obstruction for arbitrary count-based sets and lower bounds. -/
def methodFreeObstruction : Prop :=
    (∀ I : DetectionCount → Set ℝ, (4 / 5 : ℝ) ∉ I 14 →
      intervalCoverage (4 / 5) I ≤ (5298209257 : ℝ) / 6103515625 ∧
      intervalCoverage (4 / 5) I < (19 : ℝ) / 20) ∧
    (∀ ell : DetectionCount → ℝ, (4 / 5 : ℝ) < ell 14 →
      countProbability (4 / 5) (fun k => ell k ≤ 4 / 5) ≤
        (5298209257 : ℝ) / 6103515625 ∧
      countProbability (4 / 5) (fun k => ell k ≤ 4 / 5) < (19 : ℝ) / 20)

/-- `T1Statement` is the base binomial and Wald component of T1; the actual normal
quantile clauses are added by `T1WholeStatement`. -/
def T1Statement : Prop :=
    binomialMass (4 / 5) 14 = (805306368 : ℝ) / 6103515625 ∧
    (1 : ℝ) / 20 < binomialMass (4 / 5) 14 ∧
    methodFreeObstruction ∧
    (4 / 5 : ℝ) ∉ Set.Ioo (81 / 100 : ℝ) (106 / 100) ∧
    (∀ l : ℝ, roundsTwo l (81 / 100) → (4 / 5 : ℝ) < l) ∧
    printedWaldArithmetic ∧
    (∀ z : ℝ, (19599 / 10000 : ℝ) ≤ z → z ≤ (19601 / 10000 : ℝ) →
      (∀ k : DetectionCount,
        ((4 / 5 : ℝ) ∈ waldInterval z k ↔ 9 ≤ k.val ∧ k.val ≤ 13) ∧
        ((4 / 5 : ℝ) ∈ waldInterval z k ↔
          (4 / 5 - detectionProportion k) ^ 2 ≤ z ^ 2 *
            (detectionProportion k * (1 - detectionProportion k) / 15)) ∧
        (detectionProportion k - waldRadius z k ≤ (4 / 5 : ℝ) ↔ k.val ≤ 13)) ∧
      intervalCoverage (4 / 5) (waldInterval z) = (24866193408 : ℝ) / 30517578125 ∧
      intervalCoverage (4 / 5) (waldInterval z) < (19 : ℝ) / 20 ∧
      countProbability (4 / 5) (fun k => detectionProportion k - waldRadius z k ≤ 4 / 5) =
        (25417304461 : ℝ) / 30517578125 ∧
      countProbability (4 / 5) (fun k => detectionProportion k - waldRadius z k ≤ 4 / 5) <
        (19 : ℝ) / 20 ∧
      countProbability (4 / 5) (fun k => (4 / 5 : ℝ) < detectionProportion k - waldRadius z k) =
        (5100273664 : ℝ) / 30517578125 ∧
      (1 : ℝ) / 20 < countProbability (4 / 5)
        (fun k => (4 / 5 : ℝ) < detectionProportion k - waldRadius z k) ∧
      (1 : ℝ) / 40 < countProbability (4 / 5)
        (fun k => (4 / 5 : ℝ) < detectionProportion k - waldRadius z k))

end
end SAP.P040
