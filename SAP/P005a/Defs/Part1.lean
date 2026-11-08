import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables false

namespace SAP.P005a

noncomputable section
open Finset Filter
open scoped BigOperators Matrix Topology

/-- Complete randomization: each size-m subset of the n labeled units occurs once. -/
def design (n m : ℕ) : Finset (Finset (Fin n)) := univ.powersetCard m

def control {n : ℕ} (S : Finset (Fin n)) : Finset (Fin n) := univ \ S

/-- The arithmetic mean on the supplied arm, with its actual cardinality as divisor. -/
def mean {n : ℕ} (S : Finset (Fin n)) (a : Fin n → ℝ) : ℝ :=
  (∑ i ∈ S, a i) / S.card

def popMean {n : ℕ} (a : Fin n → ℝ) : ℝ := mean univ a

/-- Expectation under the uniform law on all size-m treated subsets. -/
def expectation {n : ℕ} (m : ℕ) (f : Finset (Fin n) → ℝ) : ℝ :=
  (∑ S ∈ design n m, f S) / (design n m).card

def variance {n : ℕ} (m : ℕ) (f : Finset (Fin n) → ℝ) : ℝ :=
  expectation m (fun S => (f S - expectation m f)^2)

/-- The fraction of assignments satisfying an event under that same uniform law. -/
def probability {n : ℕ} (m : ℕ) (event : Finset (Fin n) → Prop) : ℝ :=
  by
    classical
    exact ((design n m).filter event).card / ((design n m).card : ℝ)

/-- The paper's covariance estimator, using divisor equal to the arm size. -/
def sampleCov {n : ℕ} (S : Finset (Fin n)) (a b : Fin n → ℝ) : ℝ :=
  mean S (fun i => a i * b i) - mean S a * mean S b

def popCov {n : ℕ} (a b : Fin n → ℝ) : ℝ := sampleCov univ a b

def centered {n : ℕ} (a : Fin n → ℝ) (i : Fin n) : ℝ := a i - popMean a

/-- The uncentered right-hand side printed in Lemma A.1. -/
def covarianceBound {n : ℕ} (m : ℕ) (a b : Fin n → ℝ) : ℝ :=
  2 * ((n : ℝ) - m) / ((m : ℝ) * (n - 1)) *
    popMean (fun i => (a i * b i - popMean (fun j => a j * b j))^2) +
  2 * ((n : ℝ) - m) * n / ((m : ℝ)^3 * (n - 1)) *
    popMean (fun i => a i^2) * popMean (fun i => b i^2)

inductive Arm | treated | control deriving DecidableEq

def armSet {n : ℕ} (t : Arm) (S : Finset (Fin n)) : Finset (Fin n) :=
  match t with | .treated => S | .control => control S

def armSize (n m : ℕ) (t : Arm) : ℕ :=
  match t with | .treated => m | .control => n - m

def witnessA : Fin 6 → ℝ := ![0, -3, -1, 2, -4, -3]

def witnessB : Fin 6 → ℝ := ![2, 1, 3, -3, 1, 1]

end
end SAP.P005a
