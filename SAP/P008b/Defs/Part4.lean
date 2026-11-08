import SAP.P008b.Defs.Part3

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P008b

open scoped BigOperators
open MeasureTheory Filter

noncomputable section

def commonBernoulli {N : ℕ} (Q : FiniteLaw (Assignment N)) (p : ℝ) : Prop :=
  ∀ z, Q.mass z = ∏ i, if z i then p else 1 - p

def dependsOn {N : ℕ} (P : (Fin N → Bool × ℝ) → Prop) (A : Finset (Fin N)) : Prop :=
  ∀ u v, (∀ i ∈ A, u i = v i) → (P u ↔ P v)

def boundedPairDependency {N : ℕ} (Q : FiniteLaw (Assignment N))
    (M : Fin N → Assignment N → ℝ) (D : ℕ) : Prop := by
  classical
  exact ∃ G : Fin N → Fin N → Prop,
    (∀ i j, G i j ↔ G j i) ∧
    (∀ i, (Finset.univ.filter (fun j => j ≠ i ∧ G i j)).card ≤ D) ∧
    (∀ A B : Finset (Fin N), Disjoint A B →
      (∀ i ∈ A, ∀ j ∈ B, ¬ G i j) →
      ∀ P R : (Fin N → Bool × ℝ) → Prop, dependsOn P A → dependsOn R B →
      Q.prob (fun z => P (fun i => (z i, M i z)) ∧ R (fun i => (z i, M i z))) =
        Q.prob (fun z => P (fun i => (z i, M i z))) *
          Q.prob (fun z => R (fun i => (z i, M i z))))

def finiteAMR {N : ℕ} (Q : FiniteLaw (Assignment N))
    (M : Fin N → Assignment N → ℝ) : ℝ :=
  (N : ℝ)⁻¹ * ∑ i, (marginal Q (M i) i true - marginal Q (M i) i false)

def completedHajek {N : ℕ} (M : Fin N → Assignment N → ℝ)
    (exceptional : ℝ) (z : Assignment N) : ℝ :=
  if nTreated z = 0 ∨ nControl z = 0 then exceptional else hajek M z

def toyRasterOutcome {C : ℕ} (a : ℝ) (base : Fin C → ℝ)
    (r : Fin 4 → Fin C → ℝ) (c : Fin C) (z : Assignment 4) : ℝ :=
  base c + ∑ j, bit (z j) * (a * toyKernel (r j c))

def toyRasterAMR {C : ℕ} (Q : FiniteLaw (Assignment 4)) (a : ℝ)
    (base : Fin C → ℝ) (r w : Fin 4 → Fin C → ℝ) : ℝ :=
  (1 / 4 : ℝ) * ∑ i, ∑ c, w i c *
    (marginal Q (toyRasterOutcome a base r c) i true -
      marginal Q (toyRasterOutcome a base r c) i false)

/-- Positive finite circle mass and integrable potential outcomes. -/
def SpatialModel.validCircle {N : ℕ} (P : SpatialModel N) (i : Fin N) (d : ℝ) : Prop :=
  0 < P.circleMass i d ∧ P.circleMeasure i d Set.univ ≠ ⊤ ∧
    ∀ z, Integrable (fun x => P.Y x z) (P.circleMeasure i d)

/-- The supplied archived buffer formula, with the first grid index numbered zero. -/
def bufferRule {X : Type*} (B : ℕ → Finset X) (Y : X → ℝ) (j : ℕ) : ℝ :=
  if j = 0 then countMean (B 0) Y else
    ((∑ x ∈ B j, Y x) - (∑ x ∈ B (j - 1), Y x)) /
      ((B j).card - ((B (j - 1)).card : ℝ))

/-- A finite buffer selected by supplied nonnegative boundary distances. -/
def distanceBuffer {X : Type*} (C : Finset X) (ρ : X → ℝ) (r : ℝ) : Finset X := by
  classical exact C.filter (fun x => ρ x ≤ r)

end

end SAP.P008b
