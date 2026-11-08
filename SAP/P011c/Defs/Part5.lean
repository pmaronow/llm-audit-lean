import Mathlib
import SAP.P011c.Defs.Part1

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P011c

open Finset
open scoped BigOperators Classical

noncomputable section

/-- Each unordered candidate edge occurs once, with its smaller endpoint first. -/
abbrev Edge (n : ℕ) := {ij : Fin n × Fin n // ij.1 < ij.2}

def edgeDegree {n : ℕ} (S : Finset (Edge n)) (i : Fin n) : ℕ :=
  (S.filter (fun e => e.val.1 = i ∨ e.val.2 = i)).card

/-- Degree-constrained edge selections, with all mandatory edges selected. -/
def DegreeFeasible {n : ℕ} (forced : Finset (Edge n)) (d : Fin n → ℕ)
    (S : Finset (Edge n)) : Prop :=
  forced ⊆ S ∧ ∀ i, edgeDegree S i ≤ d i

/-- A 0/1 knapsack item uses one unit at each of its two endpoints. -/
def IncidenceFeasible {n : ℕ} (forced : Finset (Edge n)) (d : Fin n → ℕ)
    (S : Finset (Edge n)) : Prop :=
  forced ⊆ S ∧ ∀ i,
    (∑ e ∈ S, if e.val.1 = i ∨ e.val.2 = i then (1 : ℕ) else 0) ≤ d i

/-- Empirical edge profits in program (3.6), allowing either sign. -/
def edgeProfit {n : ℕ} (x : Fin n → ℝ) (S : Finset (Edge n)) : ℝ :=
  ∑ e ∈ S, centered x e.val.1 * centered x e.val.2

/-- The variance objective in unordered-edge coordinates, before graph maximization. -/
def edgeProgramVariance {n : ℕ} (x : Fin n → ℝ) (S : Finset (Edge n)) : ℝ :=
  ((∑ i, centered x i ^ 2) + 2 * edgeProfit x S) / (n : ℝ)^2

/-- Exactly the same maximizers in the degree program and the incidence knapsack. -/
def T30Statement : Prop :=
  ∀ (n : ℕ), 0 < n → ∀ (forced : Finset (Edge n)) (d : Fin n → ℕ)
    (x : Fin n → ℝ) (S : Finset (Edge n)),
    (DegreeFeasible forced d S ∧ ∀ T, DegreeFeasible forced d T →
      edgeProgramVariance x T ≤ edgeProgramVariance x S) ↔
    (IncidenceFeasible forced d S ∧ ∀ T, IncidenceFeasible forced d T →
      edgeProfit x T ≤ edgeProfit x S)

end
end SAP.P011c
