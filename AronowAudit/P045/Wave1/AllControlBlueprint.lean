import AronowAudit.P045.P045_Spillover

/-!
# P045-T27: a counterexample to the all-untreated equivalence

The proposition says that for every `Network n`, assignment `z`, and unit `i`,
the coded indicator `s_i < b_i` (`badAllControl`) holds if and only if every member
of the closed neighbourhood of `i` is untreated. `Target` is its negation.

The counterexample is the two-unit network with adjacency `edge2` (`i ≠ j`),
assignment `(true,false)`, and unit `0`. Its closed neighbourhood is `{0,1}` with
one treated member, so `1 < 2` holds while unit `0` itself is treated.
-/

set_option autoImplicit false

namespace AronowAudit.P045.Wave1.AllControl

open AronowAudit.P045 Finset

noncomputable section

/-- The negation of the documented all-untreated equivalence. -/
def Target : Prop :=
  ¬ ∀ {n : ℕ} (A : Network n) (z : Assignment n) (i : Fin n),
    badAllControl A.adj z i ↔ ∀ j ∈ neighborhood A.adj i, z j=false

/-- The two-unit network with a single undirected tie.
Inequality is symmetric and no unit is adjacent to itself. -/
def edge2Network : Network 2 where
  adj := edge2
  symmetric := by decide
  loopless := by decide

/-- At unit `0` in the two-unit witness, the coded inequality is `1 < 2`,
but the closed neighbourhood contains the treated unit `0`. -/
def N1 : Prop :=
  badAllControl edge2 ![true, false] 0 ∧
    ¬ ∀ j ∈ neighborhood edge2 0, (![true, false] : Assignment 2) j = false

/-- The nodes suffice: the documented biconditional at `edge2Network`, `(true,false)`,
unit `0` would turn the true coded indicator into the false all-untreated claim. -/
theorem assemble (h1 : N1) : Target := by
  intro h
  exact h1.2 ((h edge2Network ![true, false] 0).1 h1.1)

end

end AronowAudit.P045.Wave1.AllControl
