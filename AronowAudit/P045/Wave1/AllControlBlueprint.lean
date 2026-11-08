import AronowAudit.P045.P045_Spillover

/-!
# Blueprint: refutation of `AronowAudit.P045.all_control_as_documented` (P045-T27)

Record: P045-T27 / `AronowAudit.P045.all_control_as_documented`; resolution `refute`.
Frozen contract (P045_Spillover.lean:4662): for every `Network n`, assignment `z` and unit
`i`, the coded indicator `s_i < b_i` (`badAllControl`) holds iff every member of the closed
neighbourhood of `i` is untreated.

`Target` is the negation of exactly that contract; the `example` checks by `Iff.rfl` that it
is the negation of the frozen type.

Witness (paper proof, record 11): the genuine `Network 2` with adjacency `edge2`
(`i ≠ j`), assignment `(true,false)`, unit `0`. Its closed neighbourhood is `{0,1}` with
one treated member, so `1 < 2` holds while unit `0` itself is treated. The network
structure `edge2Network` (symmetry and looplessness by `decide`) and node `N1` are trivial
and proved by the blueprint author (`N1` in `AronowAudit/P045/Wave1/AllControl/N1.lean`).
-/

set_option autoImplicit false

namespace AronowAudit.P045.Wave1.AllControl

open AronowAudit.P045 Finset

noncomputable section

/-- The frozen statement to be resolved: the negation of the exact recorded contract
`all_control_as_documented`. -/
def Target : Prop :=
  ¬ ∀ {n : ℕ} (A : Network n) (z : Assignment n) (i : Fin n),
    badAllControl A.adj z i ↔ ∀ j ∈ neighborhood A.adj i, z j=false

/-- Fidelity check: `Target` is literally `¬` (type of the frozen declaration). Only the
frozen theorem's *type* is read; its `sorry` proof is never used. -/
example : Target ↔ ¬ (type_of% @AronowAudit.P045.all_control_as_documented) := Iff.rfl

/-- The two-unit network with a single undirected tie (paper proof, record 11: "Define
A.adj(i,j) to be true iff i≠j; inequality is symmetric and i≠i is false, giving a
legitimate Network 2"). -/
def edge2Network : Network 2 where
  adj := edge2
  symmetric := by decide
  loopless := by decide

/-- **Node N1** (paper proof, record 11: "badAllControl is the true inequality 1<2. The
documented universal statement is false: at unit i=0 its neighborhood contains j=0 and
z_0=true≠false"). Source: `full_neighborhood_counterexample` and `full_control_correct`. -/
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
