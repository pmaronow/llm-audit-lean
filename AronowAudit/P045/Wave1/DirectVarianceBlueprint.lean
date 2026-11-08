import AronowAudit.P045.P045_Spillover

/-!
# Blueprint: refutation of `AronowAudit.P045.direct_variance_as_printed` (P045-T26)

Record: P045-T26 / `AronowAudit.P045.direct_variance_as_printed`; resolution `refute`.
Frozen contract (P045_Spillover.lean:4649): for all `2 ≤ C ≤ G`, local sizes with
`0 < m g < n g` and real schedules `a b`, under the two-stage law
`selectedLaw n C (fun g => crMass (n g) (m g))`, the package's singleton-drop direct
variance estimate `vest` satisfies (additive effects → `E vest = Var point`) and
`Var point ≤ E vest`.

`Target` is the negation of exactly that contract; the `example` checks by `Iff.rfl` that it
is the negation of the frozen type.

Witness (paper proof, record 10): `G = 6`, `C = 3`, `n g = 3`, `m g = 2`,
`b g i = i + 1`, `a g i = b g i + 1` (constant additive effect `d = 1`). Then
`E vest = 1/3` and `Var point = 1/2`: the additive equality fails (and so does
conservativeness). Node `N1` is a direct instance of the proved
`singleton_variance_counterexample` and is proved by the blueprint author in
`AronowAudit/P045/Wave1/DirectVariance/N1.lean`.
-/

set_option autoImplicit false

namespace AronowAudit.P045.Wave1.DirectVariance

open AronowAudit.P045 Finset
open scoped BigOperators

noncomputable section

/-- The frozen statement to be resolved: the negation of the exact recorded contract
`direct_variance_as_printed`. -/
def Target : Prop :=
  ¬ ∀ {G C : ℕ}, 2 ≤ C → C ≤ G →
    ∀ (n m : Fin G → ℕ), (∀ g, 0 < m g ∧ m g < n g) →
    ∀ (a b : (g : Fin G) → Fin (n g) → ℝ),
    let law := selectedLaw n C (fun g => crMass (n g) (m g))
    let point := selectedMean C (fun g => directGroup (a g) (b g))
    let vest := directVarianceEstimate C a b
    ((∃ d : ℝ, ∀ g i, a g i=b g i+d) → expect law vest=variance law point) ∧
    variance law point ≤ expect law vest

/-- Fidelity check: `Target` is literally `¬` (type of the frozen declaration). Only the
frozen theorem's *type* is read; its `sorry` proof is never used. -/
example : Target ↔ ¬ (type_of% @AronowAudit.P045.direct_variance_as_printed) := Iff.rfl

/-- Local sizes of the witness: six groups of three units. -/
abbrev nW : Fin 6 → ℕ := fun _ => 3
/-- Treated counts of the witness: two of three units in every group. -/
abbrev mW : Fin 6 → ℕ := fun _ => 2
/-- Control schedule of the witness, `b g i = i + 1` (zero-based `i`). -/
def bW : (g : Fin 6) → Fin (nW g) → ℝ := fun _ i => (i.val : ℝ) + 1
/-- Treated schedule of the witness, `a = b + 1` (constant additive effect one). -/
def aW : (g : Fin 6) → Fin (nW g) → ℝ := fun g i => bW g i + 1

/-- **Node N1** (paper proof, record 10, paragraphs 2-3: "E D=1 and Var D=3/2 ... Hence
E vest=1/4+1/12=1/3"; "their average has variance (3/2)/3=1/2"). For the witness, the
expected package variance estimate is `1/3` and the true variance of the point
estimator is `1/2`. Direct instance of `singleton_variance_counterexample` at `m = 2`. -/
def N1 : Prop :=
  expect (selectedLaw nW 3 (fun g => crMass (nW g) (mW g))) (directVarianceEstimate 3 aW bW)
      = 1/3 ∧
    variance (selectedLaw nW 3 (fun g => crMass (nW g) (mW g)))
      (selectedMean 3 (fun g => directGroup (aW g) (bW g))) = 1/2

/-- The nodes suffice: at the witness the additive premise holds with `d = 1`, so the
frozen first conjunct would give `1/3 = 1/2`. -/
theorem assemble (h1 : N1) : Target := by
  intro h
  have key := h (G := 6) (C := 3) (by norm_num) (by norm_num) nW mW
    (fun _ => by norm_num) aW bW
  simp only at key
  have hadd := key.1 ⟨1, fun g i => rfl⟩
  rw [h1.1, h1.2] at hadd
  norm_num at hadd

/-- Nonvacuity record: every hypothesis of the frozen contract holds at the witness,
including the additive-effect premise of its first conjunct. -/
example : 2 ≤ (3 : ℕ) ∧ (3 : ℕ) ≤ 6 ∧ (∀ g, 0 < mW g ∧ mW g < nW g) ∧
    (∃ d : ℝ, ∀ g i, aW g i = bW g i + d) :=
  ⟨by norm_num, by norm_num, fun _ => by norm_num, ⟨1, fun _ _ => rfl⟩⟩

end

end AronowAudit.P045.Wave1.DirectVariance
