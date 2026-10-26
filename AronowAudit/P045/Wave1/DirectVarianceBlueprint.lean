import AronowAudit.P045.P045_Spillover

/-!
# P045-T26: a counterexample to direct-effect variance conservativeness

The proposition says that for all `2 ≤ C ≤ G`, local sizes with `0 < m g < n g`,
and real schedules `a b`, under the two-stage law
`selectedLaw n C (fun g => crMass (n g) (m g))`, the package's singleton-drop direct
variance estimate `vest` satisfies equality `E vest = Var point` under additive effects,
and satisfies `Var point ≤ E vest` in general. `Target` is the negation.

The counterexample has `G = 6`, `C = 3`, `n g = 3`, `m g = 2`,
`b g i = i + 1`, and `a g i = b g i + 1` (constant additive effect `d = 1`).
Then `E vest = 1/3` and `Var point = 1/2`, so both the additive equality and
conservativeness fail. The moment identity is an instance of
`singleton_variance_counterexample`.
-/

set_option autoImplicit false

namespace AronowAudit.P045.Wave1.DirectVariance

open AronowAudit.P045 Finset
open scoped BigOperators

noncomputable section

/-- The negation of the printed direct-effect variance proposition. -/
def Target : Prop :=
  ¬ ∀ {G C : ℕ}, 2 ≤ C → C ≤ G →
    ∀ (n m : Fin G → ℕ), (∀ g, 0 < m g ∧ m g < n g) →
    ∀ (a b : (g : Fin G) → Fin (n g) → ℝ),
    let law := selectedLaw n C (fun g => crMass (n g) (m g))
    let point := selectedMean C (fun g => directGroup (a g) (b g))
    let vest := directVarianceEstimate C a b
    ((∃ d : ℝ, ∀ g i, a g i=b g i+d) → expect law vest=variance law point) ∧
    variance law point ≤ expect law vest

/-- Local sizes of the witness: six groups of three units. -/
abbrev nW : Fin 6 → ℕ := fun _ => 3
/-- Treated counts of the witness: two of three units in every group. -/
abbrev mW : Fin 6 → ℕ := fun _ => 2
/-- Control schedule of the witness, `b g i = i + 1` (zero-based `i`). -/
def bW : (g : Fin 6) → Fin (nW g) → ℝ := fun _ i => (i.val : ℝ) + 1
/-- Treated schedule of the witness, `a = b + 1` (constant additive effect one). -/
def aW : (g : Fin 6) → Fin (nW g) → ℝ := fun g i => bW g i + 1

/-- For the witness, `E D = 1` and `Var D = 3/2`. The expected package variance
estimate is `1/4 + 1/12 = 1/3`, and the true point-estimator variance is
`(3/2)/3 = 1/2`. This is `singleton_variance_counterexample` at `m = 2`. -/
def N1 : Prop :=
  expect (selectedLaw nW 3 (fun g => crMass (nW g) (mW g))) (directVarianceEstimate 3 aW bW)
      = 1/3 ∧
    variance (selectedLaw nW 3 (fun g => crMass (nW g) (mW g)))
      (selectedMean 3 (fun g => directGroup (aW g) (bW g))) = 1/2

/-- At the witness the additive premise holds with `d = 1`, so the
first conjunct would give `1/3 = 1/2`. -/
theorem assemble (h1 : N1) : Target := by
  intro h
  have key := h (G := 6) (C := 3) (by norm_num) (by norm_num) nW mW
    (fun _ => by norm_num) aW bW
  simp only at key
  have hadd := key.1 ⟨1, fun g i => rfl⟩
  rw [h1.1, h1.2] at hadd
  norm_num at hadd

end

end AronowAudit.P045.Wave1.DirectVariance
