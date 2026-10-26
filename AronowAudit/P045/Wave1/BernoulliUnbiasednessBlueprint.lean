import AronowAudit.P045.P045_Spillover

/-!
# P045-T25: a counterexample to Bernoulli arm-mean unbiasedness

The proposition is a two-part conjunction: (i) for every `n > 0`, `0 < p < 1`,
real schedule `y`, and arm `b`, the Bernoulli conditional arm mean on its nonempty-arm
domain equals the average own-treatment marginal; (ii) five hierarchy clauses under
an arbitrary first-stage design. `Target` is the negation of the whole conjunction.
A conjunction implies its first component, so one counterexample to (i) suffices.

Take `n = 4`, `p = 1/2`, `b = true`, and `y = coMembers` (number of treated peers).
The treated arm exists with probability `15/16`; its conditional mean is
`E[K-1 | K>0] = 17/15`; every marginal is `3p = 3/2`.
-/

set_option autoImplicit false

namespace AronowAudit.P045.Wave1.BernoulliUnbiasedness

open AronowAudit.P045 Finset
open scoped BigOperators

noncomputable section

/-- The negation of the printed Bernoulli unbiasedness proposition. -/
def Target : Prop :=
  ¬ (
    (∀ n : ℕ, 0 < n → ∀ p : ℝ, 0 < p → p < 1 →
      ∀ y : Fin n → Assignment n → ℝ, ∀ b : Bool,
      condMean (bernoulli p) (armExists b) (armMean y b) = mean (fun i => marginal (bernoulli p) y i b)) ∧
    (∀ G : ℕ, 0 < G → ∀ n : Fin G → ℕ, (∀ g, 0 < n g) →
      ∀ S : Design (Assignment G), ∀ ψ φ : ℝ, 0 < ψ → ψ < 1 → 0 < φ → φ < 1 →
      ∀ y : (g : Fin G) → Fin (n g) → Assignment (n g) → ℝ,
      let law := hierarchyLaw n S ψ φ
      let M := hierarchyArm y
      let μ := hierarchyTarget y
      (∀ high b, 0 < prob law (hierarchyDomain high b) →
        condMean law (hierarchyDomain high b) (M high b) = μ (if high then ψ else φ) b) ∧
      (∀ high, let E := fun w => hierarchyDomain high true w ∧ hierarchyDomain high false w;
        0 < prob law E → condMean law E (fun w => M high true w-M high false w) =
          μ (if high then ψ else φ) true-μ (if high then ψ else φ) false) ∧
      (let E := fun w => hierarchyDomain true false w ∧ hierarchyDomain false false w;
        0 < prob law E → condMean law E (fun w => M true false w-M false false w) = μ ψ false-μ φ false) ∧
      (let E := fun w => hierarchyDomain true true w ∧ hierarchyDomain false false w;
        0 < prob law E → condMean law E (fun w => M true true w-M false false w) = μ ψ true-μ φ false) ∧
      (let E := fun w : Assignment G × GroupAssignments n =>
          (regimeGroups w.1 true).Nonempty ∧ (regimeGroups w.1 false).Nonempty;
        0 < prob law E → condMean law E (fun w => hierarchyOverall y true w-hierarchyOverall y false w) =
          mean (fun g => mean (fun i => expect (bernoulli ψ) (y g i))) -
          mean (fun g => mean (fun i => expect (bernoulli φ) (y g i)))))
    )

/-- The conditional treated-arm mean of the peer-count schedule under fair Bernoulli
assignment of four units is `32/15 - 1 = 17/15`. The count-law calculation uses
`bernoulli_arm_count_conditional` and `bernoulli_count_counterexample`. -/
def N1 : Prop :=
  condMean (bernoulli (1/2 : ℝ)) (armExists true) (armMean (coMembers (n := 4)) true) = 17/15

/-- Every treated marginal target is `3/2`, by `co_members_marginal_four`;
hence their mean is `3/2`. -/
def N2 : Prop :=
  mean (fun i : Fin 4 => marginal (bernoulli (1/2 : ℝ)) coMembers i true) = 3/2

/-- The nodes suffice: the first conjunct at `n = 4, p = 1/2, y = coMembers, b = true`
would give `17/15 = 3/2`. -/
theorem assemble (h1 : N1) (h2 : N2) : Target := by
  intro h
  have key := h.1 4 (by norm_num) (1/2) (by norm_num) (by norm_num) coMembers true
  rw [h1, h2] at key
  norm_num at key

end

end AronowAudit.P045.Wave1.BernoulliUnbiasedness
