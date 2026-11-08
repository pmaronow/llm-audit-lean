import AronowAudit.P045.P045_Spillover

/-!
# Blueprint: refutation of `AronowAudit.P045.bernoulli_unbiasedness_as_printed` (P045-T25)

Record: P045-T25 / `AronowAudit.P045.bernoulli_unbiasedness_as_printed`; resolution `refute`.
The frozen contract (P045_Spillover.lean:4618) is a two-part conjunction: (i) for every
`n > 0`, `0 < p < 1`, real schedule `y` and arm `b`, the Bernoulli conditional arm mean on
its nonempty-arm domain equals the average own-treatment marginal; (ii) five hierarchy
clauses under an arbitrary first-stage design.

`Target` is the negation of the whole frozen conjunction, copied verbatim from the source
(the `example` below checks by `Iff.rfl` that it is the negation of the frozen type).
A conjunction implies its first component, so refuting (i) at one instance suffices.

Witness (paper proof, record 8): `n = 4`, `p = 1/2`, `b = true`, `y = coMembers`
(number of treated peers). The treated arm exists with probability `15/16`; the
conditional treated-arm mean is `E[K-1 | K>0] = 17/15`; every marginal is `3p = 3/2`.

Nodes `N1`, `N2` are each one or two lines from proved source lemmas and are proved by
the blueprint author in `AronowAudit/P045/Wave1/BernoulliUnbiasedness/N1.lean`, `N2.lean`.
-/

set_option autoImplicit false

namespace AronowAudit.P045.Wave1.BernoulliUnbiasedness

open AronowAudit.P045 Finset
open scoped BigOperators

noncomputable section

/-- The frozen statement to be resolved: the negation of the exact recorded proposition
`bernoulli_unbiasedness_as_printed` (body copied verbatim from P045_Spillover.lean). -/
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

/-- Fidelity check: `Target` is literally `¬` (type of the frozen declaration). Only the
frozen theorem's *type* is read; its `sorry` proof is never used. -/
example : Target ↔ ¬ (type_of% @AronowAudit.P045.bernoulli_unbiasedness_as_printed) := Iff.rfl

/-- **Node N1** (paper proof, record 8, second paragraph: "condMean(bernoulli(1/2),
armExists(true), armMean(y,true)) = 32/15 - 1 = 17/15"): the conditional treated-arm
mean of the peer-count schedule under fair Bernoulli assignment of four units.
Source: `bernoulli_arm_count_conditional` (cube → count law) and
`bernoulli_count_counterexample` (count-law value `17/15`). -/
def N1 : Prop :=
  condMean (bernoulli (1/2 : ℝ)) (armExists true) (armMean (coMembers (n := 4)) true) = 17/15

/-- **Node N2** (paper proof, record 8, first paragraph: "marginal_i(b)=3/2 for each i ...
The mean of the four treated marginal targets is therefore 3/2"). Source:
`co_members_marginal_four`. -/
def N2 : Prop :=
  mean (fun i : Fin 4 => marginal (bernoulli (1/2 : ℝ)) coMembers i true) = 3/2

/-- The nodes suffice: the first conjunct at `n = 4, p = 1/2, y = coMembers, b = true`
would give `17/15 = 3/2`. -/
theorem assemble (h1 : N1) (h2 : N2) : Target := by
  intro h
  have key := h.1 4 (by norm_num) (1/2) (by norm_num) (by norm_num) coMembers true
  rw [h1, h2] at key
  norm_num at key

/-- Nonvacuity record: the instance satisfies the first conjunct's hypotheses
(`0 < 4`, `0 < 1/2 < 1`). The conditioning event `armExists true` has probability
`15/16 > 0` under this law (paper proof and both referees), so the failure is on the
estimator's actual domain, not an artifact of the totalized `0/0`. -/
example : 0 < (4 : ℕ) ∧ (0 : ℝ) < 1/2 ∧ (1/2 : ℝ) < 1 := by norm_num

end

end AronowAudit.P045.Wave1.BernoulliUnbiasedness
