import AronowAudit.P045.Wave1.BernoulliUnbiasednessBlueprint
import AronowAudit.P045.Wave1.BernoulliUnbiasedness.N1
import AronowAudit.P045.Wave1.BernoulliUnbiasedness.N2

/-!
P045-T25: a counterexample to conditional Bernoulli arm-mean unbiasedness.
-/

set_option autoImplicit false

namespace AronowAudit.P045.Wave1

open AronowAudit.P045 Finset
open scoped BigOperators

/-- The conditional arm-mean unbiasedness proposition fails. -/
theorem bernoulli_unbiasedness_as_printed_refuted :
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
    ) := by
  exact BernoulliUnbiasedness.assemble
    BernoulliUnbiasedness.n1_proof
    BernoulliUnbiasedness.n2_proof

end AronowAudit.P045.Wave1
