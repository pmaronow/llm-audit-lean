import AronowAudit.P045.Wave1.DirectVarianceBlueprint
import AronowAudit.P045.Wave1.DirectVariance.N1

/-!
P045-T26: a counterexample to the direct-effect variance proposition.
-/

set_option autoImplicit false

namespace AronowAudit.P045.Wave1

open AronowAudit.P045 Finset
open scoped BigOperators

/-- The direct-effect variance proposition fails on the additive witness. -/
theorem direct_variance_as_printed_refuted :
  ¬ ∀ {G C : ℕ}, 2 ≤ C → C ≤ G →
    ∀ (n m : Fin G → ℕ), (∀ g, 0 < m g ∧ m g < n g) →
    ∀ (a b : (g : Fin G) → Fin (n g) → ℝ),
    let law := selectedLaw n C (fun g => crMass (n g) (m g))
    let point := selectedMean C (fun g => directGroup (a g) (b g))
    let vest := directVarianceEstimate C a b
    ((∃ d : ℝ, ∀ g i, a g i=b g i+d) → expect law vest=variance law point) ∧
    variance law point ≤ expect law vest := by
  exact DirectVariance.assemble
    DirectVariance.n1_proof

end AronowAudit.P045.Wave1
