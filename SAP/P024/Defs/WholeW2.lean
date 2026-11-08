import Mathlib
import SAP.P024.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P024
open scoped BigOperators
noncomputable section

/-- P024-T6; between-subjects design, p. 170 (PDF p. 4).
For explicit subclasses of the paper's equal-probability individual-assignment description,
the treatment-arm outcome mean minus the control-arm outcome mean is unbiased
for the finite subject-pool average effect. Potential outcomes are fixed,
assignment is implemented as planned, all outcomes are observed, there is no
interference, and assignment is the sole randomness. The design is complete
individual randomization with 1 <= m < N, or independent common-p individual
assignment, 0 < p < 1, conditional on both arms being nonempty. The result
also covers fixed counts almost surely with actual common probabilities m/N,
and every nonempty-arm law uniform conditional on the realized count.
The Bernoulli conditioning event has positive probability; its conditional
masses are the parent masses divided by that probability. Population sizes
are at least two and both realized arms have positive denominators.
The usual measure-theoretic conditions are assumed; all laws, outcomes, and
expectations in this finite formulation are measurable and finite.
Restriction: require either a count m fixed almost surely with 0 < m < N and
every actual unit marginal m/N, or a law on proper nonempty subsets uniform
conditional on its treatment count. Complete randomization and independent
common-p assignment conditioned on nonempty arms are included. Arbitrary
equal-marginal dependent laws with varying treatment counts are not covered. -/
def T6WholeStatement_W2 : Prop :=
  (∀ (J Ω : Type*) [Fintype J] [Fintype Ω] (d : Design Ω)
      (m : ℕ), 0 < m → m < Fintype.card J →
      ∀ (z : Ω → J → Bool) (y0 y1 : J → ℝ),
      (∀ ω, d.mass ω ≠ 0 → treatedCount (z ω) = m) →
      (∀ j, exposureProbability d z j = (m : ℝ) / Fintype.card J) →
      expectation d (fun ω => clusterDIM (fun _ => 1) y0 y1 (z ω)) =
        averageEffect Finset.univ y0 y1) ∧
  (∀ (N m : ℕ), 0 < m → m < N →
      ∀ (d : Design (Finset (Fin N))), completeClusterLaw d m →
      ∀ (y0 y1 : Fin N → ℝ),
      expectation d (fun s => clusterDIM (fun _ => 1) y0 y1 (subsetExposure s)) =
        averageEffect Finset.univ y0 y1) ∧
  (∀ (k : ℕ) (p : ℝ), 0 < p → p < 1 →
      ∀ (d : Design (Finset (Fin (k + 2)))), independentClusterLaw d p →
      ∀ (y0 y1 : Fin (k + 2) → ℝ),
      0 < probability d (fun s => s ≠ ∅ ∧ s ≠ Finset.univ) ∧
      bernoulliNonemptyMass k p =
        probability d (fun s => s ≠ ∅ ∧ s ≠ Finset.univ) ∧
      (∀ s : NonemptyAllocations k, bernoulliConditionalMass k p s =
        d.mass s.val / probability d (fun t => t ≠ ∅ ∧ t ≠ Finset.univ)) ∧
      bernoulliConditionalExpectation k p
        (fun s => clusterDIM (fun _ => 1) y0 y1 (subsetExposure s.val)) =
        averageEffect Finset.univ y0 y1) ∧
  (∀ (k : ℕ) (d : Design (NonemptyAllocations k)),
      (∀ s t : NonemptyAllocations k, s.val.card = t.val.card → d.mass s = d.mass t) →
      ∀ (y0 y1 : Fin (k + 2) → ℝ),
      expectation d (fun s => clusterDIM (fun _ => 1) y0 y1 (subsetExposure s.val)) =
        averageEffect Finset.univ y0 y1)

end
end SAP.P024
