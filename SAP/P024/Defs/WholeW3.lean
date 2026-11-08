import Mathlib
import SAP.P024.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P024
open scoped BigOperators
noncomputable section

/-- Note 4's overall Horvitz–Thompson contrast, using the actual design
inclusion probabilities and the observed outcomes. The randomized units are
the disjoint union of the finite types `I b`; excluded units are absent.
Used below only when the population and both arm probabilities are positive. -/
def actualBlockedHTW3 {B Ω : Type*} [Fintype B] [Fintype Ω]
    (I : B → Type*) [∀ b, Fintype (I b)] (d : Design Ω)
    (z : Ω → (b : B) → I b → Bool) (y0 y1 : (b : B) → I b → ℝ)
    (ω : Ω) : ℝ :=
  (∑ b, ∑ i,
    (indicator (z ω b i) * observed (fun υ => z υ b) (y0 b) (y1 b) ω i /
        exposureProbability d (fun υ => z υ b) i -
    (1 - indicator (z ω b i)) * observed (fun υ => z υ b) (y0 b) (y1 b) ω i /
        (1 - exposureProbability d (fun υ => z υ b) i))) / blockPopulation I

/-- P024-T8; fixed-quota specialization of weighted blocked estimation,
p. 173 (PDF p. 7), and Note 4, p. 177 (PDF p. 11).
The actual-probability Horvitz–Thompson estimate equals on every allocation the
population-share weighted average of ordinary within-block differences in means,
and both estimators are unbiased for the individual average effect among randomized units.
Restriction: each predetermined block has a fixed quota 0 < m_b < N_b on every
assignment, and every unit in that block has actual treatment probability m_b/N_b.
These are additional design assumptions relative to the canonical statement;
variable block treatment counts and unequal within-block propensities are not covered.
Balanced nonuniform laws and dependent assignments across blocks are allowed.
Potential outcomes are fixed, depend only on own treatment, and are all observed.
Excluded units are outside the estimand. All population, arm-count and probability
denominators are positive; all expectations are finite sums on a finite design. -/
def T8WholeStatement_W3 : Prop :=
  ∀ (B Ω : Type*) [Fintype B] [Nonempty B] [Fintype Ω]
    (I : B → Type*) [∀ b, Fintype (I b)] (d : Design Ω) (m : B → ℕ),
    (∀ b, 0 < m b) → (∀ b, m b < Fintype.card (I b)) →
    ∀ (z : Ω → (b : B) → I b → Bool) (y0 y1 : (b : B) → I b → ℝ),
    (∀ ω b, treatedCount (z ω b) = m b) →
    (∀ b i, exposureProbability d (fun ω => z ω b) i =
      (m b : ℝ) / Fintype.card (I b)) →
    0 < blockPopulation I ∧
    (∀ b i, 0 < exposureProbability d (fun ω => z ω b) i ∧
      exposureProbability d (fun ω => z ω b) i < 1) ∧
    (∀ ω, actualBlockedHTW3 I d z y0 y1 ω =
      ∑ b, (Fintype.card (I b) : ℝ) / blockPopulation I *
        clusterDIM (fun _ => 1) (y0 b) (y1 b) (z ω b)) ∧
    expectation d (actualBlockedHTW3 I d z y0 y1) =
      (∑ b, ∑ i, (y1 b i - y0 b i)) / blockPopulation I ∧
    expectation d (fun ω => ∑ b, (Fintype.card (I b) : ℝ) / blockPopulation I *
      clusterDIM (fun _ => 1) (y0 b) (y1 b) (z ω b)) =
      (∑ b, ∑ i, (y1 b i - y0 b i)) / blockPopulation I

end
end SAP.P024
