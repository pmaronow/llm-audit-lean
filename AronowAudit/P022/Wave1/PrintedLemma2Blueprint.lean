import AronowAudit.P022.P022_Variance

/-!
# P022-T18: refutation of Lemma 2 as printed

`Target` negates the universal statement
`Conditions123 S H θ ρ → Lemma2Conclusions S H θ ρ` (p. 860).

The counterexample uses `reciprocalWitness`, `originLaw`, `θ = 1`, `ρ = 1/2`
(`y1_i = y0_i = -1/(i+1)`, `m = ⌊N/2⌋`, `n = N`). The theorem
`lemma2_counterexample` gives the printed conditions and `¬ Lemma2Conclusions`
for this witness (P022-E001).
-/

set_option autoImplicit false

namespace AronowAudit.P022.Wave1.PrintedLemma2

open AronowAudit.P022

/-- **Target (P022-T18).** Negation of the universal statement of printed Lemma 2. -/
def Target : Prop :=
  ¬ ∀ (S : ExperimentSequence) (H : JointLaw) (θ ρ : ℝ),
      Conditions123 S H θ ρ → Lemma2Conclusions S H θ ρ

/-- The same proposition as `Target`: the universal statement of printed Lemma 2 is false. -/
def N1 : Prop := Target

end AronowAudit.P022.Wave1.PrintedLemma2
