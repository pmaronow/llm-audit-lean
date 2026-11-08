import AronowAudit.P022.P022_Variance

/-!
# Blueprint: P022-T18, refutation of Lemma 2 as printed

Record: P022-T18 / `AronowAudit.P022.lemma2_as_printed`; resolution `refute`.

`Target` is the negation of the universal closure of the exact frozen contract
`lemma2_as_printed` (`Conditions123 S H θ ρ → Lemma2Conclusions S H θ ρ`, p. 860), checked
below by `Iff.rfl` against the frozen declaration's type.

Witness (fully proved; only the three standard foundations are used): `reciprocalWitness`, `originLaw`, `θ = 1`, `ρ = 1/2`
(`y1_i = y0_i = -1/(i+1)`, `m = ⌊N/2⌋`, `n = N`).  `lemma2_counterexample` proves the
printed conditions and `¬ Lemma2Conclusions` for it (map record 11; validator
P022-E001/v2 §2).

One-step record: the single node `N1` is `Target` itself; its proof is trivial and is
written (by the architect) in `AronowAudit/P022/Wave1/PrintedLemma2/N1.lean`.
Final file: `AronowAudit/P022/Wave1/PrintedLemma2.lean`, theorem
`AronowAudit.P022.Wave1.lemma2_as_printed_refuted`.
-/

set_option autoImplicit false

namespace AronowAudit.P022.Wave1.PrintedLemma2

open AronowAudit.P022

/-- **Target (P022-T18).** Exact negation of the universal closure of `lemma2_as_printed`. -/
def Target : Prop :=
  ¬ ∀ (S : ExperimentSequence) (H : JointLaw) (θ ρ : ℝ),
      Conditions123 S H θ ρ → Lemma2Conclusions S H θ ρ

/-- Fidelity check: `Target` is literally `¬` (type of the frozen declaration). Only the
frozen theorem's *type* is read; its unfinished draft proof is never used. -/
example : Target ↔ ¬ (type_of% @AronowAudit.P022.lemma2_as_printed) := Iff.rfl

/-- **Node N1** (map record 11: "If the universal printed contract were true, specialize
it to these S,H,theta,rho and feed it reciprocal_conditions123. Its conclusion contradicts
lemma2_counterexample's final component"). Equal to `Target`. -/
def N1 : Prop := Target

end AronowAudit.P022.Wave1.PrintedLemma2
