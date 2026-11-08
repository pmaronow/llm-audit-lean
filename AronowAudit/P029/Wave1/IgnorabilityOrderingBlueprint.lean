import AronowAudit.P029.Wave1.FiniteMeasureBlueprint

/-!
# Wave1 blueprint: P029-T20, `AronowAudit.P029.printed_ignorability_ordering` (refute)

Paper: P029 p. 499 (PDF p. 8), Assumption 1 and the comparison with "typical ignorability".
Resolution: `refute`. The printed implication (I) ⇒ (L) under the five IV assumptions is false.
Witness (mapper record 1): the six-atom law `sixMass` (types C, A, N with probabilities
1/2, 1/4, 1/4, independent fair Z), units `liftUnit case1Unit` (Y₀ = 0, Y₁ = 1_C), constant
covariate `()`. All IV assumptions and both typical-ignorability equalities hold, the profile
has mass 1 and score 1/2, but the ATE is 1/2 while the complier effect is 1.

`Target` is the negation of the universe-0 instance of the held contract; the fidelity
theorem `target_eq_negated_printed` checks by `rfl` that it is literally
`¬ (type of AronowAudit.P029.printed_ignorability_ordering.{0,0})` (the held proof itself,
which is unfinished, is never used: `type_of%` only reads its statement).

Final theorem (writers): `AronowAudit.P029.Wave1.printed_ignorability_ordering_refuted`
in `AronowAudit/P029/Wave1/IgnorabilityOrdering.lean`, proved by `assemble`.
-/

namespace AronowAudit.P029.Wave1.IgnorabilityOrdering

open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical
open AronowAudit.P029 AronowAudit.P029.Wave1.FiniteMeasure

noncomputable section

/-- The frozen final statement: the negation of the printed contract
`printed_ignorability_ordering` (universe-0 instance). -/
def Target : Prop :=
  ¬ (∀ {Ω X : Type} [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSingletonClass X]
      (μ : Measure Ω) [IsProbabilityMeasure μ] (U : Ω → PotentialUnit X) (Z : Ω → Bool),
      IVAssumptions μ U Z → ∀ (x : X), 0 < mP μ {ω | (U ω).x = x} → 0 < scoreAt μ U x →
        typicalAt μ U Z x → latentAt μ U x)

/-- Fidelity check: `Target` is literally the negation of the held declaration's statement. -/
theorem target_eq_negated_printed :
    Target = ¬ (type_of% @AronowAudit.P029.printed_ignorability_ordering.{0, 0}) := rfl

/-- The closed six-atom witness (mapper record 1, proposed statement), on the atomic measure
`atomicMeasure sixMass = ∑ᵢ ofReal(sixMass i) • δᵢ`. -/
def Witness : Prop :=
  IsProbabilityMeasure (atomicMeasure sixMass) ∧
  IVAssumptions (atomicMeasure sixMass) (liftUnit case1Unit) Prod.snd ∧
  0 < mP (atomicMeasure sixMass) {i | (liftUnit case1Unit i).x = ()} ∧
  0 < scoreAt (atomicMeasure sixMass) (liftUnit case1Unit) () ∧
  typicalAt (atomicMeasure sixMass) (liftUnit case1Unit) Prod.snd () ∧
  ¬ latentAt (atomicMeasure sixMass) (liftUnit case1Unit) ()

/-- **Node R1-N1** (`six_atom_ordering_refutation`; mapper record 1, paper-proof steps 1-5).
Given the shared adapters FM-N1, FM-N2, FM-N3, FM-N6, the six-atom law is a measure-valued
witness: transfer `ignorability_counterexample` (FIV, typical ignorability, `fE τ = 1/2`,
`fCE τ C = 1`, `fScore = 1/2`) through FM-N1/FM-N3/FM-N6; profile mass is `fP sixMass True = 1`.
Note `(case1Unit i).x = ()` always, so `{complier ∧ x = ()}` is `{complier}`. -/
def N1 : Prop :=
  FiniteMeasure.N1 → FiniteMeasure.N2 → FiniteMeasure.N3 → FiniteMeasure.N6 → Witness

/-- The nodes suffice. -/
theorem assemble (hFM1 : FiniteMeasure.N1) (hFM2 : FiniteMeasure.N2)
    (hFM3 : FiniteMeasure.N3) (hFM6 : FiniteMeasure.N6) (h1 : N1) : Target := by
  intro h
  obtain ⟨hprob, hiv, hx, hc, hi, hnot⟩ := h1 hFM1 hFM2 hFM3 hFM6
  have := hprob
  exact hnot (h (atomicMeasure sixMass) (liftUnit case1Unit) Prod.snd hiv () hx hc hi)

end

end AronowAudit.P029.Wave1.IgnorabilityOrdering
