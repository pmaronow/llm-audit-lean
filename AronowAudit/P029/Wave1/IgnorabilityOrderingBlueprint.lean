import AronowAudit.P029.Wave1.FiniteMeasureBlueprint

/-!
# P029-T20: typical ignorability does not imply latent ignorability

Paper: P029 p. 499 (PDF p. 8), Assumption 1 and the comparison with "typical ignorability".
The printed implication (I) ⇒ (L) under the five IV assumptions is false.
Witness: the six-atom law `sixMass` (types C, A, N with probabilities
1/2, 1/4, 1/4, independent fair Z), units `liftUnit case1Unit` (Y₀ = 0, Y₁ = 1_C), constant
covariate `()`. All IV assumptions and both typical-ignorability equalities hold, the profile
has mass 1 and score 1/2, but the ATE is 1/2 while the complier effect is 1.
-/

namespace AronowAudit.P029.Wave1.IgnorabilityOrdering

open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical
open AronowAudit.P029 AronowAudit.P029.Wave1.FiniteMeasure

noncomputable section

/-- Negation of the printed implication from typical ignorability to latent
ignorability (universe-0 instance). -/
def Target : Prop :=
  ¬ (∀ {Ω X : Type} [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSingletonClass X]
      (μ : Measure Ω) [IsProbabilityMeasure μ] (U : Ω → PotentialUnit X) (Z : Ω → Bool),
      IVAssumptions μ U Z → ∀ (x : X), 0 < mP μ {ω | (U ω).x = x} → 0 < scoreAt μ U x →
        typicalAt μ U Z x → latentAt μ U x)


/-- The six-atom witness on the atomic measure
`atomicMeasure sixMass = ∑ᵢ ofReal(sixMass i) • δᵢ`. -/
def Witness : Prop :=
  IsProbabilityMeasure (atomicMeasure sixMass) ∧
  IVAssumptions (atomicMeasure sixMass) (liftUnit case1Unit) Prod.snd ∧
  0 < mP (atomicMeasure sixMass) {i | (liftUnit case1Unit i).x = ()} ∧
  0 < scoreAt (atomicMeasure sixMass) (liftUnit case1Unit) () ∧
  typicalAt (atomicMeasure sixMass) (liftUnit case1Unit) Prod.snd () ∧
  ¬ latentAt (atomicMeasure sixMass) (liftUnit case1Unit) ()

/-- Given the shared adapters `FiniteMeasure.N1`, `FiniteMeasure.N2`, `FiniteMeasure.N3`, `FiniteMeasure.N6`, the six-atom law is a measure-valued
witness: transfer `ignorability_counterexample` (FIV, typical ignorability, `fE τ = 1/2`,
`fCE τ C = 1`, `fScore = 1/2`) through `FiniteMeasure.N1`/`FiniteMeasure.N3`/`FiniteMeasure.N6`; profile mass is `fP sixMass True = 1`.
Note `(case1Unit i).x = ()` always, so `{complier ∧ x = ()}` is `{complier}`. -/
def N1 : Prop :=
  FiniteMeasure.N1 → FiniteMeasure.N2 → FiniteMeasure.N3 → FiniteMeasure.N6 → Witness

/-- The intermediate propositions imply the conclusion. -/
theorem assemble (hFM1 : FiniteMeasure.N1) (hFM2 : FiniteMeasure.N2)
    (hFM3 : FiniteMeasure.N3) (hFM6 : FiniteMeasure.N6) (h1 : N1) : Target := by
  intro h
  obtain ⟨hprob, hiv, hx, hc, hi, hnot⟩ := h1 hFM1 hFM2 hFM3 hFM6
  have := hprob
  exact hnot (h (atomicMeasure sixMass) (liftUnit case1Unit) Prod.snd hiv () hx hc hi)

end

end AronowAudit.P029.Wave1.IgnorabilityOrdering
