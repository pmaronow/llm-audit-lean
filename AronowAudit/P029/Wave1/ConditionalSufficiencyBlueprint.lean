import AronowAudit.P029.Wave1.FiniteMeasureBlueprint

/-!
# Wave1 blueprint: P029-T21, `AronowAudit.P029.printed_conditional_sufficiency` (refute)

Paper: P029 p. 499 (PDF p. 8), last sentence of the sufficiency paragraph, read with
independence of effects and compliance type conditional on X (T21(c)). Resolution: `refute`.
Witness (mapper record 3): the T3(B) law `conditionalJoint` with units
`liftUnit independenceUnit`; (C,T) tables (9,3,3,1)/32 at X=0 and (1,3,3,9)/32 at X=1,
independent fair H and Z. Conditional independence holds under the literal normalized
restriction, latent ignorability and ICSW = ATE hold, but the unweighted IV ratio is 5/8
while the ATE is 1/2. The refutation negates the middle conjunct of the printed conclusion.

`Target` is the negation of the universe-0 instance of the held contract (checked by `rfl`).
Final theorem (writers): `AronowAudit.P029.Wave1.printed_conditional_sufficiency_refuted`
in `AronowAudit/P029/Wave1/ConditionalSufficiency.lean`.
-/

namespace AronowAudit.P029.Wave1.ConditionalSufficiency

open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical
open AronowAudit.P029 AronowAudit.P029.Wave1.FiniteMeasure

noncomputable section

/-- The frozen final statement: the negation of the printed contract
`printed_conditional_sufficiency` (universe-0 instance). -/
def Target : Prop :=
  ¬ (∀ {Ω X : Type} [MeasurableSpace Ω]
      [Fintype X] [MeasurableSpace X] [MeasurableSingletonClass X]
      (μ : Measure Ω) [IsProbabilityMeasure μ] (U : Ω → PotentialUnit X) (Z : Ω → Bool),
      IVAssumptions μ U Z →
      (∀ x, 0 < mP μ {ω | (U ω).x = x} → 0 < scoreAt μ U x) →
      (∀ x, 0 < mP μ {ω | (U ω).x = x} →
        IndepFun (fun ω => (U ω).tau) (fun ω => ((U ω).d0, (U ω).d1))
          (ENNReal.ofReal ((mP μ {ω | (U ω).x = x})⁻¹) • μ.restrict {ω | (U ω).x = x})) →
      (∀ x, 0 < mP μ {ω | (U ω).x = x} → latentAt μ U x) ∧
      mWald μ U Z (fun _ => 1) = (∫ ω, (U ω).tau ∂μ) ∧
      mWald μ U Z (fun ω => 1 / scoreAt μ U (U ω).x) = (∫ ω, (U ω).tau ∂μ))

/-- Fidelity check: `Target` is literally the negation of the held declaration's statement. -/
theorem target_eq_negated_printed :
    Target = ¬ (type_of% @AronowAudit.P029.printed_conditional_sufficiency.{0, 0}) := rfl

/-- **Node R3-N1** (`conditional_sufficiency_witness`; mapper record 3, paper-proof steps 1-2,
4 and 6). Under the atomic T3(B) law: probability measure, all IV assumptions, positive scores
at positive-mass profiles (scores 1/4 and 3/4), and unweighted IV `mWald (·↦1) = 5/8 ≠ 1/2 =
∫ τ`. Transfer `conditional_independence_counterexample` with FM-N1, FM-N3 and FM-N6. -/
def N1 : Prop :=
  FiniteMeasure.N1 → FiniteMeasure.N2 → FiniteMeasure.N3 → FiniteMeasure.N6 →
    IsProbabilityMeasure (atomicMeasure conditionalJoint) ∧
    IVAssumptions (atomicMeasure conditionalJoint) (liftUnit independenceUnit) Prod.snd ∧
    (∀ x : Bool, 0 < mP (atomicMeasure conditionalJoint) {i | (liftUnit independenceUnit i).x = x} →
      0 < scoreAt (atomicMeasure conditionalJoint) (liftUnit independenceUnit) x) ∧
    mWald (atomicMeasure conditionalJoint) (liftUnit independenceUnit) Prod.snd (fun _ => 1) ≠
      ∫ i, (liftUnit independenceUnit i).tau ∂(atomicMeasure conditionalJoint)

/-- **Node R3-N2** (`conditional_finite_to_measure_independence` instance; mapper record 3,
step 3). The printed conditional-independence premise holds at every positive-mass profile,
for the literal normalized restricted measure of the held contract. From the `FCondIndep`
part of `conditional_independence_counterexample` (with `T = i.1.1.2.1`), FM-N5 at
`p = conditionalJoint`, then `IndepFun.comp` with `bit` (`τ = bit T - 0`); rewrite
`mP = fP` by FM-N1 to match the scaling constant. -/
def N2 : Prop :=
  FiniteMeasure.N1 → FiniteMeasure.N2 → FiniteMeasure.N4 → FiniteMeasure.N5 →
    ∀ x : Bool, 0 < mP (atomicMeasure conditionalJoint) {i | (liftUnit independenceUnit i).x = x} →
      IndepFun (fun i => (liftUnit independenceUnit i).tau)
        (fun i => ((liftUnit independenceUnit i).d0, (liftUnit independenceUnit i).d1))
        (ENNReal.ofReal ((mP (atomicMeasure conditionalJoint)
            {i | (liftUnit independenceUnit i).x = x})⁻¹) •
          (atomicMeasure conditionalJoint).restrict {i | (liftUnit independenceUnit i).x = x})

/-- The nodes suffice. -/
theorem assemble (hFM1 : FiniteMeasure.N1) (hFM2 : FiniteMeasure.N2)
    (hFM3 : FiniteMeasure.N3) (hFM4 : FiniteMeasure.N4) (hFM5 : FiniteMeasure.N5)
    (hFM6 : FiniteMeasure.N6) (h1 : N1) (h2 : N2) : Target := by
  intro h
  obtain ⟨hprob, hiv, hpos, hne⟩ := h1 hFM1 hFM2 hFM3 hFM6
  have := hprob
  exact hne (h (atomicMeasure conditionalJoint) (liftUnit independenceUnit) Prod.snd hiv hpos
    (h2 hFM1 hFM2 hFM4 hFM5)).2.1

end

end AronowAudit.P029.Wave1.ConditionalSufficiency
