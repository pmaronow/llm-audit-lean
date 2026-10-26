import AronowAudit.P029.Wave1.FiniteMeasureBlueprint

/-!
# P029-T21: marginal independence does not imply latent ignorability

Paper: P029 p. 499 (PDF p. 8), last sentence of the sufficiency paragraph, read with
marginal independence of effects and compliance (T21(b)).
Witness: the T3(A) law `marginalJoint` with units
`liftUnit independenceUnit`; (C,T) tables (3,3,3,1)/16 at X=0 and (1,1,1,3)/16 at X=1,
independent fair H and Z. τ is independent of the complier indicator (indeed of the full
type), but latent ignorability fails at both profiles (X=0: E(τ|X)=2/5, E(τ|C,X)=1/4) and
ICSW = 7/16 ≠ 1/2. The refutation negates the first conjunct at the profile `false`.
-/

namespace AronowAudit.P029.Wave1.MarginalSufficiency

open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical
open AronowAudit.P029 AronowAudit.P029.Wave1.FiniteMeasure

noncomputable section

/-- Negation of the claim that marginal independence implies latent
ignorability and equality of both the unweighted and inverse-score weighted IV ratios
with the ATE
(universe-0 instance). -/
def Target : Prop :=
  ¬ (∀ {Ω X : Type} [MeasurableSpace Ω]
      [Fintype X] [MeasurableSpace X] [MeasurableSingletonClass X]
      (μ : Measure Ω) [IsProbabilityMeasure μ] (U : Ω → PotentialUnit X) (Z : Ω → Bool),
      IVAssumptions μ U Z →
      (∀ x, 0 < mP μ {ω | (U ω).x = x} → 0 < scoreAt μ U x) →
      IndepFun (fun ω => (U ω).tau) (fun ω => decide (U ω).complier) μ →
      (∀ x, 0 < mP μ {ω | (U ω).x = x} → latentAt μ U x) ∧
      mWald μ U Z (fun _ => 1) = (∫ ω, (U ω).tau ∂μ) ∧
      mWald μ U Z (fun ω => 1 / scoreAt μ U (U ω).x) = (∫ ω, (U ω).tau ∂μ))


/-- Under the atomic T3(A) law: probability measure, all IV assumptions, positive scores
at positive-mass profiles (2/5 and 2/3), the profile `false` has mass 5/8 > 0, and latent
ignorability fails there (`mCE τ {x = false} = 2/5 ≠ 1/4 = mCE τ {C ∧ x = false}`). Transfer
`marginal_independence_counterexample` with `FiniteMeasure.N1`, `FiniteMeasure.N3` and `FiniteMeasure.N6`. -/
def N1 : Prop :=
  FiniteMeasure.N1 → FiniteMeasure.N2 → FiniteMeasure.N3 → FiniteMeasure.N6 →
    IsProbabilityMeasure (atomicMeasure marginalJoint) ∧
    IVAssumptions (atomicMeasure marginalJoint) (liftUnit independenceUnit) Prod.snd ∧
    (∀ x : Bool, 0 < mP (atomicMeasure marginalJoint) {i | (liftUnit independenceUnit i).x = x} →
      0 < scoreAt (atomicMeasure marginalJoint) (liftUnit independenceUnit) x) ∧
    0 < mP (atomicMeasure marginalJoint) {i | (liftUnit independenceUnit i).x = false} ∧
    ¬ latentAt (atomicMeasure marginalJoint) (liftUnit independenceUnit) false

/-- The printed
marginal premise: `τ` is independent of the literal complier indicator under the atomic
measure. From the full-type `FIndep` certificate in `marginal_independence_counterexample`,
`FiniteMeasure.N2` at `p = marginalJoint`, and `IndepFun.comp` with `bit` on the left and
`(d0,d1) ↦ decide (d0 = false ∧ d1 = true)` on the right (both measurable on finite types). -/
def N2 : Prop :=
  FiniteMeasure.N2 →
    IndepFun (fun i => (liftUnit independenceUnit i).tau)
      (fun i => decide (liftUnit independenceUnit i).complier) (atomicMeasure marginalJoint)

/-- The intermediate propositions imply the conclusion. -/
theorem assemble (hFM1 : FiniteMeasure.N1) (hFM2 : FiniteMeasure.N2)
    (hFM3 : FiniteMeasure.N3) (hFM6 : FiniteMeasure.N6) (h1 : N1) (h2 : N2) : Target := by
  intro h
  obtain ⟨hprob, hiv, hpos, hx, hnot⟩ := h1 hFM1 hFM2 hFM3 hFM6
  have := hprob
  exact hnot ((h (atomicMeasure marginalJoint) (liftUnit independenceUnit) Prod.snd hiv hpos
    (h2 hFM2)).1 false hx)

end

end AronowAudit.P029.Wave1.MarginalSufficiency
