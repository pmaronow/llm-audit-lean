import Mathlib
import SAP.P010.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P010

open MeasureTheory Set Filter
open scoped ENNReal NNReal

universe u

/-- The nonnegative extended mass of the squared density ratio. Positivity
of the two densities is required almost everywhere in the transport statement. -/
noncomputable def squareRatioMass {Ω : Type u} [MeasurableSpace Ω]
    (ν : Measure Ω) (fR fO : Ω → ℝ) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal ((fR x)^2 / fO x) ∂ν

/-- Total mass under the printed study odds, with replication membership
coded one. The extended integral also records infinite weighted mass. -/
noncomputable def printedWeightedMass {Ω : Type u} [MeasurableSpace Ω]
    (ν : Measure Ω) (π : ℝ) (fR fO : Ω → ℝ) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal (fR x * odds (propensity π (fR x) (fO x))) ∂ν

/-- P010-T12; p. 578 (PDF p. 7), corrected footnote 7.
With true study propensities and positive common-support probability densities,
Bayes' odds identities hold. The odds of original-study membership transport
the replication density to the original density, and a positive constant in
the weights cancels. Coding original membership one gives these same odds.
Printed odds instead give the normalized squared-density ratio when its
extended mass is finite and positive; this equals the original density exactly
when the two densities agree almost everywhere. If that mass is infinite,
the printed weighted mass is infinite and no finite nonnegative constant
normalizes it to a probability measure. Counting measure includes discrete
covariates. These identities concern true propensities, without a claim of
exact balance for a fitted logistic propensity. -/
def T12WholeStatement : Prop :=
  ∀ (Ω : Type u) [MeasurableSpace Ω] (ν : Measure Ω) (π : ℝ) (fR fO : Ω → ℝ),
    0 < π → π < 1 →
    (∀ᵐ x ∂ν, 0 < fR x) → (∀ᵐ x ∂ν, 0 < fO x) →
    Integrable fR ν → Integrable fO ν →
    (∫ x, fR x ∂ν) = 1 → (∫ x, fO x ∂ν) = 1 →
    let Z := squareRatioMass ν fR fO
    (∀ᵐ x ∂ν,
      0 < propensity π (fR x) (fO x) ∧ propensity π (fR x) (fO x) < 1 ∧
      odds (propensity π (fR x) (fO x)) = π / (1-π) * (fR x / fO x) ∧
      fO x / fR x = π / (1-π) * reverseOdds (propensity π (fR x) (fO x))) ∧
    (∀ᵐ x ∂ν,
      odds (1 - propensity π (fR x) (fO x)) =
        reverseOdds (propensity π (fR x) (fO x))) ∧
    Integrable (fun x => fR x * reverseOdds (propensity π (fR x) (fO x))) ν ∧
    (∫ x, fR x * reverseOdds (propensity π (fR x) (fO x)) ∂ν) = (1-π) / π ∧
    ((fun x => normalizeDensity ν fR
      (fun y => reverseOdds (propensity π (fR y) (fO y))) x) =ᵐ[ν] fO) ∧
    (∀ c : ℝ, 0 < c →
      (fun x => normalizeDensity ν fR
        (fun y => c * reverseOdds (propensity π (fR y) (fO y))) x) =ᵐ[ν] fO) ∧
    printedWeightedMass ν π fR fO = ENNReal.ofReal (π / (1-π)) * Z ∧
    (Z < ⊤ →
      Integrable (fun x => (fR x)^2 / fO x) ν ∧
      0 < Z ∧ 0 < Z.toReal ∧
      0 < printedWeightedMass ν π fR fO ∧ printedWeightedMass ν π fR fO < ⊤ ∧
      Integrable (fun x => fR x * odds (propensity π (fR x) (fO x))) ν ∧
      (∫ x, fR x * odds (propensity π (fR x) (fO x)) ∂ν) =
        (π / (1-π)) * Z.toReal ∧
      0 < (∫ x, fR x * odds (propensity π (fR x) (fO x)) ∂ν) ∧
      ((fun x => normalizeDensity ν fR
        (fun y => odds (propensity π (fR y) (fO y))) x) =ᵐ[ν]
        fun x => ((fR x)^2 / fO x) / Z.toReal) ∧
      (((fun x => normalizeDensity ν fR
        (fun y => odds (propensity π (fR y) (fO y))) x) =ᵐ[ν] fO) ↔ fR =ᵐ[ν] fO)) ∧
    (Z = ⊤ →
      printedWeightedMass ν π fR fO = ⊤ ∧
      ∀ c : ℝ≥0, ¬ IsProbabilityMeasure
        (ν.withDensity (fun x => (c : ℝ≥0∞) *
          ENNReal.ofReal (fR x * odds (propensity π (fR x) (fO x))))))

/-- The observed population law of the binary check and the treatment arm. -/
noncomputable def observedCheckArmLaw {K d : ℕ} (μ : Measure (Population K d)) :
    Measure (Bool × Fin K) :=
  μ.map (fun ω => (check ω, arm ω))

/-- Corrected Assumption 3 expressed using only the observed joint law.
In the whole statement this law is a probability law with positive arm masses,
so every displayed conditional-probability denominator is positive and finite. -/
def observablePositivePassRates {K : ℕ} (Q : Measure (Bool × Fin K)) : Prop :=
  ∀ a : Fin K,
    0 < (Q {v | v.1 = true ∧ v.2 = a}).toReal / (Q {v | v.2 = a}).toReal

/-- P010-T17; p. 574 (PDF p. 3), corrected Assumption 3.
Admissible populations are required to have positive probability of passing
the manipulation check in every treatment arm: Pr(S=1 | Z=z)>0.
Under the standing probability-law and ignorability assumptions, this is
exactly the additional requirement in the population assumptions, and all
conditioning denominators are positive. The requirement is determined by
the observed joint law of (S,Z); populations with the same observed law agree
on whether it holds. This is an imposed assumption, with no additional premise
about potential passing and no assertion of certainty from a finite sample. -/
def T17WholeStatement : Prop :=
  ∀ {K d : ℕ} (μ : Measure (Population K d)),
    IsProbabilityMeasure μ → randomAssignment μ →
    (populationAssumptions μ ↔
      ∀ a : Fin K,
        0 < (μ (passed ∩ assigned a)).toReal / (μ (assigned a)).toReal) ∧
    (populationAssumptions μ →
      ∀ a : Fin K, 0 < (μ (assigned a)).toReal ∧
        0 < (μ (passed ∩ assigned a)).toReal / (μ (assigned a)).toReal) ∧
    (positivePassRates μ ↔ observablePositivePassRates (observedCheckArmLaw μ)) ∧
    (∀ {d' : ℕ} (ν : Measure (Population K d')),
      IsProbabilityMeasure ν → randomAssignment ν →
      observedCheckArmLaw μ = observedCheckArmLaw ν →
      (positivePassRates μ ↔ positivePassRates ν))

end SAP.P010
