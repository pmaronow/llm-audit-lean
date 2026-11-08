import Mathlib
import SAP.P042.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P042

noncomputable section

open Finset MeasureTheory ProbabilityTheory
open scoped BigOperators Classical

/-- Real probability of an event; all uses below are under a probability measure. -/
def eventProbabilityW2 {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (A : Set Ω) : ℝ := (μ A).toReal

/-- Mean on a positive-probability event, defined by its restricted integral. -/
def eventMeanW2 {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : Ω → ℝ) (A : Set Ω) : ℝ :=
  (∫ ω in A, X ω ∂μ) / eventProbabilityW2 μ A

/-- Note 2 and p. 30 on an arbitrary probability space: independent assignment
balances each potential outcome between the two positive-probability arms, and
the observed contrast equals the average assignment effect. -/
def RandomizedBalanceW2 : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Z : Ω → Bool), Measurable Z →
    (∀ z : Bool, 0 < eventProbabilityW2 μ {ω | Z ω = z}) →
    ∀ (Y : Ω → Bool → ℝ), (∀ t, Measurable (fun ω => Y ω t)) →
    (∀ t, Integrable (fun ω => Y ω t) μ) →
    IndepFun Z (fun ω => (Y ω false, Y ω true)) μ →
      (∀ t z : Bool, eventMeanW2 μ (fun ω => Y ω t) {ω | Z ω = z} =
        ∫ ω, Y ω t ∂μ) ∧
      eventMeanW2 μ (fun ω => Y ω (Z ω)) {ω | Z ω = true} -
        eventMeanW2 μ (fun ω => Y ω (Z ω)) {ω | Z ω = false} =
          ∫ ω, Y ω true - Y ω false ∂μ

/-- The one-sided contact model: only assigned Compliers are contacted and
outcomes depend on their own contact alone (exclusion and no interference). -/
def randomContactOutcomeW2 {Ω : Type*} (Y : Ω → Bool → ℝ)
    (c Z : Ω → Bool) (ω : Ω) : ℝ := Y ω (Z ω && c ω)

/-- Population version of p. 32 under independent assignment, with positive
arm probabilities and positive Complier share. The treated contact mean is
the Complier share; the control contact mean is zero. CACE is the conditional
mean contact effect among all Compliers, and is the turnout contrast divided
by the treated contact mean. -/
def RandomizedContactW2 : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Z c : Ω → Bool), Measurable Z → Measurable c →
    (∀ z : Bool, 0 < eventProbabilityW2 μ {ω | Z ω = z}) →
    0 < eventProbabilityW2 μ {ω | c ω = true} →
    ∀ (Y : Ω → Bool → ℝ), (∀ t, Measurable (fun ω => Y ω t)) →
    (∀ t, Integrable (fun ω => Y ω t) μ) →
    IndepFun Z (fun ω => (c ω, (Y ω false, Y ω true))) μ →
    let π := eventProbabilityW2 μ {ω | c ω = true}
    let CACE := eventMeanW2 μ (fun ω => Y ω true - Y ω false) {ω | c ω = true}
    let ITT := ∫ ω, Y ω (c ω) - Y ω false ∂μ
    let Δ := eventMeanW2 μ (randomContactOutcomeW2 Y c Z) {ω | Z ω = true} -
      eventMeanW2 μ (randomContactOutcomeW2 Y c Z) {ω | Z ω = false}
    let F := fun ω => if Z ω && c ω then (1 : ℝ) else 0
    ITT = π * CACE ∧ Δ = ITT ∧
      eventMeanW2 μ F {ω | Z ω = true} = π ∧
      eventMeanW2 μ F {ω | Z ω = false} = 0 ∧
      CACE = Δ / eventMeanW2 μ F {ω | Z ω = true}

/-- Note 2 for a uniformly sampled subject independent of the complete
assignment: the subject's own treatment indicator is independent of every
fixed subject attribute. Event factorization is stated for both treatment
values and every set of attribute values, including potential-outcome pairs
and compliance types. This is stronger than independence of a constant whole
potential-outcome schedule from the assignment vector. -/
def SampledSubjectIndependenceW2 : Prop :=
  ∀ (N m : ℕ), 2 ≤ N → 1 ≤ m → m ≤ N - 1 →
    ∀ (A : Type) (v : Fin N → A) (B : Set A) (b : Bool),
      finiteExpectation (Finset.univ : Finset (Fin N))
        (fun i => finiteExpectation (completeAssignments N m)
          (fun S => if decide (i ∈ S) = b ∧ v i ∈ B then 1 else 0)) =
      (if b then (m : ℝ) / (N : ℝ) else 1 - (m : ℝ) / (N : ℝ)) *
        finiteExpectation (Finset.univ : Finset (Fin N))
          (fun i => if v i ∈ B then 1 else 0)

/-- A binary turnout schedule, including every factual and counterfactual entry. -/
def BinaryScheduleW2 {N : ℕ} (Y : Fin N → Bool → ℝ) : Prop :=
  ∀ i t, Y i t = 0 ∨ Y i t = 1

/-- Size of the fixed Never-taker subgroup. -/
def neverTakerCountW2 {N : ℕ} (c : Fin N → Bool) : ℕ :=
  (Finset.univ.filter (fun i => c i = false)).card

/-- Average contact effect among Never-takers, used only when this group is nonempty. -/
def neverTakerEffectW2 {N : ℕ} (Y : Fin N → Bool → ℝ) (c : Fin N → Bool) : ℝ :=
  (∑ i, if c i = false then Y i true - Y i false else 0) / (neverTakerCountW2 c : ℝ)

/-- P. 32's inability to assess Never-taker contact effects: even within binary
turnout schedules, changing a Never-taker's unobserved contact outcome can
leave every observed outcome unchanged under every assignment while changing
both that subject's contact effect and the Never-taker average contact effect.
The supplied Never-taker witnesses the nonempty denominator. -/
def NeverTakerNonidentificationW2 : Prop :=
  ∀ (N : ℕ) (Y : Fin N → Bool → ℝ) (c : Fin N → Bool) (k : Fin N),
    BinaryScheduleW2 Y → c k = false →
    ∃ Y' : Fin N → Bool → ℝ,
      BinaryScheduleW2 Y' ∧
      (∀ S : Finset (Fin N), contactedOutcome S Y' c = contactedOutcome S Y c) ∧
      (∀ i t, (i ≠ k ∨ t = false) → Y' i t = Y i t) ∧
      Y' k true - Y' k false ≠ Y k true - Y k false ∧
      0 < neverTakerCountW2 c ∧
      neverTakerEffectW2 Y' c ≠ neverTakerEffectW2 Y c

/-- The sample contact-rate estimator described on p. 32. Its statistical use
below is guarded by a strictly positive realized contact rate. -/
def contactEstimatorW2 {N : ℕ} (m : ℕ) (S : Finset (Fin N))
    (Y : Fin N → Bool → ℝ) (c : Fin N → Bool) : ℝ :=
  (assignedTreatmentMean m S (contactedOutcome S Y c) -
    assignedControlMean m S (contactedOutcome S Y c)) / assignedContactRate m S c

/-- The printed sample estimator formula, on assignments where its denominator exists. -/
def RealizedEstimatorFormulaW2 : Prop :=
  ∀ (N m : ℕ), 2 ≤ N → 1 ≤ m → m ≤ N - 1 →
    ∀ (Y : Fin N → Bool → ℝ) (c : Fin N → Bool) (S : Finset (Fin N)),
    S ∈ completeAssignments N m → 0 < assignedContactRate m S c →
    contactEstimatorW2 m S Y c =
      (assignedTreatmentMean m S (contactedOutcome S Y c) -
        assignedControlMean m S (contactedOutcome S Y c)) / assignedContactRate m S c ∧
    contactEstimatorW2 m S Y c * assignedContactRate m S c =
      assignedTreatmentMean m S (contactedOutcome S Y c) -
        assignedControlMean m S (contactedOutcome S Y c)

/-- P042-T6; p. 30 (PDF p. 6), Note 2 on pp. 39–40 (PDF pp. 15–16),
and contact/CACE and the Michelson illustration on p. 32 (PDF p. 8).
Random assignment independent of subjects' potential outcomes balances the
two arms in expectation. Uniform complete randomization gives the finite
potential-outcome mean identities and an unbiased observed assignment contrast;
a uniformly sampled subject's treatment is independent of their fixed attributes.
Under one-sided contact, exclusion and no interference, ITT equals Complier
share times CACE, the expected treated contact fraction is that positive share,
and the ratio of the expected turnout contrast to the expected contact fraction
equals CACE. The same population identities hold on arbitrary probability spaces
under independent assignment. The realized estimator is the turnout contrast
divided by its positive realized contact fraction. Never-taker effects are not
identified, even with binary turnout. The illustration is (9.4 - 7.0)/0.50 = 4.8
percentage points. The usual measure-theoretic conditions are assumed.
No unbiasedness or consistency of the realized ratio is asserted. -/
def T6WholeStatement_W2 : Prop :=
  T6Statement ∧ RandomizedBalanceW2 ∧ RandomizedContactW2 ∧
    SampledSubjectIndependenceW2 ∧ NeverTakerNonidentificationW2 ∧
    RealizedEstimatorFormulaW2

end

end SAP.P042
