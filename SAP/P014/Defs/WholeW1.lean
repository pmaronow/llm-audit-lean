import Mathlib
import SAP.P014.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P014

open scoped BigOperators
open MeasureTheory
noncomputable section
universe u

/-- The actual assignment law: each positive-probability binary vector occurs
once, with its probability as weight. The population is finite even when the
underlying probability space or the outside score law is continuous. -/
def assignmentLaw {Ω : Type*} [MeasurableSpace Ω] {N : ℕ}
    (μ : Measure Ω) (Z : Ω → TreatmentVector N) :
    FiniteDistribution (TreatmentVector N) := by
  classical
  exact ⟨Finset.univ.filter (fun z => 0 < eventProbability μ (fun ω => Z ω = z)),
    fun z => eventProbability μ (fun ω => Z ω = z)⟩

/-- Conditional expectation on an event, expressed as its set integral divided
by its probability. All uses below assert positive event probability and
integrability, so this is the usual event conditional mean. -/
def eventConditionalMean {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (f : Ω → ℝ) (P : Ω → Prop) : ℝ :=
  (∫ ω in {ω | P ω}, f ω ∂μ) / eventProbability μ P

/-- All parts of the corrected T2 calculation for the actual assignment law.
The conditional arm summands are `Y_i Z_i` and `Y_i (1-Z_i)`, written using
Boolean indicators. Subtraction in every real denominator is real subtraction. -/
def WeightedIdentity {Ω : Type*} [MeasurableSpace Ω] {N : ℕ}
    (μ : Measure Ω) (Z : Ω → TreatmentVector N) (S : Finset (Fin N))
    (y : PotentialOutcomes N) (m : ℕ) : Prop :=
  let L := assignmentLaw μ Z
  IsDistribution L ∧
  PositiveArms L S ∧
  (∀ i ∈ S, ∀ a,
    armProbability L i a = eventProbability μ (fun ω => Z ω i = a) ∧
    conditionalAverage L y i a =
      eventConditionalMean μ (fun ω => y i (Z ω)) (fun ω => Z ω i = a) ∧
    Integrable (fun ω => y i (Z ω)) μ ∧
    Integrable (fun ω => if Z ω i = a then y i (Z ω) else 0) μ) ∧
  (∀ i ∈ S,
    armProbability L i true = (m : ℝ) / S.card ∧
    armProbability L i false = ((S.card : ℝ) - m) / S.card) ∧
  (∀ z ∈ L.atoms,
    armSize S z true = m ∧ armSize S z false = (S.card : ℝ) - m ∧
    0 < armSize S z true ∧ 0 < armSize S z false ∧
    differenceOfMeans S y z = observedArmTotal S y z true / m -
      observedArmTotal S y z false / ((S.card : ℝ) - m)) ∧
  (∀ᵐ ω ∂μ,
    armSize S (Z ω) true = m ∧ armSize S (Z ω) false = (S.card : ℝ) - m ∧
    0 < armSize S (Z ω) true ∧ 0 < armSize S (Z ω) false ∧
    differenceOfMeans S y (Z ω) = observedArmTotal S y (Z ω) true / m -
      observedArmTotal S y (Z ω) false / ((S.card : ℝ) - m)) ∧
  (∀ i ∈ S, ∀ a,
    (∫ ω, (if Z ω i = a then y i (Z ω) else 0) ∂μ) = armMoment L y i a ∧
    armMoment L y i a = armProbability L i a * conditionalAverage L y i a) ∧
  (∀ i ∈ S,
    armMoment L y i true = ((m : ℝ) / S.card) * conditionalAverage L y i true ∧
    armMoment L y i false = (((S.card : ℝ) - m) / S.card) *
      conditionalAverage L y i false) ∧
  Integrable (fun ω => differenceOfMeans S y (Z ω)) μ ∧
  (∫ ω, differenceOfMeans S y (Z ω) ∂μ) = expectation L (differenceOfMeans S y) ∧
  (∫ ω, differenceOfMeans S y (Z ω) ∂μ) =
    (∑ i ∈ S, armMoment L y i true) / m -
      (∑ i ∈ S, armMoment L y i false) / ((S.card : ℝ) - m) ∧
  (∫ ω, differenceOfMeans S y (Z ω) ∂μ) =
    (1 / (m : ℝ)) * ((m : ℝ) / S.card) *
      (∑ i ∈ S, conditionalAverage L y i true) -
    (1 / ((S.card : ℝ) - m)) * (((S.card : ℝ) - m) / S.card) *
      (∑ i ∈ S, conditionalAverage L y i false) ∧
  (∫ ω, differenceOfMeans S y (Z ω) ∂μ) = windowContrast S (conditionalAverage L y) ∧
  windowContrast S (conditionalAverage L y) =
    ((∑ i ∈ S, conditionalAverage L y i true) -
      ∑ i ∈ S, conditionalAverage L y i false) / S.card

def T2AssignmentWholePart : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] {N : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Z : Ω → TreatmentVector N),
  Measurable Z → ∀ (S : Finset (Fin N)) (y : PotentialOutcomes N) (m : ℕ),
  0 < m → m < S.card →
  (∀ᵐ ω ∂μ, armSize S (Z ω) true = m) →
  (∀ i ∈ S, eventProbability μ (fun ω => Z ω i = true) = (m : ℝ) / S.card) →
  WeightedIdentity μ Z S y m

def T2ScoreWholePart : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] {N : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → Fin N → ℝ) (b : ℝ) (S : Finset (Fin N)) (v : S → ℝ) (m : ℕ),
  0 < b → Function.Injective v → (∀ i, insideWindow b (v i)) →
  0 < m → m < S.card →
  (Finset.univ.filter (fun i : S => 0 ≤ v i)).card = m →
  CorrectedLocalConditions μ X b S v →
  (∀ᵐ ω ∂μ, armSize S (thresholdAssignment (X ω)) true = m) ∧
  (∀ i ∈ S, eventProbability μ (fun ω => thresholdAssignment (X ω) i = true) =
    (m : ℝ) / S.card) ∧
  (∀ y : PotentialOutcomes N,
    WeightedIdentity μ (fun ω => thresholdAssignment (X ω)) S y m)

/-- P014-T2, p. 131 (PDF p. 4), assumptions p. 130: with a fixed interior
treated count and common propensities, probability-weighted own-arm averages
are conditional expectations with positive denominators, and the unchanged
difference in means is unbiased for their bracketed window contrast. All four
displayed derivation steps hold. Corrected uniform local score arrangements
imply these hypotheses and this identity for arbitrary potential outcomes,
with the outside allocation and its dependence unrestricted. -/
def T2WholeStatement : Prop := T2AssignmentWholePart.{u} ∧ T2ScoreWholePart.{u}

/-- Discreteness of the full score vector means that its positive-probability
atoms carry the whole law. It does not assume that there are finitely many. -/
def DiscreteScoreLaw {Ω : Type*} [MeasurableSpace Ω] {N : ℕ}
    (μ : Measure Ω) (X : Ω → Fin N → ℝ) : Prop :=
  ∀ᵐ ω ∂μ, 0 < eventProbability μ (fun η => X η = X ω)

/-- The restored forward implication of T6(d). The exhibited finite set is
exactly the positive-atom support, has n! elements, and has one full vector
above each local arrangement. Outside reconstruction is required only almost
surely and only outside S; no measurability of a chosen total extension g is
presupposed or needed. -/
def FullScoreReconstruction {Ω : Type*} [MeasurableSpace Ω] {N : ℕ}
    (μ : Measure Ω) (X : Ω → Fin N → ℝ) (S : Finset (Fin N)) (v : S → ℝ) : Prop :=
  ∃ A : Finset (Fin N → ℝ),
    (∀ x, x ∈ A ↔ 0 < eventProbability μ (fun ω => X ω = x)) ∧
    A.card = S.card.factorial ∧
    (∀ σ : Equiv.Perm S, ∃! x : Fin N → ℝ, x ∈ A ∧ ∀ i : S, x i = v (σ i)) ∧
    ∃ g : (S → ℝ) → Fin N → ℝ,
      ∀ᵐ ω ∂μ, ∀ j ∉ S, X ω j = g (fun i : S => X ω i) j

def T6PrintedForwardPart : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] {N : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → Fin N → ℝ) (b : ℝ) (S : Finset (Fin N)) (v : S → ℝ) (m : ℕ),
  0 < b → 2 ≤ S.card → Function.Injective v → (∀ i, insideWindow b (v i)) →
  0 < m → m < S.card →
  (Finset.univ.filter (fun i : S => 0 ≤ v i)).card = m →
  CorrectedLocalConditions μ X b S v → DiscreteScoreLaw μ X →
  (∀ x, 0 < eventProbability μ (fun ω => X ω = x) →
    eventProbability μ (fun ω => X ω = x) = 1 / (S.card.factorial : ℝ)) →
  FullScoreReconstruction μ X S v

/-- P014-T6, p. 130 (PDF p. 3): uniform local score arrangements give fixed
interior treatment counts, common propensities, fixed window membership, the
stated empirical CDF and no distinct-subject ties. Adding discreteness and the
printed full-vector mass clause forces exactly one full supported vector per
local arrangement and makes the outside scores an almost surely deterministic
function of that arrangement. Conversely such an outside function gives n!
full support points of mass 1/n!. The specified independent outside example
has twelve points, six of mass 1/18 and six of mass 1/9, and satisfies the
correction while failing the printed full-vector mass clause. -/
def T6WholeStatement : Prop :=
  T6GeneralPart.{u} ∧ T6PrintedForwardPart.{u} ∧ T6OutsideExample

end
end SAP.P014
