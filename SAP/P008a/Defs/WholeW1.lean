import Mathlib
import SAP.P008a.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P008a

open MeasureTheory
open scoped BigOperators Classical

noncomputable section

/-- The actual coefficient vector in the binary intercept/treatment regression. -/
def wholeOLSCoefficient {N : ℕ} (z : Assignment N) (m : Fin N → ℝ) : Fin 2 → ℝ :=
  let X := binaryDesign z
  ((X.transpose * X)⁻¹).mulVec (X.transpose.mulVec m)

/-- The treatment row of the least-squares linear map. -/
def wholeOLSWeight {N : ℕ} (z : Assignment N) (i : Fin N) : ℝ :=
  let X := binaryDesign z
  ((X.transpose * X)⁻¹ * X.transpose) 1 i

def wholeOLSScore {N : ℕ} (z : Assignment N) (m : Fin N → ℝ) (i : Fin N) : ℝ :=
  wholeOLSWeight z i * olsResidual z m i

/-- These are counts of binary arms; at least one means that the arm is present. -/
def WholeOLSIdentities : Prop :=
  ∀ {N : ℕ} (z : Assignment N) (m : Fin N → ℝ),
    1 ≤ nTreated z → 1 ≤ nControl z →
    let X := binaryDesign z
    (X.transpose * X).det = nTreated z * nControl z ∧
    (X.transpose * X).det ≠ 0 ∧
    X.transpose.mulVec (olsResidual z m) = 0 ∧
    (∀ i, wholeOLSWeight z i = contrastWeight z i) ∧
    (∀ i, olsResidual z m i = groupResidual z m i) ∧
    wholeOLSScore z m = regressionScore z m ∧
    (∑ i, wholeOLSScore z m i) =
      (((X.transpose * X)⁻¹).mulVec (X.transpose.mulVec (olsResidual z m))) 1 ∧
    (∑ i, wholeOLSScore z m i) = 0 ∧
    (∀ (D : Fin N → Fin N → ℝ) (c : ℝ),
      ((X.transpose * X)⁻¹ * olsMeat z m D c * (X.transpose * X)⁻¹) 1 1 =
        hac (wholeOLSScore z m) D c)

def wholeBandwidthAssignment : Assignment 4 := ![false, false, true, true]
def wholeBandwidthMeans : Fin 4 → ℝ := ![0, 2, 4, 6]
def wholeBandwidthScores : Fin 4 → ℝ := ![1 / 2, -1 / 2, -1 / 2, 1 / 2]

def WholeBandwidthCalculations : Prop :=
  wholeOLSCoefficient wholeBandwidthAssignment wholeBandwidthMeans = ![1, 4] ∧
  olsResidual wholeBandwidthAssignment wholeBandwidthMeans = ![-1, 1, -1, 1] ∧
  wholeOLSWeight wholeBandwidthAssignment = ![-1 / 2, -1 / 2, 1 / 2, 1 / 2] ∧
  wholeOLSScore wholeBandwidthAssignment wholeBandwidthMeans = wholeBandwidthScores ∧
  (2 / 5 + 1 : ℝ) = 7 / 5 ∧ (7 / 5 : ℝ) < 2 ∧
  (2 / 5 + 2 : ℝ) = 12 / 5 ∧
  (∀ i l : Fin 4,
    (if bandwidthExampleDistance i l ≤ 7 / 5 then (1 : ℝ) else 0) =
      if i = l then 1 else 0) ∧
  (∀ i l : Fin 4,
    (if bandwidthExampleDistance i l ≤ 12 / 5 then (1 : ℝ) else 0) =
      if |(i : ℝ) - (l : ℝ)| ≤ 1 then 1 else 0) ∧
  hac wholeBandwidthScores bandwidthExampleDistance (7 / 5) =
    ∑ i, (wholeBandwidthScores i)^2 ∧
  (∑ i, (wholeBandwidthScores i)^2) = 1 ∧
  hac wholeBandwidthScores bandwidthExampleDistance (12 / 5) =
    1 + 2 * (wholeBandwidthScores 0 * wholeBandwidthScores 1 +
      wholeBandwidthScores 1 * wholeBandwidthScores 2 +
      wholeBandwidthScores 2 * wholeBandwidthScores 3) ∧
  (1 + 2 * ((-1 / 4 : ℝ) + 1 / 4 - 1 / 4)) = 1 / 2

/-- The bound applies to every configuration in the box, as the claim says. -/
def WholeBoxBound : Prop :=
  ∀ (p : Fin 4 → Plane), (∀ i a, 0 ≤ p i a ∧ p i a ≤ 4) →
    ∀ i l, dist (p i) (p l)^2 ≤ 32

def WholeSixthRow : Prop :=
  (∀ i a, 0 ≤ toyNode i a ∧ toyNode i a ≤ 4) ∧
  (2 / 5 + 6 : ℝ) = 32 / 5 ∧ (32 / 5 : ℝ)^2 = 1024 / 25 ∧
  (32 : ℝ) < 1024 / 25 ∧
  (3438 / 1000 - (-38 / 1000) : ℝ) = 869 / 250 ∧ (0 : ℝ) < 869 / 250 ∧
  (∀ (p : Fin 4 → Plane), (∀ i a, 0 ≤ p i a ∧ p i a ≤ 4) →
    ∀ (z : Assignment 4) (m : Fin 4 → ℝ),
    1 ≤ nTreated z → 1 ≤ nControl z →
    (∀ i l, (if dist (p i) (p l) ≤ 32 / 5 then (1 : ℝ) else 0) = 1) ∧
    hac (wholeOLSScore z m) (fun i l => dist (p i) (p l)) (32 / 5) =
      (∑ i, wholeOLSScore z m i)^2 ∧
    archivedVariance (wholeOLSScore z m) (fun i l => dist (p i) (p l)) (2 / 5) 6 = 0 ∧
    (∀ h : ℝ,
      ((17 / 10 + h * Real.sqrt (archivedVariance (wholeOLSScore z m)
        (fun i l => dist (p i) (p l)) (2 / 5) 6)) -
       (17 / 10 - h * Real.sqrt (archivedVariance (wholeOLSScore z m)
        (fun i l => dist (p i) (p l)) (2 / 5) 6))) = 0 ∧
      2 * h * Real.sqrt (archivedVariance (wholeOLSScore z m)
        (fun i l => dist (p i) (p l)) (2 / 5) 6) ≠ 869 / 250))

/-- P008-T9; article p. 145 (PDF p. 8); supplied archived computation;
toy call and table pp. 148–149 (PDF pp. 11–12).
The specified planar counterexample has the displayed OLS coefficient, residual,
contrast-weight and score vectors. The cutoff-plus-position rule uses the identity
kernel at position one and the adjacent-pair kernel at position two, giving variances
1 and 1/2 for the same radius and data. In every four-node configuration in [0,4]^2,
the sixth-position bandwidth covers all pairs; the normal equations force variance
and interval width zero, incompatible with the printed sixth-row width 3.476.
The assertion concerns the supplied computational model and its physical-cutoff reading. -/
def T9WholeStatement : Prop :=
  T9Statement ∧ WholeOLSIdentities ∧ WholeBandwidthCalculations ∧
    WholeBoxBound ∧ WholeSixthRow

def WholeCorrectedOLS : Prop :=
  (∀ {N : ℕ} (z : Assignment N) (m : Fin N → ℝ) (D : Fin N → Fin N → ℝ)
    (c : ℝ), 1 ≤ nTreated z → 1 ≤ nControl z → ∀ j k : ℕ,
    physicalVariance (wholeOLSScore z m) D c j = hac (wholeOLSScore z m) D c ∧
    physicalVariance (wholeOLSScore z m) D c j =
      physicalVariance (wholeOLSScore z m) D c k ∧
    (∀ (_hall : ∀ i l, D i l ≤ c),
      hac (wholeOLSScore z m) D c = (∑ i, wholeOLSScore z m i)^2 ∧
      hac (wholeOLSScore z m) D c = 0)) ∧
  (∀ i l : Fin 4,
    (if dist (toyNode i) (toyNode l) ≤ 2 / 5 then (1 : ℝ) else 0) =
      if i = l then 1 else 0) ∧
  (∀ (z : Assignment 4) (m : Fin 4 → ℝ),
    1 ≤ nTreated z → 1 ≤ nControl z →
    hac (wholeOLSScore z m) (fun i l => dist (toyNode i) (toyNode l)) (2 / 5) =
      ∑ i, (wholeOLSScore z m i)^2 ∧
    hac (wholeOLSScore z m) (fun i l => dist (toyNode i) (toyNode l)) (2 / 5) =
      hac (wholeOLSScore z m) (fun i l => dist (toyNode i) (toyNode l)) 0 ∧
    (0 < hac (wholeOLSScore z m) (fun i l => dist (toyNode i) (toyNode l)) (2 / 5) ↔
      ∃ i, olsResidual z m i ≠ 0) ∧
    (hac (wholeOLSScore z m) (fun i l => dist (toyNode i) (toyNode l)) (2 / 5) = 0 ↔
      ∀ i, olsResidual z m i = 0) ∧
    archivedVariance (wholeOLSScore z m)
      (fun i l => dist (toyNode i) (toyNode l)) (2 / 5) 6 = 0)

/-- P008-T10; article p. 145 (PDF p. 8); supplied archived computation.
Retaining cutoff as the final node-pair bandwidth makes the actual OLS sandwich
variance independent of grid position and gives variance 1 on both example grids.
The normal equations make every all-pairs regression variance zero. For the toy nodes,
cutoff 0.4 is the identity kernel and gives HC0, equal to cutoff zero and positive
exactly when some actual OLS residual is nonzero; the archived sixth-row variance is
zero. A proposed physical-radius enlargement requires its own dependence justification. -/
def T10WholeStatement : Prop :=
  T10Statement ∧ WholeOLSIdentities ∧ WholeCorrectedOLS

abbrev WholeRiskTriple := Fin 4 × Fin 4 × RiskCell
abbrev WholeRiskLabel := Fin 4 ⊕ WholeRiskTriple

def wholeRiskCentre (i : Fin 4) : Plane :=
  WithLp.toLp 2 ((![![0, 0], ![20, 0], ![0, 20], ![20, 20]] : Fin 4 → Fin 2 → ℝ) i)

def wholeRiskRadius : Fin 4 → ℝ := ![1, 3 / 2, 2, 5 / 2]

/-- Fin indices are zero based: this is the printed ell at k.val + 1. -/
def wholeRiskEll (k : RiskCell) : ℝ := 2 * (k.val + 1 : ℝ) - 40000 - 1
def wholeRiskDenominator (k : RiskCell) : ℝ := 40000^2 + wholeRiskEll k^2
def wholeRiskU (k : RiskCell) : ℝ := (40000^2 - wholeRiskEll k^2) / wholeRiskDenominator k
def wholeRiskV (k : RiskCell) : ℝ := (2 * 40000 * wholeRiskEll k) / wholeRiskDenominator k
def wholeRiskDirection (k : RiskCell) : Plane := WithLp.toLp 2 ![wholeRiskU k, wholeRiskV k]
def wholeRiskPoint (i j : Fin 4) (k : RiskCell) : Plane :=
  wholeRiskCentre i + wholeRiskRadius j • wholeRiskDirection k

def wholeRiskEmbedding : WholeRiskLabel → Plane
  | .inl i => wholeRiskCentre i
  | .inr t => wholeRiskPoint t.1 t.2.1 t.2.2

def wholeRiskField : Finset Plane := Finset.univ.image wholeRiskEmbedding
def wholeRiskCirclePoints : Finset Plane :=
  Finset.univ.image (fun t : WholeRiskTriple => wholeRiskPoint t.1 t.2.1 t.2.2)
def wholeRiskCircle (i j : Fin 4) : Finset Plane :=
  wholeRiskField.filter (fun x => dist (wholeRiskCentre i) x = wholeRiskRadius j)

/-- Both complete schedules use the same spatial field. -/
def wholeRiskLabelOutcome (companion : Bool) (l : WholeRiskLabel) (z : Assignment 4) : ℝ :=
  match l with
  | .inl _ => 0
  | .inr t => if companion then companionRiskOutcome t.1 t.2.1 t.2.2 z
      else riskOutcome t.1 t.2.1 t.2.2 z

def wholeRiskY (companion : Bool) : Plane → Assignment 4 → ℝ :=
  Function.extend wholeRiskEmbedding (wholeRiskLabelOutcome companion) (fun _ _ => 0)

def wholeRiskModel (companion : Bool) : SpatialModel 4 where
  field := ↑wholeRiskField
  node := wholeRiskCentre
  node_mem i := Finset.mem_image.mpr ⟨Sum.inl i, Finset.mem_univ _, rfl⟩
  ζ := Measure.count.restrict (↑wholeRiskField : Set Plane)
  Y := wholeRiskY companion

/-- The owner is used only on circle points, where injectivity identifies it uniquely. -/
def wholeRiskOwner : Plane → Fin 4 :=
  Function.extend (fun t : WholeRiskTriple => wholeRiskPoint t.1 t.2.1 t.2.2)
    (fun t => t.1) (fun _ => 0)

/-- Uniform sampling of actual planar circle points, followed by the own-node override. -/
def wholeRiskSpatialProbability (b : Bool) : ℝ :=
  countMean wholeRiskCirclePoints (fun x =>
    (uniformLaw (Assignment 4)).expect (fun z =>
      wholeRiskY false x (Function.update z (wholeRiskOwner x) b)))

def WholeRiskAlgebra : Prop :=
  (∀ k, 0 < wholeRiskDenominator k ∧ 1 + wholeRiskU k ≠ 0 ∧
    wholeRiskU k^2 + wholeRiskV k^2 = 1 ∧
    wholeRiskV k / (1 + wholeRiskU k) = wholeRiskEll k / 40000 ∧
    ‖wholeRiskDirection k‖ = 1) ∧
  StrictMono (fun k => wholeRiskV k / (1 + wholeRiskU k)) ∧
  Function.Injective wholeRiskDirection

def WholeRiskDistances : Prop :=
  (∀ i j k, dist (wholeRiskCentre i) (wholeRiskPoint i j k) = wholeRiskRadius j) ∧
  (∀ i l, i ≠ l → (20 : ℝ) ≤ dist (wholeRiskCentre i) (wholeRiskCentre l)) ∧
  (∀ i l, i ≠ l → ∀ x : Plane, dist (wholeRiskCentre i) x ≤ 5 / 2 →
    (35 / 2 : ℝ) ≤ dist (wholeRiskCentre l) x)

def WholeRiskCircles : Prop :=
  wholeRiskField.card = 640004 ∧
  (∀ i j, wholeRiskCircle i j = Finset.univ.image (wholeRiskPoint i j) ∧
    (wholeRiskCircle i j).card = 40000)

/-- Certifies the integrals before any circle mean is used. Arbitrary functions are
integrable on these finite counting circles. -/
def WholeRiskMeasures : Prop :=
  ∀ (companion : Bool) (i j : Fin 4),
    (wholeRiskModel companion).circle i (wholeRiskRadius j) = ↑(wholeRiskCircle i j) ∧
    (wholeRiskModel companion).circleMeasure i (wholeRiskRadius j) =
      ∑ k : RiskCell, Measure.dirac (wholeRiskPoint i j k) ∧
    (wholeRiskModel companion).circleMass i (wholeRiskRadius j) = 40000 ∧
    (wholeRiskModel companion).circleMeasure i (wholeRiskRadius j) Set.univ ≠ ⊤ ∧
    (∀ f : Plane → ℝ,
      Integrable f ((wholeRiskModel companion).circleMeasure i (wholeRiskRadius j)) ∧
      (∫ x, f x ∂(wholeRiskModel companion).circleMeasure i (wholeRiskRadius j)) =
        ∑ k : RiskCell, f (wholeRiskPoint i j k))

def WholeRiskOutcomes : Prop :=
  (∀ companion i z, wholeRiskY companion (wholeRiskCentre i) z = 0) ∧
  (∀ i j k z, wholeRiskY false (wholeRiskPoint i j k) z = riskOutcome i j k z) ∧
  (∀ i j k z, wholeRiskY true (wholeRiskPoint i j k) z = 1 - bit (z i)) ∧
  (∀ companion, ∀ x ∈ wholeRiskField, ∀ z,
    wholeRiskY companion x z = 0 ∨ wholeRiskY companion x z = 1) ∧
  (∀ i j z, (wholeRiskModel false).M i (wholeRiskRadius j) z = riskM i j z) ∧
  (∀ i j z, (wholeRiskModel true).M i (wholeRiskRadius j) z = companionRiskM i j z)

def WholeRiskSampling : Prop :=
  wholeRiskCirclePoints.card = 640000 ∧
  (∀ i j k, wholeRiskOwner (wholeRiskPoint i j k) = i) ∧
  (∀ f : Plane → ℝ, countMean wholeRiskCirclePoints f =
    (16 : ℝ)⁻¹ * ∑ i : Fin 4, ∑ j : Fin 4,
      countMean Finset.univ (fun k : RiskCell => f (wholeRiskPoint i j k)))

def WholeRiskSpatialConclusions : Prop :=
  (∀ i j b, (wholeRiskModel false).m (uniformLaw (Assignment 4)) i b (wholeRiskRadius j) =
    ((riskBaseline i : ℝ) - 321 * bit b) / 40000) ∧
  (∀ i j, (wholeRiskModel false).nodeEffect (uniformLaw (Assignment 4)) i
    (wholeRiskRadius j) = -321 / 40000) ∧
  (∀ j, (wholeRiskModel false).amr (uniformLaw (Assignment 4)) (wholeRiskRadius j) =
    -321 / 40000) ∧
  (∀ j, hajek (fun i z => (wholeRiskModel false).M i (wholeRiskRadius j) z)
    ![true, true, false, false] = -321 / 40000) ∧
  (∑ j, hajek (fun i z => (wholeRiskModel false).M i (wholeRiskRadius j) z)
    ![true, true, false, false]) = -321 / 10000 ∧
  (∑ j, (wholeRiskModel false).amr (uniformLaw (Assignment 4)) (wholeRiskRadius j)) =
    -321 / 10000 ∧
  (∀ b, wholeRiskSpatialProbability b = riskSamplingProbability (uniformLaw (Assignment 4)) b) ∧
  wholeRiskSpatialProbability false = 7 / 400 ∧
  wholeRiskSpatialProbability true = 379 / 40000 ∧
  wholeRiskSpatialProbability true - wholeRiskSpatialProbability false = -321 / 40000 ∧
  (∀ w : Fin 4 → ℝ, (∀ j, 0 ≤ w j) → (∑ j, w j = 1) →
    (∑ j, w j * (wholeRiskModel false).amr (uniformLaw (Assignment 4)) (wholeRiskRadius j)) =
      wholeRiskSpatialProbability true - wholeRiskSpatialProbability false) ∧
  wholeRiskSpatialProbability false + (-321 / 10000) = -73 / 5000 ∧
  (∀ i j b, (wholeRiskModel true).m (uniformLaw (Assignment 4)) i b (wholeRiskRadius j) =
    1 - bit b) ∧
  (∀ j, (wholeRiskModel true).amr (uniformLaw (Assignment 4)) (wholeRiskRadius j) = -1) ∧
  (∑ j, (wholeRiskModel true).amr (uniformLaw (Assignment 4)) (wholeRiskRadius j)) = -4 ∧
  (∀ j, hajek (fun i z => (wholeRiskModel true).M i (wholeRiskRadius j) z)
    ![true, true, false, false] = -1) ∧
  (∑ j, hajek (fun i z => (wholeRiskModel true).M i (wholeRiskRadius j) z)
    ![true, true, false, false]) = -4 ∧
  (∀ a b : ℝ, 0 ≤ a → a ≤ 1 → 0 ≤ b → b ≤ 1 → -1 ≤ a - b ∧ a - b ≠ -4) ∧
  (-321 / 40000 : ℝ) = -0.008025 ∧ (-321 / 10000 : ℝ) = -0.0321 ∧
  100 * (-321 / 40000 : ℝ) = -0.8025

/-- P008-T7; p. 153 (PDF p. 16).
The specified four centres, four radii and 40,000 distinct rational directions give
640,004 distinct planar field points and exactly 40,000 points on each counting circle.
Both complete binary outcome schedules vanish at the centres. Under independent
Bernoulli(1/2) assignment, their actual spatial circle means, effects and Hajek estimates
give the stated sums -0.0321 and -4. Uniform sampling from the 640,000 planar circle
points gives risk difference -0.008025, preserved by every normalized radius weighting;
adding the unweighted sum to baseline risk gives a negative number. The companion
sum -4 cannot be a difference of probabilities. This is the specified synthetic
counterexample to the probability interpretation, with no empirical reconstruction. -/
def T7WholeStatement : Prop :=
  T7Statement ∧ WholeRiskAlgebra ∧ WholeRiskDistances ∧
    Function.Injective wholeRiskEmbedding ∧ WholeRiskCircles ∧ WholeRiskMeasures ∧
    WholeRiskOutcomes ∧ WholeRiskSampling ∧ WholeRiskSpatialConclusions

end
end SAP.P008a
