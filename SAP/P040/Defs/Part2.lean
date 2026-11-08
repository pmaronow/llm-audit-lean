import SAP.P040.Defs.Part1

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P040
open scoped BigOperators
open MeasureTheory
noncomputable section

/-- Endpoints are actual roots; rounded numbers are not used as endpoints. -/
def exactEndpointDescription : Prop :=
    ∃ L U L_one : ℝ,
      (680515 / 1000000 : ℝ) < L ∧ L < (680516 / 1000000 : ℝ) ∧
      (998313 / 1000000 : ℝ) < U ∧ U < (998314 / 1000000 : ℝ) ∧
      (720603 / 1000000 : ℝ) < L_one ∧ L_one < (720604 / 1000000 : ℝ) ∧
      observedUpperPolynomial L = (1 : ℝ) / 40 ∧
      observedUpperPolynomial L_one = (1 : ℝ) / 20 ∧
      U ^ 15 = (39 : ℝ) / 40 ∧ U = (39 / 40 : ℝ) ^ ((15 : ℝ)⁻¹) ∧
      (∀ p ∈ Set.Icc (0 : ℝ) 1, observedUpperPolynomial p = (1 : ℝ) / 40 → p = L) ∧
      (∀ p ∈ Set.Icc (0 : ℝ) 1, observedUpperPolynomial p = (1 : ℝ) / 20 → p = L_one) ∧
      (∀ p ∈ Set.Icc (0 : ℝ) 1, (1 - p ^ 15 : ℝ) = (1 : ℝ) / 40 → p = U) ∧
      exactDetectionInterval 14 = Set.Icc L U ∧
      exactDetectionLowerSet 14 = Set.Icc L_one 1 ∧
      L < L_one ∧ L_one < (4 / 5 : ℝ) ∧
      roundsTwo L (68 / 100) ∧ roundsTwo U 1

/-- The exact binomial correction, including uniform finite-sample coverage. -/
def T2Statement : Prop :=
    roundsTwo (detectionProportion 14) (93 / 100) ∧
    (∀ p : ℝ, upperDetectionTail p 14 = observedUpperPolynomial p ∧
      lowerDetectionTail p 14 = 1 - p ^ 15) ∧
    Continuous observedUpperPolynomial ∧
    StrictMonoOn observedUpperPolynomial (Set.Icc 0 1) ∧
    StrictAntiOn (fun p : ℝ => 1 - p ^ 15) (Set.Icc 0 1) ∧
    (∀ p : ℝ, HasDerivAt observedUpperPolynomial (210 * p ^ 13 * (1 - p)) p) ∧
    (∀ p ∈ Set.Ioo (0 : ℝ) 1, 0 < 210 * p ^ 13 * (1 - p)) ∧
    observedUpperPolynomial 0 = 0 ∧ observedUpperPolynomial 1 = 1 ∧
    exactEndpointDescription ∧
    (∀ L U : ℝ, L ∈ Set.Icc (0 : ℝ) 1 → U ∈ Set.Icc (0 : ℝ) 1 →
      observedUpperPolynomial L = (1 : ℝ) / 40 → U ^ 15 = (39 : ℝ) / 40 →
      roundsSix L (680515 / 1000000) ∧ roundsSix U (998314 / 1000000)) ∧
    upperDetectionTail (4 / 5) 14 = (5100273664 : ℝ) / 30517578125 ∧
    lowerDetectionTail (4 / 5) 14 = (29443836301 : ℝ) / 30517578125 ∧
    (1 : ℝ) / 20 < upperDetectionTail (4 / 5) 14 ∧
    (1 : ℝ) / 40 ≤ lowerDetectionTail (4 / 5) 14 ∧
    (4 / 5 : ℝ) ∈ exactDetectionInterval 14 ∧
    (4 / 5 : ℝ) ∈ exactDetectionLowerSet 14 ∧
    (∀ p ∈ Set.Icc (0 : ℝ) 1,
      (19 : ℝ) / 20 ≤ intervalCoverage p exactDetectionInterval ∧
      (19 : ℝ) / 20 ≤ intervalCoverage p exactDetectionLowerSet) ∧
    methodFreeObstruction

/-- The retained mathematical content P1 and P2 of the corrected canonical T3 passage. -/
def T3Statement : Prop :=
    roundsTwo (detectionProportion 14) (93 / 100) ∧ printedWaldArithmetic

end
end SAP.P040
