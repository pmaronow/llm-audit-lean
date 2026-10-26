import AronowAudit.P044.Wave1.SimulatedVariance.N16

namespace AronowAudit.P044.Wave1.SimulatedVariance

open MeasureTheory ProbabilityTheory
open scoped BigOperators
open AronowAudit.P044

noncomputable section

/-- The cross-label summand. Its zero adjustment has a minus sign and has
no off-diagonal guard, so all diagonal cross zeros are retained. -/
def momentCrossLabelTerm (e s : Bool) (d d' : Exposure) : ℚ :=
  (if 0 < momentTypeJoint e s d d' .d01 .d00 then
    ((cliqueJointTable e s .d01 .d00 : ℚ) / 66) *
      (1 / (momentTypeWeight d .d01 * momentTypeWeight d' .d00) -
        1 / momentTypeJoint e s d d' .d01 .d00)
  else 0) -
  (if momentTypeJoint e s d d' .d01 .d00 = 0 then
    ((cliqueFullCount .d01 : ℚ) / 66) * (1 / (2 * momentTypeWeight d .d01)) +
      ((cliqueFullCount .d00 : ℚ) / 66) * (1 / (2 * momentTypeWeight d' .d00))
  else 0)

theorem momentCrossLabel_reduction (t : Fin 66) :
    expectedTotalCovariance (cliqueObservationMarginal t false) (cliqueObservationJoint t false)
      cliqueY (cliqueWeights t) (cliqueJoints t) .d01 .d00 =
      ∑ i : Fin 12, ∑ j : Fin 12,
        momentCrossLabelTerm (decide (i = j)) (decide (i.val / 4 = j.val / 4))
          (cliqueF t i) (cliqueF t j) := by
  unfold expectedTotalCovariance
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have hJ := momentObservationJoint_eq t i j .d01 .d00 (Or.inl rfl) (Or.inr rfl)
  have hq := momentJoints_eq t i j .d01 .d00 (Or.inl rfl) (Or.inr rfl)
  simp only [momentCrossLabelTerm, hJ, hq, momentTypeWeight_eq,
    momentObservationMarginal_eq, cliqueY, one_pow, one_mul]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
theorem n19_proof : N19 := by
  intro htypes
  change expect (fun _ : Fin 66 => (1 / 66 : ℚ)) (fun t =>
    expectedTotalCovariance (cliqueObservationMarginal t false) (cliqueObservationJoint t false)
      cliqueY (cliqueWeights t) (cliqueJoints t) .d01 .d00) = -3863683 / 171941
  have hdiag : momentTypeRow momentCrossLabelTerm true true = -104989 / 1624 := by
    norm_num [momentTypeRow, moment_sum_exposure, momentCrossLabelTerm,
      momentTypeJoint, momentTypeWeight, cliqueJointTable, cliqueFullCount]
  have hsame : momentTypeRow momentCrossLabelTerm false true = -104989 / 1624 := by
    norm_num [momentTypeRow, moment_sum_exposure, momentCrossLabelTerm,
      momentTypeJoint, momentTypeWeight, cliqueJointTable, cliqueFullCount]
  have hdiff : momentTypeRow momentCrossLabelTerm false false = 2110235 / 125048 := by
    norm_num [momentTypeRow, moment_sum_exposure, momentCrossLabelTerm,
      momentTypeJoint, momentTypeWeight, cliqueJointTable, cliqueFullCount]
  have havg : expect (fun _ : Fin 66 => (1 / 66 : ℚ)) (fun t =>
      expectedTotalCovariance (cliqueObservationMarginal t false) (cliqueObservationJoint t false)
        cliqueY (cliqueWeights t) (cliqueJoints t) .d01 .d00) =
      momentTypeSum momentCrossLabelTerm / 66 := by
    simp_rw [momentCrossLabel_reduction]
    exact moment_pair_average htypes momentCrossLabelTerm
  rw [havg, momentTypeSum_eq, hdiag, hsame, hdiff] <;> norm_num

end

end AronowAudit.P044.Wave1.SimulatedVariance
