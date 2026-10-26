import AronowAudit.P044.Wave1.SimulatedVariance.N17

namespace AronowAudit.P044.Wave1.SimulatedVariance

open MeasureTheory ProbabilityTheory
open scoped BigOperators
open AronowAudit.P044

noncomputable section

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
theorem n18_proof : N18 := by
  intro htypes
  change expect (fun _ : Fin 66 => (1 / 66 : ℚ)) (fun t =>
    expectedTotalVariance (cliqueObservationMarginal t false) (cliqueObservationJoint t false)
      cliqueY (cliqueWeights t) (cliqueJoints t) .d00) = 188343164 / 20398455
  have hdiag : momentTypeRow (momentSameLabelTerm .d00) true true = 71326 / 841 := by
    norm_num [momentTypeRow, moment_sum_exposure, momentSameLabelTerm,
      momentTypeJoint, momentTypeWeight, cliqueJointTable, cliqueFullCount]
  have hsame : momentTypeRow (momentSameLabelTerm .d00) false true = 1872500 / 22707 := by
    norm_num [momentTypeRow, moment_sum_exposure, momentSameLabelTerm,
      momentTypeJoint, momentTypeWeight, cliqueJointTable, cliqueFullCount]
  have hdiff : momentTypeRow (momentSameLabelTerm .d00) false false = -14496243 / 412090 := by
    norm_num [momentTypeRow, moment_sum_exposure, momentSameLabelTerm,
      momentTypeJoint, momentTypeWeight, cliqueJointTable, cliqueFullCount]
  rw [momentSameLabel_average htypes .d00 (Or.inr rfl),
    momentTypeSum_eq, hdiag, hsame, hdiff] <;> norm_num

end

end AronowAudit.P044.Wave1.SimulatedVariance
