import AronowAudit.P044.Wave1.SimulatedVariance.N16

namespace AronowAudit.P044.Wave1.SimulatedVariance

open MeasureTheory ProbabilityTheory
open scoped BigOperators
open AronowAudit.P044

noncomputable section

/-- The same-label summand, including both the positive-joint branch and the
off-diagonal zero-joint adjustment. This definition also serves node N18. -/
def momentSameLabelTerm (a : Exposure) (e s : Bool) (d d' : Exposure) : ℚ :=
  (if 0 < momentTypeJoint e s d d' a a then
    ((cliqueJointTable e s a a : ℚ) / 66) *
      (1 / (momentTypeWeight d a * momentTypeWeight d' a) -
        1 / momentTypeJoint e s d d' a a)
  else 0) +
  (if e = false ∧ momentTypeJoint e s d d' a a = 0 then
    ((cliqueFullCount a : ℚ) / 66) * (1 / (2 * momentTypeWeight d a)) +
      ((cliqueFullCount a : ℚ) / 66) * (1 / (2 * momentTypeWeight d' a))
  else 0)

theorem momentSameLabel_reduction (a : Exposure) (ha : a = .d01 ∨ a = .d00)
    (t : Fin 66) :
    expectedTotalVariance (cliqueObservationMarginal t false) (cliqueObservationJoint t false)
      cliqueY (cliqueWeights t) (cliqueJoints t) a =
      ∑ i : Fin 12, ∑ j : Fin 12,
        momentSameLabelTerm a (decide (i = j)) (decide (i.val / 4 = j.val / 4))
          (cliqueF t i) (cliqueF t j) := by
  unfold expectedTotalVariance
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have hJ := momentObservationJoint_eq t i j a a ha ha
  have hq := momentJoints_eq t i j a a ha ha
  -- Express `i ≠ j` as `e = false` for the Boolean equality flag.
  simp only [momentSameLabelTerm, hJ, hq, momentTypeWeight_eq,
    momentObservationMarginal_eq, cliqueY, one_pow, one_mul] <;>
    (by_cases hij : i = j <;> simp [hij])

theorem momentSameLabel_average (htypes : TypeCount2) (a : Exposure)
    (ha : a = .d01 ∨ a = .d00) :
    expect (fun _ : Fin 66 => (1 / 66 : ℚ)) (fun t =>
      expectedTotalVariance (cliqueObservationMarginal t false) (cliqueObservationJoint t false)
        cliqueY (cliqueWeights t) (cliqueJoints t) a) =
      momentTypeSum (momentSameLabelTerm a) / 66 := by
  simp_rw [momentSameLabel_reduction a ha]
  exact moment_pair_average htypes (momentSameLabelTerm a)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
theorem n17_proof : N17 := by
  intro htypes
  change expect (fun _ : Fin 66 => (1 / 66 : ℚ)) (fun t =>
    expectedTotalVariance (cliqueObservationMarginal t false) (cliqueObservationJoint t false)
      cliqueY (cliqueWeights t) (cliqueJoints t) .d01) = 3564985 / 349272
  have hdiag : momentTypeRow (momentSameLabelTerm .d01) true true = 35295 / 392 := by
    norm_num [momentTypeRow, moment_sum_exposure, momentSameLabelTerm,
      momentTypeJoint, momentTypeWeight, cliqueJointTable, cliqueFullCount]
  have hsame : momentTypeRow (momentSameLabelTerm .d01) false true = 5770075 / 190512 := by
    norm_num [momentTypeRow, moment_sum_exposure, momentSameLabelTerm,
      momentTypeJoint, momentTypeWeight, cliqueJointTable, cliqueFullCount]
  have hdiff : momentTypeRow (momentSameLabelTerm .d01) false false = -655 / 42 := by
    norm_num [momentTypeRow, moment_sum_exposure, momentSameLabelTerm,
      momentTypeJoint, momentTypeWeight, cliqueJointTable, cliqueFullCount]
  rw [momentSameLabel_average htypes .d01 (Or.inl rfl),
    momentTypeSum_eq, hdiag, hsame, hdiff] <;> norm_num

end

end AronowAudit.P044.Wave1.SimulatedVariance
