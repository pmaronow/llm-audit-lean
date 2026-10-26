import AronowAudit.P044.Wave1.SimulatedVarianceBlueprint

namespace AronowAudit.P044.Wave1.SimulatedVariance

open MeasureTheory ProbabilityTheory
open scoped BigOperators
open AronowAudit.P044

noncomputable section

/-- Reconstruct the full-joint identity from the joint-count hypothesis. -/
private theorem n12_full_joint (hN3 : N3) (i j : Fin 12) (a b : Exposure) :
    jointCount cliqueF i j a b = cliqueFullJoint i j a b := by
  unfold N3 at hN3
  rw [hN3 i j a b]
  cases a <;> cases b <;>
    by_cases hij : i = j <;>
    by_cases hs : i.val / 4 = j.val / 4 <;>
    simp [cliqueFullJoint, cliqueJointTable, hij, hs, hN3]

/-- Reconstruct the independent conditional moments using the general
finite-expectation identities and the marginal/joint count hypotheses. -/
theorem n12_proof : N12 := by
  intro hN2 hN3
  change ConditionalMoments
  intro t
  have hm :
      marginal (fun _ : Fin 66 => (1 / 66 : ℚ)) cliqueF =
        cliqueObservationMarginal t false := by
    funext i a
    calc
      marginal (fun _ : Fin 66 => (1 / 66 : ℚ)) cliqueF i a =
          (exposureCount cliqueF i a : ℚ) / 66 := by
        simpa only [Nat.cast_ofNat] using
          (exhaustive_probabilities (K := ℚ) (by decide : 0 < 66)
            cliqueF i i a a).1
      _ = cliqueObservationMarginal t false i a := by
        change (exposureCount cliqueF i a : ℚ) / 66 = (cliqueFullCount a : ℚ) / 66
        rw [hN2 i a]
  have hj :
      joint (fun _ : Fin 66 => (1 / 66 : ℚ)) cliqueF =
        cliqueObservationJoint t false := by
    funext i j a b
    calc
      joint (fun _ : Fin 66 => (1 / 66 : ℚ)) cliqueF i j a b =
          (jointCount cliqueF i j a b : ℚ) / 66 := by
        simpa only [Nat.cast_ofNat] using
          (exhaustive_probabilities (K := ℚ) (by decide : 0 < 66)
            cliqueF i j a b).2
      _ = cliqueObservationJoint t false i j a b := by
        change (jointCount cliqueF i j a b : ℚ) / 66 =
          (cliqueFullJoint i j a b : ℚ) / 66
        rw [n12_full_joint hN3 i j a b]
  refine ⟨?_, ?_, ?_⟩
  · unfold cliqueT htContrast
    rw [expect_sub, htMean_expectation, htMean_expectation]
    simp only [cliqueY, one_mul, hm]
    unfold cliqueConditionalMean
    ring
  · unfold cliqueT
    rw [htContrast_second_moment]
    simp only [hj]
    simp [cliqueY, cliqueConditionalSecond, div_eq_mul_inv, mul_inv_rev] <;> norm_num
  · change expect (fun _ : Fin 66 => (1 / 66 : ℚ))
      (varianceEstimate cliqueF cliqueY (cliqueWeights t) (cliqueJoints t) .d01 .d00) = _
    simpa only [cliqueConditionalV, hm, hj] using
      (varianceEstimate_expectation (fun _ : Fin 66 => (1 / 66 : ℚ))
        cliqueF cliqueY (cliqueWeights t) (cliqueJoints t) .d01 .d00)

end

end AronowAudit.P044.Wave1.SimulatedVariance
