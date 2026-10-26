import AronowAudit.P044.P044_NetworkSpillovers
import AronowAudit.P045.P045_ExposureVariance

namespace AronowAudit.P044.Wave1
open Finset
open scoped BigOperators
noncomputable section
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

/- P045 proves the same finite calculations for a separately defined exposure
   type.  The following helpers transport those kernel-checked calculations
   through the explicit bijection of the four labels. -/
private def gp044Reduced_label : Exposure → AronowAudit.P045.ExposureVariance.Exposure
  | .d11 => .d11 | .d10 => .d10 | .d01 => .d01 | .d00 => .d00

private lemma gp044Reduced_injective : Function.Injective gp044Reduced_label := by
  intro a b h
  cases a <;> cases b <;> simp_all [gp044Reduced_label]

private lemma gp044Reduced_f (t : Fin 66) (i : Fin 12) :
    gp044Reduced_label (cliqueF t i) = AronowAudit.P045.ExposureVariance.cliqueF t i := by
  have hp : AronowAudit.P045.ExposureVariance.cliquePairs t = cliquePairs t := rfl
  simp only [cliqueF, AronowAudit.P045.ExposureVariance.cliqueF, hp]
  split_ifs <;> rfl

private lemma gp044Reduced_fullCount (a : Exposure) :
    cliqueFullCount a = AronowAudit.P045.ExposureVariance.cliqueFullCount (gp044Reduced_label a) := by
  cases a <;> rfl

private lemma gp044Counts_exposureTransport (i : Fin 12) (a : Exposure) :
    exposureCount cliqueF i a = AronowAudit.P045.ExposureVariance.exposureCount
      AronowAudit.P045.ExposureVariance.cliqueF i (gp044Reduced_label a) := by
  unfold exposureCount AronowAudit.P045.ExposureVariance.exposureCount
  congr 1
  ext r
  simp only [Finset.mem_filter, ← gp044Reduced_f, gp044Reduced_injective.eq_iff]

private lemma gp044Counts_jointTransport (i j : Fin 12) (a b : Exposure) :
    jointCount cliqueF i j a b = AronowAudit.P045.ExposureVariance.jointCount
      AronowAudit.P045.ExposureVariance.cliqueF i j (gp044Reduced_label a) (gp044Reduced_label b) := by
  unfold jointCount AronowAudit.P045.ExposureVariance.jointCount
  congr 1
  ext r
  simp only [Finset.mem_filter, ← gp044Reduced_f, gp044Reduced_injective.eq_iff]

private lemma gp044Reduced_fullJoint (i j : Fin 12) (a b : Exposure)
    (ha : a = .d01 ∨ a = .d00) (hb : b = .d01 ∨ b = .d00) :
    cliqueFullJoint i j a b = AronowAudit.P045.ExposureVariance.cliqueFullJoint
      i j (gp044Reduced_label a) (gp044Reduced_label b) := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> rfl

private lemma gp044Reduced_weights (t : Fin 66) (i : Fin 12) (a : Exposure) :
    cliqueWeights t i a = AronowAudit.P045.ExposureVariance.cliqueWeights t i (gp044Reduced_label a) := by
  unfold cliqueWeights AronowAudit.P045.ExposureVariance.cliqueWeights
  rw [← gp044Reduced_fullCount]
  simp only [← gp044Reduced_f, gp044Reduced_injective.eq_iff]

private lemma gp044Reduced_marginal (t : Fin 66) (i : Fin 12) (a : Exposure) :
    cliqueObservationMarginal t false i a =
      AronowAudit.P045.ExposureVariance.cliqueObservationMarginal t false i (gp044Reduced_label a) := by
  change (cliqueFullCount a : ℚ) / 66 =
    (AronowAudit.P045.ExposureVariance.cliqueFullCount (gp044Reduced_label a) : ℚ) / 66
  rw [gp044Reduced_fullCount]

private lemma gp044Reduced_joint (t : Fin 66) (i j : Fin 12) (a b : Exposure)
    (ha : a = .d01 ∨ a = .d00) (hb : b = .d01 ∨ b = .d00) :
    cliqueObservationJoint t false i j a b =
      AronowAudit.P045.ExposureVariance.cliqueObservationJoint t false i j
        (gp044Reduced_label a) (gp044Reduced_label b) := by
  unfold cliqueObservationJoint AronowAudit.P045.ExposureVariance.cliqueObservationJoint
  change (cliqueFullJoint i j a b : ℚ) / 66 =
    (AronowAudit.P045.ExposureVariance.cliqueFullJoint i j (gp044Reduced_label a) (gp044Reduced_label b) : ℚ) / 66
  rw [gp044Reduced_fullJoint i j a b ha hb]

private lemma gp044Reduced_joints (t : Fin 66) (i j : Fin 12) (a b : Exposure)
    (ha : a = .d01 ∨ a = .d00) (hb : b = .d01 ∨ b = .d00) :
    cliqueJoints t i j a b = AronowAudit.P045.ExposureVariance.cliqueJoints t i j
      (gp044Reduced_label a) (gp044Reduced_label b) := by
  unfold cliqueJoints AronowAudit.P045.ExposureVariance.cliqueJoints
  rw [← gp044Reduced_fullJoint i j a b ha hb]
  simp only [← gp044Reduced_f, gp044Reduced_injective.eq_iff]

private lemma gp044Reduced_mean (t : Fin 66) :
    cliqueConditionalMean t false = AronowAudit.P045.ExposureVariance.cliqueConditionalMean t false := by
  unfold cliqueConditionalMean AronowAudit.P045.ExposureVariance.cliqueConditionalMean
  simp only [gp044Reduced_marginal, gp044Reduced_weights, gp044Reduced_label]

private lemma gp044Reduced_second (t : Fin 66) :
    cliqueConditionalSecond t false = AronowAudit.P045.ExposureVariance.cliqueConditionalSecond t false := by
  have hkk := fun i j => gp044Reduced_joint t i j .d01 .d01 (Or.inl rfl) (Or.inl rfl)
  have hll := fun i j => gp044Reduced_joint t i j .d00 .d00 (Or.inr rfl) (Or.inr rfl)
  have hkl := fun i j => gp044Reduced_joint t i j .d01 .d00 (Or.inl rfl) (Or.inr rfl)
  have hlk := fun i j => gp044Reduced_joint t i j .d00 .d01 (Or.inr rfl) (Or.inl rfl)
  unfold cliqueConditionalSecond AronowAudit.P045.ExposureVariance.cliqueConditionalSecond
  simp only [hkk, hll, hkl, hlk, gp044Reduced_weights, gp044Reduced_label]

private lemma gp044Reduced_value (t : Fin 66) :
    cliqueConditionalV t false = AronowAudit.P045.ExposureVariance.cliqueConditionalV t false := by
  have hkk := fun i j => gp044Reduced_joint t i j .d01 .d01 (Or.inl rfl) (Or.inl rfl)
  have hll := fun i j => gp044Reduced_joint t i j .d00 .d00 (Or.inr rfl) (Or.inr rfl)
  have hkl := fun i j => gp044Reduced_joint t i j .d01 .d00 (Or.inl rfl) (Or.inr rfl)
  have qkk := fun i j => gp044Reduced_joints t i j .d01 .d01 (Or.inl rfl) (Or.inl rfl)
  have qll := fun i j => gp044Reduced_joints t i j .d00 .d00 (Or.inr rfl) (Or.inr rfl)
  have qkl := fun i j => gp044Reduced_joints t i j .d01 .d00 (Or.inl rfl) (Or.inr rfl)
  unfold cliqueConditionalV AronowAudit.P045.ExposureVariance.cliqueConditionalV
    expectedVariance AronowAudit.P045.ExposureVariance.expectedVariance
    expectedTotalVariance AronowAudit.P045.ExposureVariance.expectedTotalVariance
    expectedTotalCovariance AronowAudit.P045.ExposureVariance.expectedTotalCovariance
  simp only [hkk, hll, hkl, qkk, qll, qkl, gp044Reduced_weights,
    gp044Reduced_marginal, cliqueY, AronowAudit.P045.ExposureVariance.cliqueY, gp044Reduced_label]

theorem clique_fixed_reduced_arithmetic_proof :
    cliqueConditionalSecond 0 false - (cliqueConditionalMean 0 false)^2 = 2810528137/5767941312 ∧
    cliqueConditionalV 0 false = 267260522663/634473544320 ∧
    cliqueConditionalV 0 false < cliqueConditionalSecond 0 false - (cliqueConditionalMean 0 false)^2 ∧
    cliqueConditionalSecond 3 false - (cliqueConditionalMean 3 false)^2 = 937589375/1922647104 ∧
    cliqueConditionalV 3 false = 4830430961/10574559072 ∧
    cliqueConditionalV 3 false < cliqueConditionalSecond 3 false - (cliqueConditionalMean 3 false)^2 ∧
    cliqueConditionalV 0 false - (cliqueConditionalSecond 0 false - (cliqueConditionalMean 0 false)^2) =
      -1551761941/23499020160 ∧
    cliqueConditionalV 3 false - (cliqueConditionalSecond 3 false - (cliqueConditionalMean 3 false)^2) =
      -72513467/2349902016 := by
  simp only [gp044Reduced_mean, gp044Reduced_second, gp044Reduced_value]
  exact AronowAudit.P045.ExposureVariance.clique_fixed_reduced_arithmetic

private lemma gp044Counts_marginal (i : Fin 12) (a : Exposure) :
    exposureCount cliqueF i a = cliqueFullCount a := by
  rw [gp044Counts_exposureTransport,
    AronowAudit.P045.ExposureVariance.clique_full_counts.1 i (gp044Reduced_label a),
    gp044Reduced_fullCount]

private lemma gp044Counts_joint (i j : Fin 12) (a b : Exposure)
    (ha : a = .d01 ∨ a = .d00) (hb : b = .d01 ∨ b = .d00) :
    jointCount cliqueF i j a b = cliqueFullJoint i j a b := by
  have ha' : gp044Reduced_label a = .d01 ∨ gp044Reduced_label a = .d00 := by
    rcases ha with rfl | rfl <;> simp [gp044Reduced_label]
  have hb' : gp044Reduced_label b = .d01 ∨ gp044Reduced_label b = .d00 := by
    rcases hb with rfl | rfl <;> simp [gp044Reduced_label]
  rw [gp044Counts_jointTransport,
    AronowAudit.P045.ExposureVariance.clique_full_counts.2 i j _ _ ha' hb',
    gp044Reduced_fullJoint i j a b ha hb]

private lemma gp044Fixed_marginal (t : Fin 66) (i : Fin 12) (a : Exposure) :
    marginal (fun _ : Fin 66 => (1/66 : ℚ)) cliqueF i a =
      cliqueObservationMarginal t false i a := by
  calc
    _ = (exposureCount cliqueF i a : ℚ) / 66 := by
      simpa using (exhaustive_probabilities (K := ℚ) (by decide : 0 < 66) cliqueF i i a a).1
    _ = _ := by rw [gp044Counts_marginal]; rfl

private lemma gp044Fixed_joint (t : Fin 66) (i j : Fin 12) (a b : Exposure)
    (ha : a = .d01 ∨ a = .d00) (hb : b = .d01 ∨ b = .d00) :
    joint (fun _ : Fin 66 => (1/66 : ℚ)) cliqueF i j a b =
      cliqueObservationJoint t false i j a b := by
  calc
    _ = (jointCount cliqueF i j a b : ℚ) / 66 := by
      simpa using (exhaustive_probabilities (K := ℚ) (by decide : 0 < 66) cliqueF i j a b).2
    _ = _ := by rw [gp044Counts_joint i j a b ha hb]; rfl

private lemma gp044Fixed_moments (t : Fin 66) :
    expect (fun _ : Fin 66 => (1/66 : ℚ)) (cliqueT t) = cliqueConditionalMean t false ∧
    expect (fun _ : Fin 66 => (1/66 : ℚ)) (fun z => cliqueT t z ^ 2) = cliqueConditionalSecond t false ∧
    expect (fun _ : Fin 66 => (1/66 : ℚ)) (cliqueV t) = cliqueConditionalV t false := by
  have hkk := fun i j => gp044Fixed_joint t i j .d01 .d01 (Or.inl rfl) (Or.inl rfl)
  have hll := fun i j => gp044Fixed_joint t i j .d00 .d00 (Or.inr rfl) (Or.inr rfl)
  have hkl := fun i j => gp044Fixed_joint t i j .d01 .d00 (Or.inl rfl) (Or.inr rfl)
  have hlk := fun i j => gp044Fixed_joint t i j .d00 .d01 (Or.inr rfl) (Or.inl rfl)
  refine ⟨?_, ?_, ?_⟩
  · unfold cliqueT htContrast
    rw [expect_sub, htMean_expectation, htMean_expectation]
    simp only [cliqueY, one_mul]
    simp_rw [gp044Fixed_marginal t]
    unfold cliqueConditionalMean
    ring
  · unfold cliqueT
    rw [htContrast_second_moment]
    simp_rw [hkk, hll, hkl, hlk]
    simp [cliqueY, cliqueConditionalSecond, div_eq_mul_inv, mul_inv_rev] <;> norm_num
  · unfold cliqueV
    rw [varianceEstimate_expectation]
    unfold expectedVariance cliqueConditionalV expectedVariance expectedTotalVariance expectedTotalCovariance
    simp_rw [hkk, hll, hkl, gp044Fixed_marginal t]

theorem clique_fixed_table_counterexamples_proof :
    designVariance (fun _ : Fin 66 => (1/66 : ℚ)) (cliqueT 0) = 2810528137/5767941312 ∧
    expect (fun _ : Fin 66 => (1/66 : ℚ)) (cliqueV 0) = 267260522663/634473544320 ∧
    expect (fun _ : Fin 66 => (1/66 : ℚ)) (cliqueV 0) <
      designVariance (fun _ : Fin 66 => (1/66 : ℚ)) (cliqueT 0) ∧
    designVariance (fun _ : Fin 66 => (1/66 : ℚ)) (cliqueT 3) = 937589375/1922647104 ∧
    expect (fun _ : Fin 66 => (1/66 : ℚ)) (cliqueV 3) = 4830430961/10574559072 ∧
    expect (fun _ : Fin 66 => (1/66 : ℚ)) (cliqueV 3) <
      designVariance (fun _ : Fin 66 => (1/66 : ℚ)) (cliqueT 3) := by
  unfold designVariance
  have hM := fun t => (gp044Fixed_moments t).1
  have hS := fun t => (gp044Fixed_moments t).2.1
  have hV := fun t => (gp044Fixed_moments t).2.2
  simp_rw [hS, hM, hV]
  have h := clique_fixed_reduced_arithmetic_proof
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1⟩

theorem clique_full_counts_proof :
    (∀ i a, exposureCount cliqueF i a = cliqueFullCount a) ∧
    (∀ i j a b, (a = Exposure.d01 ∨ a = .d00) → (b = Exposure.d01 ∨ b = .d00) →
      jointCount cliqueF i j a b = cliqueFullJoint i j a b) := by
  exact ⟨gp044Counts_marginal, gp044Counts_joint⟩

end
end AronowAudit.P044.Wave1
