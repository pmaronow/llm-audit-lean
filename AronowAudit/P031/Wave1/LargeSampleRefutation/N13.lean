import AronowAudit.P031.Wave1.LargeSampleRefutationBlueprint

/-! The strict relative-error event includes exactly the non-tied treated pairs. -/

namespace AronowAudit.P031.Wave1.LargeSampleRefutation
noncomputable section
open scoped BigOperators Matrix Topology
open Filter MeasureTheory
attribute [local instance] Classical.propDecidable

set_option backward.isDefEq.respectTransparency false in
theorem n13_proof : N13 := by
  intro n s hs
  change Finset (Fin (hcN n)) at s
  change ((1 / 4 : ℝ) * |hc2Estimator (hypercubePopulation n) s| <
      |hrEstimator (hypercubePopulation n) s - hc2Estimator (hypercubePopulation n) s|) ↔
    ¬ ∃ i ∈ s, ∃ j ∈ s, i ≠ j ∧ hcQ n i = hcQ n j
  have ha := population_assignment_admissible (hypercubePopulation n) s hs
  have hcard : s.card = 2 := (Finset.mem_powersetCard.mp hs).2
  obtain ⟨i, j, hij, rfl⟩ := Finset.card_eq_two.mp hcard
  let Y := observed {i, j} (hypercubePopulation n).y1 (hypercubePopulation n).y0
  have hzero : ∀ a ∈ ({i, j} : Finset (Fin (hcN n)))ᶜ, Y a = 0 := by
    intro a ha'
    exact observed_control {i, j} _ _ ha'
  have hHR : hrEstimator (hypercubePopulation n) {i, j} =
      hc2Estimator (hypercubePopulation n) {i, j} / 2 :=
    (two_treated_zero_controls {i, j} Y ha (Finset.card_pair hij) hzero).1
  have hVC : sampleVariance ({i, j} : Finset (Fin (hcN n)))ᶜ Y = 0 := by
    rw [sample_variance_congr _ hzero]
    simp [sampleVariance, groupMean]
  have hVT : sampleVariance {i, j} Y =
      ((hypercubePopulation n).y1 i - (hypercubePopulation n).y1 j) ^ 2 / 2 := by
    rw [sample_variance_congr {i, j} (v := Y) (w := (hypercubePopulation n).y1)
      (fun a ha' => observed_treatment {i, j} _ _ ha')]
    norm_num [sampleVariance, groupMean, hij, hij.symm] <;> ring
  have hB : hc2Estimator (hypercubePopulation n) {i, j} =
      ((hypercubePopulation n).y1 i - (hypercubePopulation n).y1 j) ^ 2 / 4 := by
    change hc2 {i, j} Y = _
    rw [hc2_eq_neyman {i, j} Y ha]
    unfold neyman
    rw [hVC, hVT, Finset.card_pair hij]
    norm_num <;> ring
  have hBnonneg : 0 ≤ hc2Estimator (hypercubePopulation n) {i, j} := by
    rw [hB]
    positivity
  have hBzero : hc2Estimator (hypercubePopulation n) {i, j} = 0 ↔
      hcQ n i = hcQ n j := by
    rw [hB]
    constructor
    · intro h
      have hsq : ((hypercubePopulation n).y1 i -
          (hypercubePopulation n).y1 j) ^ 2 = 0 := by linarith
      have hy := sub_eq_zero.mp (sq_eq_zero_iff.mp hsq)
      change hcQ n i / (2 : ℝ) ^ (2 * (n + 1) ^ 2) =
        hcQ n j / (2 : ℝ) ^ (2 * (n + 1) ^ 2) at hy
      exact (div_left_inj' (by positivity : (2 : ℝ) ^ (2 * (n + 1) ^ 2) ≠ 0)).mp hy
    · intro h
      simp [hypercubePopulation, h]
  have hTie : (∃ a ∈ ({i, j} : Finset (Fin (hcN n))),
      ∃ b ∈ ({i, j} : Finset (Fin (hcN n))), a ≠ b ∧ hcQ n a = hcQ n b) ↔
      hcQ n i = hcQ n j := by
    constructor
    · rintro ⟨a, ha', b, hb', hab, hq⟩
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha' hb'
      rcases ha' with rfl | rfl <;> rcases hb' with rfl | rfl
      · exact (hab rfl).elim
      · exact hq
      · exact hq.symm
      · exact (hab rfl).elim
    · intro hq
      exact ⟨i, by simp, j, by simp, hij, hq⟩
  rw [hHR, abs_of_nonneg hBnonneg,
    abs_of_nonpos (by linarith : hc2Estimator (hypercubePopulation n) {i, j} / 2 -
      hc2Estimator (hypercubePopulation n) {i, j} ≤ 0), hTie, ← hBzero]
  constructor
  · intro h hz
    rw [hz] at h
    norm_num at h
  · intro h
    have hp : 0 < hc2Estimator (hypercubePopulation n) {i, j} :=
      lt_of_le_of_ne hBnonneg (Ne.symm h)
    linarith

end
end AronowAudit.P031.Wave1.LargeSampleRefutation
