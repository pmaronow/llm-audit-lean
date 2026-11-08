import SAP.P031.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P031.WH.W1.P.T6_L1

open SAP.P031.WH.W1
open AronowAudit.P031.Wave1.LargeSampleRefutation (hcN hcQ hypercubePopulation)
open scoped BigOperators
open Finset

private lemma sqrt_pair_variance (a b : ℝ) :
    Real.sqrt ((a - b) ^ 2 / 4) = |a - b| / 2 := by
  have h : (a - b) ^ 2 / 4 = ((a - b) / 2) ^ 2 := by ring
  rw [h, Real.sqrt_sq_eq_abs]
  norm_num [abs_div]

private lemma abs_midpoint_iff_product_nonpos (a b : ℝ) :
    |(a + b) / 2| ≤ |a - b| / 2 ↔ a * b ≤ 0 := by
  have htwo : (0 : ℝ) < 2 := by norm_num
  have hrel : |(a + b) / 2| ≤ |a - b| / 2 ↔ |a + b| ≤ |a - b| := by
    simp only [abs_div, abs_of_pos htwo]
    rw [div_le_div_iff₀ htwo htwo]
    constructor <;> intro h <;> nlinarith
  rw [hrel]
  constructor
  · intro h
    have hs : |a + b| ^ 2 ≤ |a - b| ^ 2 :=
      (sq_le_sq₀ (abs_nonneg _) (abs_nonneg _)).2 h
    rw [sq_abs, sq_abs] at hs
    nlinarith
  · intro h
    have hs : (a + b) ^ 2 ≤ (a - b) ^ 2 := by nlinarith
    have hs' : |a + b| ^ 2 ≤ |a - b| ^ 2 := by
      simpa only [sq_abs] using hs
    exact (sq_le_sq₀ (abs_nonneg _) (abs_nonneg _)).1 hs'

private lemma scaled_pair_coverage_iff (n : ℕ) (i j : Fin (hcN n)) :
    |((hcQ n i / (2 : ℝ) ^ (2 * (n + 1) ^ 2) +
        hcQ n j / (2 : ℝ) ^ (2 * (n + 1) ^ 2)) / 2)| ≤
      Real.sqrt (((hcQ n i / (2 : ℝ) ^ (2 * (n + 1) ^ 2) -
        hcQ n j / (2 : ℝ) ^ (2 * (n + 1) ^ 2)) ^ 2) / 4) ↔
      hcQ n i * hcQ n j ≤ 0 := by
  let d : ℝ := (2 : ℝ) ^ (2 * (n + 1) ^ 2)
  let a : ℝ := hcQ n i / d
  let b : ℝ := hcQ n j / d
  have hd : 0 < d := by positivity
  have hab : a * b = hcQ n i * hcQ n j / d ^ 2 := by
    dsimp [a, b]
    field_simp [ne_of_gt hd] <;> ring
  rw [show Real.sqrt ((a - b) ^ 2 / 4) = |a - b| / 2 from sqrt_pair_variance _ _]
  change |(a + b) / 2| ≤ |a - b| / 2 ↔ hcQ n i * hcQ n j ≤ 0
  rw [abs_midpoint_iff_product_nonpos]
  rw [hab, div_le_iff₀ (by positivity : (0 : ℝ) < d ^ 2)]
  simp

private lemma pair_sign_event_iff (n : ℕ) (i j : Fin (hcN n)) (hij : i ≠ j) :
    (∃ a ∈ ({i, j} : Finset (Fin (hcN n))),
      ∃ b ∈ ({i, j} : Finset (Fin (hcN n))),
        a ≠ b ∧ hcQ n a * hcQ n b ≤ 0) ↔ hcQ n i * hcQ n j ≤ 0 := by
  constructor
  · rintro ⟨a, ha, b, hb, hab, hq⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact (hab rfl).elim
    · exact hq
    · simpa [mul_comm] using hq
    · exact (hab rfl).elim
  · intro hq
    exact ⟨i, by simp, j, by simp, hij, hq⟩

end SAP.P031.WH.W1.P.T6_L1

open AronowAudit.P031.Wave1.LargeSampleRefutation (hcN hcQ hypercubePopulation)

theorem SAP.P031.WH.W1.T6_L1_proof : SAP.P031.WH.W1.T6_L1 := by
  classical
  intro n
  let P : SAP.P031.Population := SAP.P031.WH.W1.coveragePopulation n
  have hEffect : SAP.P031.populationEffect P = 0 := by
    change AronowAudit.P031.populationEffect
      (AronowAudit.P031.Wave1.LargeSampleRefutation.hypercubePopulation n) = 0
    exact (AronowAudit.P031.Wave1.LargeSampleRefutation.n3_proof
      AronowAudit.P031.Wave1.LargeSampleRefutation.n2_proof n).2
  unfold SAP.P031.coverage SAP.P031.eventProbability SAP.P031.expectation
  apply congrArg (fun x : ℝ => x /
    (((Finset.univ : Finset (Fin (SAP.P031.WH.W1.coveragePopulation n).N)).powersetCard
      (SAP.P031.WH.W1.coveragePopulation n).M).card : ℝ))
  apply Finset.sum_congr rfl
  intro s hs
  have hcard : s.card = 2 := (Finset.mem_powersetCard.mp hs).2
  obtain ⟨i, j, hij, rfl⟩ := Finset.card_eq_two.mp hcard
  have hN : P.N = hcN n := rfl
  let ii : Fin (hcN n) := Fin.cast hN i
  let jj : Fin (hcN n) := Fin.cast hN j
  have hiCast : ii = i := by
    apply Fin.ext
    rfl
  have hjCast : jj = j := by
    apply Fin.ext
    rfl
  dsimp only
  let Y := SAP.P031.observed ({i, j} : Finset (Fin (P.N))) P.y1 P.y0
  have hzero : ∀ a ∈ ({i, j} : Finset (Fin (P.N)))ᶜ, Y a = 0 := by
    intro a ha
    change AronowAudit.P031.observed ({i, j} : Finset (Fin (P.N))) P.y1 P.y0 a = 0
    rw [AronowAudit.P031.observed_control ({i, j} : Finset (Fin (P.N))) P.y1 P.y0 ha]
    simp [P, SAP.P031.WH.W1.coveragePopulation, SAP.P031.Bridge.fromPopulation,
      AronowAudit.P031.Wave1.LargeSampleRefutation.hypercubePopulation]
  have hmeanT : SAP.P031.groupMean ({i, j} : Finset (Fin (P.N))) Y =
      (P.y1 i + P.y1 j) / 2 := by
    norm_num [Y, SAP.P031.groupMean, SAP.P031.observed, SAP.P031.treatment,
      hij, hij.symm] <;> ring
  have hmeanC : SAP.P031.groupMean ({i, j} : Finset (Fin (P.N)))ᶜ Y = 0 := by
    unfold SAP.P031.groupMean
    rw [Finset.sum_eq_zero]
    · simp
    · intro a ha
      exact hzero a ha
  have hBeta : SAP.P031.pointEstimate P {i, j} = (P.y1 i + P.y1 j) / 2 := by
    change SAP.P031.estimate ({i, j} : Finset (Fin (P.N))) Y = _
    unfold SAP.P031.estimate
    rw [hmeanT, hmeanC]
    simp
  have hVarT : SAP.P031.sampleVariance ({i, j} : Finset (Fin (P.N))) P.y1 =
      (P.y1 i - P.y1 j) ^ 2 / 2 := by
    norm_num [SAP.P031.sampleVariance, SAP.P031.groupMean, hij, hij.symm] <;> ring
  have hVarC : SAP.P031.sampleVariance ({i, j} : Finset (Fin (P.N)))ᶜ P.y0 = 0 := by
    simp [SAP.P031.sampleVariance, SAP.P031.groupMean, P,
      SAP.P031.WH.W1.coveragePopulation, SAP.P031.Bridge.fromPopulation,
      AronowAudit.P031.Wave1.LargeSampleRefutation.hypercubePopulation]
  change AronowAudit.P031.sampleVariance ({i, j} : Finset (Fin (P.N))) P.y1 =
      (P.y1 i - P.y1 j) ^ 2 / 2 at hVarT
  change AronowAudit.P031.sampleVariance ({i, j} : Finset (Fin (P.N)))ᶜ P.y0 = 0 at hVarC
  have hVariance : SAP.P031.neymanEstimator P {i, j} =
      (P.y1 i - P.y1 j) ^ 2 / 4 := by
    change AronowAudit.P031.neyman ({i, j} : Finset (Fin (P.N)))
      (AronowAudit.P031.observed ({i, j} : Finset (Fin (P.N))) P.y1 P.y0) = _
    rw [AronowAudit.P031.observed_neyman, hVarT, hVarC, Finset.card_pair hij]
    norm_num <;> ring
  have hYi : P.y1 i = hcQ n ii /
      (2 : ℝ) ^ (2 * (n + 1) ^ 2) := by
    rfl
  have hYj : P.y1 j = hcQ n jj /
      (2 : ℝ) ^ (2 * (n + 1) ^ 2) := by
    rfl
  have hCoverP :
      (|SAP.P031.pointEstimate P {i, j} - SAP.P031.populationEffect P| ≤
        1 * Real.sqrt (SAP.P031.neymanEstimator P {i, j})) ↔
        hcQ n i * hcQ n j ≤ 0 := by
    rw [hBeta, hEffect, hVariance]
    simp only [sub_zero, one_mul]
    rw [hYi, hYj]
    simpa only [hiCast, hjCast] using
      SAP.P031.WH.W1.P.T6_L1.scaled_pair_coverage_iff n ii jj
  have hCover :
      (|SAP.P031.pointEstimate (SAP.P031.WH.W1.coveragePopulation n) {i, j} -
          SAP.P031.populationEffect (SAP.P031.WH.W1.coveragePopulation n)| ≤
        1 * Real.sqrt (SAP.P031.neymanEstimator
          (SAP.P031.WH.W1.coveragePopulation n) {i, j})) ↔
        hcQ n i * hcQ n j ≤ 0 := by
    simpa [P] using hCoverP
  have hEventP :
      (∃ a ∈ ({i, j} : Finset (Fin (P.N))),
        ∃ b ∈ ({i, j} : Finset (Fin (P.N))), a ≠ b ∧
          hcQ n a * hcQ n b ≤ 0) ↔ hcQ n i * hcQ n j ≤ 0 := by
    constructor
    · rintro ⟨a, ha, b, hb, hab, hq⟩
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
      · exact (hab rfl).elim
      · exact hq
      · simpa [mul_comm] using hq
      · exact (hab rfl).elim
    · intro hq
      exact ⟨i, by simp, j, by simp, hij, hq⟩
  have hEvent :
      (∃ a ∈ ({i, j} : Finset (Fin ((SAP.P031.WH.W1.coveragePopulation n).N))),
        ∃ b ∈ ({i, j} : Finset (Fin ((SAP.P031.WH.W1.coveragePopulation n).N))),
          a ≠ b ∧ hcQ n a * hcQ n b ≤ 0) ↔ hcQ n i * hcQ n j ≤ 0 := by
    simpa [P] using hEventP
  simpa only [hCover, hEvent]
