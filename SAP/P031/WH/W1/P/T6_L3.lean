import SAP.P031.WH.W1.Leaves
import AronowAudit.P031.Wave1.LargeSampleRefutation

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P031.WH.W1.P.T6_L3

open scoped BigOperators Topology
open Filter Finset

noncomputable section

def orderedTieFrequency (n : ℕ) : ℝ :=
  ((Finset.univ.filter (fun ij : Fin (AronowAudit.P031.Wave1.LargeSampleRefutation.hcN n) ×
      Fin (AronowAudit.P031.Wave1.LargeSampleRefutation.hcN n) =>
      AronowAudit.P031.Wave1.LargeSampleRefutation.hcQ n ij.1 =
        AronowAudit.P031.Wave1.LargeSampleRefutation.hcQ n ij.2)).card : ℝ) /
    (AronowAudit.P031.Wave1.LargeSampleRefutation.hcN n : ℝ) ^ 2

end
end SAP.P031.WH.W1.P.T6_L3

open SAP.P031.WH.W1.P.T6_L3
open Filter

theorem SAP.P031.WH.W1.T6_L3_proof : SAP.P031.WH.W1.T6_L3 := by
  classical
  let hcN := AronowAudit.P031.Wave1.LargeSampleRefutation.hcN
  let hcQ := AronowAudit.P031.Wave1.LargeSampleRefutation.hcQ
  let hypercubePopulation := AronowAudit.P031.Wave1.LargeSampleRefutation.hypercubePopulation
  have hPair : AronowAudit.P031.Wave1.LargeSampleRefutation.PairComparison :=
    AronowAudit.P031.Wave1.LargeSampleRefutation.n4_proof
  have hActual : AronowAudit.P031.Wave1.LargeSampleRefutation.TieProbabilityVanishes :=
    AronowAudit.P031.Wave1.LargeSampleRefutation.n16_proof
      AronowAudit.P031.Wave1.FootnoteThreeProbability.n7_proof
      hPair
      AronowAudit.P031.Wave1.LargeSampleRefutation.n14_proof
      AronowAudit.P031.Wave1.LargeSampleRefutation.n15_proof
  have hN : Tendsto hcN atTop atTop :=
    AronowAudit.P031.Wave1.LargeSampleRefutation.n1_proof
  have hInvN : Tendsto (fun n => 1 / (hcN n : ℝ)) atTop (nhds 0) :=
    tendsto_one_div_atTop_nhds_zero_nat.comp hN
  have hActualPlus : Tendsto
      (fun n => AronowAudit.P031.eventProbability (hypercubePopulation n)
        (fun s => ∃ i ∈ s, ∃ j ∈ s, i ≠ j ∧ hcQ n i = hcQ n j) +
          1 / (hcN n : ℝ)) atTop (nhds 0) := by
    simpa only [zero_add] using hActual.add hInvN
  have hCompare (n : ℕ) :
      |AronowAudit.P031.eventProbability (hypercubePopulation n)
          (fun s => ∃ i ∈ s, ∃ j ∈ s, i ≠ j ∧ hcQ n i = hcQ n j) -
        orderedTieFrequency n| ≤ 1 / (hcN n : ℝ) := by
    have h := hPair (hypercubePopulation n) (fun i j => hcQ n i = hcQ n j) rfl
      (fun _ _ hEq => hEq.symm)
    change |AronowAudit.P031.eventProbability (hypercubePopulation n)
        (fun s => ∃ i ∈ s, ∃ j ∈ s, i ≠ j ∧ hcQ n i = hcQ n j) -
      ((Finset.univ.filter (fun ij : Fin (hcN n) × Fin (hcN n) =>
        hcQ n ij.1 = hcQ n ij.2)).card : ℝ) / (hcN n : ℝ) ^ 2| ≤
      1 / (hcN n : ℝ) at h
    simpa [orderedTieFrequency] using h
  have hTieFrequency : Tendsto orderedTieFrequency atTop (nhds 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hActualPlus
    · intro n
      unfold orderedTieFrequency
      apply div_nonneg
      · exact Nat.cast_nonneg _
      · positivity
    · intro n
      have hAbs := abs_le.mp (hCompare n)
      dsimp [orderedTieFrequency] at hAbs ⊢
      linarith
  have hRoot : Tendsto (fun n => Real.sqrt (orderedTieFrequency n)) atTop
      (nhds 0) := by
    simpa only [Real.sqrt_zero] using hTieFrequency.sqrt
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hRoot
  · intro n
    unfold zeroFraction
    apply div_nonneg
    · exact Nat.cast_nonneg _
    · positivity
  · intro n
    let Z : Finset (Fin (hcN n)) :=
      Finset.univ.filter (fun i => hcQ n i = 0)
    let T : Finset (Fin (hcN n) × Fin (hcN n)) :=
      Finset.univ.filter (fun ij => hcQ n ij.1 = hcQ n ij.2)
    have hSub : Z ×ˢ Z ⊆ T := by
      intro ij hij
      rcases Finset.mem_product.mp hij with ⟨hi, hj⟩
      have hi0 : hcQ n ij.1 = 0 := (Finset.mem_filter.mp hi).2
      have hj0 : hcQ n ij.2 = 0 := (Finset.mem_filter.mp hj).2
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi0.trans hj0.symm⟩
    have hCard : Z.card ^ 2 ≤ T.card := by
      calc
        Z.card ^ 2 = (Z ×ˢ Z).card := by simp [Finset.card_product, pow_two]
        _ ≤ T.card := Finset.card_le_card hSub
    have hCardReal : (Z.card : ℝ) ^ 2 ≤ (T.card : ℝ) := by exact_mod_cast hCard
    have hSquare : (zeroFraction (hcQ n)) ^ 2 ≤ orderedTieFrequency n := by
      change ((Z.card : ℝ) / (hcN n : ℝ)) ^ 2 ≤
        (T.card : ℝ) / (hcN n : ℝ) ^ 2
      calc
        _ = (Z.card : ℝ) ^ 2 / (hcN n : ℝ) ^ 2 := by ring
        _ ≤ (T.card : ℝ) / (hcN n : ℝ) ^ 2 :=
          div_le_div_of_nonneg_right hCardReal (sq_nonneg _)
    have hp : 0 ≤ zeroFraction (hcQ n) := by
      unfold zeroFraction
      apply div_nonneg
      · exact Nat.cast_nonneg _
      · positivity
    have ht : 0 ≤ orderedTieFrequency n := by
      unfold orderedTieFrequency
      apply div_nonneg
      · exact Nat.cast_nonneg _
      · positivity
    have hroot : 0 ≤ Real.sqrt (orderedTieFrequency n) := Real.sqrt_nonneg _
    have hsquare : (zeroFraction (hcQ n)) ^ 2 ≤
        (Real.sqrt (orderedTieFrequency n)) ^ 2 := by
      rw [Real.sq_sqrt ht]
      exact hSquare
    exact (sq_le_sq₀ hp hroot).mp hsquare

