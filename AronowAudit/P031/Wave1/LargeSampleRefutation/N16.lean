import AronowAudit.P031.Wave1.LargeSampleRefutationBlueprint
import AronowAudit.P031.Wave1.LargeSampleRefutation.N1

/-! Squeeze the actual tie probability between zero and a vanishing explicit bound. -/

namespace AronowAudit.P031.Wave1.LargeSampleRefutation
noncomputable section
open scoped BigOperators Matrix Topology
open Filter MeasureTheory
attribute [local instance] Classical.propDecidable

theorem n16_proof : N16 := by
  intro hEC hPair hTie hDecay
  have hK : Tendsto hcK atTop atTop := by
    refine tendsto_atTop_mono (fun n => ?_) tendsto_id
    dsimp [hcK]
    nlinarith
  have hN : Tendsto hcN atTop atTop := n1_proof
  have hInvK : Tendsto (fun n => 1 / ((hcK n : ℝ) + 1)) atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat.comp hK
  have hRoot : Tendsto (fun n => 1 / Real.sqrt ((hcK n : ℝ) + 1))
      atTop (nhds 0) := by
    simpa only [Real.sqrt_div (show (0 : ℝ) ≤ 1 by norm_num),
      Real.sqrt_one, Real.sqrt_zero] using hInvK.sqrt
  have hInvN : Tendsto (fun n => 1 / (hcN n : ℝ)) atTop (nhds 0) :=
    tendsto_one_div_atTop_nhds_zero_nat.comp hN
  have hUpper : Tendsto (fun n => 1 / Real.sqrt ((hcK n : ℝ) + 1) +
      1 / (hcN n : ℝ)) atTop (nhds 0) := by
    simpa only [zero_add] using hRoot.add hInvN
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hUpper
  · intro n
    exact (hEC (hypercubePopulation n)).1 _
  · intro n
    have hCmp := hPair (hypercubePopulation n)
      (fun i j => hcQ n i = hcQ n j) rfl (fun _ _ h => h.symm)
    have hden : (hcN n : ℝ) ^ 2 = (4 : ℝ) ^ hcK n := by
      calc
        (hcN n : ℝ) ^ 2 = ((2 : ℝ) ^ hcK n) ^ 2 := by simp [hcN]
        _ = (2 : ℝ) ^ (hcK n * 2) := (pow_mul _ _ _).symm
        _ = (2 : ℝ) ^ (2 * hcK n) := by rw [Nat.mul_comm (hcK n) 2]
        _ = ((2 : ℝ) ^ 2) ^ hcK n := pow_mul _ _ _
        _ = (4 : ℝ) ^ hcK n := by norm_num
    change |eventProbability (hypercubePopulation n)
      (fun s => ∃ i ∈ s, ∃ j ∈ s, i ≠ j ∧ hcQ n i = hcQ n j) -
        ((Finset.univ.filter (fun ij : Fin (hcN n) × Fin (hcN n) =>
          hcQ n ij.1 = hcQ n ij.2)).card : ℝ) / (hcN n : ℝ) ^ 2| ≤
        1 / (hcN n : ℝ) at hCmp
    rw [hTie n, hden] at hCmp
    have hOneSided := (abs_le.mp hCmp).2
    have hBinom := hDecay (hcK n)
    linarith

end
end AronowAudit.P031.Wave1.LargeSampleRefutation
