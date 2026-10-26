import AronowAudit.P013.Wave1.PrintedWaldBlueprint
import Mathlib.Analysis.SpecificLimits.Basic

set_option autoImplicit false

namespace AronowAudit.P013.Wave1.PrintedWald

open AronowAudit.P013 AronowAudit.P013.Wave1.CorrectedCoverage Filter Finset
open scoped BigOperators Topology NNReal ENNReal

noncomputable section

/-- The singleton proportion vanishes, the full-pair proportion tends to one half,
and the probability that a pair is split tends to one. -/
theorem n6_proof : N6 := by
  have hsize : Tendsto (fun n : ℕ => n + 1) atTop atTop := tendsto_add_atTop_nat 1
  have hmax : Tendsto (fun n : ℕ => max 4 (n + 1)) atTop atTop := by
    apply tendsto_atTop_mono (fun n => le_max_right 4 (n + 1)) hsize
  have hinv : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one] using
      (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ)).comp hsize
  have hepsilon : Tendsto (fun n : ℕ => pairEpsilon (max 4 (n + 1))) atTop (𝓝 0) := by
    have h := ((tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ)).comp hmax).pow 2
    simpa only [Function.comp_def, pairEpsilon, div_pow, one_pow, zero_pow (by decide : 2 ≠ 0)] using h
  have hsplit : Tendsto (fun n : ℕ => pairSplitProbability (max 4 (n + 1)))
      atTop (𝓝 1) := by
    have h := (tendsto_const_nhds (x := (1 : ℝ))).sub (hepsilon.const_mul 2)
    simpa only [pairSplitProbability, mul_zero, sub_zero] using h
  have hrem : Tendsto (fun n : ℕ => (((n + 1) % 2 : ℕ) : ℝ) / ((n : ℝ) + 1))
      atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hinv
    · intro n
      positivity
    · intro n
      have hs : ((((n + 1) % 2 : ℕ) : ℝ)) ≤ 1 := by
        exact_mod_cast (show (n + 1) % 2 ≤ 1 by omega)
      exact div_le_div_of_nonneg_right hs (by positivity)
  have hdecomp (n : ℕ) :
      (((n + 1) / 2 : ℕ) : ℝ) / ((n : ℝ) + 1) =
        (1 - (((n + 1) % 2 : ℕ) : ℝ) / ((n : ℝ) + 1)) / 2 := by
    have hnat := Nat.div_add_mod (n + 1) 2
    have hreal : 2 * (((n + 1) / 2 : ℕ) : ℝ) + (((n + 1) % 2 : ℕ) : ℝ) =
        (n : ℝ) + 1 := by exact_mod_cast hnat
    have hN : (n : ℝ) + 1 ≠ 0 := by positivity
    field_simp [hN]
    nlinarith [hreal]
  have hpair : Tendsto (fun n : ℕ => (((n + 1) / 2 : ℕ) : ℝ) / ((n : ℝ) + 1))
      atTop (𝓝 (1 / 2)) := by
    have h : Tendsto
        (fun n : ℕ => (1 - (((n + 1) % 2 : ℕ) : ℝ) / ((n : ℝ) + 1)) / 2)
        atTop (𝓝 (1 / 2)) := by
      simpa only [sub_zero] using
        ((tendsto_const_nhds (x := (1 : ℝ))).sub hrem).div_const 2
    exact h.congr (fun n => (hdecomp n).symm)
  have h := ((hpair.mul hsplit).const_mul 16).add (hrem.const_mul 4)
  change Tendsto (fun n : ℕ =>
    (16 * (((n + 1) / 2 : ℕ) : ℝ) * pairSplitProbability (max 4 (n + 1)) +
      4 * (((n + 1) % 2 : ℕ) : ℝ)) / ((n : ℝ) + 1)) atTop (𝓝 8)
  convert h using 1
  · funext n
    ring
  · norm_num

end

end AronowAudit.P013.Wave1.PrintedWald
