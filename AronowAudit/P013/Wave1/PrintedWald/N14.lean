import AronowAudit.P013.Wave1.PrintedWaldBlueprint
import Mathlib.Analysis.SpecificLimits.Basic

set_option autoImplicit false

namespace AronowAudit.P013.Wave1.PrintedWald

open AronowAudit.P013 AronowAudit.P013.Wave1.CorrectedCoverage Filter Finset
open scoped BigOperators Topology NNReal ENNReal

noncomputable section

/-- The exact variance ratio on the all-split event is nonnegative and tends to 3/4. -/
theorem n14_proof : N14 := by
  constructor
  · intro k
    obtain ⟨he0, he1⟩ := pairEpsilon_even_bounds k
    have ht : 0 < pairSplitProbability (2 * k + 4) := by
      unfold pairSplitProbability
      linarith
    have htlo : 1 / 4 ≤ pairSplitProbability (2 * k + 4) := by
      unfold pairSplitProbability
      linarith
    have hfrac : 2 / pairSplitProbability (2 * k + 4) ≤ 8 := by
      apply (div_le_iff₀ ht).mpr
      linarith
    unfold evenRatio
    exact div_nonneg (by linarith) (mul_nonneg (by norm_num) ht.le)
  · have hφ : Tendsto (fun k : ℕ => 2 * k + 4) atTop atTop := by
      apply tendsto_atTop_mono (fun k => (by omega : k ≤ 2 * k + 4)) tendsto_id
    have hinv : Tendsto (fun k : ℕ => 1 / ((2 * k + 4 : ℕ) : ℝ)) atTop (𝓝 0) :=
      (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ)).comp hφ
    have heps : Tendsto (fun k : ℕ => pairEpsilon (2 * k + 4)) atTop (𝓝 0) := by
      simpa [pairEpsilon, div_pow] using hinv.pow 2
    have ht : Tendsto (fun k : ℕ => pairSplitProbability (2 * k + 4)) atTop (𝓝 1) := by
      simpa [pairSplitProbability] using
        (tendsto_const_nhds (x := (1 : ℝ))).sub (heps.const_mul 2)
    have hnum := (tendsto_const_nhds (x := (8 : ℝ))).sub
      ((tendsto_const_nhds (x := (2 : ℝ))).div ht (by norm_num))
    have hden := ht.const_mul 8
    have hlim : Tendsto evenRatio atTop (𝓝 ((8 - 2 / (1 : ℝ)) / (8 * 1))) :=
      hnum.div hden (by norm_num)
    norm_num at hlim
    exact hlim

end

end AronowAudit.P013.Wave1.PrintedWald
