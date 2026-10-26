import AronowAudit.P031.Wave1.FootnoteThreeProbabilityBlueprint

namespace AronowAudit.P031.Wave1.FootnoteThreeProbability
noncomputable section
open scoped BigOperators Matrix Topology
open Filter

/-- Normalize both weights by the population size before taking limits. -/
theorem n6_proof : N6 := by
  intro P hN p hp hp1 hAlloc
  have hp0 : p ≠ 0 := hp.ne'
  have hpc : 1 - p ≠ 0 := by linarith
  have hn : Tendsto (fun n => ((P n).N : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hN
  have hInv : Tendsto (fun n => 1 / ((P n).N : ℝ)) atTop (nhds (0 : ℝ)) :=
    hn.const_div_atTop 1
  have hComp : Tendsto (fun n => 1 - ((P n).M : ℝ) / (P n).N)
      atTop (nhds (1 - p)) := tendsto_const_nhds.sub hAlloc
  have hOne : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds (1 : ℝ)) := tendsto_const_nhds
  have hSum := (hOne.div hAlloc hp0).add (hOne.div hComp hpc)
  have hRatio := population_ratio_tends_one P hN 2 (by norm_num)
  have hT := (hRatio.mul (hAlloc.sub hInv)).mul hSum
  have hC := (hRatio.mul (hComp.sub hInv)).mul hSum
  have hTLim : 1 * (p - 0) * (1 / p + 1 / (1 - p)) = 1 / (1 - p) := by
    field_simp [hp0, hpc] <;> ring
  have hCLim : 1 * ((1 - p) - 0) * (1 / p + 1 / (1 - p)) = 1 / p := by
    field_simp [hp0, hpc] <;> ring
  rw [hTLim] at hT
  rw [hCLim] at hC
  simp only [Pi.div_apply] at hT hC
  have hRows : ∀ n,
      (((P n).N : ℝ) / (((P n).N : ℝ) - 2) *
        (((P n).M : ℝ) / (P n).N - 1 / ((P n).N : ℝ)) *
        (1 / (((P n).M : ℝ) / (P n).N) + 1 / (1 - ((P n).M : ℝ) / (P n).N)) =
          olsWeightT (P n)) ∧
      (((P n).N : ℝ) / (((P n).N : ℝ) - 2) *
        ((1 - ((P n).M : ℝ) / (P n).N) - 1 / ((P n).N : ℝ)) *
        (1 / (((P n).M : ℝ) / (P n).N) + 1 / (1 - ((P n).M : ℝ) / (P n).N)) =
          olsWeightC (P n)) := by
    intro n
    have hs := population_sizes (P n)
    have hmR : (2 : ℝ) ≤ (P n).M := by exact_mod_cast hs.1
    have hkR : (2 : ℝ) ≤ ((P n).N : ℝ) - (P n).M := by
      have hk : (2 : ℝ) ≤ (((P n).N - (P n).M : ℕ) : ℝ) := by exact_mod_cast hs.2.1
      simpa only [Nat.cast_sub hs.2.2.1] using hk
    have hnR : (4 : ℝ) ≤ (P n).N := by exact_mod_cast hs.2.2.2
    have hm : ((P n).M : ℝ) ≠ 0 := by linarith
    have hk : ((P n).N : ℝ) - (P n).M ≠ 0 := by linarith
    have hn0 : ((P n).N : ℝ) ≠ 0 := by linarith
    have hn2 : ((P n).N : ℝ) - 2 ≠ 0 := by linarith
    have hComplement : 1 - ((P n).M : ℝ) / (P n).N =
        (((P n).N : ℝ) - (P n).M) / (P n).N := by
      field_simp [hn0] <;> ring
    constructor <;> simp only [olsWeightT, olsWeightC, hComplement] <;>
      field_simp [hm, hk, hn0, hn2] <;> ring
  exact ⟨hT.congr (fun n => (hRows n).1), hC.congr (fun n => (hRows n).2)⟩

end
end AronowAudit.P031.Wave1.FootnoteThreeProbability
