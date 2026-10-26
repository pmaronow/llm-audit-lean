import AronowAudit.P004.Wave1.ObservationalCoverageBlueprint
import AronowAudit.P004.Wave1.ObservationalCoverage.O9
import AronowAudit.P004.Wave1.DesignLimits.DL2
import AronowAudit.P004.Wave1.DesignLimits.DL4
import Mathlib.Analysis.SpecificLimits.Basic

/-! Laws of large numbers with finite-design probabilities.
The deterministic count errors are bounded for every incomplete last block. -/

namespace AronowAudit.P004.Wave1.ObservationalCoverage

set_option autoImplicit false
noncomputable section
open AronowAudit.P004 MeasureTheory Filter
open AronowAudit.P004.Wave1.DesignLimits
open scoped BigOperators Classical

theorem oc_inProb_congr {p : ∀ N, Fin N → ℝ} {U V : ∀ N, Assignment N → ℝ}
    (h : ∀ᶠ N in atTop, ∀ z, U N z = V N z) (hU : InProb p U) : InProb p V := by
  intro ε hε
  refine (hU ε hε).congr' ?_
  filter_upwards [h] with N hN
  exact prob_congr _ _ _ (fun z => by rw [hN z])

theorem oc_normalLimit_congr {p : ∀ N, Fin N → ℝ} {U V : ∀ N, Assignment N → ℝ}
    (h : ∀ᶠ N in atTop, ∀ z, U N z = V N z) (hU : NormalLimit p U) : NormalLimit p V := by
  intro x
  refine (hU x).congr' ?_
  filter_upwards [h] with N hN
  exact prob_congr _ _ _ (fun z => by rw [hN z])

theorem oc_expect_nonneg (N : ℕ) (U : Assignment N → ℝ) (hU : ∀ z, 0 ≤ U z) :
    0 ≤ expect (propensities (activeO N) activeTheta) U := by
  simpa only [expect_const] using
    expect_mono _ (oc_admissible N) (fun _ => 0) U hU

theorem oc_nH_ratio_tendsto :
    Tendsto (fun N => nH N / N) atTop (nhds (1 / 4 : ℝ)) := by
  have he : Tendsto (fun N => nH N / N - 1 / 4) atTop (nhds (0 : ℝ)) := by
    refine squeeze_zero_norm' ?_ (tendsto_const_div_atTop_nhds_zero_nat (2 : ℝ))
    filter_upwards [eventually_gt_atTop 0] with N hN
    have hNr : (0 : ℝ) < N := by exact_mod_cast hN
    have hid : nH N / N - (1 / 4 : ℝ) = (nH N - (N : ℝ) / 4) / N := by
      field_simp [ne_of_gt hNr] <;> ring
    rw [Real.norm_eq_abs, hid, abs_div, abs_of_pos hNr]
    exact div_le_div_of_nonneg_right (oc_nH_count_error N) hNr.le
  simpa only [sub_add_cancel, zero_add] using
    he.add (tendsto_const_nhds (x := (1 / 4 : ℝ)))

theorem oc_nL_ratio_tendsto :
    Tendsto (fun N => nL N / N) atTop (nhds (3 / 4 : ℝ)) := by
  have h : Tendsto (fun N => 1 - nH N / N) atTop (nhds (3 / 4 : ℝ)) := by
    convert (tendsto_const_nhds (x := (1 : ℝ))).sub oc_nH_ratio_tendsto using 1 <;> norm_num
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with N hN
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hp := oc_group_partition N
  field_simp [ne_of_gt hNr]
  linarith

theorem oc_nH_inv_tendsto :
    Tendsto (fun N => 1 / nH N) atTop (nhds (0 : ℝ)) := by
  have h : Tendsto (fun N : ℕ => (1 / (N : ℝ)) / (nH N / N)) atTop (nhds (0 : ℝ)) := by
    have h0 := (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).div
      oc_nH_ratio_tendsto (by norm_num : (1 / 4 : ℝ) ≠ 0)
    rw [zero_div] at h0
    exact h0
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with N hN
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  field_simp [ne_of_gt hNr, ne_of_gt (oc_nH_pos N hN)]

/-- The elementary moment-to-zero estimate used for all three unnormalized sums. -/
theorem oc_div_second_tendsto (U : ∀ N, Assignment N → ℝ)
    (hU : ∀ N, 0 < N →
      expect (propensities (activeO N) activeTheta) (fun z => (U N z)^2) ≤ N) :
    Tendsto (fun N => expect (propensities (activeO N) activeTheta)
      (fun z => (U N z / N)^2)) atTop (nhds (0 : ℝ)) := by
  refine squeeze_zero'
    (Filter.Eventually.of_forall fun N => oc_expect_nonneg N _ (fun z => sq_nonneg _))
    ?_ (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ))
  filter_upwards [eventually_gt_atTop 0] with N hN
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hm := hU N hN
  simp only [div_pow, expect_div]
  apply (div_le_iff₀ (sq_pos_of_pos hNr)).mpr
  have hid : 1 / (N : ℝ) * (N : ℝ)^2 = N := by
    field_simp [ne_of_gt hNr] <;> ring
  rw [hid]
  exact hm

theorem oc_phat_second_tendsto :
    Tendsto (fun N => expect (propensities (activeO N) activeTheta)
      (fun z => (pHatH N z - 1 / 2)^2)) atTop (nhds (0 : ℝ)) := by
  refine squeeze_zero'
    (Filter.Eventually.of_forall fun N => oc_expect_nonneg N _ (fun z => sq_nonneg _))
    ?_ oc_nH_inv_tendsto
  filter_upwards [eventually_gt_atTop 0] with N hN
  calc
    expect (propensities (activeO N) activeTheta) (fun z => (pHatH N z - 1 / 2)^2) ≤
        expect (propensities (activeO N) activeTheta) (fun z => (1 - 2 * pHatH N z)^2) := by
      apply expect_mono _ (oc_admissible N)
      intro z
      nlinarith [sq_nonneg (pHatH N z - 1 / 2)]
    _ ≤ 1 / nH N := (o9_proof N hN).2

theorem o10_proof : O10 := by
  let p : ∀ N, Fin N → ℝ := fun N => propensities (activeO N) activeTheta
  have hp : AdmissibleSeq p := oc_admissible
  obtain ⟨hadd, hscale, hdet⟩ := dl4_proof p hp
  have hKmom : Tendsto (fun N => expect (p N)
      (fun z => ((KAct N z - nH N / 2) / N)^2)) atTop (nhds (0 : ℝ)) := by
    apply oc_div_second_tendsto (fun N z => KAct N z - nH N / 2)
    intro N hN
    rw [oc_K_centered_second]
    have hn := oc_nH_le N
    have hn0 := oc_nH_nonneg N
    linarith
  have hJmom : Tendsto (fun N => expect (p N)
      (fun z => ((JAct N z - nL N / 10) / N)^2)) atTop (nhds (0 : ℝ)) := by
    apply oc_div_second_tendsto (fun N z => JAct N z - nL N / 10)
    intro N hN
    rw [oc_J_centered_second]
    have hn := oc_group_partition N
    have hh0 := oc_nH_nonneg N
    have hl0 := oc_nL_nonneg N
    linarith
  have hSmom : Tendsto (fun N => expect (p N)
      (fun z => (SAct N z / N)^2)) atTop (nhds (0 : ℝ)) := by
    exact oc_div_second_tendsto SAct (fun N hN => (o9_proof N hN).1)
  have hK0 : InProb p (fun N z => (KAct N z - nH N / 2) / N) :=
    (dl2_proof p hp _).2 hKmom
  have hJ0 : InProb p (fun N z => (JAct N z - nL N / 10) / N) :=
    (dl2_proof p hp _).2 hJmom
  have hS0 : InProb p (fun N z => SAct N z / N) :=
    (dl2_proof p hp _).2 hSmom
  have hdK : Tendsto (fun N => nH N / N / 2 - 1 / 8) atTop (nhds (0 : ℝ)) := by
    convert (oc_nH_ratio_tendsto.div_const (2 : ℝ)).sub
      (tendsto_const_nhds (x := (1 / 8 : ℝ))) using 1 <;> norm_num
  have hdJ : Tendsto (fun N => nL N / N / 10 - 3 / 40) atTop (nhds (0 : ℝ)) := by
    convert (oc_nL_ratio_tendsto.div_const (10 : ℝ)).sub
      (tendsto_const_nhds (x := (3 / 40 : ℝ))) using 1 <;> norm_num
  have hK : InProb p (fun N z => KAct N z / N - 1 / 8) := by
    apply oc_inProb_congr (U := fun N z =>
      (KAct N z - nH N / 2) / N + (nH N / N / 2 - 1 / 8))
    · exact Filter.Eventually.of_forall fun N z => by ring
    · exact hadd _ _ hK0 (hdet _ hdK)
  have hJ : InProb p (fun N z => JAct N z / N - 3 / 40) := by
    apply oc_inProb_congr (U := fun N z =>
      (JAct N z - nL N / 10) / N + (nL N / N / 10 - 3 / 40))
    · exact Filter.Eventually.of_forall fun N z => by ring
    · exact hadd _ _ hJ0 (hdet _ hdJ)
  have hph : InProb p (fun N z => pHatH N z - 1 / 2) :=
    (dl2_proof p hp _).2 oc_phat_second_tendsto
  exact ⟨hK, hJ, by simpa only [sub_zero] using hS0, hph, oc_nH_ratio_tendsto⟩

end
end AronowAudit.P004.Wave1.ObservationalCoverage
