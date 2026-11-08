import SAP.P061a.Defs
import SAP.P061a.Bridge
import AronowAudit.P061.P061_Foundations
import AronowAudit.P061.P061_PaperDomains
import AronowAudit.P061.P061_Refutations
import SAP.P061a.WH.W1.Proofs.T4
import SAP.P061a.WH.W1.Proofs.T7
import SAP.P061a.WH.W2.Proofs.T5

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter Asymptotics
open scoped Topology

theorem SAP.P061a.T1 : SAP.P061a.T1Statement := SAP.P061a.Bridge.version_correspondence

theorem SAP.P061a.T2 : SAP.P061a.T2Statement := SAP.P061a.Bridge.edge_correspondence

theorem SAP.P061a.T3 : SAP.P061a.T3Statement := SAP.P061a.Bridge.comparison_correspondence

theorem SAP.P061a.T4 : SAP.P061a.T4WholeStatement := SAP.P061a.WH.W1.T4_whole

theorem SAP.P061a.T5 : SAP.P061a.T5WholeStatement_W2 := SAP.P061a.WH.W2.T5_whole

theorem SAP.P061a.T6 : SAP.P061a.T6Statement := SAP.P061a.Bridge.attribution_correspondence

theorem SAP.P061a.T7 : SAP.P061a.T7WholeStatement := SAP.P061a.WH.W1.T7_whole

theorem SAP.P061a.T8 : SAP.P061a.T8Statement := SAP.P061a.Bridge.first_moment_correspondence

theorem SAP.P061a.T9 : SAP.P061a.T9Statement := SAP.P061a.Bridge.sampling_correspondence

theorem SAP.P061a.T10 (dmax davg : ℕ → ℝ)
    (hmax : ∀ N, 0 ≤ dmax N) (havg : ∀ N, 0 ≤ davg N) :
    (IsLittleO atTop dmax (fun N => Real.rpow (N : ℝ) (1/4 : ℝ)) ↔
      Tendsto (fun N => dmax N / Real.rpow (N : ℝ) (1/4 : ℝ)) atTop (𝓝 0)) ∧
    (IsBigO atTop davg (fun _ => (1 : ℝ)) ↔ ∃ C : ℝ, ∀ N, davg N ≤ C) ∧
    (IsBigO atTop dmax (fun N => Real.rpow (N : ℝ) (1/2 : ℝ)) ↔
      ∃ C : ℝ, ∀ N : ℕ, 0 < N → dmax N / Real.rpow (N : ℝ) (1/2 : ℝ) ≤ C) := by
  have row := AronowAudit.P061.corrected_degree_rates dmax davg
  have nonzero (a : ℝ) : ∀ᶠ N : ℕ in atTop, Real.rpow (N : ℝ) a ≠ 0 := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
    exact ne_of_gt (Real.rpow_pos_of_pos (by exact_mod_cast hN) a)
  have quarter : IsLittleO atTop dmax (fun N => Real.rpow (N : ℝ) (1/4 : ℝ)) ↔
      AronowAudit.P061.MaxDegreeQuarterRate dmax := by
    exact isLittleO_iff_tendsto' ((nonzero (1/4)).mono fun _ hn hz => (hn hz).elim)
  have average : IsBigO atTop davg (fun _ => (1 : ℝ)) ↔
      AronowAudit.P061.AverageDegreeBounded davg := by
    simpa only [AronowAudit.P061.AverageDegreeBounded, Real.norm_eq_abs, abs_of_nonneg (havg _)] using
      (isBigO_one_nat_atTop_iff (f := davg))
  have half : IsBigO atTop dmax (fun N => Real.rpow (N : ℝ) (1/2 : ℝ)) ↔
      AronowAudit.P061.MaxDegreeHalfRate dmax := by
    rw [isBigO_iff_div_isBoundedUnder ((nonzero (1/2)).mono fun _ hn hz => (hn hz).elim),
      ← (isBigO_one_iff (F := ℝ)), isBigO_one_nat_atTop_iff]
    have habs (N : ℕ) : |dmax N / Real.rpow (N : ℝ) (1/2 : ℝ)| =
        dmax N / Real.rpow (N : ℝ) (1/2 : ℝ) :=
      abs_of_nonneg (div_nonneg (hmax N) (Real.rpow_nonneg (Nat.cast_nonneg N) _))
    simp only [AronowAudit.P061.MaxDegreeHalfRate, Real.norm_eq_abs, habs]
  refine ⟨quarter.trans row.1, average.trans row.2.1, (half.trans row.2.2).trans ?_⟩
  constructor
  · rintro ⟨C,hC⟩
    exact ⟨C,fun N _ => hC N⟩
  · rintro ⟨C,hC⟩
    refine ⟨max C 0,fun N => ?_⟩
    cases N with
    | zero => simp
    | succ n => exact (hC _ (Nat.succ_pos _)).trans (le_max_left _ _)

theorem SAP.P061a.T11 : SAP.P061a.T11Statement := SAP.P061a.Bridge.finite_targets_correspondence
