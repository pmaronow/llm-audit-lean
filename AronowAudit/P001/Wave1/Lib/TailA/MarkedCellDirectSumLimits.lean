import AronowAudit.P001.Wave1.Lib.TailA.MarkedCellDirectFullIntegrals

/-! Exact iid sampling lifts for the full one- and two-query limits. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology
namespace AronowAudit.P001.TailA
local instance instDecidableMarkedCellDirectSumLimits (p : Prop) : Decidable p :=
  Classical.propDecidable p
set_option maxHeartbeats 1000000
set_option maxRecDepth 3000

theorem marked_original_test_exp_bound (c : ℕ) :
    0 ≤ (if c = 0 then (1 : ℝ) else 0) ∧
      (if c = 0 then (1 : ℝ) else 0) ≤ Real.exp (-(c : ℝ)/4) := by
  by_cases hc : c = 0
  · simp [hc]
  · simp only [if_neg hc]
    exact ⟨le_rfl,(Real.exp_pos _).le⟩

theorem marked_retained_test_exp_bound (m d c k : ℕ) (hm : 0 < m) (hd : d ≤ 3)
    (hk : k ≤ d) (hc : c ≤ m) :
    0 ≤ markedRetainedDrawPower (m+d) c k ∧
      markedRetainedDrawPower (m+d) c k ≤ Real.exp (-(c : ℝ)/4) :=
  ⟨(marked_retained_draw_power_bounds _ _ _).1,
    (marked_retained_power_le_draw _ _ _).trans (marked_draw_power_exp_bound m d c k hm hd hk hc)⟩

theorem marked_union_test_pair_bound (m : ℕ) (f : ℕ → ℝ)
    (hf : ∀ c, c ≤ m → 0 ≤ f c ∧ f c ≤ Real.exp (-(c : ℝ)/4)) :
    MarkedPairKernelBound m (fun _ _ c => f c) := by
  intro a b c ha hb hc hac hbc
  refine ⟨(hf c hc).1,?_,?_⟩
  · apply (hf c hc).2.trans
    apply Real.exp_le_exp.mpr
    have hh : (a : ℝ) ≤ c := by exact_mod_cast hac
    linarith
  · apply (hf c hc).2.trans
    apply Real.exp_le_exp.mpr
    have hh : (b : ℝ) ≤ c := by exact_mod_cast hbc
    linarith

theorem marked_product_test_pair_bound (m : ℕ) (f g : ℕ → ℝ)
    (hf : ∀ c, c ≤ m → 0 ≤ f c ∧ f c ≤ 1 ∧ f c ≤ Real.exp (-(c : ℝ)/4))
    (hg : ∀ c, c ≤ m → 0 ≤ g c ∧ g c ≤ 1 ∧ g c ≤ Real.exp (-(c : ℝ)/4)) :
    MarkedPairKernelBound m (fun a b _ => f a*g b) := by
  intro a b c ha hb hc hac hbc
  obtain ⟨hf0,hf1,hfe⟩ := hf a ha
  obtain ⟨hg0,hg1,hge⟩ := hg b hb
  refine ⟨mul_nonneg hf0 hg0,?_,?_⟩
  · exact (mul_le_of_le_one_right hf0 hg1).trans hfe
  · exact (mul_le_of_le_one_left hg0 hf1).trans hge

/-- Full one-recipient kernel limits are transferred to the actual sample
sum with the exact finite sampling factor. -/
theorem marked_recipient_full_sum_limit (p : ℝ)
    (hp : p ∈ Set.Ioo (1/4 : ℝ) (3/4)) (K : ℕ → ℕ → ℝ)
    (hKb : ∀ n c, |K n c| ≤ 1)
    (hKe : ∀ m, 0 < m → ∀ c, c ≤ m →
      0 ≤ K (m+1) c ∧ K (m+1) c ≤ Real.exp (-(c : ℝ)/4))
    (L : ℝ → ℝ)
    (hlim : ∀ t, Tendsto (fun m => markedCountKernel m p (K (m+1)) t) atTop (𝓝 (L t))) :
    Tendsto (fun n => mean (MatchProduct n) (fun z => ∑ i, markedRecipientCountTest p (K n) z i))
      atTop (𝓝 (∫ t : ℝ, 2*(1-p)*L t)) := by
  have hi := marked_full_single_integral_limit p hp (fun m => K (m+1)) hKe L hlim
  have hh := marked_recipient_sampling_factor_limits.1.mul hi
  simp only [one_mul] at hh
  apply (tendsto_add_atTop_iff_nat 1).mp
  apply hh.congr'
  filter_upwards [eventually_ge_atTop 1] with m hm
  exact (marked_recipient_scaled_sum_integral m (by omega) p (K (m+1)) (by norm_num)
    (hKb (m+1))).symm

/-- Full union/product limits transfer to the ordered distinct-recipient
sum, with the actual remaining sample and both Jacobian factors retained. -/
theorem marked_recipient_pair_full_sum_limit (p : ℝ)
    (hp : p ∈ Set.Ioo (1/4 : ℝ) (3/4)) (K : ℕ → ℕ → ℕ → ℕ → ℝ)
    (hKb : ∀ n a b c, |K n a b c| ≤ 1)
    (hKe : ∀ m, 0 < m → MarkedPairKernelBound m (K (m+2)))
    (L : ℝ × ℝ → ℝ)
    (hlim : ∀ q, Tendsto (fun m => markedPairKernel m p (K (m+2)) q) atTop (𝓝 (L q))) :
    Tendsto (fun n => mean (MatchProduct n) (fun z => ∑ i, ∑ j,
      if i = j then 0 else markedRecipientPairCountTest p (K n) z i j))
      atTop (𝓝 (∫ q : ℝ × ℝ, (2*(1-p))^2*L q)) := by
  have hi := marked_full_pair_integral_limit p hp (fun m => K (m+2)) hKe L hlim
  have hh := marked_recipient_sampling_factor_limits.2.mul hi
  simp only [one_mul] at hh
  apply (tendsto_add_atTop_iff_nat 2).mp
  apply hh.congr'
  filter_upwards [eventually_ge_atTop 1] with m hm
  rw [marked_pair_density_integral_iterated m (by omega) p ⟨hp.1.le,hp.2.le⟩ (K (m+2)) (hKe m (by omega))]
  exact (marked_recipient_pair_scaled_sum_integral m (by omega) p (K (m+2)) (by norm_num)
    (hKb (m+2))).symm

end AronowAudit.P001.TailA
