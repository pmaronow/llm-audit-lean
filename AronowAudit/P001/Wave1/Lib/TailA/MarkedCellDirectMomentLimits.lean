import AronowAudit.P001.Wave1.Lib.TailA.MarkedCellDirectSumLimits
import AronowAudit.P001.Wave1.Lib.TailA.MarkedCellDirectIntegralValues

/-! Full recipient-sum limits under the actual iid and finite bootstrap laws. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology
namespace AronowAudit.P001.TailA
local instance instDecidableMarkedCellDirectMomentLimits (p : Prop) : Decidable p :=
  Classical.propDecidable p
set_option maxHeartbeats 1000000
set_option maxRecDepth 3000

theorem marked_matchS_bounds : 0 < matchS ∧ matchS < 1 := by
  unfold matchS
  have h1 := Real.exp_lt_one_iff.mpr (by norm_num : (-1 : ℝ) < 0)
  have h0 := Real.exp_pos (-1 : ℝ)
  constructor <;> linarith

theorem marked_directional_overlap_self (t : ℝ) : markedDirectionalOverlap t t = |t| := by
  rcases le_total 0 t with ht | ht
  · simp [markedDirectionalOverlap,max_eq_left ht,max_eq_right (neg_nonpos.mpr ht),abs_of_nonneg ht]
  · simp [markedDirectionalOverlap,max_eq_right ht,max_eq_left (neg_nonneg.mpr ht),abs_of_nonpos ht]

/-- The original single-recipient contribution has its full limiting mean. -/
theorem marked_original_recipient_sum_limit (p : ℝ)
    (hp : p ∈ Set.Ioo (1/4 : ℝ) (3/4)) :
    Tendsto (fun n => mean (MatchProduct n) (fun z => ∑ i,
      markedRecipientCountTest p (fun c => if c = 0 then 1 else 0) z i)) atTop
      (𝓝 ((1-p)/p)) := by
  have hi := marked_recipient_full_sum_limit p hp (fun _ c => if c = 0 then 1 else 0)
    (by intro n c; split_ifs <;> norm_num)
    (fun _ _ c _ => marked_original_test_exp_bound c)
    (fun t => Real.exp (-4*p*|t|))
    (fun t => marked_direct_original_recipient_kernel_limit p t hp id tendsto_id)
  have hp0 : 0 < p := by linarith [hp.1]
  have he (t : ℝ) : -4*p*|t| = -(4*p)*|t| := by ring
  simp_rw [he] at hi
  rw [integral_const_mul,marked_exp_abs_integral (mul_pos (by norm_num) hp0)] at hi
  convert hi using 1
  congr 1
  field_simp
  <;> ring

/-- Fixing one recipient leaves bootstrap size `m+2`, including the pin. -/
theorem marked_draw_recipient_sum_limit (p : ℝ)
    (hp : p ∈ Set.Ioo (1/4 : ℝ) (3/4)) (k : ℕ) (hk : k ≤ 2) :
    Tendsto (fun n => mean (MatchProduct n) (fun z => ∑ i,
      markedRecipientCountTest p (fun c => markedDrawPower (n+1) c k) z i)) atTop
      (𝓝 (((1-p)/p)/matchS)) := by
  have hi := marked_recipient_full_sum_limit p hp (fun n c => markedDrawPower (n+1) c k)
    (fun n c => by rw [abs_of_nonneg (marked_draw_power_bounds _ _ _).1]; exact (marked_draw_power_bounds _ _ _).2)
    (fun m hm c hc => ⟨(marked_draw_power_bounds _ _ _).1,
      marked_draw_power_exp_bound m 2 c k hm (by norm_num) hk hc⟩)
    (fun t => Real.exp (-4*p*matchS*|t|)) (fun t => by
      simpa only [markedCountKernel,Nat.add_assoc,id_eq] using
        (marked_direct_recipient_kernel_limits p t hp id (fun m => m+2) tendsto_id (tendsto_add_atTop_nat 2) k).1)
  have hp0 : 0 < p := by linarith [hp.1]
  have he (t : ℝ) : -4*p*matchS*|t| = -(4*p*matchS)*|t| := by ring
  simp_rw [he] at hi
  rw [integral_const_mul,marked_exp_abs_integral (mul_pos (mul_pos (by norm_num) hp0) marked_matchS_bounds.1)] at hi
  convert hi using 1
  congr 1
  field_simp [hp0.ne',marked_matchS_bounds.1.ne']
  <;> ring

theorem marked_retained_recipient_sum_limit (p : ℝ)
    (hp : p ∈ Set.Ioo (1/4 : ℝ) (3/4)) (k : ℕ) (hk : k ≤ 2) :
    Tendsto (fun n => mean (MatchProduct n) (fun z => ∑ i,
      markedRecipientCountTest p (fun c => markedRetainedDrawPower (n+1) c k) z i)) atTop
      (𝓝 ((1-p)/p)) := by
  have hi := marked_recipient_full_sum_limit p hp (fun n c => markedRetainedDrawPower (n+1) c k)
    (fun n c => by rw [abs_of_nonneg (marked_retained_draw_power_bounds _ _ _).1]; exact (marked_retained_draw_power_bounds _ _ _).2)
    (fun m hm c hc => marked_retained_test_exp_bound m 2 c k hm (by norm_num) hk hc)
    (fun t => matchS*Real.exp (-4*p*matchS*|t|)) (fun t => by
      simpa only [markedCountKernel,Nat.add_assoc,id_eq] using
        (marked_direct_recipient_kernel_limits p t hp id (fun m => m+2) tendsto_id (tendsto_add_atTop_nat 2) k).2)
  have hp0 : 0 < p := by linarith [hp.1]
  have he (t : ℝ) : -4*p*matchS*|t| = -(4*p*matchS)*|t| := by ring
  simp_rw [he] at hi
  rw [integral_const_mul,integral_const_mul,
    marked_exp_abs_integral (mul_pos (mul_pos (by norm_num) hp0) marked_matchS_bounds.1)] at hi
  convert hi using 1
  congr 1
  field_simp [hp0.ne',marked_matchS_bounds.1.ne']
  <;> ring

/-- A recipient appearing in both replica sums carries the square of its
conditional retention kernel, rather than an independent-recipient term. -/
theorem marked_retained_square_recipient_sum_limit (p : ℝ)
    (hp : p ∈ Set.Ioo (1/4 : ℝ) (3/4)) :
    Tendsto (fun n => mean (MatchProduct n) (fun z => ∑ i,
      markedRecipientCountTest p (fun c => (markedRetainedDrawPower (n+1) c 1)^2) z i)) atTop
      (𝓝 (matchS*((1-p)/p)/(2-matchS))) := by
  have hb (n c : ℕ) : |(markedRetainedDrawPower (n+1) c 1)^2| ≤ 1 := by
    rw [abs_of_nonneg (sq_nonneg _)]
    obtain ⟨h0,h1⟩ := marked_retained_draw_power_bounds (n+1) c 1
    nlinarith
  have he (m : ℕ) (hm : 0 < m) (c : ℕ) (hc : c ≤ m) :
      0 ≤ (markedRetainedDrawPower (m+1+1) c 1)^2 ∧
        (markedRetainedDrawPower (m+1+1) c 1)^2 ≤ Real.exp (-(c : ℝ)/4) := by
    have hh := marked_retained_test_exp_bound m 2 c 1 hm (by norm_num) (by norm_num) hc
    have h1 := (marked_retained_draw_power_bounds (m+2) c 1).2
    exact ⟨sq_nonneg _,(by nlinarith)⟩
  have hlim (t : ℝ) : Tendsto (fun m => markedCountKernel m p
      (fun c => (markedRetainedDrawPower (m+1+1) c 1)^2) t) atTop
        (𝓝 (matchS^2*Real.exp (-(4*p*matchS*(2-matchS))*|t|))) := by
    have hh := marked_direct_recipient_pair_kernel_limit p t t hp id (fun m => m+2)
      tendsto_id (tendsto_add_atTop_nat 2) 1 1
    have heq : -(4*p)*(matchS*(|t|+|t|)-matchS^2*|t|) = -(4*p*matchS*(2-matchS))*|t| := by ring
    simp only [marked_directional_overlap_self,id_eq] at hh
    rw [heq] at hh
    simpa only [markedCountKernel,Nat.add_assoc,pow_two] using hh
  have hi := marked_recipient_full_sum_limit p hp
    (fun n c => (markedRetainedDrawPower (n+1) c 1)^2) hb he _ hlim
  have hp0 : 0 < p := by linarith [hp.1]
  have hs2 : 0 < 2-matchS := by linarith [marked_matchS_bounds.2]
  rw [integral_const_mul,integral_const_mul,marked_exp_abs_integral
    (mul_pos (mul_pos (mul_pos (by norm_num) hp0) marked_matchS_bounds.1) hs2)] at hi
  convert hi using 1
  congr 1
  field_simp [hp0.ne',marked_matchS_bounds.1.ne',hs2.ne']
  <;> ring

/-- The original ordered distinct-recipient contribution over the whole line. -/
theorem marked_original_recipient_pair_sum_limit (p : ℝ)
    (hp : p ∈ Set.Ioo (1/4 : ℝ) (3/4)) :
    Tendsto (fun n => mean (MatchProduct n) (fun z => ∑ i, ∑ j,
      if i = j then 0 else markedRecipientPairCountTest p (fun _ _ c => if c = 0 then 1 else 0) z i j))
      atTop (𝓝 (3*((1-p)/p)^2/2)) := by
  have hi := marked_recipient_pair_full_sum_limit p hp (fun _ _ _ c => if c = 0 then 1 else 0)
    (by intro n a b c; split_ifs <;> norm_num)
    (fun m hm => marked_union_test_pair_bound m _ (fun c _ => marked_original_test_exp_bound c))
    (fun q => Real.exp (-4*p*markedDirectionalSpan q.1 q.2)) (fun q =>
      marked_direct_original_union_kernel_limit p q.1 q.2 hp id tendsto_id)
  have hp0 : 0 < p := by linarith [hp.1]
  have he (q : ℝ × ℝ) : -4*p*markedDirectionalSpan q.1 q.2 = -(4*p)*markedDirectionalSpan q.1 q.2 := by ring
  simp_rw [he] at hi
  rw [integral_const_mul,marked_union_full_integral (mul_pos (by norm_num) hp0)] at hi
  convert hi using 1
  congr 1
  field_simp
  <;> ring

/-- The one-replica distinct-recipient term includes exactly one separate
central-retention factor. -/
theorem marked_retained_union_recipient_pair_sum_limit (p : ℝ)
    (hp : p ∈ Set.Ioo (1/4 : ℝ) (3/4)) (k : ℕ) (hk : k ≤ 2) :
    Tendsto (fun n => mean (MatchProduct n) (fun z => ∑ i, ∑ j,
      if i = j then 0 else markedRecipientPairCountTest p
        (fun _ _ c => markedRetainedDrawPower (n+1) c k) z i j))
      atTop (𝓝 (3*((1-p)/p)^2/(2*matchS))) := by
  have hi := marked_recipient_pair_full_sum_limit p hp (fun n _ _ c => markedRetainedDrawPower (n+1) c k)
    (fun n a b c => by rw [abs_of_nonneg (marked_retained_draw_power_bounds _ _ _).1]; exact (marked_retained_draw_power_bounds _ _ _).2)
    (fun m hm => marked_union_test_pair_bound m _
      (fun c hc => marked_retained_test_exp_bound m 3 c k hm (by norm_num) (by omega) hc))
    (fun q => matchS*Real.exp (-4*p*matchS*markedDirectionalSpan q.1 q.2)) (fun q => by
      simpa only [markedPairKernel,Nat.add_assoc,id_eq] using
        (marked_direct_union_kernel_limits p q.1 q.2 hp id (fun m => m+3)
          tendsto_id (tendsto_add_atTop_nat 3) k).2)
  have hp0 : 0 < p := by linarith [hp.1]
  have he (q : ℝ × ℝ) : -4*p*matchS*markedDirectionalSpan q.1 q.2 =
      -(4*p*matchS)*markedDirectionalSpan q.1 q.2 := by ring
  simp_rw [he] at hi
  rw [integral_const_mul,integral_const_mul,
    marked_union_full_integral (mul_pos (mul_pos (by norm_num) hp0) marked_matchS_bounds.1)] at hi
  convert hi using 1
  congr 1
  field_simp [hp0.ne',marked_matchS_bounds.1.ne']
  <;> ring

/-- Both replicas use the same original sites, including all shared donor
locations; the limit contains their exact intersection correction. -/
theorem marked_retained_product_recipient_pair_sum_limit (p : ℝ)
    (hp : p ∈ Set.Ioo (1/4 : ℝ) (3/4)) :
    Tendsto (fun n => mean (MatchProduct n) (fun z => ∑ i, ∑ j,
      if i = j then 0 else markedRecipientPairCountTest p
        (fun a b _ => markedRetainedDrawPower (n+1) a 1*markedRetainedDrawPower (n+1) b 1) z i j))
      atTop (𝓝 (((1-p)/p)^2*(4-matchS)/(2*(2-matchS)))) := by
  have hb (n a b c : ℕ) :
      |markedRetainedDrawPower (n+1) a 1*markedRetainedDrawPower (n+1) b 1| ≤ 1 := by
    rw [abs_of_nonneg (mul_nonneg (marked_retained_draw_power_bounds _ _ _).1
      (marked_retained_draw_power_bounds _ _ _).1)]
    exact mul_le_one₀ (marked_retained_draw_power_bounds _ _ _).2
      (marked_retained_draw_power_bounds _ _ _).1 (marked_retained_draw_power_bounds _ _ _).2
  have he (m : ℕ) (hm : 0 < m) : MarkedPairKernelBound m
      (fun a b _ => markedRetainedDrawPower (m+2+1) a 1*markedRetainedDrawPower (m+2+1) b 1) := by
    apply marked_product_test_pair_bound
    all_goals intro c hc
    all_goals exact ⟨(marked_retained_draw_power_bounds _ _ _).1,
      (marked_retained_draw_power_bounds _ _ _).2,
      (marked_retained_test_exp_bound m 3 c 1 hm (by norm_num) (by norm_num) hc).2⟩
  have hi := marked_recipient_pair_full_sum_limit p hp
    (fun n a b _ => markedRetainedDrawPower (n+1) a 1*markedRetainedDrawPower (n+1) b 1) hb he
    (fun q => matchS^2*markedSignedSurvival (4*p) matchS q.1 q.2) (fun q => by
      simpa only [markedPairKernel,markedSignedSurvival,Nat.add_assoc,id_eq] using
        marked_direct_recipient_pair_kernel_limit p q.1 q.2 hp id (fun m => m+3)
          tendsto_id (tendsto_add_atTop_nat 3) 1 1)
  have hp0 : 0 < p := by linarith [hp.1]
  rw [integral_const_mul,integral_const_mul,marked_shared_full_integral
    (mul_pos (by norm_num) hp0) marked_matchS_bounds.1 marked_matchS_bounds.2] at hi
  convert hi using 1
  congr 1
  field_simp [hp0.ne',marked_matchS_bounds.1.ne',(show (2-matchS : ℝ) ≠ 0 by linarith [marked_matchS_bounds.2])]
  <;> ring

end AronowAudit.P001.TailA
