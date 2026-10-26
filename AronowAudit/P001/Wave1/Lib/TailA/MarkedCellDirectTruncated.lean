import AronowAudit.P001.Wave1.Lib.TailA.MarkedCellDirectWindows

/-! Measurability of the scaled donor-count kernels and bounds and limits for
the recipient score density with its finite-sample support cutoff. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology

namespace AronowAudit.P001.TailA
local instance instDecidableMarkedCellDirectTruncated (p : Prop) : Decidable p :=
  Classical.propDecidable p
set_option maxHeartbeats 1000000
set_option maxRecDepth 3000

/-- Joint measurability of the actual count in a query-dependent donor window. -/
theorem marked_scaled_closer_count_measurable (n : ℕ) (p : ℝ) :
    Measurable (fun y : ℝ × (Fin n → MatchUnit) =>
      markedWindowCount (markedCloserDonors p (p+y.1/(n : ℝ))) y.2) := by
  simp only [markedWindowCount,Finset.card_filter]
  apply Finset.measurable_sum
  intro i _
  have hs : Measurable (fun y : ℝ × (Fin n → MatchUnit) => p+y.1/(n : ℝ)) := by fun_prop
  have hi : Measurable (fun y : ℝ × (Fin n → MatchUnit) => y.2 i) :=
    (measurable_pi_apply i).comp measurable_snd
  have hleft : Measurable (fun y : ℝ × (Fin n → MatchUnit) =>
      |(y.2 i).1-(p+y.1/(n : ℝ))|) := continuous_abs.measurable.comp (hi.fst.sub hs)
  have hright : Measurable (fun y : ℝ × (Fin n → MatchUnit) =>
      |p-(p+y.1/(n : ℝ))|) := continuous_abs.measurable.comp (measurable_const.sub hs)
  exact Measurable.ite
    ((measurableSet_eq_fun hi.snd.fst measurable_const).inter
      (measurableSet_lt hleft hright)) measurable_const measurable_const

/-- Every test of the finite count is measurable in the recipient position
before and after averaging the other original observations. -/
theorem marked_direct_count_kernel_measurable (n : ℕ) (p : ℝ) (f : ℕ → ℝ) :
    Measurable (fun t : ℝ => mean (MatchProduct n) (fun z =>
      f (markedWindowCount (markedCloserDonors p (p+t/(n : ℝ))) z))) := by
  exact (((measurable_of_countable f).comp
    (marked_scaled_closer_count_measurable n p)).stronglyMeasurable.integral_prod_right').measurable


/-- The actual recipient score density, with its finite-sample support cutoff. -/
def markedScaledRecipientDensity (n : ℕ) (p t : ℝ) : ℝ :=
  if p+t/(n : ℝ) ∈ Set.Icc (1/4 : ℝ) (3/4) then 2*(1-(p+t/(n : ℝ))) else 0

theorem marked_scaled_recipient_density_measurable (n : ℕ) (p : ℝ) :
    Measurable (markedScaledRecipientDensity n p) := by
  apply Measurable.ite (measurableSet_Icc.preimage (by fun_prop))
  · fun_prop
  · exact measurable_const

theorem marked_scaled_recipient_density_bound (n : ℕ) (p t : ℝ) :
    |markedScaledRecipientDensity n p t| ≤ 2 := by
  unfold markedScaledRecipientDensity
  split_ifs with h
  · rw [abs_of_nonneg (by linarith [h.2])]
    linarith [h.1]
  · norm_num

theorem marked_scaled_recipient_density_limit (p t : ℝ)
    (hp : p ∈ Set.Ioo (1/4 : ℝ) (3/4)) (m : ℕ → ℕ) (hm : Tendsto m atTop atTop) :
    Tendsto (fun n => markedScaledRecipientDensity (m n) p t) atTop (𝓝 (2*(1-p))) := by
  have hi := tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.comp hm :
    Tendsto (fun n => (m n : ℝ)) atTop atTop)
  have hq : Tendsto (fun n => p+t/(m n : ℝ)) atTop (𝓝 p) := by
    simpa only [div_eq_mul_inv,Function.comp_def,mul_zero,add_zero] using
      (tendsto_const_nhds (x := p)).add (hi.const_mul t)
  have ht := ((tendsto_const_nhds (x := (1 : ℝ))).sub hq).const_mul 2
  apply ht.congr'
  filter_upwards [hq.eventually (isOpen_Ioo.mem_nhds hp)] with n hn
  have hmem : p+t/(m n : ℝ) ∈ Set.Icc (1/4 : ℝ) (3/4) := ⟨hn.1.le,hn.2.le⟩
  simp only [markedScaledRecipientDensity,if_pos hmem]


end AronowAudit.P001.TailA
