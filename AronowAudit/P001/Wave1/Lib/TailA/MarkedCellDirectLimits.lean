import AronowAudit.P001.Wave1.Lib.TailA.MarkedCellFiniteAvoidance

/-! Limits of the direct finite multinomial kernels after fixing recipients.

Each kernel is a bounded function of actual rare donor counts.  Central-mark
retention is the difference between avoidance of `c` and `c+1` labels.  No marked
point process, cell moment, or convergence of assignment weights is assumed.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology

namespace AronowAudit.P001.TailA
local instance instDecidableMarkedCellDirectLimits (p : Prop) : Decidable p :=
  Classical.propDecidable p
set_option maxHeartbeats 1000000
set_option maxRecDepth 3000

/-- Leave `k` specified draws out of an avoidance power.  The maximum makes
all unused initial rows and impossible count values harmless. -/
def markedDrawPower (N c k : ℕ) : ℝ :=
  (max 0 (1-(c : ℝ)/(N : ℝ)))^(N-k)

theorem marked_draw_power_bounds (N c k : ℕ) :
    0 ≤ markedDrawPower N c k ∧ markedDrawPower N c k ≤ 1 := by
  have hb : max 0 (1-(c : ℝ)/(N : ℝ)) ≤ 1 := by
    apply max_le (by norm_num)
    have hd : 0 ≤ (c : ℝ)/(N : ℝ) := by positivity
    linarith
  exact ⟨pow_nonneg (le_max_left _ _) _,pow_le_one₀ (le_max_left _ _) hb⟩

theorem marked_draw_power_of_le {N c : ℕ} (hN : 0 < N) (hc : c ≤ N) (k : ℕ) :
    markedDrawPower N c k = (1-(c : ℝ)/(N : ℝ))^(N-k) := by
  have hb : 0 ≤ 1-(c : ℝ)/(N : ℝ) :=
    sub_nonneg.mpr ((div_le_one (Nat.cast_pos.mpr hN)).mpr (by exact_mod_cast hc))
  simp only [markedDrawPower,max_eq_right hb]

theorem marked_draw_power_limit (m : ℕ → ℕ) (hm : Tendsto m atTop atTop)
    (c k : ℕ) :
    Tendsto (fun n => markedDrawPower (m n) c k) atTop
      (𝓝 (Real.exp (-(c : ℝ)))) := by
  have hr : Tendsto (fun n => (m n : ℝ)*((c : ℝ)/(m n : ℝ))) atTop (𝓝 (c : ℝ)) := by
    apply (tendsto_const_nhds (x := (c : ℝ))).congr'
    filter_upwards [hm.eventually (eventually_ge_atTop 1)] with n hn
    have hn0 : (m n : ℝ) ≠ 0 := by positivity
    field_simp
  have ht := rare_counts_residual_power m hm (fun n => (c : ℝ)/(m n : ℝ))
    (c : ℝ) hr k
  apply ht.congr'
  filter_upwards [hm.eventually (eventually_ge_atTop (max c 1))] with n hn
  exact (marked_draw_power_of_le (by omega) (by omega) k).symm

/-- The central-label retention correction. -/
def markedRetainedDrawPower (N c k : ℕ) : ℝ :=
  markedDrawPower N c k-markedDrawPower N (c+1) k

theorem marked_retained_draw_power_bounds (N c k : ℕ) :
    0 ≤ markedRetainedDrawPower N c k ∧ markedRetainedDrawPower N c k ≤ 1 := by
  obtain ⟨h0,h1⟩ := marked_draw_power_bounds N c k
  obtain ⟨h2,h3⟩ := marked_draw_power_bounds N (c+1) k
  have hm : markedDrawPower N (c+1) k ≤ markedDrawPower N c k := by
    apply pow_le_pow_left₀ (le_max_left _ _)
    apply max_le_max (le_refl _)
    have hd := div_le_div_of_nonneg_right
      (show (c : ℝ) ≤ (c+1 : ℕ) by exact_mod_cast Nat.le_succ c)
      (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
    linarith
  exact ⟨sub_nonneg.mpr hm,by dsimp [markedRetainedDrawPower]; linarith⟩

theorem marked_retained_draw_power_limit (m : ℕ → ℕ) (hm : Tendsto m atTop atTop)
    (c k : ℕ) :
    Tendsto (fun n => markedRetainedDrawPower (m n) c k) atTop
      (𝓝 (matchS*Real.exp (-(c : ℝ)))) := by
  have he : Real.exp (-(c : ℝ))-Real.exp (-((c+1 : ℕ) : ℝ)) =
      matchS*Real.exp (-(c : ℝ)) := by
    simp only [Nat.cast_add,Nat.cast_one,neg_add,Real.exp_add,matchS]
    ring
  simpa only [markedRetainedDrawPower,he] using
    (marked_draw_power_limit m hm c k).sub (marked_draw_power_limit m hm (c+1) k)

def markedPairCoefficient (N : ℕ) : ℝ := ((N-1 : ℕ) : ℝ)/(N : ℝ)


theorem marked_pair_coefficient_limit (m : ℕ → ℕ) (hm : Tendsto m atTop atTop) :
    Tendsto (fun n => markedPairCoefficient (m n)) atTop (𝓝 1) := by
  have hi := tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.comp hm :
    Tendsto (fun n => (m n : ℝ)) atTop atTop)
  have ht := (tendsto_const_nhds (x := (1 : ℝ))).sub hi
  apply (show Tendsto (fun n => 1-(m n : ℝ)⁻¹) atTop (𝓝 1) by simpa using ht).congr'
  filter_upwards [hm.eventually (eventually_ge_atTop 1)] with n hn
  simp only [markedPairCoefficient,Nat.cast_sub hn,Nat.cast_one]
  have hn0 : (m n : ℝ) ≠ 0 := by positivity
  field_simp

/-- For any actual rare donor category, the weighted kernels converge after
averaging the original sample.  This is a statement about finite multinomial
resampling, not a construction of a process with stipulated moments. -/
theorem marked_direct_single_category_limits
    (m N : ℕ → ℕ) (hm : Tendsto m atTop atTop) (hN : Tendsto N atTop atTop)
    (E : ℕ → Set MatchUnit) (hE : ∀ n, MeasurableSet (E n)) (rate : ℝ≥0)
    (hrate : Tendsto (fun n => (m n : ℝ)*matchingUnitLaw.real (E n)) atTop
      (𝓝 (rate : ℝ))) (k : ℕ) :
    Tendsto (fun n => mean (MatchProduct (m n)) (fun z =>
      markedDrawPower (N n) (markedWindowCount (E n) z) k)) atTop
      (𝓝 (Real.exp (-matchS*(rate : ℝ)))) ∧
    Tendsto (fun n => mean (MatchProduct (m n)) (fun z =>
      markedRetainedDrawPower (N n) (markedWindowCount (E n) z) k)) atTop
      (𝓝 (matchS*Real.exp (-matchS*(rate : ℝ)))) := by
  let X : (n : ℕ) → (Fin (m n) → MatchUnit) → Fin 1 → ℕ :=
    fun n z _ => markedWindowCount (E n) z
  let rates : Fin 1 → ℝ≥0 := fun _ => rate
  have hX (n : ℕ) : Measurable (X n) :=
    measurable_pi_lambda (fun _ => marked_window_count_measurable _ _ (hE n))
  have hw := rare_partition_counts 1 m hm (fun _ => matchingUnitLaw)
    (fun _ => inferInstance) (fun n _ => E n) (fun n _ => hE n)
    (fun n i j hij => False.elim (hij (Subsingleton.elim i j))) rates (fun _ => hrate)
  have he : (∫ v : Fin 1 → ℕ, Real.exp (-(v 0 : ℝ))
      ∂Measure.pi (fun i => poissonMeasure (rates i))) =
        Real.exp (-matchS*(rate : ℝ)) := by
    have hh := marked_poisson_product_power_integral 1 rates (fun _ => Real.exp (-1))
    simp only [Fin.prod_univ_one,Fin.sum_univ_one,rates] at hh
    simp only [← Real.exp_nat_mul] at hh
    convert hh using 1
    · congr 1
      funext v
      congr 1
      ring
    · congr 1
      unfold matchS
      ring
  have hdraw := marked_discrete_varying_test_limit (fun n => MatchProduct (m n))
    (fun _ => inferInstance) X hX _ hw
    (fun n v => markedDrawPower (N n) (v 0) k) (fun v => Real.exp (-(v 0 : ℝ)))
    (by norm_num : (0 : ℝ) ≤ 1)
    (fun n v => by
      rw [abs_of_nonneg (marked_draw_power_bounds _ _ _).1]
      exact (marked_draw_power_bounds _ _ _).2)
    (fun v => marked_draw_power_limit N hN (v 0) k)
  have hret := marked_discrete_varying_test_limit (fun n => MatchProduct (m n))
    (fun _ => inferInstance) X hX _ hw
    (fun n v => markedRetainedDrawPower (N n) (v 0) k)
    (fun v => matchS*Real.exp (-(v 0 : ℝ)))
    (by norm_num : (0 : ℝ) ≤ 1)
    (fun n v => by
      rw [abs_of_nonneg (marked_retained_draw_power_bounds _ _ _).1]
      exact (marked_retained_draw_power_bounds _ _ _).2)
    (fun v => marked_retained_draw_power_limit N hN (v 0) k)
  exact ⟨by simpa only [mean,X,he] using hdraw,
    by simpa only [mean,X,integral_const_mul,he] using hret⟩

end AronowAudit.P001.TailA
