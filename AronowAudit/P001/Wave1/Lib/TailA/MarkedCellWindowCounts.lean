import AronowAudit.P001.Wave1.Lib.TailA.MarkedCellDensity

/-! Actual finite-window count cutoffs for the pinned experiment. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology

namespace AronowAudit.P001.TailA

local instance instDecidableMarkedCellWindowCounts (p : Prop) : Decidable p :=
  Classical.propDecidable p
set_option maxHeartbeats 1000000

def markedWindowCount {n : ℕ} (E : Set MatchUnit) (z : Fin n → MatchUnit) : ℕ :=
  (Finset.univ.filter (fun i => z i ∈ E)).card

theorem marked_window_count_measurable (n : ℕ) (E : Set MatchUnit)
    (hE : MeasurableSet E) : Measurable (fun z : Fin n → MatchUnit => markedWindowCount E z) := by
  have heq : (fun z : Fin n → MatchUnit => markedWindowCount E z) =
      fun z => ∑ i, if z i ∈ E then (1 : ℕ) else 0 := by
    funext z
    simp only [Finset.sum_boole, markedWindowCount, Nat.cast_id]
  rw [heq]
  exact Finset.measurable_sum _ (fun i _ =>
    Measurable.ite (hE.preimage (measurable_pi_apply i)) measurable_const measurable_const)

theorem marked_window_count_integrable (n : ℕ) (E : Set MatchUnit)
    (hE : MeasurableSet E) :
    Integrable (fun z : Fin n → MatchUnit => (markedWindowCount E z : ℝ)) (MatchProduct n) := by
  apply Integrable.of_bound ((measurable_of_countable (fun j : ℕ => (j : ℝ))).comp
    (marked_window_count_measurable n E hE)).aestronglyMeasurable
    (n : ℝ)
  exact ae_of_all _ (fun z => by
    rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]
    have hd : markedWindowCount E z ≤ n := by
      simpa only [markedWindowCount, Finset.card_univ, Fintype.card_fin] using
        (Finset.card_filter_le (s := (Finset.univ : Finset (Fin n))) (p := fun i => z i ∈ E))
    change (markedWindowCount E z : ℝ) ≤ (n : ℝ)
    exact_mod_cast hd)

/-- Expected count in any measurable category, under the actual product sample. -/
theorem marked_window_count_mean (n : ℕ) (E : Set MatchUnit) (hE : MeasurableSet E) :
    mean (MatchProduct n) (fun z => (markedWindowCount E z : ℝ)) =
      (n : ℝ)*matchingUnitLaw.real E := by
  let f : MatchUnit → ℝ := E.indicator (fun _ => 1)
  have hi : Integrable f matchingUnitLaw := (integrable_const (1 : ℝ)).indicator hE
  have heq (z : Fin n → MatchUnit) :
      (markedWindowCount E z : ℝ) = ∑ i, f (z i) := by
    simp only [f, Set.indicator, Pi.one_apply, Finset.sum_boole, markedWindowCount]
  simp only [heq, mean]
  change (∫ z : Fin n → MatchUnit, ∑ i, f (z i) ∂Measure.pi
    (fun _ => matchingUnitLaw)) = _
  rw [integral_finsetSum _ (fun i _ => integrable_comp_eval hi)]
  have heval (i : Fin n) :
      (∫ z : Fin n → MatchUnit, f (z i) ∂Measure.pi (fun _ => matchingUnitLaw)) =
      ∫ u, f u ∂matchingUnitLaw :=
    integral_comp_eval (μ := fun _ : Fin n => matchingUnitLaw) (i := i)
      hi.aestronglyMeasurable
  simp_rw [heval]
  simp only [f, integral_indicator_const _ hE, smul_eq_mul, mul_one,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- A count cutoff has its ordinary first-moment bound before taking any limit. -/
theorem marked_window_count_tail (n : ℕ) (E : Set MatchUnit) (hE : MeasurableSet E)
    {K : ℝ} (hK : 0 < K) :
    (MatchProduct n).real {z | K ≤ (markedWindowCount E z : ℝ)} ≤
      (n : ℝ)*matchingUnitLaw.real E/K := by
  apply (le_div_iff₀ hK).mpr
  rw [mul_comm]
  have h := mul_meas_ge_le_integral_of_nonneg
    (μ := MatchProduct n) (f := fun z => (markedWindowCount E z : ℝ))
    (ae_of_all _ (fun _ => Nat.cast_nonneg _))
    (marked_window_count_integrable n E hE) K
  exact h.trans_eq (marked_window_count_mean n E hE)

/-- The untyped score-window mass is exactly twice its length inside the support. -/
theorem marked_score_interval_probability (a b : ℝ)
    (hab : a ≤ b) (ha : (1/4 : ℝ) ≤ a) (hb : b ≤ (3/4 : ℝ)) :
    matchingUnitLaw.real {u : MatchUnit | u.1 ∈ Set.Ioc a b} = 2*(b-a) := by
  have hmap := congrArg (fun μ : Measure ℝ => μ (Set.Ioc a b))
    matching_score_marginal.map_eq
  rw [Measure.map_apply measurable_fst measurableSet_Ioc] at hmap
  change matchingUnitLaw (Prod.fst ⁻¹' Set.Ioc a b) = MatchingScoreLaw (Set.Ioc a b) at hmap
  change (matchingUnitLaw (Prod.fst ⁻¹' Set.Ioc a b)).toReal = _
  rw [hmap, MatchingScoreLaw, Measure.smul_apply,
    Measure.restrict_apply measurableSet_Ioc]
  have hsub : Set.Ioc a b ⊆ Set.Icc (1/4 : ℝ) (3/4) :=
    fun x hx => ⟨ha.trans hx.1.le, hx.2.trans hb⟩
  rw [Set.inter_eq_left.mpr hsub, Real.volume_Ioc, smul_eq_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (sub_nonneg.mpr hab)]
  norm_num

/-- In a fixed scaled window the count tail is bounded by `4R/K`, uniformly
over all rows whose physical window is inside the score support. -/
theorem marked_scaled_window_count_tail {n : ℕ} (hn : 0 < n) (p R : ℝ)
    (hR : 0 ≤ R) (ha : (1/4 : ℝ) ≤ p-R/(n : ℝ))
    (hb : p+R/(n : ℝ) ≤ (3/4 : ℝ)) {K : ℝ} (hK : 0 < K) :
    (MatchProduct n).real {z | K ≤ (markedWindowCount
      {u : MatchUnit | u.1 ∈ Set.Ioc (p-R/(n : ℝ)) (p+R/(n : ℝ))} z : ℝ)} ≤ 4*R/K := by
  have hab : p-R/(n : ℝ) ≤ p+R/(n : ℝ) := by
    have hd : 0 ≤ R/(n : ℝ) := div_nonneg hR (Nat.cast_nonneg _)
    linarith
  have ht := marked_window_count_tail n
    {u : MatchUnit | u.1 ∈ Set.Ioc (p-R/(n : ℝ)) (p+R/(n : ℝ))}
    (measurableSet_Ioc.preimage measurable_fst) hK
  rw [marked_score_interval_probability _ _ hab ha hb] at ht
  convert ht using 1
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  field_simp
  <;> ring

end AronowAudit.P001.TailA
