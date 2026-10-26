import AronowAudit.P013.Wave1.CorrectedCoverageBlueprint

set_option autoImplicit false

namespace AronowAudit.P013.Wave1.CorrectedCoverage

open AronowAudit.P013 Filter Finset
open scoped BigOperators Topology NNReal ENNReal

noncomputable section

/-- Finite CDF differences give half-open intervals, without any atomlessness premise. -/
private theorem probability_Ioc {Ω : Type} [Fintype Ω] (P : Design Ω)
    (X : Ω → ℝ) (l u : ℝ) (hlu : l ≤ u) :
    probability P (fun z => l < X z ∧ X z ≤ u) =
      probability P (fun z => X z ≤ u) - probability P (fun z => X z ≤ l) := by
  classical
  unfold probability
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro z _
  by_cases hl : X z ≤ l
  · have hu : X z ≤ u := hl.trans hlu
    simp [hl, hu, not_lt.mpr hl]
  · have hl' : l < X z := lt_of_not_ge hl
    by_cases hu : X z ≤ u <;> simp [hl, hl', hu]

/-- Elementary continuous squeeze, in the form used by the finite CDF argument. -/
private theorem finite_continuous_squeeze {G : ℕ → ℝ} {F : ℝ → ℝ}
    (hF : ContinuousAt F 0)
    (hb : ∀ ε > (0 : ℝ), ∀ᶠ n in atTop, F (-ε) - ε ≤ G n ∧ G n ≤ F ε + ε) :
    Tendsto G atTop (𝓝 (F 0)) := by
  rw [Metric.tendsto_nhds]
  intro η hη
  obtain ⟨δ, hδ, hδF⟩ := Metric.tendsto_nhds_nhds.mp hF (η / 2) (by linarith)
  let ε := min (δ / 2) (η / 4)
  have he : 0 < ε := lt_min (by linarith) (by linarith)
  have hed : ε ≤ δ / 2 := min_le_left _ _
  have heη : ε ≤ η / 4 := min_le_right _ _
  have hl := hδF (show dist (-ε) 0 < δ by
    rw [Real.dist_eq, sub_zero, abs_neg, abs_of_pos he]
    linarith)
  have hr := hδF (show dist ε 0 < δ by
    rw [Real.dist_eq, sub_zero, abs_of_pos he]
    linarith)
  rw [Real.dist_eq, abs_lt] at hl hr
  filter_upwards [hb ε he] with n hn
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith [hn.1, hn.2]

/-- Direct finite-design proof: enlarge and shrink the two CDF endpoints. -/
theorem n7_proof : N7 := by
  intro h6 L instL P X w a hX ha hw
  classical
  have hF : Continuous normalCDF := h6.1
  have hFm : Monotone normalCDF := h6.2.1.monotone
  let C : ℕ → ℝ → ℝ := fun n t => probability (P n) (fun z => X n z ≤ t)
  let Ψ : ℝ → ℝ := fun ε => normalCDF (a + ε) - normalCDF (-a - ε)
  have hΨ : Continuous Ψ := by
    dsimp [Ψ]
    exact (hF.comp (continuous_const.add continuous_id)).sub
      (hF.comp (continuous_const.sub continuous_id))
  have hCD (t : ℝ) : Tendsto (fun n => C n t) atTop (𝓝 (normalCDF t)) := hX t
  have hlim (l u : ℝ) : Tendsto (fun n => C n u - C n l) atTop
      (𝓝 (normalCDF u - normalCDF l)) := (hCD u).sub (hCD l)
  have hg : Tendsto (fun n => probability (P n) (fun z => |X n z| ≤ w n)) atTop
      (𝓝 (Ψ 0)) := by
    apply finite_continuous_squeeze hΨ.continuousAt
    intro ε hε
    have hwidth : ∀ᶠ n in atTop, |w n - a| < ε / 2 := by
      simpa only [Real.dist_eq] using
        Metric.tendsto_nhds.mp hw (ε / 2) (by linarith)
    have hupper : ∀ᶠ n in atTop,
        probability (P n) (fun z => |X n z| ≤ w n) ≤
          C n (a + ε) - C n (-a - ε) := by
      filter_upwards [hwidth] with n hn
      dsimp only [C]
      rw [← probability_Ioc (P n) (X n) (-a - ε) (a + ε) (by linarith)]
      apply probability_mono
      intro z hz
      have hw' := (abs_lt.mp hn).2
      obtain ⟨hl, hu⟩ := abs_le.mp hz
      constructor <;> linarith
    have hlow : ∀ᶠ n in atTop,
        Ψ (-ε) - ε ≤ probability (P n) (fun z => |X n z| ≤ w n) := by
      by_cases hsmall : ε < a
      · have hlower : ∀ᶠ n in atTop,
            C n (a - ε) - C n (-a + ε) ≤
              probability (P n) (fun z => |X n z| ≤ w n) := by
          filter_upwards [hwidth] with n hn
          dsimp only [C]
          rw [← probability_Ioc (P n) (X n) (-a + ε) (a - ε) (by linarith)]
          apply probability_mono
          intro z hz
          have hw' := (abs_lt.mp hn).1
          rw [abs_le]
          constructor <;> linarith [hz.1, hz.2]
        have hl := (hlim (-a + ε) (a - ε)).eventually
          (lt_mem_nhds (show normalCDF (a - ε) - normalCDF (-a + ε) - ε <
            normalCDF (a - ε) - normalCDF (-a + ε) by linarith))
        filter_upwards [hlower, hl] with n hn hln
        dsimp [Ψ]
        rw [sub_neg_eq_add]
        change normalCDF (a - ε) - normalCDF (-a + ε) - ε ≤ _
        linarith
      · have hΨneg : Ψ (-ε) ≤ 0 := by
          dsimp [Ψ]
          have hm := hFm (show a + -ε ≤ -a - -ε by linarith)
          linarith
        exact Eventually.of_forall (fun n => by
          have hp := probability_nonneg (P n) (fun z => |X n z| ≤ w n)
          linarith)
    have hu := (hlim (-a - ε) (a + ε)).eventually
      (gt_mem_nhds (show normalCDF (a + ε) - normalCDF (-a - ε) <
        normalCDF (a + ε) - normalCDF (-a - ε) + ε by linarith))
    filter_upwards [hlow, hupper, hu] with n hln hun hlimn
    refine ⟨hln, ?_⟩
    dsimp [Ψ]
    linarith
  have hvalue : Ψ 0 = 2 * normalCDF a - 1 := by
    simp only [Ψ, add_zero, sub_zero, h6.2.2.1 a]
    ring
  rwa [hvalue] at hg

end

end AronowAudit.P013.Wave1.CorrectedCoverage
