import AronowAudit.P001.Wave1.UnbiasedMeanVarianceBlueprint

namespace AronowAudit.P001.Wave1.UnbiasedMeanVariance

set_option autoImplicit false
noncomputable section
open AronowAudit.P001 MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology
local instance instDecidableUnbiasedMeanVarianceN2 (p : Prop) : Decidable p :=
  Classical.propDecidable p

theorem n2_proof : N2 := by
  intro Ω _ μ _ Z c a hZ ha ε hε
  have ha0 : Tendsto (fun n => a n - 1) atTop (nhds (0 : ℝ)) := by
    simpa using ha.sub_const 1
  have habs0 : Tendsto (fun n => |a n - 1|) atTop (nhds (0 : ℝ)) := by
    simpa only [abs_zero] using ha0.abs
  have hprod0 : Tendsto (fun n => |(a n - 1) * c|) atTop (nhds (0 : ℝ)) := by
    have ht : Tendsto (fun n => (a n - 1) * c) atTop (nhds (0 : ℝ)) := by
      simpa using ha0.mul_const c
    simpa only [abs_zero] using ht.abs
  have hupper : ∀ᶠ n in atTop,
      prob μ {ω | ε ≤ dist (a n * Z n ω) c} ≤
        prob μ {ω | ε / 4 ≤ dist (Z n ω) c} := by
    filter_upwards [(tendsto_order.mp habs0).2 1 zero_lt_one,
      (tendsto_order.mp hprod0).2 (ε / 2) (by positivity)] with n han hac
    refine measureReal_mono ?_ (measure_ne_top μ _)
    intro ω hω
    simp only [Set.mem_setOf_eq, Real.dist_eq] at hω ⊢
    by_contra h
    have hz : |Z n ω - c| < ε / 4 := lt_of_not_ge h
    have ha2 : |a n| ≤ 2 := by
      have htri : |a n| ≤ |a n - 1| + 1 := by
        calc
          |a n| = |(a n - 1) + 1| := by congr 1; ring
          _ ≤ |a n - 1| + |(1 : ℝ)| := abs_add_le _ _
          _ = |a n - 1| + 1 := by norm_num
      linarith
    have hmul : |a n| * |Z n ω - c| < ε / 2 := by
      calc
        _ ≤ 2 * |Z n ω - c| := mul_le_mul_of_nonneg_right ha2 (abs_nonneg _)
        _ < ε / 2 := by linarith
    have htri : |a n * Z n ω - c| ≤
        |a n| * |Z n ω - c| + |(a n - 1) * c| := by
      calc
        _ = |a n * (Z n ω - c) + (a n - 1) * c| := by congr 1; ring
        _ ≤ |a n * (Z n ω - c)| + |(a n - 1) * c| := abs_add_le _ _
        _ = _ := by rw [abs_mul]
    linarith
  exact squeeze_zero' (Eventually.of_forall (fun n => ENNReal.toReal_nonneg))
    hupper (hZ (ε / 4) (by positivity))

end
end AronowAudit.P001.Wave1.UnbiasedMeanVariance
