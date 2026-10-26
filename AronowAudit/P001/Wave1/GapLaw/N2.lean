import AronowAudit.P001.Wave1.GapLawBlueprint
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Topology.Piecewise

set_option autoImplicit false

namespace AronowAudit.P001.Wave1.GapLaw

open AronowAudit.P001 MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal

noncomputable section

theorem n2_proof : N2 := by
  classical
  let q : ℝ → ℝ := fun x => x * (1 - x ^ 2) ^ 2
  let d : ℝ → ℝ := fun x => 1 - 6 * x ^ 2 + 5 * x ^ 4
  let D : ℝ → ℝ := fun x => if |x| < 1 then d x else 0
  have hq (x : ℝ) : HasDerivAt q (d x) x := by
    have hp := (hasDerivAt_id' x).mul
      (((hasDerivAt_const x (1 : ℝ)).sub ((hasDerivAt_id' x).pow 2)).pow 2)
    exact hp.congr_deriv (by simp only [d]; norm_num <;> ring)
  have hvan (x : ℝ) (hx : 1 ≤ |x|) : pdaBump x = 0 := by
    simp [pdaBump, not_lt.mpr hx]
  have hboundary (x : ℝ) (hx : |x| = 1) : q x = 0 ∧ d x = 0 := by
    rcases (abs_eq (by norm_num : (0 : ℝ) ≤ 1)).mp hx with hx | hx
    · subst x
      norm_num [q, d]
    · subst x
      norm_num [q, d]
  have hD (x : ℝ) : HasDerivAt pdaBump (D x) x := by
    by_cases hin : |x| < 1
    · have he : pdaBump =ᶠ[nhds x] q := by
        filter_upwards [((isOpen_lt continuous_abs continuous_const).mem_nhds hin)]
          with y hy
        simp [pdaBump, hy, q]
      simpa only [D, if_pos hin] using (hq x).congr_of_eventuallyEq he
    · by_cases hout : 1 < |x|
      · have he : pdaBump =ᶠ[nhds x] (fun _ : ℝ => 0) := by
          filter_upwards [((isOpen_lt continuous_const continuous_abs).mem_nhds hout)]
            with y hy
          exact hvan y hy.le
        simpa only [D, if_neg hin] using
          (hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq he
      · have hb : |x| = 1 := le_antisymm (not_lt.mp hout) (not_lt.mp hin)
        have hv : pdaBump x = 0 := hvan x hb.ge
        have hleft : HasDerivWithinAt pdaBump 0 {y : ℝ | |y| < 1} x := by
          have hp : HasDerivWithinAt q 0 {y : ℝ | |y| < 1} x := by
            simpa only [(hboundary x hb).2] using (hq x).hasDerivWithinAt
          apply hp.congr
          · intro y hy
            simp only [pdaBump, q]
            exact if_pos hy
          · rw [hv, (hboundary x hb).1]
        have hright : HasDerivWithinAt pdaBump 0 {y : ℝ | ¬ |y| < 1} x := by
          apply (hasDerivAt_const x (0 : ℝ)).hasDerivWithinAt.congr
          · intro y hy
            exact hvan y (not_lt.mp hy)
          · exact hv
        have hu : {y : ℝ | |y| < 1} ∪ {y : ℝ | ¬ |y| < 1} = Set.univ := by
          ext y
          simp only [Set.mem_union, Set.mem_setOf_eq, Set.mem_univ, iff_true]
          exact em _
        have hh := hleft.union hright
        rw [hu, hasDerivWithinAt_univ] at hh
        simpa only [D, if_neg hin] using hh
  have hd : Continuous d := by
    dsimp [d]
    fun_prop
  have hcD : Continuous D := by
    apply Continuous.if _ hd continuous_const
    intro x hx
    have hb : |x| = 1 := frontier_lt_subset_eq continuous_abs continuous_const hx
    exact (hboundary x hb).2
  have heq : deriv pdaBump = D := funext fun x => (hD x).deriv
  refine ⟨contDiff_one_iff_deriv.mpr ⟨fun x => (hD x).differentiableAt, ?_⟩,
    hvan, ?_⟩
  · rw [heq]
    exact hcD
  · simpa [D, d] using hD 0

end

end AronowAudit.P001.Wave1.GapLaw
