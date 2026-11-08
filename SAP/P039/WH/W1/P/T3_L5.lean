import SAP.P039.WH.W1.Leaves
import Mathlib.Analysis.Calculus.Deriv.MeanValue

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P039.WH.W1.P.T3_L5

noncomputable section

def lowerGap (x : ℝ) : ℝ := Real.arctan x - (x - x ^ 3 / 3)
def upperGap (x : ℝ) : ℝ := x - x ^ 3 / 3 + x ^ 5 / 5 - Real.arctan x

lemma lowerGap_hasDerivAt (x : ℝ) :
    HasDerivAt lowerGap (x ^ 4 / (1 + x ^ 2)) x := by
  convert (Real.hasDerivAt_arctan x).sub
    ((hasDerivAt_id' x).sub (((hasDerivAt_id' x).pow 3).div_const 3)) using 1 <;>
    all_goals try (field_simp <;> ring)
  all_goals (funext y; simp [lowerGap]; ring)

lemma upperGap_hasDerivAt (x : ℝ) :
    HasDerivAt upperGap (x ^ 6 / (1 + x ^ 2)) x := by
  convert (((hasDerivAt_id' x).sub (((hasDerivAt_id' x).pow 3).div_const 3)).add
    (((hasDerivAt_id' x).pow 5).div_const 5)).sub (Real.hasDerivAt_arctan x) using 1 <;>
    all_goals try (field_simp <;> ring)
  all_goals (funext y; simp [upperGap]; ring)

lemma lowerGap_monotone (x : ℝ) (hx : 0 ≤ x) :
    MonotoneOn lowerGap (Set.Icc (0 : ℝ) x) := by
  apply monotoneOn_of_deriv_nonneg (convex_Icc 0 x)
    (continuous_iff_continuousAt.mpr (fun t => (lowerGap_hasDerivAt t).continuousAt)).continuousOn
    (fun t _ => (lowerGap_hasDerivAt t).differentiableAt.differentiableWithinAt)
  intro t ht
  rw [(lowerGap_hasDerivAt t).deriv]
  positivity

lemma upperGap_monotone (x : ℝ) (hx : 0 ≤ x) :
    MonotoneOn upperGap (Set.Icc (0 : ℝ) x) := by
  apply monotoneOn_of_deriv_nonneg (convex_Icc 0 x)
    (continuous_iff_continuousAt.mpr (fun t => (upperGap_hasDerivAt t).continuousAt)).continuousOn
    (fun t _ => (upperGap_hasDerivAt t).differentiableAt.differentiableWithinAt)
  intro t ht
  rw [(upperGap_hasDerivAt t).deriv]
  positivity

lemma lowerGap_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ lowerGap x := by
  have h := lowerGap_monotone x hx (show (0 : ℝ) ∈ Set.Icc 0 x from ⟨le_rfl, hx⟩)
    (show x ∈ Set.Icc (0 : ℝ) x from ⟨hx, le_rfl⟩) hx
  simpa [lowerGap] using h

lemma upperGap_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ upperGap x := by
  have h := upperGap_monotone x hx (show (0 : ℝ) ∈ Set.Icc 0 x from ⟨le_rfl, hx⟩)
    (show x ∈ Set.Icc (0 : ℝ) x from ⟨hx, le_rfl⟩) hx
  simpa [upperGap] using h

end

end SAP.P039.WH.W1.P.T3_L5

theorem SAP.P039.WH.W1.T3_L5_proof : SAP.P039.WH.W1.T3_L5 := by
  intro x hx
  constructor
  · have h := SAP.P039.WH.W1.P.T3_L5.lowerGap_nonneg hx
    dsimp [SAP.P039.WH.W1.P.T3_L5.lowerGap] at h
    linarith
  · have h := SAP.P039.WH.W1.P.T3_L5.upperGap_nonneg hx
    dsimp [SAP.P039.WH.W1.P.T3_L5.upperGap] at h
    linarith
