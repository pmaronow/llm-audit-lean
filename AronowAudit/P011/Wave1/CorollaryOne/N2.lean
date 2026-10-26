import AronowAudit.P011.Wave1.CorollaryOneBlueprint
import AronowAudit.P011.P011_BlockOLSCompletion

set_option autoImplicit false

namespace AronowAudit.P011.Wave1.CorollaryOne

open AronowAudit.P011 AronowAudit.P011.Wave1.PropositionOne MeasureTheory ProbabilityTheory
  Filter Finset
open scoped BigOperators Topology

noncomputable section

/-- Each centered coordinate has second moment one, in every block. -/
theorem n2_proof : N2 := by
  intro k
  have hdiag (i : Fin (PF.size k)) : covariance (PF.model k) i i = 1 := by
    let r : Fin 3 := localIndex (by decide) i
    let μ : Fin 3 → ℝ := ![2, -4, 2]
    have hfour (j : Fin 3) :
        (∑ u : Fin 2 → Bool,
          (pathBlock 2 (sign (u 0)) (sign (u 1)) j - μ j) *
            (pathBlock 2 (sign (u 0)) (sign (u 1)) j - μ j)) / 4 = 1 := by
      rw [← (finTwoArrowEquiv Bool).symm.sum_comp]
      fin_cases j <;>
        norm_num [μ, Fintype.sum_prod_type, Fintype.sum_bool, finTwoArrowEquiv, pathBlock, sign]
    have hmean : expectation (PF.model k) (fun y => weighted (PF.model k) y i) = μ r := by
      change expectation (pathModel 2 (k + 1)) (fun y => 1 * y i) = μ r
      simpa only [one_mul, μ, show (-2 : ℝ) * 2 = -4 by norm_num] using
        BlockOLSCompletion.path_coordinate_mean (2 : ℝ) (k + 1) i
    unfold covariance
    simp only [hmean]
    have hw (y : Fin (PF.size k) → ℝ) : weighted (PF.model k) y i = y i := by
      change 1 * y i = y i
      exact one_mul _
    simp only [hw]
    change (∫ y : Fin (3 * (k + 1)) → ℝ,
      (y i - μ r) * (y i - μ r) ∂uniformLaw (pathSource (k + 1))) = 1
    rw [uniform_integral (pathSource (k + 1)) (measurable_of_finite _)
      (fun y => (y i - μ r) * (y i - μ r)) (by fun_prop)]
    let f : (Fin 2 → Bool) → ℝ := fun u =>
      (pathBlock 2 (sign (u 0)) (sign (u 1)) r - μ r) *
        (pathBlock 2 (sign (u 0)) (sign (u 1)) r - μ r)
    change (∑ u : Fin (k + 1) → Fin 2 → Bool, f (u (blockIndex (by decide) i))) /
      (Fintype.card (Fin (k + 1) → Fin 2 → Bool) : ℝ) = 1
    rw [BlockOLSCompletion.uniform_coordinate_sum (blockIndex (by decide) i) f]
    norm_num only [Fintype.card_fun, Fintype.card_fin, Fintype.card_bool]
    exact hfour r
  intro i j
  rw [hdiag i, hdiag j]

end

end AronowAudit.P011.Wave1.CorollaryOne
