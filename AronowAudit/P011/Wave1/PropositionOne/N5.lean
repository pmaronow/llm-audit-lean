import AronowAudit.P011.Wave1.PropositionOneBlueprint
import AronowAudit.P011.P011_BlockOLSCompletion

/-! Exact centering and the almost sure support bound for the path witness. -/

set_option autoImplicit false

namespace AronowAudit.P011.Wave1.PropositionOne

open AronowAudit.P011 MeasureTheory ProbabilityTheory Filter Finset
open scoped BigOperators Topology

noncomputable section

set_option backward.isDefEq.respectTransparency false

private lemma path_weighted_id (K : ℕ) (y : Fin (3 * K) → ℝ) :
    weighted (pathModel 2 K) y = y := by
  funext i
  exact one_mul (y i)

private lemma path_beta_zero (K : ℕ) : beta (pathModel 2 K) = 0 := by
  classical
  letI : IsProbabilityMeasure (pathModel 2 K).law := (pathModel 2 K).probability
  have hL2 (i : Fin (3 * K)) :
      MemLp (fun y : Fin (3 * K) → ℝ => y i) 2 (pathModel 2 K).law :=
    NewFiniteCompletion.finite_memLp (pathSource K) (fun y => y i)
      (measurable_pi_apply i) 2
  unfold beta expectation betaHat
  simp only [path_weighted_id, average]
  rw [integral_div,
    integral_finsetSum Finset.univ (fun i _ => (hL2 i).integrable (by norm_num))]
  change (∑ i : Fin (3 * K), expectation (pathModel 2 K) (fun y => y i)) /
    ((3 * K : ℕ) : ℝ) = 0
  simp_rw [BlockOLSCompletion.path_coordinate_mean]
  rw [BlockOLSCompletion.local_sum (by decide : 0 < 3)]
  norm_num [Fin.sum_univ_succ]

private lemma path_support_bound (K : ℕ) :
    ∀ᵐ y ∂uniformLaw (pathSource K), ∀ i, |y i| ≤ 6 := by
  classical
  have hsource : Measurable (pathSource K) := measurable_of_finite _
  have hbound_meas : MeasurableSet {y : Fin (3 * K) → ℝ | ∀ i, |y i| ≤ 6} := by
    simp only [Set.setOf_forall]
    exact MeasurableSet.iInter (fun i =>
      measurableSet_le
        (show Measurable (fun y : Fin (3 * K) → ℝ => |y i|) by fun_prop)
        measurable_const)
  unfold uniformLaw
  rw [← PMF.toMeasure_map (pathSource K)
    (PMF.uniformOfFintype (Fin K → Fin 2 → Bool)) hsource]
  apply (ae_map_iff hsource.aemeasurable hbound_meas).mpr
  have hblock_bound (r : Fin 3) (a b : Bool) :
      |pathBlock 2 (sign a) (sign b) r| ≤ 6 := by
    fin_cases r <;> cases a <;> cases b <;> norm_num [pathBlock, sign]
  filter_upwards [] with u
  intro i
  exact hblock_bound (localIndex (by decide) i)
    (u (blockIndex (by decide) i) 0) (u (blockIndex (by decide) i) 1)

theorem n5_proof : N5 := by
  intro k
  refine ⟨path_beta_zero (k + 1), ?_⟩
  have h := path_support_bound (k + 1)
  change ∀ᵐ y ∂uniformLaw (pathSource (k + 1)), _
  filter_upwards [h] with y hy
  intro i
  rw [show beta (PF.model k) = 0 from path_beta_zero (k + 1)]
  change |1 * y i - 0| ≤ 6
  simpa only [one_mul, sub_zero] using hy i

end

end AronowAudit.P011.Wave1.PropositionOne
