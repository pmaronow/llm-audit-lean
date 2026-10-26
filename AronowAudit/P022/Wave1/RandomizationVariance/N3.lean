import AronowAudit.P022.Wave1.RandomizationVarianceBlueprint

set_option autoImplicit false
namespace AronowAudit.P022.Wave1.RandomizationVariance
open AronowAudit.P022 MeasureTheory Filter Finset
open scoped BigOperators
noncomputable section

private theorem linear_product_moment (h : N1) {N : ℕ} (a b A B : Fin N → ℝ)
    (ha : finiteMean a = 0) (hb : finiteMean b = 0) :
    (𝔼 π : Equiv.Perm (Fin N), (∑ s, A s * a (π s)) * (∑ t, B t * b (π t))) =
      finiteMean (fun i => a i * b i) *
        (∑ s, A s * B s - ((∑ s, A s) * (∑ t, B t) - ∑ s, A s * B s) / ((N : ℝ) - 1)) := by
  classical
  let C := finiteMean (fun i => a i * b i)
  let D := (N : ℝ) - 1
  have hp (s t : Fin N) :
      (𝔼 π : Equiv.Perm (Fin N), A s * a (π s) * (B t * b (π t))) =
        (C + C / D) * (if s = t then A s * B t else 0) - C / D * (A s * B t) := by
    have heq : (fun π : Equiv.Perm (Fin N) => A s * a (π s) * (B t * b (π t))) =
        (fun π => (A s * B t) * (a (π s) * b (π t))) := by funext π; ring
    rw [heq, ← Finset.mul_expect]
    by_cases hs : s = t
    · rw [(h a b s t).1 hs, if_pos hs]
      dsimp [C]
      ring
    · rw [(h a b s t).2 hs, ha, hb, if_neg hs]
      dsimp [C, D]
      ring
  calc
    _ = ∑ s, ∑ t, (𝔼 π : Equiv.Perm (Fin N), A s * a (π s) * (B t * b (π t))) := by
      simp_rw [Finset.sum_mul_sum, Finset.expect_sum_comm]
    _ = ∑ s, ∑ t, ((C + C / D) * (if s = t then A s * B t else 0) - C / D * (A s * B t)) := by
      simp_rw [hp]
    _ = (C + C / D) * (∑ s, A s * B s) - C / D * ((∑ s, A s) * (∑ t, B t)) := by
      simp_rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
      simp [← Finset.sum_mul]
    _ = _ := by dsimp [C, D]; ring

theorem n3_proof : N3 := by
  intro h N u v α γ _ hu hv
  have huu := linear_product_moment h u u α α hu hu
  have huv := linear_product_moment h u v α γ hu hv
  have hvv := linear_product_moment h v v γ γ hv hv
  have hexp : (fun π : Equiv.Perm (Fin N) => (∑ s, (α s * u (π s) + γ s * v (π s))) ^ 2) =
      (fun π => (∑ s, α s * u (π s)) * (∑ s, α s * u (π s)) +
        2 * ((∑ s, α s * u (π s)) * (∑ s, γ s * v (π s))) +
        (∑ s, γ s * v (π s)) * (∑ s, γ s * v (π s))) := by
    funext π
    rw [Finset.sum_add_distrib]
    ring
  rw [hexp, Finset.expect_add_distrib, Finset.expect_add_distrib, ← Finset.mul_expect,
    huu, huv, hvv]
  simp only [← sq]
  ring

end
end AronowAudit.P022.Wave1.RandomizationVariance
