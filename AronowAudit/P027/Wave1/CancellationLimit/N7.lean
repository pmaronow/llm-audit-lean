import AronowAudit.P027.Wave1.CancellationLimitBlueprint

/-! Reduce the signal energy to a constant times a convergent reciprocal sequence. -/

namespace AronowAudit.P027.Wave1.CancellationLimit

set_option autoImplicit false
noncomputable section
open AronowAudit.P027 MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
attribute [local instance] Classical.propDecidable

theorem n7_proof : N7 := by
  intro r hr ρ β hβ
  have hrR : (r : ℝ) ≠ 0 := by exact_mod_cast hr.ne'
  have henergy (n : ℕ) :
      (∑ g : Fin r × Fin 2, (signal r (n+1) (β n) g)^2) =
        16 * (β n)^2 / (2 * (r : ℝ)) := by
    have hmR : (((n+1 : ℕ) : ℝ)) ≠ 0 := by positivity
    have hpoint (g : Fin r × Fin 2) :
        (signal r (n+1) (β n) g)^2 = 16 * (β n)^2 / (2 * (r : ℝ))^2 := by
      by_cases hg : g.2 = 0 <;>
        simp only [signal, hg, ite_true, ite_false] <;>
        field_simp [hrR, hmR] <;> ring
    simp_rw [hpoint]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod,
      Fintype.card_fin, nsmul_eq_mul, Nat.cast_mul, Nat.cast_ofNat]
    field_simp [hrR] <;> ring
  have hformula (n : ℕ) :
      (∑ g : Fin r × Fin 2, (signal r (n+1) (β n) g)^2) =
        (900 * ρ^2 / (2 * (r : ℝ))) *
          (1 - (1 / (2 * (r : ℝ))) * (1 / ((n : ℝ) + 1))) := by
    rw [henergy n, hβ n]
    have hn : (n : ℝ) + 1 ≠ 0 := by positivity
    push_cast
    field_simp [hrR, hn] <;> ring
  have hsmall := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul
    (1 / (2 * (r : ℝ)))
  have hlim : Tendsto
      (fun n : ℕ => (900 * ρ^2 / (2 * (r : ℝ))) *
        (1 - (1 / (2 * (r : ℝ))) * (1 / ((n : ℝ) + 1))))
      atTop (𝓝 (900 * ρ^2 / (2 * (r : ℝ)))) := by
    simpa only [mul_zero, sub_zero, mul_one] using
      (hsmall.const_sub 1).const_mul (900 * ρ^2 / (2 * (r : ℝ)))
  exact hlim.congr (fun n => (hformula n).symm)

end
end AronowAudit.P027.Wave1.CancellationLimit
