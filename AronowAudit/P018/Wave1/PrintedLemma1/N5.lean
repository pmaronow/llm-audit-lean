import AronowAudit.P018.Wave1.PrintedLemma1Blueprint
import Mathlib.MeasureTheory.Integral.Pi

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096
namespace AronowAudit.P018.Wave1.PrintedLemma1
open AronowAudit.P018 Finset Matrix MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology BoundedContinuousFunction Matrix.Norms.Elementwise ENNReal
noncomputable section

private abbrev μ3 := Measure.pi (fun _ : Fin 3 => uniformUnitLaw)
private def monomial (a : Fin 3 → ℕ) (ω : Fin 3 → ℝ) : ℝ := ∏ i, ω i ^ a i
private def moment (n : ℕ) : ℝ := (1-(-1 : ℝ)^(n+1))/(2*(n+1 : ℝ))

private theorem monomial_integrable (a : Fin 3 → ℕ) : Integrable (monomial a) μ3 :=
  Integrable.fintype_prod_dep (fun i => (uniform_unit_power_L2 (a i)).integrable one_le_two)

private theorem monomial_integral (a : Fin 3 → ℕ) :
    (∫ ω, monomial a ω ∂ μ3) = ∏ i, moment (a i) := by
  unfold monomial μ3
  rw [integral_fintype_prod_eq_prod (fun (i : Fin 3) (z : ℝ) => z ^ a i)]
  simp only [uniform_unit_moment, moment]

private theorem polynomial_integral {m : ℕ} (c : Fin m → ℝ) (a : Fin m → Fin 3 → ℕ) :
    (∫ ω, ∑ j, c j * monomial (a j) ω ∂ μ3) = ∑ j, c j * ∏ i, moment (a j i) := by
  rw [integral_finsetSum univ (fun j _ => (monomial_integrable (a j)).const_mul (c j))]
  simp_rw [integral_const_mul, monomial_integral]

private def coef : Fin 7 → ℝ := ![-2,2,2,2,2,2,2]
private def exps : Fin 7 → Fin 3 → ℕ :=
  ![![0,0,0], ![2,0,0], ![0,2,0], ![0,0,2], ![1,1,0], ![1,0,1], ![0,1,1]]
private def poly (ω : Fin 3 → ℝ) : ℝ :=
  (ω 0 + ω 1)^2 + (ω 0 + ω 2)^2 + (ω 1 + ω 2)^2 - 2

private theorem poly_expansion (ω : Fin 3 → ℝ) :
    poly ω = ∑ j, coef j * monomial (exps j) ω := by
  simp [poly, coef, exps, monomial, Fin.sum_univ_succ, Fin.prod_univ_succ]
  ring

private theorem square_expansion (ω : Fin 3 → ℝ) :
    (poly ω)^2 = ∑ j, ∑ k, (coef j * coef k) * monomial (fun i => exps j i + exps k i) ω := by
  simp_rw [monomial, pow_add, Finset.prod_mul_distrib]
  rw [pow_two, poly_expansion, Finset.sum_mul_sum]
  simp only [monomial]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro k hk
  ring

private theorem poly_mean : (∫ ω, poly ω ∂ μ3) = 0 := by
  simp_rw [poly_expansion]
  rw [polynomial_integral]
  norm_num [coef, exps, moment, Fin.sum_univ_succ, Fin.prod_univ_succ]

private theorem poly_sq_integrable : Integrable (fun ω => (poly ω)^2) μ3 := by
  simp_rw [square_expansion]
  apply integrable_finset_sum
  intro j hj
  apply integrable_finset_sum
  intro k hk
  exact (monomial_integrable (fun i => exps j i + exps k i)).const_mul _

private theorem poly_second : (∫ ω, (poly ω)^2 ∂ μ3) = 12/5 := by
  simp_rw [square_expansion]
  rw [integral_finsetSum univ (fun j _ => integrable_finset_sum _
    (fun k _ => (monomial_integrable (fun i => exps j i + exps k i)).const_mul _))]
  simp_rw [polynomial_integral]
  norm_num [coef, exps, moment, Fin.sum_univ_succ, Fin.prod_univ_succ]

theorem n5_proof : N5 := by
  have hmem : MemLp poly 2 μ3 :=
    (memLp_two_iff_integrable_sq (by unfold poly; fun_prop)).mpr poly_sq_integrable
  change variance poly μ3 = 12/5
  rw [variance_eq_sub hmem]
  change (∫ ω, (poly ω)^2 ∂ μ3) - (∫ ω, poly ω ∂ μ3)^2 = 12/5
  rw [poly_mean, poly_second]
  norm_num
end
end AronowAudit.P018.Wave1.PrintedLemma1
