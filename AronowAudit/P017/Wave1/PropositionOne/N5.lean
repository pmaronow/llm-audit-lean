import AronowAudit.P017.Wave1.PropositionOne.N1
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Probability.Moments.Variance

set_option autoImplicit false

namespace AronowAudit.P017.Wave1.PropositionOne

open AronowAudit.P017 MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal

noncomputable section

private theorem fairPair_ae (a b : ℝ) : ∀ᵐ x ∂fairPair a b, x = a ∨ x = b := by
  have ha : ∀ᵐ x ∂Measure.dirac a, x = a ∨ x = b := by simp [ae_dirac_eq]
  have hb : ∀ᵐ x ∂Measure.dirac b, x = a ∨ x = b := by simp [ae_dirac_eq]
  rw [fairPair, ae_add_measure_iff]
  exact ⟨Measure.ae_smul_measure ha (1 / 2 : ℝ≥0∞), Measure.ae_smul_measure hb (1 / 2 : ℝ≥0∞)⟩

-- Keep the half weights nested so no ENNReal arithmetic is needed in this measure identity.
private theorem binary_product_expansion (a b c d : ℝ) :
    (fairPair a b).prod (fairPair c d) =
      (1 / 2 : ℝ≥0∞) •
        ((1 / 2 : ℝ≥0∞) • Measure.dirac (a, c) +
          (1 / 2 : ℝ≥0∞) • Measure.dirac (a, d)) +
      (1 / 2 : ℝ≥0∞) •
        ((1 / 2 : ℝ≥0∞) • Measure.dirac (b, c) +
          (1 / 2 : ℝ≥0∞) • Measure.dirac (b, d)) := by
  unfold fairPair
  rw [Measure.add_prod, Measure.prod_smul_left, Measure.prod_smul_left,
    Measure.prod_add, Measure.prod_add]
  simp only [Measure.prod_smul_right, Measure.dirac_prod_dirac]

private theorem binary_product_integral (f : ℝ × ℝ → ℝ) (a b c d : ℝ) :
    (∫ z, f z ∂(fairPair a b).prod (fairPair c d)) =
      (f (a, c) + f (a, d) + f (b, c) + f (b, d)) / 4 := by
  have hhalf : (1 / 2 : ℝ≥0∞) ≠ ⊤ := by norm_num
  have hi (x y : ℝ) : Integrable f ((1 / 2 : ℝ≥0∞) • Measure.dirac (x, y)) :=
    (integrable_dirac (by finiteness)).smul_measure hhalf
  have ha := (hi a c).add_measure (hi a d)
  have hb := (hi b c).add_measure (hi b d)
  rw [binary_product_expansion,
    integral_add_measure (ha.smul_measure hhalf) (hb.smul_measure hhalf)]
  simp only [integral_smul_measure]
  rw [integral_add_measure (hi a c) (hi a d), integral_add_measure (hi b c) (hi b d)]
  simp only [integral_smul_measure, integral_dirac]
  norm_num [smul_eq_mul] <;> ring

theorem n5_proof : N5 := by
  have hm : Measurable ipwSummand := by
    unfold ipwSummand ipwObserved ipwY1 ipwY0
    fun_prop
  have hgood : ∀ᵐ ω ∂ipwPopulation,
      ω.1 ∈ Ioo (0 : ℝ) 1 ∧
        (ω.2.1 = -1 ∨ ω.2.1 = 1) ∧ (ω.2.2 = 0 ∨ ω.2.2 = 1) := by
    change ∀ᵐ ω ∂uniform01.prod ((fairPair (-1) 1).prod (fairPair 0 1)), _
    apply (Measure.ae_prod_iff_ae_ae (by measurability)).mpr
    filter_upwards [uniform_mem] with u hu
    apply (Measure.ae_prod_iff_ae_ae (by measurability)).mpr
    filter_upwards [fairPair_ae (-1) 1] with b hb
    filter_upwards [fairPair_ae 0 1] with t ht
    exact ⟨hu, hb, ht⟩
  have hbound : ∀ᵐ ω ∂ipwPopulation, ‖ipwSummand ω‖ ≤ 4 := by
    filter_upwards [hgood] with ω hω
    rcases ω with ⟨u, b, t⟩
    rcases hω with ⟨hu, hb, ht⟩
    simp only at hu hb ht
    obtain ⟨hu0, hu1⟩ := hu
    rcases hb with rfl | rfl <;> rcases ht with rfl | rfl <;>
      simp only [ipwSummand, ipwObserved, ipwY1, ipwY0, Real.norm_eq_abs] <;>
      apply abs_le.mpr <;> constructor <;> nlinarith
  have hLp : MemLp ipwSummand 2 ipwPopulation :=
    MemLp.of_bound hm.aestronglyMeasurable 4 hbound
  have hi : Integrable ipwSummand ipwPopulation := hLp.integrable (by norm_num)
  have hi2 : Integrable (fun ω => ipwSummand ω ^ 2) ipwPopulation := hLp.integrable_sq
  have hinner1 (u : ℝ) :
      (∫ bt, ipwSummand (u, bt) ∂(fairPair (-1) 1).prod (fairPair 0 1)) = u := by
    rw [binary_product_integral]
    dsimp [ipwSummand, ipwObserved, ipwY1, ipwY0]
    ring
  have hinner2 (u : ℝ) :
      (∫ bt, ipwSummand (u, bt) ^ 2 ∂(fairPair (-1) 1).prod (fairPair 0 1)) =
        4 + 2 * u ^ 2 := by
    rw [binary_product_integral]
    dsimp [ipwSummand, ipwObserved, ipwY1, ipwY0]
    ring
  have hmean : (∫ ω, ipwSummand ω ∂ipwPopulation) = 1 / 2 := by
    rw [show ipwPopulation = uniform01.prod ((fairPair (-1) 1).prod (fairPair 0 1))
      from rfl, integral_prod _ hi]
    simp only [hinner1]
    exact uniform_first_moment
  have hu2 : Integrable (fun u : ℝ => u ^ 2) uniform01 := by
    apply Integrable.of_bound (by fun_prop) 1
    filter_upwards [uniform_mem] with u hu
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg u)]
    nlinarith [mul_nonneg hu.1.le (sub_nonneg.mpr hu.2.le)]
  have hsecond : (∫ ω, ipwSummand ω ^ 2 ∂ipwPopulation) = 14 / 3 := by
    rw [show ipwPopulation = uniform01.prod ((fairPair (-1) 1).prod (fairPair 0 1))
      from rfl, integral_prod _ hi2]
    simp only [hinner2]
    rw [integral_add (integrable_const 4) (hu2.const_mul 2), integral_const_mul,
      uniform_second_moment]
    norm_num
  have hvar : variance ipwSummand ipwPopulation = 53 / 12 := by
    rw [variance_eq_sub hLp]
    change (∫ ω, ipwSummand ω ^ 2 ∂ipwPopulation) -
      (∫ ω, ipwSummand ω ∂ipwPopulation) ^ 2 = 53 / 12
    rw [hsecond, hmean]
    norm_num
  change Measurable ipwSummand ∧ MemLp ipwSummand 2 ipwPopulation ∧
    (∫ ω, ipwSummand ω ∂ipwPopulation) = 1 / 2 ∧
      variance ipwSummand ipwPopulation = 53 / 12
  exact ⟨hm, hLp, hmean, hvar⟩

end

end AronowAudit.P017.Wave1.PropositionOne
