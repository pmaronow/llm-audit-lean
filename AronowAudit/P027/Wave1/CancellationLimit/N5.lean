import AronowAudit.P027.Wave1.CancellationLimitBlueprint

/-! The deterministic weighted square estimate, summed over the phases. -/

namespace AronowAudit.P027.Wave1.CancellationLimit

set_option autoImplicit false
noncomputable section
open AronowAudit.P027 MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
attribute [local instance] Classical.propDecidable

theorem n5_proof : N5 := by
  intro ι _ a R t ht
  have hpoint (i : ι) : |-(a i + R i)^2 + (a i)^2| ≤
      t * (a i)^2 + (1 + 1 / t) * (R i)^2 := by
    have hclear : t * (t * (a i)^2 + (R i)^2 / t) =
        (t * a i)^2 + (R i)^2 := by
      field_simp [ht.ne'] <;> ring
    have hplus : 2 * a i * R i ≤ t * (a i)^2 + (R i)^2 / t := by
      apply (mul_le_mul_iff_of_pos_left ht).mp
      rw [hclear]
      nlinarith only [sq_nonneg (t * a i - R i)]
    have hminus : -(2 * a i * R i) ≤ t * (a i)^2 + (R i)^2 / t := by
      apply (mul_le_mul_iff_of_pos_left ht).mp
      rw [hclear]
      nlinarith only [sq_nonneg (t * a i + R i)]
    have hdiv : (R i)^2 / t = (1 / t) * (R i)^2 := by ring
    rw [hdiv] at hplus hminus
    apply abs_le.mpr
    constructor <;> nlinarith only [hplus, hminus, sq_nonneg (R i)]
  calc
    |(-∑ i, (a i + R i)^2) + ∑ i, (a i)^2| =
        |∑ i, (-(a i + R i)^2 + (a i)^2)| := by
      rw [Finset.sum_add_distrib, Finset.sum_neg_distrib]
    _ ≤ ∑ i, |-(a i + R i)^2 + (a i)^2| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, (t * (a i)^2 + (1 + 1 / t) * (R i)^2) :=
      Finset.sum_le_sum (fun i _ => hpoint i)
    _ = t * ∑ i, (a i)^2 + (1 + 1 / t) * ∑ i, (R i)^2 := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]

end
end AronowAudit.P027.Wave1.CancellationLimit
