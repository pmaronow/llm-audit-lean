import AronowAudit.P002.Wave1.E61EigenvalueBlueprint
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Option

namespace AronowAudit.P002.Wave1.E61Eigenvalue
noncomputable section
open scoped BigOperators ENNReal Matrix Topology
open Filter MeasureTheory
attribute [local instance] Classical.propDecidable

/-- Expand the quadratic error, then use the triangle inequality and Cauchy--Schwarz. -/
theorem n11_proof : N11 := by
  intro k H G D hentry b
  have hDnonneg : 0 ≤ D :=
    (abs_nonneg (H none none - G none none)).trans (hentry none none)
  let L : ℝ := ∑ s, |b s|
  have hCS : L ^ 2 ≤ ((k : ℝ) + 1) * normSq b := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq
      (Finset.univ : Finset (Option (Fin k))) (fun _ => (1 : ℝ)) (fun s => |b s|)
    simpa [L, normSq, Fintype.card_option, sq_abs] using h
  have hform (M : Matrix (Option (Fin k)) (Option (Fin k)) ℝ) :
      dotProduct b (M *ᵥ b) = ∑ s, ∑ t, b s * M s t * b t := by
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]
  have hdifference :
      dotProduct b (H *ᵥ b) - dotProduct b (G *ᵥ b) =
        ∑ s, ∑ t, b s * (H s t - G s t) * b t := by
    rw [hform H, hform G, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro s _hs
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro t _ht
    ring
  have htriangle :
      |∑ s, ∑ t, b s * (H s t - G s t) * b t| ≤
        ∑ s, ∑ t, |b s| * D * |b t| := by
    calc
      |∑ s, ∑ t, b s * (H s t - G s t) * b t| ≤
          ∑ s, |∑ t, b s * (H s t - G s t) * b t| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ s, ∑ t, |b s * (H s t - G s t) * b t| := by
        apply Finset.sum_le_sum
        intro s _hs
        exact Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ s, ∑ t, |b s| * D * |b t| := by
        apply Finset.sum_le_sum
        intro s _hs
        apply Finset.sum_le_sum
        intro t _ht
        simp only [abs_mul]
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (hentry s t) (abs_nonneg _)) (abs_nonneg _)
  have hfactor : (∑ s, ∑ t, |b s| * D * |b t|) = D * L ^ 2 := by
    calc
      (∑ s, ∑ t, |b s| * D * |b t|) =
          (∑ s, |b s| * D) * (∑ t, |b t|) := by
        simp only [Finset.sum_mul, Finset.mul_sum]
        exact Finset.sum_comm
      _ = D * L ^ 2 := by
        rw [← Finset.sum_mul]
        dsimp only [L]
        ring
  calc
    |dotProduct b (H *ᵥ b) - dotProduct b (G *ᵥ b)| =
        |∑ s, ∑ t, b s * (H s t - G s t) * b t| := congrArg abs hdifference
    _ ≤ ∑ s, ∑ t, |b s| * D * |b t| := htriangle
    _ = D * L ^ 2 := hfactor
    _ ≤ D * (((k : ℝ) + 1) * normSq b) := mul_le_mul_of_nonneg_left hCS hDnonneg
    _ = ((k : ℝ) + 1) * D * normSq b := by ring

end
end AronowAudit.P002.Wave1.E61Eigenvalue
