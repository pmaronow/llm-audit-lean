import AronowAudit.P002.Wave1.E61EigenvalueBlueprint

namespace AronowAudit.P002.Wave1.E61Eigenvalue
noncomputable section
open scoped BigOperators ENNReal Matrix Topology
open Filter MeasureTheory
attribute [local instance] Classical.propDecidable

universe u

/-- The pointwise inequality `2 (uv)² ≤ u⁴ + v⁴` gives the required fourth-moment
bound directly, including both intercept cases. -/
theorem n6_proof : N6 := by
  intro n k P δ e A B r hXi s t
  obtain ⟨hD, -, -, -, -, -, -, -, hfour, -⟩ := hXi
  have hn : (0 : ℝ) < n := by
    exact_mod_cast (show 0 < n by have := hD.1; omega)
  have hfour_aug (v : Option (Fin k)) :
      (∑ i, augmented P.x i v ^ 4) ≤ (n : ℝ) * max 1 A := by
    cases v with
    | none =>
        simpa only [augmented, one_pow, Finset.sum_const, Finset.card_univ,
          Fintype.card_fin, nsmul_eq_mul, mul_one] using
          mul_le_mul_of_nonneg_left (le_max_left (1 : ℝ) A) hn.le
    | some v =>
        have hv : (∑ i, P.x i v ^ 4) ≤ A * (n : ℝ) :=
          (div_le_iff₀ hn).mp (hfour v)
        have hA : A ≤ max 1 A := le_max_right _ _
        change (∑ i, P.x i v ^ 4) ≤ (n : ℝ) * max 1 A
        calc
          _ ≤ A * (n : ℝ) := hv
          _ ≤ max 1 A * (n : ℝ) := mul_le_mul_of_nonneg_right hA hn.le
          _ = _ := mul_comm _ _
  have hpoint :
      2 * (∑ i, (augmented P.x i s * augmented P.x i t) ^ 2) ≤
        (∑ i, augmented P.x i s ^ 4) + (∑ i, augmented P.x i t ^ 4) := by
    calc
      _ = ∑ i, 2 * (augmented P.x i s * augmented P.x i t) ^ 2 := by
        rw [Finset.mul_sum]
      _ ≤ ∑ i, (augmented P.x i s ^ 4 + augmented P.x i t ^ 4) := by
        apply Finset.sum_le_sum
        intro i _
        nlinarith [sq_nonneg (augmented P.x i s ^ 2 - augmented P.x i t ^ 2)]
      _ = _ := by rw [Finset.sum_add_distrib]
  unfold mean
  apply (div_le_iff₀ hn).2
  nlinarith [hfour_aug s, hfour_aug t]

end
end AronowAudit.P002.Wave1.E61Eigenvalue
