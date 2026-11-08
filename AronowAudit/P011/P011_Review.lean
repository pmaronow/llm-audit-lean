import AronowAudit.P011.P011_Audit

/-!
Finite components of the broader repair accepted in the 19 October review.
This proves the capacity-based PSD route and invariance of maximization under
a graph-independent correction. The asymptotic compatible-graph construction,
residual rates, and general condition (C) are separate remaining obligations.
-/

namespace AronowAudit.P011

open scoped BigOperators
noncomputable section

/-- The known-edge capacity matrix K_R = I + A_R + diag(h-r).
Subtraction is in the reals, so no truncated natural subtraction is hidden. -/
def recruitmentCapacityMatrix {n : ℕ} (R : Graph n) (h : Fin n → ℕ) :
    Matrix (Fin n) (Fin n) ℝ :=
  oracleMatrix R + Matrix.diagonal (fun i => (h i : ℝ) - (degree R i : ℝ))

/-- The signless graph Laplacian A_R + diag(r) is PSD, including an empty
graph and isolated vertices. -/
theorem signless_laplacian_psd {n : ℕ} (R : Graph n) :
    PSD (adjacency R + Matrix.diagonal (fun i => (degree R i : ℝ))) := by
  constructor
  · intro i j
    have hs : adjacency R i j = adjacency R j i := by
      unfold adjacency
      rw [R.property.1 i j]
    by_cases hij : i = j
    · subst j; rfl
    · simp [Matrix.add_apply, Matrix.diagonal_apply, hij, Ne.symm hij, hs]
  · intro x
    rw [quadratic_add, quadratic_diagonal]
    have hb := (abs_le.mp (adjacency_quadratic_bound R x)).1
    linarith

/-- Exact finite decomposition used in the accepted h_i ≥ 2r_i-1 route. -/
theorem recruitmentCapacityMatrix_decomposition {n : ℕ} (R : Graph n)
    (h : Fin n → ℕ) :
    recruitmentCapacityMatrix R h =
      (adjacency R + Matrix.diagonal (fun i => (degree R i : ℝ))) +
        Matrix.diagonal (fun i => 1 + (h i : ℝ) - 2 * (degree R i : ℝ)) := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp only [recruitmentCapacityMatrix, oracleMatrix, Matrix.add_apply,
      Matrix.one_apply_eq, Matrix.diagonal_apply_eq]
    ring
  · simp [recruitmentCapacityMatrix, oracleMatrix, Matrix.add_apply,
      Matrix.one_apply, Matrix.diagonal_apply, hij, Ne.symm hij]

/-- Review's sufficient capacity condition implies K_R is PSD. This finite
matrix statement alone does not claim oracle consistency or the full
asymptotic conservativeness theorem. -/
theorem recruitmentCapacityMatrix_psd {n : ℕ} (R : Graph n)
    (h : Fin n → ℕ) (hc : ∀ i, 2 * (degree R i : ℝ) - 1 ≤ (h i : ℝ)) :
    PSD (recruitmentCapacityMatrix R h) := by
  rw [recruitmentCapacityMatrix_decomposition]
  apply psd_add _ _ (signless_laplacian_psd R)
  apply psd_diagonal
  intro i
  linarith [hc i]

/-- A fixed correction added after graph maximization preserves every
maximizer, regardless of ties. The constant can be vᵀQv for a fixed input v. -/
theorem maximizes_add_constant_iff {n : ℕ} (R : Graph n) (d : Fin n → ℕ)
    (f : Graph n → ℝ) (c : ℝ) (A : Graph n) :
    Maximizes R d (fun B => f B + c) A ↔ Maximizes R d f A := by
  constructor
  · rintro ⟨ha, hm⟩
    exact ⟨ha, fun B hB => (add_le_add_iff_right c).mp (hm B hB)⟩
  · rintro ⟨ha, hm⟩
    exact ⟨ha, fun B hB => (add_le_add_iff_right c).mpr (hm B hB)⟩

/-- A PSD capacity matrix makes every normalized relevant mean direction
nonnegative, for each finite n. No restriction on the mean vector is added. -/
theorem capacity_mean_direction_nonnegative {n : ℕ} (R : Graph n)
    (h : Fin n → ℕ) (hc : ∀ i, 2 * (degree R i : ℝ) - 1 ≤ (h i : ℝ))
    (δ : Fin n → ℝ) :
    0 ≤ quadratic (recruitmentCapacityMatrix R h) δ / (n : ℝ) := by
  exact div_nonneg ((recruitmentCapacityMatrix_psd R h hc).2 δ) (Nat.cast_nonneg n)

end
end AronowAudit.P011

#print axioms AronowAudit.P011.signless_laplacian_psd
#print axioms AronowAudit.P011.recruitmentCapacityMatrix_decomposition
#print axioms AronowAudit.P011.recruitmentCapacityMatrix_psd
#print axioms AronowAudit.P011.maximizes_add_constant_iff
#print axioms AronowAudit.P011.capacity_mean_direction_nonnegative
