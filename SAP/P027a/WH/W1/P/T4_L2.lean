import SAP.P027a.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P027a.WH.W1.P.T4_L2

open scoped BigOperators

lemma sum_sq_sub_const (n : ℕ) (x : ℝ) (z : Fin n → ℝ) :
    (∑ i, (x - z i) ^ 2) =
      (n : ℝ) * x ^ 2 - 2 * x * (∑ i, z i) + ∑ i, (z i) ^ 2 := by
  simp_rw [sub_sq]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  have hfactor : (∑ i : Fin n, 2 * x * z i) = 2 * x * (∑ i : Fin n, z i) := by
    rw [← Finset.mul_sum]
  rw [hfactor]

lemma edge_sum_succ (n : ℕ) (y : Fin (n + 1) → ℝ) :
    (∑ i : Fin (n + 1), ∑ j : Fin (n + 1),
      if i < j then (y i - y j) ^ 2 else 0) =
      (∑ i : Fin n, ∑ j : Fin n,
        if i < j then (y i.succ - y j.succ) ^ 2 else 0) +
        ∑ j : Fin n, (y 0 - y j.succ) ^ 2 := by
  simp [Fin.sum_univ_succ] <;> ac_rfl

end SAP.P027a.WH.W1.P.T4_L2

theorem SAP.P027a.WH.W1.T4_L2_proof : SAP.P027a.WH.W1.T4_L2 := by
  intro n y
  induction n with
  | zero => simp
  | succ n ih =>
      let z : Fin n → ℝ := fun i => y i.succ
      have hsum : (∑ i : Fin (n + 1), y i) = y 0 + ∑ i : Fin n, z i := by
        simp [z, Fin.sum_univ_succ]
      have hsquares : (∑ i : Fin (n + 1), (y i) ^ 2) =
          y 0 ^ 2 + ∑ i : Fin n, (z i) ^ 2 := by
        simp [z, Fin.sum_univ_succ]
      have hEdges := SAP.P027a.WH.W1.P.T4_L2.edge_sum_succ n y
      have hAlgebra :
          (↑(n + 1) : ℝ) * (y 0 ^ 2 + ∑ i : Fin n, (z i) ^ 2) -
              (y 0 + ∑ i : Fin n, z i) ^ 2 =
            ((n : ℝ) * (∑ i : Fin n, (z i) ^ 2) -
                (∑ i : Fin n, z i) ^ 2) + ∑ i : Fin n, (y 0 - z i) ^ 2 := by
        rw [SAP.P027a.WH.W1.P.T4_L2.sum_sq_sub_const]
        push_cast
        ring
      rw [hsquares, hsum, hEdges, ← ih]
      exact hAlgebra
