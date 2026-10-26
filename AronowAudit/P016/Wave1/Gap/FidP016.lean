import AronowAudit.P016.P016_Interference

open scoped BigOperators

namespace AronowAudit.P016.Wave1

/-- T10(d): symmetry identifies the column sums with the row sums,
including each diagonal entry once, without a zero-diagonal hypothesis. -/
theorem t10_symmetric_network
    {n : ℕ} (S : Fin n → Fin n → ℝ)
    (hS : ∀ i j, S i j = S j i)
    (hbin : ∀ i j, S i j = 0 ∨ S i j = 1)
    (z : AronowAudit.P016.Assignment n)
    (h0 : 0 < AronowAudit.P016.groupSize z false)
    (h1 : 0 < AronowAudit.P016.groupSize z true)
    (i : Fin n) :
    AronowAudit.P016.treatedNeighbors S z i =
      (∑ j, S i j * AronowAudit.P016.bit (z j)) ∧
    AronowAudit.P016.degree S i = (∑ j, S i j) := by
  constructor
  · change (∑ j, AronowAudit.P016.bit (z j) * S j i) =
      ∑ j, S i j * AronowAudit.P016.bit (z j)
    apply Finset.sum_congr rfl
    intro j _
    rw [hS j i, mul_comm]
  · change (∑ j, S j i) = ∑ j, S i j
    apply Finset.sum_congr rfl
    intro j _
    exact hS j i

end AronowAudit.P016.Wave1
