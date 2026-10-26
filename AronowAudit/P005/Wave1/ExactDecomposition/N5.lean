import AronowAudit.P005.Wave1.ExactDecompositionBlueprint

set_option autoImplicit false

namespace AronowAudit.P005.Wave1.ExactDecomposition

open AronowAudit.P005 Finset
open scoped BigOperators

noncomputable section

theorem n5_proof : N5 := by
  classical
  intro hcomp htreated n d m P hn hm hmn hx y
  have hcpos : 0 < n - m := Nat.sub_pos_of_lt hmn
  have hcle : n - m ≤ n := Nat.sub_le n m
  have hcast : ((n - m : ℕ) : ℝ) = (n : ℝ) - m := Nat.cast_sub hmn.le
  rw [hcomp n m hmn.le (fun S => dot (xMean P S) (armNu1 P S y)),
    htreated P hn hcpos hcle hx y]
  rw [hcast]
  congr 1
  ring

end

end AronowAudit.P005.Wave1.ExactDecomposition
