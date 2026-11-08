import SAP.P003b.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P003b.WH.W1.P.T35_L1

open SAP.P003b
open SAP.P003b.WH.W1
attribute [local instance 0] Classical.propDecidable

private theorem excluded (K : ℕ) (initial : (Fin 3 × Fin 3) → Fin K → Assignment 2 1)
    (seeds : (Fin 3 × Fin 3) → Fin 2 → Fin K →
      (Fin (Nat.factorial 2) × Fin (Nat.factorial 2))) :
    w1T35Theta w1T35Population ∉
      w1LiteralSet (1 / 4) w1T35Theta (fun _ _ => 0) ⟨0,1,0,1⟩ initial seeds := by
  intro hm
  simp only [w1LiteralSet, Set.mem_setOf_eq] at hm
  rcases hm with ⟨ij, v, hbase, k, hk, hka, hkd, hpossible, htheta, hrank⟩
  have hvector : reuseVector v k = w1T35Population := by
    have hθ : w1T35Theta (reuseVector v k) = 1 := by
      simpa [w1T35Theta, w1T35Population] using htheta.symm
    by_cases heq : reuseVector v k = w1T35Population
    · exact heq
    · have hfalse :
          w1T35Theta (reuseVector v k) = 0 := by
        simp only [w1T35Theta, if_neg heq]
      rw [hfalse] at hθ
      norm_num at hθ
  cases ij with
  | mk ix jx =>
    fin_cases ix
    · have hb : w1LiteralBase ⟨0,1,0,1⟩
          ((candidateNumerators ⟨0,1,0,1⟩).reverse[0]!) =
            some (1, (⟨0,1,0,1⟩ : Counts)) := by decide +kernel
      rw [hb] at hbase
      simp only [Option.some.injEq, Prod.mk.injEq] at hbase
      rcases hbase with ⟨_, rfl⟩
      have hk0 : k = 0 := Nat.eq_zero_of_le_zero (by simpa using hka)
      subst k
      simp [reuseVector, w1T35Population] at hvector
    · have hb : w1LiteralBase ⟨0,1,0,1⟩
          ((candidateNumerators ⟨0,1,0,1⟩).reverse[1]!) =
            some (0, (⟨0,0,0,2⟩ : Counts)) := by decide +kernel
      rw [hb] at hbase
      simp only [Option.some.injEq, Prod.mk.injEq] at hbase
      rcases hbase with ⟨_, rfl⟩
      have hk0 : k = 0 := Nat.eq_zero_of_le_zero (by simpa using hka)
      subst k
      simp [reuseVector, w1T35Population] at hvector
    · have hb : w1LiteralBase ⟨0,1,0,1⟩
          ((candidateNumerators ⟨0,1,0,1⟩).reverse[2]!) =
            some (0, (⟨0,0,1,1⟩ : Counts)) := by decide +kernel
      rw [hb] at hbase
      simp only [Option.some.injEq, Prod.mk.injEq] at hbase
      rcases hbase with ⟨_, rfl⟩
      have hk0 : k = 0 := Nat.eq_zero_of_le_zero (by simpa using hka)
      subst k
      simp [reuseVector, w1T35Population] at hvector

end SAP.P003b.WH.W1.P.T35_L1

theorem SAP.P003b.WH.W1.T35_L1_proof : SAP.P003b.WH.W1.T35_L1 := by
  intro K hK initial seeds
  constructor
  · exact SAP.P003b.WH.W1.P.T35_L1.excluded K initial seeds
  · simp only [w1LiteralSet, Set.mem_setOf_eq]
    refine ⟨(⟨1, by decide⟩, ⟨1, by decide⟩), w1T35Population, ?_, 0,
      by decide, by decide, by decide, ?_, ?_, ?_⟩
    · decide +kernel
    · have hp : Possible ⟨1,0,1,0⟩ w1T35Population := by decide +kernel
      simpa [reuseVector, w1T35Population] using hp
    · simp [reuseVector, w1T35Theta, w1T35Population]
    · rw [rankZero]
      norm_num
