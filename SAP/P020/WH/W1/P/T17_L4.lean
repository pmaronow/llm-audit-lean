import SAP.P020.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P020.WH.W1.P.T17_L4

open SAP.P020.WH.W1
open scoped BigOperators

lemma copiedN_succ (P : ClusterPopulation) (h : ℕ) :
    W1CopiedN P (h + 1) = W1CopiedN P h + populationSize P := by
  simp [W1CopiedN, Fintype.sum_prod_type, populationSize, Nat.add_mul]

lemma copiedArmSum_succ (P : ClusterPopulation) (ω : W1Path P) (a : Bool) (r : ℕ) :
    (∑ i : Fin (r + 2), armSize P a (ω i.val).val) =
      (∑ i : Fin (r + 1), armSize P a (ω i.val).val) +
        armSize P a (ω (r + 1)).val := by
  rw [Fin.sum_univ_castSucc]
  simp

lemma local_populationSize_pos (P : ClusterPopulation) : 0 < SAP.P020.populationSize P := by
  change 0 < AronowAudit.P020.populationSize (SAP.P020.Bridge.toPopulation P)
  exact AronowAudit.P020.populationSize_pos (SAP.P020.Bridge.toPopulation P)

lemma local_arm_size_pos (P : ClusterPopulation) (a : Bool) (s : W1Assignment P) :
    0 < SAP.P020.armSize P a s.val := by
  change 0 < AronowAudit.P020.armSize (SAP.P020.Bridge.toPopulation P) a s.val
  apply AronowAudit.P020.arm_size_pos (SAP.P020.Bridge.toPopulation P) a s.val
  change s.val ∈ AronowAudit.P020.assignments (SAP.P020.Bridge.toPopulation P)
  exact s.property

lemma local_replicated_size (P : ClusterPopulation) (h : ℕ) (hh : 0 < h) :
    SAP.P020.populationSize (SAP.P020.replicateWithin P h hh) =
      h * SAP.P020.populationSize P := by
  simp [SAP.P020.populationSize, SAP.P020.replicateWithin, Finset.mul_sum]

lemma local_replicated_arm_size (P : ClusterPopulation) (h : ℕ) (hh : 0 < h)
    (a : Bool) (s : W1Assignment P) :
    SAP.P020.armSize (SAP.P020.replicateWithin P h hh) a s.val =
      (h : ℝ) * SAP.P020.armSize P a s.val := by
  cases a <;> simp [SAP.P020.armSize, SAP.P020.armSum,
    SAP.P020.replicateWithin, Nat.cast_mul, ← Finset.mul_sum]

end SAP.P020.WH.W1.P.T17_L4

open SAP.P020.WH.W1.P.T17_L4

theorem SAP.P020.WH.W1.T17_L4_proof : SAP.P020.WH.W1.T17_L4 := by
  intro P
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply strictMono_nat_of_lt_succ
    intro r
    rw [copiedN_succ P (r + 1)]
    exact Nat.lt_add_of_pos_right (local_populationSize_pos P)
  · intro ω a
    apply strictMono_nat_of_lt_succ
    intro r
    rw [copiedArmSum_succ P ω a r]
    have hPos := local_arm_size_pos P a (ω (r + 1))
    linarith
  · apply strictMono_nat_of_lt_succ
    intro r
    rw [local_replicated_size P (r + 1) (Nat.succ_pos r),
      local_replicated_size P (r + 2) (Nat.succ_pos (r + 1))]
    have hN : 0 < SAP.P020.populationSize P := local_populationSize_pos P
    nlinarith
  · intro s a
    apply strictMono_nat_of_lt_succ
    intro r
    rw [local_replicated_arm_size P (r + 1) (Nat.succ_pos r) a s,
      local_replicated_arm_size P (r + 2) (Nat.succ_pos (r + 1)) a s]
    have hA : 0 < SAP.P020.armSize P a s.val := local_arm_size_pos P a s
    push_cast
    nlinarith
