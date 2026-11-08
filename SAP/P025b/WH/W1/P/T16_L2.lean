import SAP.P025b.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P025b.WH.W1.P.T16_L2

open scoped BigOperators

end SAP.P025b.WH.W1.P.T16_L2

theorem SAP.P025b.WH.W1.T16_L2_proof : SAP.P025b.WH.W1.T16_L2 := by
  classical
  intro n₀ n₁ κ κ' hκ hκ' d e
  constructor
  · intro i
    simp only [SAP.P025b.inclusion, SAP.P025b.designExpectation,
      SAP.P025b.sumDesign]
    simp_rw [Fintype.sum_prod_type]
    simp
    have htotal (x : κ) :
        (∑ y : κ', d.probability x * e.probability y) = d.probability x := by
      rw [← Finset.mul_sum, e.total, mul_one]
    simp_rw [htotal]
  · intro i
    simp only [SAP.P025b.inclusion, SAP.P025b.designExpectation,
      SAP.P025b.sumDesign]
    simp_rw [Fintype.sum_prod_type]
    simp
    rw [Finset.sum_comm]
    have hfactor (x : κ) (y : κ') :
        (if i ∈ e.sample y then d.probability x * e.probability y else 0) =
          d.probability x * (if i ∈ e.sample y then e.probability y else 0) := by
      by_cases h : i ∈ e.sample y <;> simp [h]
    simp_rw [hfactor]
    have htotal (y : κ') :
        (∑ x : κ, d.probability x * (if i ∈ e.sample y then e.probability y else 0)) =
          (if i ∈ e.sample y then e.probability y else 0) := by
      rw [← Finset.sum_mul, d.total, one_mul]
    simp_rw [htotal]
