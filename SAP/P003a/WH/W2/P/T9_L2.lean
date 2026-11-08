import SAP.P003a.WH.W2.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P003a.WH.W2.P.T9_L2

end SAP.P003a.WH.W2.P.T9_L2

open scoped BigOperators
open SAP.P003a.WH.W2
attribute [local instance 0] Classical.propDecidable

theorem SAP.P003a.WH.W2.T9_L2_proof : SAP.P003a.WH.W2.T9_L2 := by
  have hsum : HasSum w2BSumMass (1 : ℝ) := by
    unfold w2BSumMass
    convert (((hasSum_ite_eq (-1 : ℤ) (1/3 : ℝ)).add
      (hasSum_ite_eq (0 : ℤ) (1/6 : ℝ))).add
      (hasSum_ite_eq (1 : ℤ) (1/6 : ℝ))).add
      (hasSum_ite_eq (2 : ℤ) (1/3 : ℝ)) using 1 <;> norm_num
  have hmomentFun : (fun j : ℤ => (j : ℝ) * w2BSumMass j) =
      (fun j => if j = -1 then (-1/3 : ℝ) else
        if j = 1 then 1/6 else if j = 2 then 2/3 else 0) := by
    funext j
    by_cases h0 : j = -1
    · subst j
      norm_num [w2BSumMass]
    by_cases h1 : j = 0
    · subst j
      norm_num [w2BSumMass]
    by_cases h2 : j = 1
    · subst j
      norm_num [w2BSumMass]
    by_cases h3 : j = 2
    · subst j
      norm_num [w2BSumMass]
    simp [w2BSumMass, h0, h1, h2, h3]
  have hmoment : HasSum (fun j : ℤ => (j : ℝ) * w2BSumMass j) (1/2 : ℝ) := by
    rw [hmomentFun]
    convert ((hasSum_ite_eq (-1 : ℤ) (-1/3 : ℝ)).add
      (hasSum_ite_eq (1 : ℤ) (1/6 : ℝ))).add
      (hasSum_ite_eq (2 : ℤ) (2/3 : ℝ)) using 1
    · funext j
      by_cases h0 : j = -1 <;> by_cases h1 : j = 1 <;>
        by_cases h2 : j = 2 <;> simp_all
    · norm_num
  have hnonneg : ∀ j : ℤ, 0 ≤ w2BSumMass j := by
    intro j
    unfold w2BSumMass
    split_ifs <;> norm_num
  have hsym : ∀ j : ℤ, w2BSumMass (1-j) = w2BSumMass j := by
    intro j
    by_cases h0 : j = -1
    · subst j
      norm_num [w2BSumMass]
    by_cases h1 : j = 0
    · subst j
      norm_num [w2BSumMass]
    by_cases h2 : j = 1
    · subst j
      norm_num [w2BSumMass]
    by_cases h3 : j = 2
    · subst j
      norm_num [w2BSumMass]
    have hr0 : 1-j ≠ -1 := by omega
    have hr1 : 1-j ≠ 0 := by omega
    have hr2 : 1-j ≠ 1 := by omega
    have hr3 : 1-j ≠ 2 := by omega
    simp [w2BSumMass, h0, h1, h2, h3, hr0, hr1, hr2, hr3]
  refine ⟨⟨hnonneg, hsum.summable, hsum.tsum_eq, hmoment.summable⟩,
    hmoment.tsum_eq, hsym⟩

