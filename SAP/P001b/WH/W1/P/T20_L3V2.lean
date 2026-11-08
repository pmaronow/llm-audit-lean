import SAP.P001b.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal Classical

local instance : MeasurableSpace (ℕ × Bool) := ⊤

namespace SAP.P001b.WH.W1.P.T20_L3V2

noncomputable section

private def weight (z : ℕ × Bool) : ℝ :=
  if z.2 then W1OverlapT z.1 else W1OverlapC z.1

private theorem donor_weights :
    Summable W1OverlapT ∧ Summable W1OverlapC ∧
      (∑' k, W1OverlapT k) = 1 / 2 ∧ (∑' k, W1OverlapC k) = 1 / 2 := by
  obtain ⟨hsT, hsC, ht, hc, _, _⟩ :=
    AronowAudit.P001.complete_overlap_without_uniform_positivity
  change Summable W1OverlapT at hsT
  change Summable W1OverlapC at hsC
  change (∑' k, W1OverlapT k) = 1 / 2 at ht
  change (∑' k, W1OverlapC k) = 1 / 2 at hc
  exact ⟨hsT, hsC, ht, hc⟩

private theorem weight_nonneg (z : ℕ × Bool) : 0 ≤ weight z := by
  dsimp [weight, W1OverlapT, W1OverlapC]
  split_ifs <;> positivity

private theorem weight_summable : Summable weight := by
  obtain ⟨hsT, hsC, _, _⟩ := donor_weights
  apply (summable_prod_of_nonneg (fun z => weight_nonneg z)).2
  constructor
  · intro k
    exact Summable.of_finite
  · simpa [weight, tsum_fintype, Fintype.sum_bool] using hsT.add hsC

private theorem weight_tsum : (∑' z : ℕ × Bool, weight z) = 1 := by
  obtain ⟨hsT, hsC, ht, hc⟩ := donor_weights
  rw [weight_summable.tsum_prod]
  calc
    (∑' k : ℕ, ∑' b : Bool, weight (k, b)) =
        (∑' k : ℕ, (W1OverlapT k + W1OverlapC k)) := by
      congr 1
      funext k
      simp [weight, tsum_fintype, Fintype.sum_bool]
    _ = 1 := by
      rw [Summable.tsum_add hsT hsC, ht, hc]
      norm_num

private theorem eval_measure (A : Set (ℕ × Bool)) :
    W1GeometricLaw A = ∑' z : ℕ × Bool,
      ENNReal.ofReal (if z ∈ A then weight z else 0) := by
  rw [W1GeometricLaw, Measure.sum_apply _ (by trivial)]
  apply tsum_congr
  intro z
  by_cases hz : z ∈ A <;> simp [weight, Measure.smul_apply, hz]

private theorem eval_probability (A : Set (ℕ × Bool)) :
    probability W1GeometricLaw A = ∑' z : ℕ × Bool,
      if z ∈ A then weight z else 0 := by
  unfold probability
  rw [eval_measure A, ENNReal.tsum_toReal_eq (fun _ => ENNReal.ofReal_ne_top)]
  apply tsum_congr
  intro z
  by_cases hz : z ∈ A
  · simp [hz, ENNReal.toReal_ofReal, weight_nonneg]
  · simp [hz]

private theorem arm_treated_tsum (A : Set (ℕ × Bool))
    (hA : ∀ z, z ∈ A ↔ W1BinaryValue z.2 = 1) :
    Summable (fun z : ℕ × Bool => if z ∈ A then weight z else 0) := by
  obtain ⟨hsT, _, _, _⟩ := donor_weights
  apply (summable_prod_of_nonneg (fun z => by
    split_ifs
    · exact weight_nonneg z
    · exact le_rfl)).2
  constructor
  · intro k
    exact Summable.of_finite
  · simpa [hA, W1BinaryValue, weight, tsum_fintype, Fintype.sum_bool] using hsT

private theorem arm_control_tsum (A : Set (ℕ × Bool))
    (hA : ∀ z, z ∈ A ↔ W1BinaryValue z.2 = 0) :
    Summable (fun z : ℕ × Bool => if z ∈ A then weight z else 0) := by
  obtain ⟨_, hsC, _, _⟩ := donor_weights
  apply (summable_prod_of_nonneg (fun z => by
    split_ifs
    · exact weight_nonneg z
    · exact le_rfl)).2
  constructor
  · intro k
    exact Summable.of_finite
  · simpa [hA, W1BinaryValue, weight, tsum_fintype, Fintype.sum_bool] using hsC

private theorem arm_treated_eval (A : Set (ℕ × Bool))
    (hA : ∀ z, z ∈ A ↔ W1BinaryValue z.2 = 1) :
    probability W1GeometricLaw A = ∑' k : ℕ, W1OverlapT k := by
  have hs := arm_treated_tsum A hA
  rw [eval_probability A, hs.tsum_prod]
  congr 1
  funext k
  simp [hA, W1BinaryValue, weight, tsum_fintype, Fintype.sum_bool]

private theorem arm_control_eval (A : Set (ℕ × Bool))
    (hA : ∀ z, z ∈ A ↔ W1BinaryValue z.2 = 0) :
    probability W1GeometricLaw A = ∑' k : ℕ, W1OverlapC k := by
  have hs := arm_control_tsum A hA
  rw [eval_probability A, hs.tsum_prod]
  congr 1
  funext k
  simp [hA, W1BinaryValue, weight, tsum_fintype, Fintype.sum_bool]

end
end SAP.P001b.WH.W1.P.T20_L3V2

theorem SAP.P001b.WH.W1.T20_L3V2_proof : SAP.P001b.WH.W1.T20_L3V2 := by
  obtain ⟨hsT, hsC, ht, hc⟩ := SAP.P001b.WH.W1.P.T20_L3V2.donor_weights
  constructor
  · constructor
    change W1GeometricLaw Set.univ = 1
    rw [SAP.P001b.WH.W1.P.T20_L3V2.eval_measure Set.univ]
    simp only [Set.mem_univ, if_true]
    rw [← ENNReal.ofReal_tsum_of_nonneg
      SAP.P001b.WH.W1.P.T20_L3V2.weight_nonneg
      SAP.P001b.WH.W1.P.T20_L3V2.weight_summable,
      SAP.P001b.WH.W1.P.T20_L3V2.weight_tsum]
    norm_num
  constructor
  · intro k
    constructor
    · change probability W1GeometricLaw
        {z : ℕ × Bool | Prod.fst z = k ∧ W1BinaryValue z.2 = 1} = W1OverlapT k
      have hset : {z : ℕ × Bool | Prod.fst z = k ∧ W1BinaryValue z.2 = 1} =
          {(k, true)} := by
        ext z
        rcases z with ⟨n, b⟩
        cases b <;> simp [W1BinaryValue]
      rw [hset]
      unfold probability
      rw [W1GeometricLaw, Measure.sum_smul_dirac_singleton]
      simp [ENNReal.toReal_ofReal, W1OverlapT]
    · change probability W1GeometricLaw
        {z : ℕ × Bool | Prod.fst z = k ∧ W1BinaryValue z.2 = 0} = W1OverlapC k
      have hset : {z : ℕ × Bool | Prod.fst z = k ∧ W1BinaryValue z.2 = 0} =
          {(k, false)} := by
        ext z
        rcases z with ⟨n, b⟩
        cases b <;> simp [W1BinaryValue]
      rw [hset]
      unfold probability
      rw [W1GeometricLaw, Measure.sum_smul_dirac_singleton]
      simp [ENNReal.toReal_ofReal, W1OverlapC]
  constructor
  · have hA : ∀ z : ℕ × Bool, z ∈ {z | W1BinaryValue z.2 = 0} ↔
        W1BinaryValue z.2 = 0 := by intro z; rfl
    rw [SAP.P001b.WH.W1.P.T20_L3V2.arm_control_eval _ hA, hc]
  · have hA : ∀ z : ℕ × Bool, z ∈ {z | W1BinaryValue z.2 = 1} ↔
        W1BinaryValue z.2 = 1 := by intro z; rfl
    rw [SAP.P001b.WH.W1.P.T20_L3V2.arm_treated_eval _ hA, ht]
