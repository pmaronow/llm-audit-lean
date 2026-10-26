import AronowAudit.P004.Wave1.FiniteConditioningBlueprint

namespace AronowAudit.P004.Wave1.FiniteConditioning

set_option autoImplicit false
noncomputable section
open AronowAudit.P004 MeasureTheory Filter
open scoped BigOperators

/-- Every cylinder has strictly positive normalizing mass under overlap. -/
theorem conditioning_mass_pos {N : ℕ} (p : Fin N → ℝ) (hp : Admissible p)
    (J : Finset (Fin N)) (z : Assignment N) :
    0 < ∏ j ∈ J, coin (p j) (z j) := by
  classical
  apply Finset.prod_pos
  intro j _
  cases h : z j with
  | false => simpa only [coin, h, Bool.false_eq_true, if_false] using sub_pos.mpr (hp j).2
  | true => simpa only [coin, h, if_true] using (hp j).1

/-- The subtype product used by the product-design split is the cylinder denominator. -/
theorem conditioning_cubeWeight {N : ℕ} (p : Fin N → ℝ)
    (J : Finset (Fin N)) (z : Assignment N) :
    GraphCompletion.cubeWeight (fun j : (J : Set (Fin N)) => p j) (fun j => z j) =
      ∏ j ∈ J, coin (p j) (z j) := by
  classical
  unfold GraphCompletion.cubeWeight
  exact (Finset.prod_subtype J (by intro j; rfl) (fun j => coin (p j) (z j))).symm

/-- Split a cylinder expectation into its retained-coordinate mass and an expectation
over the complementary coordinates. No sign restriction on the coins is needed here. -/
theorem conditioning_cylinder_expect {N : ℕ} (p : Fin N → ℝ)
    (J : Finset (Fin N)) (U : Assignment N → ℝ) (z : Assignment N) :
    expect p (fun w => if ∀ j ∈ J, w j = z j then U w else 0) =
      (∏ j ∈ J, coin (p j) (z j)) *
        ∑ b : {j : Fin N // j ∉ (J : Set (Fin N))} → Bool,
          GraphCompletion.cubeWeight
            (fun j : {j : Fin N // j ∉ (J : Set (Fin N))} => p j) b *
            U (GraphCompletion.join (J : Set (Fin N)) (fun j => z j) b) := by
  classical
  let S : Set (Fin N) := J
  let a0 : S → Bool := fun j => z j
  have hmatch (a : S → Bool) (b : {j : Fin N // j ∉ S} → Bool) :
      (∀ j ∈ J, GraphCompletion.join S a b j = z j) ↔ a = a0 := by
    constructor
    · intro ha
      funext j
      exact (GraphCompletion.join_left S a b j).symm.trans (ha j j.property)
    · rintro rfl
      intro j hj
      exact GraphCompletion.join_left S a0 b ⟨j, hj⟩
  rw [GraphCompletion.expect_split p S]
  rw [Finset.sum_eq_single a0]
  · rw [Finset.mul_sum]
    refine Finset.sum_congr (by congr 1 <;> exact Subsingleton.elim _ _) (fun b _ => ?_)
    rw [if_pos ((hmatch a0 b).2 rfl)]
    rw [← conditioning_cubeWeight p J z, mul_assoc]
    congr 1
    · congr 1
      exact Subsingleton.elim _ _
    · congr 1 <;> first | rfl | (congr 1; exact Subsingleton.elim _ _)
  · intro a _ ha
    apply Finset.sum_eq_zero
    intro b _
    rw [if_neg (fun h => ha ((hmatch a b).1 h)), mul_zero]
  · intro h
    simp at h

/-- The actual conditional expectation is the normalized product expectation on the
complement. The positive cylinder factor cancels, including when `J` is empty or full. -/
theorem conditionOn_eq_sum {N : ℕ} (p : Fin N → ℝ) (hp : Admissible p)
    (J : Finset (Fin N)) (U : Assignment N → ℝ) (z : Assignment N) :
    conditionOn p J U z =
      ∑ b : {j : Fin N // j ∉ (J : Set (Fin N))} → Bool,
        GraphCompletion.cubeWeight
          (fun j : {j : Fin N // j ∉ (J : Set (Fin N))} => p j) b *
          U (GraphCompletion.join (J : Set (Fin N)) (fun j => z j) b) := by
  classical
  unfold conditionOn
  rw [conditioning_cylinder_expect]
  exact mul_div_cancel_left₀ _ (ne_of_gt (conditioning_mass_pos p hp J z))

/-- Constants, the two linearity identities, and pull-out on retained coordinates. -/
theorem fc2_proof : FC2 := by
  classical
  intro N p hp J
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro c z
    rw [conditionOn_eq_sum p hp J]
    have h1 : (∑ i : {j : Fin N // j ∉ (J : Set (Fin N))} → Bool,
        GraphCompletion.cubeWeight (fun j : {j : Fin N // j ∉ (J : Set (Fin N))} => p j) i) = 1 := by
      convert GraphCompletion.cube_normalized
        (fun j : {j : Fin N // j ∉ (J : Set (Fin N))} => p j)
    rw [← Finset.sum_mul, h1, one_mul]
  · intro U V z
    simp only [conditionOn_eq_sum p hp J, mul_add, Finset.sum_add_distrib]
  · intro U V z
    simp only [conditionOn_eq_sum p hp J, mul_sub, Finset.sum_sub_distrib]
  · intro F U hF z
    have hFz (b : {j : Fin N // j ∉ (J : Set (Fin N))} → Bool) :
        F (GraphCompletion.join (J : Set (Fin N)) (fun j => z j) b) = F z := by
      apply hF
      intro j hj
      exact GraphCompletion.join_left (J : Set (Fin N)) (fun j => z j) b ⟨j, hj⟩
    rw [conditionOn_eq_sum p hp J, conditionOn_eq_sum p hp J]
    simp_rw [hFz]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _
    ring

end
end AronowAudit.P004.Wave1.FiniteConditioning
