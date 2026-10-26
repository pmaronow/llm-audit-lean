import Mathlib

/-! Direct finite counting for a four-position connected-support estimate.
This helper makes no probabilistic or cumulant assertion. -/
namespace AronowAudit.P011.DenseTreeCount
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

variable {ι : Type*} [Fintype ι] (G : ι → ι → Prop) [DecidableRel G]

/-- A rooted growth order: each new position joins an earlier one. -/
def Grow4 (a b c d : ι) : Prop :=
  G a b ∧ (G a c ∨ G b c) ∧ (G a d ∨ G b d ∨ G c d)

/-- All six growth orders rooted at the first position. -/
def Connected4 (a b c d : ι) : Prop :=
  Grow4 G a b c d ∨ Grow4 G a b d c ∨ Grow4 G a c b d ∨
  Grow4 G a c d b ∨ Grow4 G a d b c ∨ Grow4 G a d c b

private theorem indicator_or_two (P Q : Prop) [Decidable P] [Decidable Q] :
    (if P ∨ Q then (1 : ℝ) else 0) ≤
      (if P then 1 else 0) + (if Q then 1 else 0) := by
  by_cases hP : P <;> by_cases hQ : Q <;> simp [hP, hQ]

private theorem indicator_or_three (P Q R : Prop)
    [Decidable P] [Decidable Q] [Decidable R] :
    (if P ∨ Q ∨ R then (1 : ℝ) else 0) ≤
      (if P then 1 else 0) + (if Q then 1 else 0) + (if R then 1 else 0) := by
  by_cases hP : P <;> by_cases hQ : Q <;> by_cases hR : R <;> simp [hP, hQ, hR]

omit [Fintype ι] in
private theorem grow_indicator (a b c d : ι) :
    (if Grow4 G a b c d then (1 : ℝ) else 0) =
      (if G a b then 1 else 0) * (if G a c ∨ G b c then 1 else 0) *
        (if G a d ∨ G b d ∨ G c d then 1 else 0) := by
  classical
  by_cases h₁ : G a b <;> by_cases h₂ : G a c ∨ G b c <;>
    by_cases h₃ : G a d ∨ G b d ∨ G c d <;> simp [Grow4, h₁, h₂, h₃]

/-- One specified growth order has at most 6 n D³ weighted labels. -/
theorem grow4_count_le (D : ℝ) (hD : 0 ≤ D)
    (hrow : ∀ a, (∑ b, if G a b then (1 : ℝ) else 0) ≤ D) :
    (∑ a, ∑ b, ∑ c, ∑ d, if Grow4 G a b c d then (1 : ℝ) else 0) ≤
      6 * (Fintype.card ι : ℝ) * D ^ 3 := by
  classical
  have htwo (a b : ι) : (∑ c, if G a c ∨ G b c then (1 : ℝ) else 0) ≤ 2 * D := by
    calc
      _ ≤ ∑ c, ((if G a c then (1 : ℝ) else 0) + (if G b c then 1 else 0)) := by
        apply Finset.sum_le_sum
        intro c _
        exact indicator_or_two _ _
      _ ≤ _ := by rw [Finset.sum_add_distrib]; linarith [hrow a, hrow b]
  have hthree (a b c : ι) :
      (∑ d, if G a d ∨ G b d ∨ G c d then (1 : ℝ) else 0) ≤ 3 * D := by
    calc
      _ ≤ ∑ d, ((if G a d then (1 : ℝ) else 0) +
          (if G b d then 1 else 0) + (if G c d then 1 else 0)) := by
        apply Finset.sum_le_sum
        intro d _
        exact indicator_or_three _ _ _
      _ ≤ _ := by
        simp only [Finset.sum_add_distrib]
        linarith [hrow a, hrow b, hrow c]
  have hd (a b c : ι) :
      (∑ d, if Grow4 G a b c d then (1 : ℝ) else 0) ≤
        (if G a b then 1 else 0) * (if G a c ∨ G b c then 1 else 0) * (3 * D) := by
    simp_rw [grow_indicator]
    rw [← Finset.mul_sum]
    apply mul_le_mul_of_nonneg_left (hthree a b c)
    apply mul_nonneg <;> split_ifs <;> norm_num
  have hc (a b : ι) :
      (∑ c, ∑ d, if Grow4 G a b c d then (1 : ℝ) else 0) ≤
        (if G a b then 1 else 0) * (2 * D) * (3 * D) := by
    calc
      _ ≤ ∑ c, (if G a b then (1 : ℝ) else 0) *
          (if G a c ∨ G b c then 1 else 0) * (3 * D) :=
        Finset.sum_le_sum (fun c _ => hd a b c)
      _ = (if G a b then (1 : ℝ) else 0) *
          (∑ c, if G a c ∨ G b c then 1 else 0) * (3 * D) := by
        rw [← Finset.sum_mul, ← Finset.mul_sum]
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        apply mul_le_mul_of_nonneg_left (htwo a b)
        split_ifs <;> norm_num
  have hb (a : ι) :
      (∑ b, ∑ c, ∑ d, if Grow4 G a b c d then (1 : ℝ) else 0) ≤ 6 * D ^ 3 := by
    calc
      _ ≤ ∑ b, (if G a b then (1 : ℝ) else 0) * (2 * D) * (3 * D) :=
        Finset.sum_le_sum (fun b _ => hc a b)
      _ = (∑ b, if G a b then (1 : ℝ) else 0) * (2 * D) * (3 * D) := by
        rw [← Finset.sum_mul, ← Finset.sum_mul]
      _ ≤ D * (2 * D) * (3 * D) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact mul_le_mul_of_nonneg_right (hrow a) (by positivity)
      _ = _ := by ring
  calc
    _ ≤ ∑ _a : ι, 6 * D ^ 3 := Finset.sum_le_sum (fun a _ => hb a)
    _ = 6 * (Fintype.card ι : ℝ) * D ^ 3 := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      ring

omit [Fintype ι] [DecidableRel G] in
private theorem connected_indicator_le (a b c d : ι) :
    (if Connected4 G a b c d then (1 : ℝ) else 0) ≤
      (if Grow4 G a b c d then 1 else 0) + (if Grow4 G a b d c then 1 else 0) +
      (if Grow4 G a c b d then 1 else 0) + (if Grow4 G a c d b then 1 else 0) +
      (if Grow4 G a d b c then 1 else 0) + (if Grow4 G a d c b then 1 else 0) := by
  classical
  by_cases h₁ : Grow4 G a b c d <;> by_cases h₂ : Grow4 G a b d c <;>
    by_cases h₃ : Grow4 G a c b d <;> by_cases h₄ : Grow4 G a c d b <;>
    by_cases h₅ : Grow4 G a d b c <;> by_cases h₆ : Grow4 G a d c b <;>
    norm_num [Connected4, h₁, h₂, h₃, h₄, h₅, h₆]

private theorem sum_cycle (f : ι → ι → ι → ℝ) :
    (∑ b, ∑ c, ∑ d, f c d b) = ∑ b, ∑ c, ∑ d, f b c d := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c _
  exact Finset.sum_comm

private theorem sum_reverse (f : ι → ι → ι → ℝ) :
    (∑ b, ∑ c, ∑ d, f d c b) = ∑ b, ∑ c, ∑ d, f b c d := by
  calc
    _ = ∑ b, ∑ d, ∑ c, f d c b := by
      apply Finset.sum_congr rfl
      intro b _
      exact Finset.sum_comm
    _ = ∑ d, ∑ b, ∑ c, f d c b := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro d _
      exact Finset.sum_comm

/-- Six rooted orders bound all connected four-position labels; no symmetry
assumption is needed for this purely combinatorial count. -/
theorem connected4_count_le (D : ℝ) (hD : 0 ≤ D)
    (hrow : ∀ a, (∑ b, if G a b then (1 : ℝ) else 0) ≤ D) :
    (∑ a, ∑ b, ∑ c, ∑ d, if Connected4 G a b c d then (1 : ℝ) else 0) ≤
      36 * (Fintype.card ι : ℝ) * D ^ 3 := by
  classical
  have hg := grow4_count_le G D hD hrow
  have hperm₁ : (∑ a, ∑ b, ∑ c, ∑ d, if Grow4 G a b d c then (1 : ℝ) else 0) ≤
      6 * (Fintype.card ι : ℝ) * D ^ 3 := by
    convert hg using 1
    congr 1; funext a
    congr 1; funext b
    exact Finset.sum_comm
  have hperm₂ : (∑ a, ∑ b, ∑ c, ∑ d, if Grow4 G a c b d then (1 : ℝ) else 0) ≤
      6 * (Fintype.card ι : ℝ) * D ^ 3 := by
    convert hg using 1
    congr 1; funext a
    exact Finset.sum_comm
  have hperm₃ : (∑ a, ∑ b, ∑ c, ∑ d, if Grow4 G a c d b then (1 : ℝ) else 0) ≤
      6 * (Fintype.card ι : ℝ) * D ^ 3 := by
    convert hg using 1
    congr 1; funext a
    exact sum_cycle (fun b c d => if Grow4 G a b c d then (1 : ℝ) else 0)
  have hperm₄ : (∑ a, ∑ b, ∑ c, ∑ d, if Grow4 G a d b c then (1 : ℝ) else 0) ≤
      6 * (Fintype.card ι : ℝ) * D ^ 3 := by
    convert hg using 1
    congr 1; funext a
    exact (sum_cycle (fun b c d => if Grow4 G a d b c then (1 : ℝ) else 0)).symm
  have hperm₅ : (∑ a, ∑ b, ∑ c, ∑ d, if Grow4 G a d c b then (1 : ℝ) else 0) ≤
      6 * (Fintype.card ι : ℝ) * D ^ 3 := by
    convert hg using 1
    congr 1; funext a
    exact sum_reverse (fun b c d => if Grow4 G a b c d then (1 : ℝ) else 0)
  calc
    _ ≤ ∑ a, ∑ b, ∑ c, ∑ d,
        ((if Grow4 G a b c d then (1 : ℝ) else 0) + (if Grow4 G a b d c then 1 else 0) +
        (if Grow4 G a c b d then 1 else 0) + (if Grow4 G a c d b then 1 else 0) +
        (if Grow4 G a d b c then 1 else 0) + (if Grow4 G a d c b then 1 else 0)) := by
      apply Finset.sum_le_sum; intro a _
      apply Finset.sum_le_sum; intro b _
      apply Finset.sum_le_sum; intro c _
      apply Finset.sum_le_sum; intro d _
      exact connected_indicator_le G a b c d
    _ ≤ _ := by
      simp only [Finset.sum_add_distrib]
      linarith

end
end AronowAudit.P011.DenseTreeCount
