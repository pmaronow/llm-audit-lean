import AronowAudit.P011.P011_DenseTreeCount
import AronowAudit.P011.P011_DensePairBound

/-! A finite contraction estimate. The covariance/cumulant bounds below are
explicit algebraic premises; this module makes no claim to have obtained them
from a probability law. -/
namespace AronowAudit.P011.DenseContractionBound
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

variable {ι : Type*} [Fintype ι]

abbrev sum4 (f : ι → ι → ι → ι → ℝ) : ℝ := ∑ i, ∑ j, ∑ k, ∑ l, f i j k l

private theorem sum4_mono (f g : ι → ι → ι → ι → ℝ) (h : ∀ i j k l, f i j k l ≤ g i j k l) :
    sum4 f ≤ sum4 g := by
  apply Finset.sum_le_sum; intro i _
  apply Finset.sum_le_sum; intro j _
  apply Finset.sum_le_sum; intro k _
  apply Finset.sum_le_sum; intro l _
  exact h i j k l

private theorem sum4_mul (c : ℝ) (f : ι → ι → ι → ι → ℝ) :
    sum4 (fun i j k l => c * f i j k l) = c * sum4 f := by
  simp only [sum4, Finset.mul_sum]

private theorem sum4_swap_last (f : ι → ι → ι → ι → ℝ) :
    sum4 (fun i j k l => f i j l k) = sum4 f := by
  unfold sum4
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _
  exact Finset.sum_comm

open DensePairBound DenseTreeCount

/-- Finite covariance/cumulant contraction bound, with no stochastic conclusion
assumed. The array C and the four-array κ may be arbitrary subject to the displayed
entrywise bounds. -/
theorem dense_contraction_bound (G : ι → ι → Prop) [DecidableRel G]
    (hG : ∀ ⦃i j⦄, G i j → G j i)
    (D B K : ℝ) (hD : 0 ≤ D) (_hB : 0 ≤ B) (hK : 0 ≤ K)
    (hrow : ∀ i, (∑ j, if G i j then (1 : ℝ) else 0) ≤ D)
    (A C : ι → ι → ℝ) (κ : ι → ι → ι → ι → ℝ)
    (hAsymm : ∀ i j, A i j = A j i)
    (hA : ∀ i j, |A i j| ≤ K)
    (hFrob : (∑ i, ∑ j, (A i j)^2) ≤ (Fintype.card ι : ℝ) * K^2)
    (hC : ∀ i j, |C i j| ≤ B^2 * edgeIndicator G i j)
    (hκ : ∀ i j k l, |κ i j k l| ≤
      4 * B^4 * (if Connected4 G i j k l then (1 : ℝ) else 0)) :
    (∑ i, ∑ j, ∑ k, ∑ l,
      A i j * A k l * (κ i j k l + C i k * C j l + C i l * C j k)) ≤
      (144 * D^3 + 2 * D^2) * B^4 * K^2 * (Fintype.card ι : ℝ) := by
  have hprod (i j k l : ι) : |A i j * A k l| ≤ K^2 := by
    rw [abs_mul, pow_two]
    exact mul_le_mul (hA i j) (hA k l) (abs_nonneg _) hK
  have hkpoint (i j k l : ι) : A i j * A k l * κ i j k l ≤
      (4 * B^4 * K^2) * (if Connected4 G i j k l then (1 : ℝ) else 0) := by
    calc
      _ ≤ |A i j * A k l * κ i j k l| := le_abs_self _
      _ = |A i j * A k l| * |κ i j k l| := abs_mul _ _
      _ ≤ K^2 * (4 * B^4 * (if Connected4 G i j k l then (1 : ℝ) else 0)) :=
        mul_le_mul (hprod i j k l) (hκ i j k l) (abs_nonneg _) (sq_nonneg K)
      _ = _ := by ring
  have hk : sum4 (fun i j k l => A i j * A k l * κ i j k l) ≤
      144 * D^3 * B^4 * K^2 * (Fintype.card ι : ℝ) := by
    calc
      _ ≤ sum4 (fun i j k l => (4 * B^4 * K^2) *
          (if Connected4 G i j k l then (1 : ℝ) else 0)) :=
        sum4_mono _ _ hkpoint
      _ = (4 * B^4 * K^2) * sum4 (fun i j k l =>
          if Connected4 G i j k l then (1 : ℝ) else 0) := sum4_mul _ _
      _ ≤ (4 * B^4 * K^2) * (36 * (Fintype.card ι : ℝ) * D^3) :=
        mul_le_mul_of_nonneg_left (connected4_count_le G D hD hrow) (by positivity)
      _ = _ := by ring
  have hpPoint (i j k l : ι) :
      A i j * A k l * (C i k * C j l) ≤
        B^4 * (|A i j * A k l| * edgeIndicator G i k * edgeIndicator G j l) := by
    calc
      _ ≤ |A i j * A k l * (C i k * C j l)| := le_abs_self _
      _ = |A i j * A k l| * (|C i k| * |C j l|) := by simp only [abs_mul]
      _ ≤ |A i j * A k l| * ((B^2 * edgeIndicator G i k) * (B^2 * edgeIndicator G j l)) := by
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
        exact mul_le_mul (hC i k) (hC j l) (abs_nonneg _)
          (mul_nonneg (sq_nonneg B) (edgeIndicator_nonnegative G i k))
      _ = _ := by ring
  have hp : sum4 (fun i j k l => A i j * A k l * (C i k * C j l)) ≤
      D^2 * B^4 * K^2 * (Fintype.card ι : ℝ) := by
    calc
      _ ≤ sum4 (fun i j k l => B^4 *
          (|A i j * A k l| * edgeIndicator G i k * edgeIndicator G j l)) :=
        sum4_mono _ _ hpPoint
      _ = B^4 * sum4 (fun i j k l =>
          |A i j * A k l| * edgeIndicator G i k * edgeIndicator G j l) := sum4_mul _ _
      _ ≤ B^4 * (D^2 * (∑ i, ∑ j, (A i j)^2)) :=
        mul_le_mul_of_nonneg_left (graph_pair_sum_le G hG D hD hrow A) (by positivity)
      _ ≤ B^4 * (D^2 * ((Fintype.card ι : ℝ) * K^2)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact mul_le_mul_of_nonneg_left hFrob (sq_nonneg D)
      _ = _ := by ring
  have hcross : sum4 (fun i j k l => A i j * A k l * (C i l * C j k)) =
      sum4 (fun i j k l => A i j * A k l * (C i k * C j l)) := by
    calc
      _ = sum4 (fun i j k l => A i j * A l k * (C i k * C j l)) :=
        sum4_swap_last (fun i j k l => A i j * A l k * (C i k * C j l))
      _ = _ := by
        congr 1
        funext i j k l
        rw [hAsymm l k]
  have hdecomp :
      sum4 (fun i j k l => A i j * A k l *
        (κ i j k l + C i k * C j l + C i l * C j k)) =
        sum4 (fun i j k l => A i j * A k l * κ i j k l) +
        sum4 (fun i j k l => A i j * A k l * (C i k * C j l)) +
        sum4 (fun i j k l => A i j * A k l * (C i l * C j k)) := by
    simp only [sum4, mul_add, Finset.sum_add_distrib]
  change sum4 _ ≤ _
  rw [hdecomp, hcross]
  calc
    _ ≤ 144 * D^3 * B^4 * K^2 * (Fintype.card ι : ℝ) +
        D^2 * B^4 * K^2 * (Fintype.card ι : ℝ) +
        D^2 * B^4 * K^2 * (Fintype.card ι : ℝ) := add_le_add (add_le_add hk hp) hp
    _ = _ := by ring

end
end AronowAudit.P011.DenseContractionBound
