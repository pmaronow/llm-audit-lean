import Mathlib

/-! Direct finite weighted-pair bounds for the covariance part of a quadratic
variance expansion. No probabilistic, independence, or operator-norm premise is
assumed in this helper. -/
namespace AronowAudit.P011.DensePairBound
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Nonnegative weights with bounded row and column sums control absolute
quadratic products by the squared coefficient sum. -/
theorem weighted_pair_sum_le {α : Type*} [Fintype α]
    (a : α → ℝ) (W : α → α → ℝ) (C : ℝ)
    (hW : ∀ p q, 0 ≤ W p q)
    (hrow : ∀ p, (∑ q, W p q) ≤ C)
    (hcol : ∀ q, (∑ p, W p q) ≤ C) :
    (∑ p, ∑ q, |a p * a q| * W p q) ≤ C * ∑ p, (a p)^2 := by
  have hfirst : (∑ p, ∑ q, (a p)^2 * W p q) ≤ C * ∑ p, (a p)^2 := by
    calc
      _ = ∑ p, (a p)^2 * ∑ q, W p q := by simp_rw [Finset.mul_sum]
      _ ≤ ∑ p, (a p)^2 * C := by
        apply Finset.sum_le_sum
        intro p _
        exact mul_le_mul_of_nonneg_left (hrow p) (sq_nonneg _)
      _ = _ := by rw [←Finset.sum_mul]; ring
  have hsecond : (∑ p, ∑ q, (a q)^2 * W p q) ≤ C * ∑ p, (a p)^2 := by
    calc
      _ = ∑ q, ∑ p, (a q)^2 * W p q := Finset.sum_comm
      _ = ∑ q, (a q)^2 * ∑ p, W p q := by simp_rw [Finset.mul_sum]
      _ ≤ ∑ q, (a q)^2 * C := by
        apply Finset.sum_le_sum
        intro q _
        exact mul_le_mul_of_nonneg_left (hcol q) (sq_nonneg _)
      _ = _ := by rw [←Finset.sum_mul]; ring
  have htwo : 2 * (∑ p, ∑ q, |a p * a q| * W p q) ≤
      2 * (C * ∑ p, (a p)^2) := by
    calc
      _ = ∑ p, ∑ q, (2 * |a p * a q|) * W p q := by
        simp_rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro p _
        apply Finset.sum_congr rfl
        intro q _
        ring
      _ ≤ ∑ p, ∑ q, ((a p)^2 + (a q)^2) * W p q := by
        apply Finset.sum_le_sum
        intro p _
        apply Finset.sum_le_sum
        intro q _
        apply mul_le_mul_of_nonneg_right _ (hW p q)
        simpa only [abs_mul, sq_abs, mul_assoc] using (two_mul_le_add_sq |a p| |a q|)
      _ = (∑ p, ∑ q, (a p)^2 * W p q) + (∑ p, ∑ q, (a q)^2 * W p q) := by
        simp_rw [add_mul, Finset.sum_add_distrib]
      _ ≤ _ := by linarith
  linarith

variable {ι : Type*} [Fintype ι] (G : ι → ι → Prop) [DecidableRel G]

/-- The real indicator of the closed adjacency relation. -/
def edgeIndicator (i j : ι) : ℝ := if G i j then 1 else 0

omit [Fintype ι] in
lemma edgeIndicator_nonnegative (i j : ι) : 0 ≤ edgeIndicator G i j := by
  unfold edgeIndicator
  split_ifs <;> norm_num

omit [Fintype ι] in
lemma edgeIndicator_symm (hG : ∀ ⦃i j⦄, G i j → G j i) (i j : ι) :
    edgeIndicator G i j = edgeIndicator G j i := by
  by_cases hij : G i j
  · simp [edgeIndicator, hij, hG hij]
  · have hji : ¬G j i := fun h => hij (hG h)
    simp [edgeIndicator, hij, hji]

/-- Each covariance pairing is bounded by D² times the squared-entry sum.
Symmetry supplies the column bound; the coefficient array itself is arbitrary. -/
theorem graph_pair_sum_le (hG : ∀ ⦃i j⦄, G i j → G j i) (D : ℝ) (hD : 0 ≤ D)
    (hrow : ∀ i, (∑ j, if G i j then (1 : ℝ) else 0) ≤ D)
    (A : ι → ι → ℝ) :
    (∑ i, ∑ j, ∑ k, ∑ l,
      |A i j * A k l| * edgeIndicator G i k * edgeIndicator G j l) ≤
      D ^ 2 * (∑ i, ∑ j, (A i j)^2) := by
  let W : (ι × ι) → (ι × ι) → ℝ :=
    fun p q => edgeIndicator G p.1 q.1 * edgeIndicator G p.2 q.2
  have hW (p q : ι × ι) : 0 ≤ W p q :=
    mul_nonneg (edgeIndicator_nonnegative G _ _) (edgeIndicator_nonnegative G _ _)
  have hrows (p : ι × ι) : (∑ q, W p q) ≤ D ^ 2 := by
    calc
      _ = (∑ k, edgeIndicator G p.1 k) * (∑ l, edgeIndicator G p.2 l) := by
        simp only [W, Fintype.sum_prod_type, Finset.sum_mul, Finset.mul_sum]
        exact Finset.sum_comm
      _ ≤ D * D := by
        apply mul_le_mul (hrow p.1) (hrow p.2)
        · exact Finset.sum_nonneg (fun l _ => edgeIndicator_nonnegative G p.2 l)
        · exact hD
      _ = _ := by ring
  have hcols (q : ι × ι) : (∑ p, W p q) ≤ D ^ 2 := by
    have heq : (∑ p, W p q) = ∑ p, W q p := by
      apply Finset.sum_congr rfl
      intro p _
      dsimp [W]
      rw [edgeIndicator_symm G hG p.1 q.1, edgeIndicator_symm G hG p.2 q.2]
    rw [heq]
    exact hrows q
  have hh := weighted_pair_sum_le (fun p : ι × ι => A p.1 p.2) W (D^2) hW hrows hcols
  simpa only [W, Fintype.sum_prod_type, mul_assoc] using hh

end
end AronowAudit.P011.DensePairBound
