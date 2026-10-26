import AronowAudit.P004.Wave1.DesignLimitsBlueprint
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Topology.MetricSpace.Pseudo.Pi
import Mathlib.Topology.Algebra.Monoid

/-!
Finite-dimensional continuous mapping for the finite design laws.
The probability helpers use the finite-expectation algebra.
-/

namespace AronowAudit.P004.Wave1.DesignLimits

set_option autoImplicit false
noncomputable section
open AronowAudit.P004 MeasureTheory Filter
open scoped BigOperators

namespace DLbSupport

theorem prob_congr {N : ℕ} (p : Fin N → ℝ) (A B : Assignment N → Prop)
    (h : ∀ z, A z ↔ B z) : prob p A = prob p B := by
  classical
  have hAB : A = B := funext (fun z => propext (h z))
  rw [hAB]

theorem prob_nonneg {N : ℕ} (p : Fin N → ℝ)
    (hp : ∀ i, 0 < p i ∧ p i < 1) (A : Assignment N → Prop) :
    0 ≤ prob p A := by
  classical
  unfold prob expect
  apply Finset.sum_nonneg
  intro z _
  apply mul_nonneg (design_weight_nonneg p hp z)
  dsimp only
  split_ifs <;> norm_num

theorem prob_mono {N : ℕ} (p : Fin N → ℝ)
    (hp : ∀ i, 0 < p i ∧ p i < 1) (A B : Assignment N → Prop)
    (h : ∀ z, A z → B z) : prob p A ≤ prob p B := by
  classical
  apply expect_mono p hp
  intro z
  by_cases ha : A z
  · simpa only [if_pos ha, if_pos (h z ha)] using (le_rfl : (1 : ℝ) ≤ 1)
  · by_cases hb : B z <;> simp [ha, hb]

/-- A two-event union bound in the form needed for event sandwiches. -/
theorem prob_le_add {N : ℕ} (p : Fin N → ℝ)
    (hp : ∀ i, 0 < p i ∧ p i < 1) (A B C : Assignment N → Prop)
    (h : ∀ z, A z → B z ∨ C z) : prob p A ≤ prob p B + prob p C := by
  classical
  unfold prob
  rw [← expect_add]
  apply expect_mono p hp
  intro z
  by_cases ha : A z
  · rcases h z ha with hb | hc
    · by_cases hc : C z <;> simp [ha, hb, hc]
    · by_cases hb : B z <;> simp [ha, hb, hc]
  · by_cases hb : B z <;> by_cases hc : C z <;> simp [ha, hb, hc]

/-- A finite union bound, including the empty coordinate type. -/
theorem prob_le_sum {N m : ℕ} (p : Fin N → ℝ)
    (hp : ∀ i, 0 < p i ∧ p i < 1) (A : Assignment N → Prop)
    (B : Fin m → Assignment N → Prop) (h : ∀ z, A z → ∃ k, B k z) :
    prob p A ≤ ∑ k, prob p (B k) := by
  classical
  have hpoint (z : Assignment N) :
      (if A z then (1 : ℝ) else 0) ≤ ∑ k, if B k z then (1 : ℝ) else 0 := by
    by_cases ha : A z
    · obtain ⟨k, hk⟩ := h z ha
      rw [if_pos ha]
      calc
        (1 : ℝ) = (if B k z then (1 : ℝ) else 0) := (if_pos hk).symm
        _ ≤ ∑ j, if B j z then (1 : ℝ) else 0 :=
          Finset.single_le_sum (f := fun j => if B j z then (1 : ℝ) else 0)
            (fun j _ => by split_ifs <;> norm_num) (Finset.mem_univ k)
    · rw [if_neg ha]
      exact Finset.sum_nonneg (fun k _ => by split_ifs <;> norm_num)
  have he := expect_mono p hp
    (fun z => if A z then (1 : ℝ) else 0)
    (fun z => ∑ k, if B k z then (1 : ℝ) else 0) hpoint
  rw [expect_sum] at he
  exact he

end DLbSupport

/-- Continuous mapping for finitely many coordinate limits in probability. -/
theorem dl9_proof : DL9 := by
  classical
  intro p hp m U c F hF hU ε hε
  obtain ⟨δ, hδ, hnear⟩ := (Metric.continuousAt_iff.mp hF) ε hε
  have hhalf : 0 < δ / 2 := by linarith
  have hbad (N : ℕ) (z : Assignment N)
      (hz : ε < |F (fun k => U k N z) - F c|) :
      ∃ k, δ / 2 < |U k N z - c k| := by
    by_contra hnone
    have hcoord (k : Fin m) : dist (U k N z) (c k) < δ := by
      have hk : |U k N z - c k| ≤ δ / 2 := by
        apply le_of_not_gt
        intro hk
        exact hnone ⟨k, hk⟩
      rw [Real.dist_eq]
      linarith
    have hvec : dist (fun k => U k N z) c < δ :=
      (dist_pi_lt_iff hδ).mpr hcoord
    have hclose : dist (F (fun k => U k N z)) (F c) < ε := hnear hvec
    rw [Real.dist_eq] at hclose
    linarith
  have hupper (N : ℕ) :
      prob (p N) (fun z => ε < |F (fun k => U k N z) - F c|) ≤
        ∑ k, prob (p N) (fun z => δ / 2 < |U k N z - c k|) :=
    DLbSupport.prob_le_sum (p N) (hp N) _ _ (hbad N)
  have hsum : Tendsto
      (fun N => ∑ k, prob (p N) (fun z => δ / 2 < |U k N z - c k|))
      atTop (nhds (0 : ℝ)) := by
    simpa only [Finset.sum_const_zero] using
      (tendsto_finsetSum (s := Finset.univ)
        (fun k _ => hU k (δ / 2) hhalf))
  exact squeeze_zero
    (fun N => DLbSupport.prob_nonneg (p N) (hp N) _)
    hupper hsum

end
end AronowAudit.P004.Wave1.DesignLimits
