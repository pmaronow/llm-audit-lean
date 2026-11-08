import SAP.P061a.WH.W1.Leaves
import AronowAudit.P061.P061_Foundations

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators ENNReal

namespace SAP.P061a.WH.W1.P.T7_L1

open SAP.P061a.WH.W1

private theorem positive_expectation_not_finite
    (D : AtomicDesign ℝ) (f : ℝ → ℝ) (c : ℝ) (hc : 0 < c)
    (a : ℕ → ℝ) (hdiv : ¬ Summable (fun k => max (a k) 0))
    (hterm : ∀ k : ℕ, D.mass ((k+1 : ℕ) : ℝ) * f ((k+1 : ℕ) : ℝ) =
      c * a k) :
    positiveExpectationW1 D f = ⊤ := by
  by_contra hfinite
  change (∑' z : ℝ, ENNReal.ofReal (D.mass z * max (f z) 0)) ≠ ⊤ at hfinite
  have hsum : Summable (fun z : ℝ =>
      (ENNReal.ofReal (D.mass z * max (f z) 0)).toReal) := by
    apply ENNReal.summable_toReal
    change (∑' z : ℝ, ENNReal.ofReal (D.mass z * max (f z) 0)) ≠ ⊤
    exact hfinite
  have hinj : Function.Injective (fun k : ℕ => ((k+1 : ℕ) : ℝ)) := by
    intro m n h
    exact Nat.add_right_cancel (Nat.cast_injective h)
  have hseq := hsum.comp_injective hinj
  have hterms : (fun k : ℕ =>
      (ENNReal.ofReal (D.mass ((k+1 : ℕ) : ℝ) * max (f ((k+1 : ℕ) : ℝ)) 0)).toReal) =
      (fun k : ℕ => c * max (a k) 0) := by
    funext k
    have hmass := D.mass_nonnegative ((k+1 : ℕ) : ℝ)
    have harg : 0 ≤ D.mass ((k+1 : ℕ) : ℝ) * max (f ((k+1 : ℕ) : ℝ)) 0 :=
      mul_nonneg hmass (le_max_right _ _)
    rw [ENNReal.toReal_ofReal harg]
    rw [mul_max_of_nonneg _ _ hmass]
    rw [hterm k]
    rw [mul_max_of_nonneg _ _ hc.le]
    simp only [mul_zero]
  exact hdiv ((summable_mul_left_iff hc.ne').mp (hterms ▸ hseq))

end SAP.P061a.WH.W1.P.T7_L1

theorem SAP.P061a.WH.W1.T7_L1_proof : SAP.P061a.WH.W1.T7_L1 := by
  intro D f c hc hterm
  have hnegterm : ∀ k : ℕ,
      D.mass ((k+1 : ℕ) : ℝ) * (-f ((k+1 : ℕ) : ℝ)) =
        c * (-((-1 : ℝ)^k)) := by
    intro k
    calc
      D.mass ((k+1 : ℕ) : ℝ) * (-f ((k+1 : ℕ) : ℝ)) =
          -(D.mass ((k+1 : ℕ) : ℝ) * f ((k+1 : ℕ) : ℝ)) := by ring
      _ = -(c * (-1 : ℝ)^k) := by rw [hterm k]
      _ = c * (-((-1 : ℝ)^k)) := by ring
  constructor
  · exact SAP.P061a.WH.W1.P.T7_L1.positive_expectation_not_finite
      D f c hc (fun k => (-1 : ℝ)^k)
      AronowAudit.P061.divergent_parts_not_summable.1 hterm
  · change positiveExpectationW1 D (fun z => -f z) = ⊤
    exact SAP.P061a.WH.W1.P.T7_L1.positive_expectation_not_finite
      D (fun z => -f z) c hc (fun k => -((-1 : ℝ)^k))
      AronowAudit.P061.divergent_parts_not_summable.2 hnegterm
