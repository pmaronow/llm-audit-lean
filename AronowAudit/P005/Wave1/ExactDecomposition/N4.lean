import AronowAudit.P005.Wave1.ExactDecompositionBlueprint

set_option autoImplicit false

namespace AronowAudit.P005.Wave1.ExactDecomposition

open AronowAudit.P005 Finset
open scoped BigOperators

noncomputable section

/-- Apply the product-of-means identity coordinatewise, then collect leverage. -/
theorem n4_proof : N4 := by
  classical
  intro hmeans n d m P hn hm hmn hx y
  have hnpos : 0 < n := by omega
  let a : Fin d → Fin n → ℝ := fun k i => P.x i k
  let b : Fin d → Fin n → ℝ := fun k i => centered y i * P.x i k
  let c : ℝ := ((n : ℝ) - m) / ((m : ℝ) * ((n : ℝ) - 1))
  have ha (k : Fin d) : popMean (a k) = 0 := by
    simpa only [a, xMean, popMean, Pi.zero_apply] using
      congrArg (fun v : Fin d → ℝ => v k) hx
  have hsub (f g : Finset (Fin n) → ℝ) :
      expectation m (fun S => f S - g S) = expectation m f - expectation m g := by
    simp only [expectation, Finset.sum_sub_distrib, sub_div]
  have hcoord (k : Fin d) :
      expectation m (fun S => mean S (a k) * (mean S (b k) - popMean (b k))) =
        c * popMean (fun i => a k i * b k i) := by
    have hab := hmeans n m hn hm hmn (a k) (b k)
    have hamean : expectation m (fun S => mean S (a k)) = 0 := by
      rw [mean_unbiased hnpos hm hmn, ha k]
    have hcov : popCov (a k) (b k) = popMean (fun i => a k i * b k i) := by
      change popMean (fun i => a k i * b k i) - popMean (a k) * popMean (b k) = _
      rw [ha k]
      ring
    calc
      _ = expectation m (fun S => mean S (a k) * mean S (b k) -
          popMean (b k) * mean S (a k)) := by
        apply expectation_congr
        intro S _
        ring
      _ = expectation m (fun S => mean S (a k) * mean S (b k)) -
          popMean (b k) * expectation m (fun S => mean S (a k)) := by
        rw [hsub, expectation_mul]
      _ = c * popMean (fun i => a k i * b k i) := by
        rw [hab, hamean, ha k, hcov]
        dsimp only [c]
        ring
  have hlev : (∑ k, popMean (fun i => a k i * b k i)) = leverageCov P y := by
    rw [← popMean_sum]
    have hf : (fun i => ∑ k, a k i * b k i) =
        (fun i => leverage P i * y i - popMean y * leverage P i) := by
      funext i
      change (∑ k, P.x i k * ((y i - popMean y) * P.x i k)) =
        (∑ k, P.x i k * P.x i k) * y i - popMean y * (∑ k, P.x i k * P.x i k)
      calc
        _ = (y i - popMean y) * ∑ k, P.x i k * P.x i k := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro k _
          ring
        _ = _ := by ring
    rw [hf]
    change mean univ (fun i => leverage P i * y i - popMean y * leverage P i) = _
    rw [mean_sub, mean_mul]
    change popMean (fun i => leverage P i * y i) - popMean y * popMean (leverage P) =
      popMean (fun i => leverage P i * y i) - popMean (leverage P) * popMean y
    ring
  change expectation m (fun S => ∑ k, mean S (a k) *
    (mean S (b k) - popMean (b k))) = _
  rw [expectation_sum]
  simp_rw [hcoord]
  rw [← Finset.mul_sum, hlev]
  dsimp only [c]
  rw [mul_comm (m : ℝ) ((n : ℝ) - 1)]

end

end AronowAudit.P005.Wave1.ExactDecomposition
