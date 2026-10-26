import AronowAudit.P005.Wave1.ExactDecompositionBlueprint

set_option autoImplicit false

namespace AronowAudit.P005.Wave1.ExactDecomposition

open AronowAudit.P005 Finset
open scoped BigOperators

noncomputable section

/-- Centered outcome and fixed-slope terms have zero expectation in both arms. -/
theorem n7_proof : N7 := by
  classical
  intro hcomp hslopes n d m P hn hm hmn hP hreg
  have hnpos : 0 < n := by omega
  have hcpos : 0 < n - m := Nat.sub_pos_of_lt hmn
  have hcle : n - m ≤ n := Nat.sub_le n m
  have hx (k : Fin d) : popMean (fun i => P.x i k) = 0 := by
    simpa only [xMean, popMean, Pi.zero_apply] using
      congrArg (fun v : Fin d → ℝ => v k) hP.1
  have hsub (f g : Finset (Fin n) → ℝ) :
      expectation m (fun S => f S - g S) = expectation m f - expectation m g := by
    simp only [expectation, Finset.sum_sub_distrib, sub_div]
  have hadd (f g : Finset (Fin n) → ℝ) :
      expectation m (fun S => f S + g S) = expectation m f + expectation m g := by
    simp only [expectation, Finset.sum_add_distrib, add_div]
  have hden : ((design n m).card : ℝ) ≠ 0 := by
    have hcard : (design n m).card = n.choose m := by
      simp only [design, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
    rw [hcard]
    exact_mod_cast Nat.ne_of_gt (Nat.choose_pos hmn.le)
  have hconst (c : ℝ) : expectation m (fun _ : Finset (Fin n) => c) = c := by
    simp only [expectation, Finset.sum_const, nsmul_eq_mul]
    field_simp [hden] <;> ring
  have hmeanT : expectation m (fun S => mean S P.yT) = popMean P.yT :=
    mean_unbiased hnpos hm hmn.le P.yT
  have hmeanC : expectation m (fun S => mean (control S) P.yC) = popMean P.yC := by
    rw [hcomp n m hmn.le (fun S => mean S P.yC),
      mean_unbiased hnpos hcpos hcle]
  have hdotmean (t : ℕ) (ht : 0 < t) (htn : t ≤ n) (v : Fin d → ℝ) :
      expectation t (fun S => dot (xMean P S) v) = 0 := by
    change expectation t (fun S => ∑ k, mean S (fun i => P.x i k) * v k) = 0
    rw [expectation_sum]
    apply Finset.sum_eq_zero
    intro k _
    calc
      _ = expectation t (fun S => v k * mean S (fun i => P.x i k)) := by
        apply expectation_congr
        intro S _
        ring
      _ = v k * popMean (fun i => P.x i k) := by
        rw [expectation_mul, mean_unbiased hnpos ht htn]
      _ = 0 := by rw [hx k]; ring
  have hdotT (v : Fin d → ℝ) : expectation m (fun S => dot (xMean P S) v) = 0 :=
    hdotmean m hm hmn.le v
  have hdotC (v : Fin d → ℝ) :
      expectation m (fun S => dot (xMean P (control S)) v) = 0 := by
    rw [hcomp n m hmn.le (fun S => dot (xMean P S) v)]
    exact hdotmean (n - m) hcpos hcle v
  have hdotadd (u v w : Fin d → ℝ) : dot u (v + w) = dot u v + dot u w := by
    simp only [dot, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  let deltaT : Finset (Fin n) → Fin d → ℝ := fun S =>
    armNu1 P S P.yT + armNu2 P S P.yT + armNu3 P S P.yT
  let deltaC : Finset (Fin n) → Fin d → ℝ := fun S =>
    armNu1 P (control S) P.yC + armNu2 P (control S) P.yC + armNu3 P (control S) P.yC
  have hpoint : ∀ S ∈ design n m, interactedATE P S - ate P =
      (mean S P.yT - mean (control S) P.yC - ate P) +
        dot (xMean P (control S)) (populationSlope P P.yC) -
        dot (xMean P S) (populationSlope P P.yT) +
        dot (xMean P (control S)) (deltaC S) - dot (xMean P S) (deltaT S) := by
    intro S hS
    obtain ⟨hsT, hsC⟩ := hslopes P hn hm hmn hP hreg S hS
    have hsT' : armBetaHat P S P.yT = populationSlope P P.yT + deltaT S := by
      rw [hsT]
      dsimp only [deltaT]
      abel
    have hsC' : armBetaHat P (control S) P.yC =
        populationSlope P P.yC + deltaC S := by
      rw [hsC]
      dsimp only [deltaC]
      abel
    unfold interactedATE
    rw [hsT', hsC', hdotadd (xMean P S) (populationSlope P P.yT) (deltaT S),
      hdotadd (xMean P (control S)) (populationSlope P P.yC) (deltaC S)]
    ring
  change expectation m (fun S => interactedATE P S - ate P) =
    expectation m (fun S => dot (xMean P (control S)) (deltaC S)) -
      expectation m (fun S => dot (xMean P S) (deltaT S))
  rw [expectation_congr m _ _ hpoint]
  simp only [hsub, hadd, hmeanT, hmeanC, hconst, hdotT, hdotC]
  unfold ate
  ring

end

end AronowAudit.P005.Wave1.ExactDecomposition
