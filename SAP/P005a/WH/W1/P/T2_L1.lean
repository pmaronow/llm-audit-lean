import SAP.P005a.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P005a.WH.W1.P.T2_L1

open SAP.P005a.WH.W1
open Finset
open scoped BigOperators Matrix

noncomputable section

lemma transpose_contraction {n : ℕ} (u v : Fin n → ℝ) :
    (∑ i, ∑ j, (u i * v j) * (u j * v i)) = (∑ i, u i*v i)^2 := by
  calc
    _ = ∑ i, ∑ j, (u i * v i) * (u j * v j) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = _ := by
      simp_rw [← Finset.mul_sum, ← Finset.sum_mul]
      ring

lemma diagonal_square_contraction {n : ℕ} (u v : Fin n → ℝ) :
    (∑ i, (u i * v i)^2) = ∑ i, u i^2 * v i^2 := by
  apply Finset.sum_congr rfl
  intro i _
  ring

end

end SAP.P005a.WH.W1.P.T2_L1

open SAP.P005a.WH.W1.P.T2_L1
open SAP.P005a.WH.W1
open Finset
open scoped BigOperators Matrix

theorem SAP.P005a.WH.W1.T2_L1_proof : SAP.P005a.WH.W1.T2_L1 := by
  intro n s hn hs hsn u v hu hv
  let Q : Matrix (Fin n) (Fin n) ℝ := fun i j => u i * v j
  let G : ℝ := ∑ i, u i * v i
  let A : ℝ := ∑ i, u i^2
  let B : ℝ := ∑ i, v i^2
  let D : ℝ := ∑ i, u i^2 * v i^2
  have hsle : s ≤ n := Nat.le_of_lt hsn
  have hr : ∀ i, (∑ j, Q i j) = 0 := by
    intro i
    simp only [Q, ← Finset.mul_sum, hv, mul_zero]
  have hc : ∀ j, (∑ i, Q i j) = 0 := by
    intro j
    simp only [Q, ← Finset.sum_mul, hu, zero_mul]
  have houter : ∀ S : Finset (Fin n),
      AronowAudit.Literature.principalSum n Q S = W1Z u v S := by
    intro S
    exact AronowAudit.P005.Wave1.CondP002P005P006_outer n u v S
  have hfun : (fun S : Finset (Fin n) => W1Z u v S) =
      AronowAudit.Literature.principalSum n Q := by
    funext S
    exact (houter S).symm
  have htotal : (∑ i, ∑ j, Q i j) = 0 := by
    calc
      _ = (∑ i, u i) * (∑ j, v j) := by
        simp only [Q, ← Finset.mul_sum, ← Finset.sum_mul]
      _ = 0 := by rw [hu, hv]; ring
  have hdiag : (∑ i, Q i i) = G := by
    simp [Q, G]
  have hfrob : (∑ i, ∑ j, (Q i j)^2) = A * B := by
    dsimp [Q, A, B]
    simp_rw [mul_pow, ← Finset.mul_sum, ← Finset.sum_mul]
  have htrans : (∑ i, ∑ j, Q i j * Q j i) = G^2 := by
    simpa [Q, G] using transpose_contraction u v
  have hdiagSq : (∑ i, (Q i i)^2) = D := by
    simpa [Q, D] using diagonal_square_contraction u v
  have hfirst0 := AronowAudit.P005.Wave1.qtc_expectation_positive hn hs hsle Q
  rw [← hfun] at hfirst0
  rw [hdiag, htotal, mul_zero, add_zero] at hfirst0
  have hfirst : AronowAudit.P005.expectation s (W1Z u v) = W1Alpha n s * G := by
    simpa [G, W1Alpha] using hfirst0
  have hsecond0 := AronowAudit.P005.Wave1.qtc_matrix_second_moment
    hn hs hsle Q hr hc
  rw [← hfun] at hsecond0
  rw [hdiag, hfrob, htrans, hdiagSq] at hsecond0
  let p1 : ℝ := (s : ℝ) / n
  let p2 : ℝ := (s : ℝ) * (s-1) / ((n : ℝ) * (n-1))
  let p3 : ℝ := (s : ℝ) * (s-1) * (s-2) / ((n : ℝ) * (n-1) * (n-2))
  let p4 : ℝ := (s : ℝ) * (s-1) * (s-2) * (s-3) /
    ((n : ℝ) * (n-1) * (n-2) * (n-3))
  have hnR : (4 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hsR : (1 : ℝ) ≤ (s : ℝ) := by exact_mod_cast (show 1 ≤ s by omega)
  have hsnR : (s : ℝ) ≤ (n : ℝ) := by exact_mod_cast hsle
  have hgap : (s : ℝ) = (n : ℝ) ∨ (s : ℝ) + 1 ≤ (n : ℝ) := by
    right
    exact_mod_cast (show s + 1 ≤ n by omega)
  have hcoeff0 :=
    AronowAudit.P005.Wave1.GP005B4c_four_coefficients (n : ℝ) (s : ℝ)
      hnR hsR hsnR hgap
  rcases hcoeff0 with ⟨_, _, _, _, hcoeff0⟩
  have hn0 : (n : ℝ) ≠ 0 := by linarith
  have hn1 : (n : ℝ) - 1 ≠ 0 := by linarith
  have hn2 : (n : ℝ) - 2 ≠ 0 := by linarith
  have hn3 : (n : ℝ) - 3 ≠ 0 := by linarith
  have hell : p2 - 2*p3 + p4 = W1Ell n s := by
    dsimp [p2, p3, p4, W1Ell]
    field_simp [hn0, hn1, hn2, hn3]
    <;> ring
  have hcoef : p1 - 7*p2 + 12*p3 - 6*p4 =
      W1Alpha n s - 6*W1Ell n s := by
    calc
      p1 - 7*p2 + 12*p3 - 6*p4 =
          (s : ℝ) * ((n : ℝ) - s) / ((n : ℝ) * (n-1)) -
            6 * (p2 - 2*p3 + p4) := by
              have h := hcoeff0
              change p1 - 7*p2 + 12*p3 - 6*p4 =
                (s : ℝ) * ((n : ℝ) - s) / ((n : ℝ) * (n-1)) -
                  6 * (p2 - 2*p3 + p4) at h
              simpa [p1, p2, p3, p4] using h
      _ = W1Alpha n s - 6*W1Ell n s := by rw [hell]; rfl
  have hsecond : AronowAudit.P005.expectation s (fun S => (W1Z u v S)^2) =
      (p2 - 2*p3 + p4) * (G^2 + A*B + G^2) +
        (p1 - 7*p2 + 12*p3 - 6*p4) * D := by
    simpa [p1, p2, p3, p4, G, A, B, D] using hsecond0
  have hvariance :=
    AronowAudit.P005.Wave1.GP005B4c_variance_identity hsle (W1Z u v)
  constructor
  · change AronowAudit.P005.expectation s (W1Z u v) =
      W1Alpha n s * (∑ i, u i*v i)
    rw [hfirst]
  · change AronowAudit.P005.variance s (W1Z u v) = _
    rw [hvariance, hsecond, hfirst, hell, hcoef]
    dsimp [G, A, B, D]
    ring
