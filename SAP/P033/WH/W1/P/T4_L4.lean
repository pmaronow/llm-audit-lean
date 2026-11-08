import SAP.P033.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u v w

namespace SAP.P033.WH.W1.P.T4_L4

open scoped BigOperators

noncomputable section

private def G (n p : ℕ) : Matrix (Fin (p+1)) (Fin (p+1)) ℝ :=
  wholeGridGram (shrinkingDistance n) (shrinkingKernel n) p

private def rhs (n p : ℕ) (y : Fin n → ℝ) : Fin (p+1) → ℝ :=
  fun r => ∑ j, shrinkingKernel n j * shrinkingDistance n j ^ r.val * y j

private def detMoment (n : ℕ) : ℝ :=
  shrinkingMoment n 0 * shrinkingMoment n 2 - shrinkingMoment n 1 ^ 2

private theorem fit_normal (n p : ℕ) (y : Fin n → ℝ)
    (hunit : IsUnit (G n p)) (r : Fin (p+1)) :
    ∑ s, G n p r s * wholeNormalizedFit n p y s = rhs n p y r := by
  let A := G n p
  have hdet : IsUnit A.det := A.isUnit_iff_isUnit_det.mp hunit
  have hmul : A * A⁻¹ = 1 := Matrix.mul_nonsing_inv A hdet
  have hv : Matrix.mulVec A (Matrix.mulVec A⁻¹ (rhs n p y)) = rhs n p y := by
    rw [Matrix.mulVec_mulVec, hmul, Matrix.one_mulVec]
  have hrow := congrFun hv r
  simpa [A, G, wholeNormalizedFit, wholeGridFit, rhs, wholeGridGram,
    Matrix.mulVec, dotProduct, Finset.mul_sum, mul_comm, mul_left_comm, mul_assoc] using hrow

private theorem intercept_sum (n : ℕ) (hD : detMoment n ≠ 0)
    (f : Fin n → ℝ) :
    detMoment n * (∑ j, shrinkingIntercept n j * f j) =
      shrinkingMoment n 2 * (∑ j, shrinkingKernel n j * f j) -
      shrinkingMoment n 1 * (∑ j, shrinkingKernel n j * shrinkingDistance n j * f j) := by
  have hc (j : Fin n) : detMoment n * shrinkingIntercept n j =
      shrinkingKernel n j * (shrinkingMoment n 2 - shrinkingMoment n 1 * shrinkingDistance n j) := by
    unfold detMoment at hD ⊢
    unfold shrinkingIntercept
    field_simp [hD]
  calc
    detMoment n * (∑ j, shrinkingIntercept n j * f j) =
        ∑ j, (detMoment n * shrinkingIntercept n j) * f j := by
          rw [Finset.mul_sum]
          congr 1
          funext j
          ring
    _ = ∑ j, (shrinkingKernel n j *
        (shrinkingMoment n 2 - shrinkingMoment n 1 * shrinkingDistance n j)) * f j := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [hc]
    _ = shrinkingMoment n 2 * (∑ j, shrinkingKernel n j * f j) -
        shrinkingMoment n 1 * (∑ j, shrinkingKernel n j * shrinkingDistance n j * f j) := by
          calc
            _ = ∑ j, (shrinkingMoment n 2 * (shrinkingKernel n j * f j) -
                shrinkingMoment n 1 * (shrinkingKernel n j * shrinkingDistance n j * f j)) := by
                  apply Finset.sum_congr rfl
                  intro j hj
                  ring
            _ = _ := by
                  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]

private theorem linear_normal0 (n : ℕ) (y : Fin n → ℝ)
    (hu : IsUnit (G n 1)) :
    shrinkingMoment n 0 * wholeNormalizedFit n 1 y 0 +
      shrinkingMoment n 1 * wholeNormalizedFit n 1 y 1 =
        ∑ j, shrinkingKernel n j * y j := by
  have h := fit_normal n 1 y hu ⟨0, by decide⟩
  simpa [G, wholeGridGram, rhs, shrinkingMoment, Fin.sum_univ_two] using h

private theorem linear_normal1 (n : ℕ) (y : Fin n → ℝ)
    (hu : IsUnit (G n 1)) :
    shrinkingMoment n 1 * wholeNormalizedFit n 1 y 0 +
      shrinkingMoment n 2 * wholeNormalizedFit n 1 y 1 =
        ∑ j, shrinkingKernel n j * shrinkingDistance n j * y j := by
  have h := fit_normal n 1 y hu ⟨1, by decide⟩
  simpa [G, wholeGridGram, rhs, shrinkingMoment, Fin.sum_univ_two] using h

private theorem quadratic_normal0 (n : ℕ) (y : Fin n → ℝ)
    (hu : IsUnit (G n 2)) :
    shrinkingMoment n 0 * wholeNormalizedFit n 2 y 0 +
      shrinkingMoment n 1 * wholeNormalizedFit n 2 y 1 +
      shrinkingMoment n 2 * wholeNormalizedFit n 2 y 2 =
        ∑ j, shrinkingKernel n j * y j := by
  have h := fit_normal n 2 y hu ⟨0, by decide⟩
  simpa [G, wholeGridGram, rhs, shrinkingMoment, Fin.sum_univ_succ, add_assoc] using h

private theorem quadratic_normal1 (n : ℕ) (y : Fin n → ℝ)
    (hu : IsUnit (G n 2)) :
    shrinkingMoment n 1 * wholeNormalizedFit n 2 y 0 +
      shrinkingMoment n 2 * wholeNormalizedFit n 2 y 1 +
      shrinkingMoment n 3 * wholeNormalizedFit n 2 y 2 =
        ∑ j, shrinkingKernel n j * shrinkingDistance n j * y j := by
  have h := fit_normal n 2 y hu ⟨1, by decide⟩
  simpa [G, wholeGridGram, rhs, shrinkingMoment, Fin.sum_univ_succ, add_assoc] using h

end

end SAP.P033.WH.W1.P.T4_L4

open SAP.P033.WH.W1 SAP.P033.WH.W1.P.T4_L4

theorem SAP.P033.WH.W1.T4_L4_proof : SAP.P033.WH.W1.T4_L4 := by
  intro n hn hr
  rcases AronowAudit.P033.shrinking_wls_certificate n hn with
    ⟨hm0, hm1, hm2, hd, hdp, _, _, _, _⟩
  have hdp' : 0 < shrinkingMoment n 0 * shrinkingMoment n 2 - shrinkingMoment n 1 ^ 2 := by
    simpa [SAP.P033.shrinkingMoment, AronowAudit.P033.shrinkingMoment,
      SAP.P033.shrinkingKernel, AronowAudit.P033.shrinkingKernel,
      SAP.P033.shrinkingDistance, AronowAudit.P033.shrinkingDistance] using hdp
  have hD : detMoment n ≠ 0 := by
    exact ne_of_gt (by simpa [detMoment] using hdp')
  have hu1 : IsUnit (G n 1) := (hr 1 (Or.inl rfl)).1
  have hu2 : IsUnit (G n 2) := (hr 2 (Or.inr rfl)).1
  have hlinear : ∀ y : Fin n → ℝ,
      wholeNormalizedFit n 1 y 0 = ∑ j, shrinkingIntercept n j * y j := by
    intro y
    have h0 := linear_normal0 n y hu1
    have h1 := linear_normal1 n y hu1
    have hcomb : detMoment n * wholeNormalizedFit n 1 y 0 =
        shrinkingMoment n 2 * (∑ j, shrinkingKernel n j * y j) -
        shrinkingMoment n 1 * (∑ j, shrinkingKernel n j * shrinkingDistance n j * y j) := by
      calc
        detMoment n * wholeNormalizedFit n 1 y 0 =
            shrinkingMoment n 2 * (shrinkingMoment n 0 * wholeNormalizedFit n 1 y 0 +
              shrinkingMoment n 1 * wholeNormalizedFit n 1 y 1) -
            shrinkingMoment n 1 * (shrinkingMoment n 1 * wholeNormalizedFit n 1 y 0 +
              shrinkingMoment n 2 * wholeNormalizedFit n 1 y 1) := by
                unfold detMoment
                ring
        _ = _ := by rw [h0, h1]
    have hsum := intercept_sum n hD y
    have heq : detMoment n * wholeNormalizedFit n 1 y 0 =
        detMoment n * (∑ j, shrinkingIntercept n j * y j) := hcomb.trans hsum.symm
    exact mul_left_cancel₀ hD heq
  refine ⟨hlinear, ?_⟩
  intro y
  let M : ℝ := ∑ j, shrinkingIntercept n j * shrinkingDistance n j ^ 2
  let b0 := wholeNormalizedFit n 2 y 0
  let b1 := wholeNormalizedFit n 2 y 1
  let b2 := wholeNormalizedFit n 2 y 2
  have hq0 := quadratic_normal0 n y hu2
  have hq1 := quadratic_normal1 n y hu2
  have hM : detMoment n * M =
      shrinkingMoment n 2 ^ 2 - shrinkingMoment n 1 * shrinkingMoment n 3 := by
    have ht := intercept_sum n hD (fun j => shrinkingDistance n j ^ 2)
    have hs2 : (∑ j, shrinkingKernel n j * shrinkingDistance n j ^ 2) =
        shrinkingMoment n 2 := rfl
    have hs3 : (∑ j, shrinkingKernel n j * shrinkingDistance n j *
        shrinkingDistance n j ^ 2) = shrinkingMoment n 3 := by
      unfold shrinkingMoment
      apply Finset.sum_congr rfl
      intro j hj
      ring
    dsimp [M]
    rw [hs2, hs3] at ht
    simpa [pow_two] using ht
  have hprod : detMoment n * wholeNormalizedFit n 1 y 0 =
      detMoment n * (b0 + M * b2) := by
    have hsum := intercept_sum n hD y
    have hl := hlinear y
    rw [← hl] at hsum
    calc
      detMoment n * wholeNormalizedFit n 1 y 0 =
          shrinkingMoment n 2 * (∑ j, shrinkingKernel n j * y j) -
          shrinkingMoment n 1 * (∑ j, shrinkingKernel n j * shrinkingDistance n j * y j) := hsum
      _ = detMoment n * (b0 + M * b2) := by
        calc
          _ = detMoment n * b0 +
              (shrinkingMoment n 2 ^ 2 - shrinkingMoment n 1 * shrinkingMoment n 3) * b2 := by
                rw [← hq0, ← hq1]
                unfold detMoment
                dsimp [b0, b1, b2]
                ring
          _ = detMoment n * (b0 + M * b2) := by rw [← hM]; ring
  have hcoeff := mul_left_cancel₀ hD hprod
  unfold wholeNormalizedCorrected
  dsimp [M, b0, b2] at hcoeff ⊢
  rw [hcoeff]
  ring
