import SAP.P037c.Defs.WholeW1
import SAP.P037c.Bridge
import AronowAudit.P037.P037_Regression

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P037c.WH.W1
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- The inverse-form WLS coefficient really minimizes the objective under full rank. -/
theorem inverse_minimum {n p : ℕ} (H : Matrix (Fin n) (Fin p) ℝ)
    (w y : Fin n → ℝ) (hw : ∀ i, 0 < w i)
    (hH : Function.Injective H.mulVec) :
    regressionMinimum w H y ((regressionMap w H).mulVec y) := by
  classical
  let _ : DecidableEq (Fin n) := fun a b => Classical.propDecidable (a = b)
  let G : Matrix (Fin p) (Fin p) ℝ := H.transpose * Matrix.diagonal w * H
  let L := regressionMap w H
  let b := L.mulVec y
  have hG : IsUnit G.det := by
    simpa only [G] using
      AronowAudit.P037.RegressionCompletion.weighted_gram_unit w H hw hH
  have hGL : G * L = H.transpose * Matrix.diagonal w := by
    dsimp only [G, L, regressionMap]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hG,
      Matrix.one_mul]
  have hz : (H.transpose * Matrix.diagonal w).mulVec (y - H.mulVec b) = 0 := by
    rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec]
    change (H.transpose * Matrix.diagonal w).mulVec y - G.mulVec (L.mulVec y) = 0
    rw [Matrix.mulVec_mulVec, hGL, sub_self]
  have hn (j : Fin p) : (∑ i, w i * (y i - H.mulVec b i) * H i j) = 0 := by
    have hdiag : (Matrix.diagonal w).mulVec (y - H.mulVec b) =
        fun i => w i * (y i - H.mulVec b i) := by
      funext i
      rw [Matrix.mulVec_diagonal]
      rfl
    have hj := congrFun hz j
    rw [← Matrix.mulVec_mulVec, hdiag] at hj
    change (∑ i, H i j * (w i * (y i - H.mulVec b i))) = 0 at hj
    convert hj using 1
    apply Finset.sum_congr rfl
    intro i _
    ring
  exact (AronowAudit.P037.regression_unique_of_normal w H y b
    (fun i => (hw i).le) hn (fun c hc => hH (funext (fun i => hc i (hw i)))) b).2 rfl

/-- An objective depends on a coefficient vector only through its fitted vector. -/
theorem minimum_transport {n p q : ℕ} (H : Matrix (Fin n) (Fin p) ℝ)
    (B : Matrix (Fin n) (Fin q) ℝ) (w y : Fin n → ℝ)
    (hle : wholeColumnSpace H ≤ wholeColumnSpace B) (a : Fin p → ℝ) (b : Fin q → ℝ)
    (hf : H.mulVec a = B.mulVec b) (hb : regressionMinimum w B y b) :
    regressionMinimum w H y a := by
  intro c
  have hc : H.mulVec c ∈ wholeColumnSpace H := ⟨c,rfl⟩
  rcases hle hc with ⟨v,hv⟩
  change B.mulVec v = H.mulVec c at hv
  simpa only [hf,hv] using hb v

/-- Translation of coefficients translates the response by the same design vector. -/
theorem minimum_shift {n p : ℕ} (H : Matrix (Fin n) (Fin p) ℝ)
    (w y : Fin n → ℝ) (theta a : Fin p → ℝ)
    (ha : regressionMinimum w H y a) :
    regressionMinimum w H (y + H.mulVec theta) (a + theta) := by
  have he (c : Fin p → ℝ) :
      (∑ i, w i * ((y + H.mulVec theta) i - H.mulVec c i)^2) =
      (∑ i, w i * (y i - H.mulVec (c - theta) i)^2) := by
    apply Finset.sum_congr rfl
    intro i _
    simp only [Pi.add_apply, Matrix.mulVec_sub, Pi.sub_apply]
    ring
  intro c
  rw [he, he]
  simpa only [add_sub_cancel_right] using ha (c - theta)

/-- A functional that kills the design kernel takes the same value on equal fits. -/
theorem estimable_equal_fit {n p : ℕ} (H : Matrix (Fin n) (Fin p) ℝ)
    (ell : (Fin p → ℝ) →ₗ[ℝ] ℝ) (he : wholeEstimable H ell)
    (a b : Fin p → ℝ) (hf : H.mulVec a = H.mulVec b) : ell a = ell b := by
  have hz := he (a-b) (by rw [Matrix.mulVec_sub, hf, sub_self])
  simpa only [map_sub, sub_eq_zero] using hz

end SAP.P037c.WH.W1
