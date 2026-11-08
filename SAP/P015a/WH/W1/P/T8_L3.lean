import SAP.P015a.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open Matrix
open scoped BigOperators

namespace SAP.P015a.WH.W1.P.T8_L3

theorem residual_mulVec_eq {n K : ℕ} (W : Matrix (Fin n) (Fin (K + 2)) ℝ)
    (Y : Fin n → ℝ) (p f : ℝ) (δ : Fin (K + 2) → ℝ) :
    W.transpose.mulVec (fun i => Y i - (p + f * W.mulVec δ i)) =
      centeredResidual W Y p - f • (W.transpose * W).mulVec δ := by
  have hv : (fun i => Y i - (p + f * W.mulVec δ i)) =
      (fun i => (Y i - p) - f * W.mulVec δ i) := by
    funext i
    ring
  have hpi : (fun i => (Y i - p) - f * W.mulVec δ i) =
      (fun i => Y i - p) - f • W.mulVec δ := by
    funext i
    rfl
  rw [hv, hpi, Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_mulVec]
  rfl

theorem intercept_predictor {n K : ℕ} (W : Matrix (Fin n) (Fin (K + 2)) ℝ)
    (hW : ∀ i, W i 0 = 1) (η : ℝ) (δ : Fin (K + 2) → ℝ) :
    ∀ i, W.mulVec (interceptVector K η + δ) i = η + W.mulVec δ i := by
  intro i
  have hparam : AronowAudit.P015.affineTheta (0 : Fin (K + 2)) η 1 δ =
      interceptVector K η + δ := by
    ext j
    simp [AronowAudit.P015.affineTheta, interceptVector]
  rw [← hparam]
  simpa using AronowAudit.P015.affine_predictor W 0 hW η 1 δ i

theorem affine_fitted_predictor {n K : ℕ} (W : Matrix (Fin n) (Fin (K + 2)) ℝ)
    (hW : ∀ i, W i 0 = 1) (p f η : ℝ) (δ : Fin (K + 2) → ℝ) :
    ∀ i, W.mulVec (affineParameter K (p - f * η) f
      (interceptVector K η + δ)) i = p + f * W.mulVec δ i := by
  intro i
  have hA := AronowAudit.P015.affine_predictor W (0 : Fin (K + 2)) hW
    (p - f * η) f (interceptVector K η + δ) i
  have hparam : AronowAudit.P015.affineTheta (0 : Fin (K + 2)) (p - f * η) f
      (interceptVector K η + δ) =
      affineParameter K (p - f * η) f (interceptVector K η + δ) := by
    ext j
    simp [AronowAudit.P015.affineTheta, affineParameter, interceptVector]
    <;> split_ifs <;> ring
  rw [hparam] at hA
  rw [hA]
  have hi := intercept_predictor W hW η δ i
  rw [hi]
  ring

theorem first_taylor_fitted {n K : ℕ} (W : Matrix (Fin n) (Fin (K + 2)) ℝ)
    (hW : ∀ i, W i 0 = 1) (m : ℝ → ℝ) (η : ℝ)
    (δ : Fin (K + 2) → ℝ) :
    ∀ i, firstTaylorPolynomial m η (W.mulVec (interceptVector K η + δ) i) =
      m η + deriv m η * W.mulVec δ i := by
  intro i
  rw [intercept_predictor W hW η δ i]
  simp [firstTaylorPolynomial]

end SAP.P015a.WH.W1.P.T8_L3

theorem SAP.P015a.WH.W1.T8_L3_proof : SAP.P015a.WH.W1.T8_L3 := by
  intro n K W Y hW m η hdiff
  dsimp [SAP.P015a.WH.W1.T8_L3, wholeResidualLinearization]
  let p : ℝ := m η
  let f : ℝ := deriv m η
  let r : Fin (K + 2) → ℝ := centeredResidual W Y p
  let A : Matrix (Fin (K + 2)) (Fin (K + 2)) ℝ := W.transpose * W
  constructor
  · intro δ
    have hTaylor := SAP.P015a.WH.W1.P.T8_L3.first_taylor_fitted W hW m η δ
    have hResEq : residualEquation W (fun _ => 1) Y (firstTaylorPolynomial m η)
        (interceptVector K η + δ) =
        W.transpose.mulVec (fun i => Y i - firstTaylorPolynomial m η
          (W.mulVec (interceptVector K η + δ) i)) := by
      ext j
      simp [residualEquation, Matrix.mulVec, dotProduct, Matrix.transpose_apply]
    have hEq : residualEquation W (fun _ => 1) Y (firstTaylorPolynomial m η)
        (interceptVector K η + δ) =
        W.transpose.mulVec (fun i => Y i - (p + f * W.mulVec δ i)) := by
      rw [hResEq]
      congr 1
      funext i
      rw [hTaylor i]
    have hBase : residualEquation W (fun _ => 1) Y (firstTaylorPolynomial m η)
        (interceptVector K η + δ) = r - f • A.mulVec δ := by
      rw [hEq]
      simpa [r, A, p, f] using
        SAP.P015a.WH.W1.P.T8_L3.residual_mulVec_eq W Y p f δ
    have hAff := SAP.P015a.WH.W1.P.T8_L3.affine_fitted_predictor W hW p f η δ
    have hEq₂ : W.transpose.mulVec (fun i => Y i - W.mulVec
        (affineParameter K (p - f * η) f (interceptVector K η + δ)) i) =
        W.transpose.mulVec (fun i => Y i - (p + f * W.mulVec δ i)) := by
      congr 1
      funext i
      rw [hAff i]
    have hBase₂ : W.transpose.mulVec (fun i => Y i - W.mulVec
        (affineParameter K (p - f * η) f (interceptVector K η + δ)) i) =
        r - f • A.mulVec δ := by
      rw [hEq₂]
      simpa [r, A, p, f] using
        SAP.P015a.WH.W1.P.T8_L3.residual_mulVec_eq W Y p f δ
    constructor
    · rw [hBase]
      change r - f • A.mulVec δ = 0 ↔ f • A.mulVec δ = r
      exact (sub_eq_zero).trans eq_comm
    · rw [hBase₂]
      change r - f • A.mulVec δ = 0 ↔ f • A.mulVec δ = r
      exact (sub_eq_zero).trans eq_comm
  · intro hf θ
    let b : ℝ := p - f * η
    constructor
    · ext j
      by_cases hj : j = 0
      · subst j
        simp [affineParameter, interceptVector, b, p, f]
        field_simp [hf]
        <;> ring
      · simp [affineParameter, interceptVector, b, hj]
        field_simp [hf]
        <;> ring
    · ext j
      by_cases hj : j = 0
      · subst j
        simp [affineParameter, interceptVector, b, p, f]
        field_simp [hf]
        <;> ring
      · simp [affineParameter, interceptVector, b, hj]
        field_simp [hf]
        <;> ring
