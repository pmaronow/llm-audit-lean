import SAP.P005a.WH.W2.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P005a.WH.W2.P.T9_L1

noncomputable section

open Finset
open scoped BigOperators Matrix

lemma spectral_repr {k : ℕ} (A : Matrix (Fin k) (Fin k) ℝ)
    (hA : A.IsHermitian) :
    A = (hA.eigenvectorUnitary : Matrix (Fin k) (Fin k) ℝ) *
      Matrix.diagonal hA.eigenvalues *
      (hA.eigenvectorUnitary : Matrix (Fin k) (Fin k) ℝ)ᵀ := by
  simpa [Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_eq_transpose_of_trivial, Function.comp_def] using hA.spectral_theorem

lemma exp_scaled_spectral {k : ℕ} (A : Matrix (Fin k) (Fin k) ℝ)
    (hA : A.IsHermitian) (c : ℝ) :
    NormedSpace.exp (c • A) =
      (hA.eigenvectorUnitary : Matrix (Fin k) (Fin k) ℝ) *
        Matrix.diagonal (fun i => Real.exp (c * hA.eigenvalues i)) *
        (hA.eigenvectorUnitary : Matrix (Fin k) (Fin k) ℝ)ᵀ := by
  let U : Matrix (Fin k) (Fin k) ℝ := hA.eigenvectorUnitary
  have hUmul : U * Uᵀ = 1 := by
    simpa [U, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
      using Unitary.coe_mul_star_self hA.eigenvectorUnitary
  have hUunit : IsUnit U := isUnit_iff_exists_inv.mpr ⟨Uᵀ, hUmul⟩
  have hUdet : IsUnit U.det := Matrix.isUnit_iff_isUnit_det U |>.mp hUunit
  have hUinv : U⁻¹ = Uᵀ := by
    calc
      U⁻¹ = U⁻¹ * (U * Uᵀ) := by rw [hUmul, mul_one]
      _ = (U⁻¹ * U) * Uᵀ := by rw [mul_assoc]
      _ = Uᵀ := by rw [Matrix.nonsing_inv_mul U hUdet, one_mul]
  have hscaled : c • A = U * Matrix.diagonal (fun i => c * hA.eigenvalues i) * Uᵀ := by
    let g := Unitary.conjStarAlgAut ℝ _ hA.eigenvectorUnitary
    have hs : c • A = g (c • Matrix.diagonal hA.eigenvalues) := by
      calc
        c • A = c • g (Matrix.diagonal hA.eigenvalues) :=
          congrArg (fun M => c • M) hA.spectral_theorem
        _ = g (c • Matrix.diagonal hA.eigenvalues) := by simp [g, map_smul]
    have hd : c • Matrix.diagonal hA.eigenvalues =
        Matrix.diagonal (fun i => c * hA.eigenvalues i) := by
      ext i j
      simp [Matrix.diagonal, smul_eq_mul]
    have hs' : c • A = g (Matrix.diagonal (fun i => c * hA.eigenvalues i)) := by
      calc
        c • A = g (c • Matrix.diagonal hA.eigenvalues) := hs
        _ = g (Matrix.diagonal (fun i => c * hA.eigenvalues i)) := congrArg g hd
    simpa [U, g, Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial, Function.comp_def] using hs'
  calc
    NormedSpace.exp (c • A) =
        NormedSpace.exp (U * Matrix.diagonal (fun i => c * hA.eigenvalues i) * U⁻¹) := by
          rw [hscaled, hUinv]
    _ = U * NormedSpace.exp (Matrix.diagonal (fun i => c * hA.eigenvalues i)) * U⁻¹ :=
          Matrix.exp_conj U _ hUunit
    _ = U * Matrix.diagonal (fun i => Real.exp (c * hA.eigenvalues i)) * Uᵀ := by
          rw [Matrix.exp_diagonal, hUinv]
          simp [Pi.exp_def, Real.exp_eq_exp_ℝ]

lemma shift_spectral {k : ℕ} (A : Matrix (Fin k) (Fin k) ℝ)
    (hA : A.IsHermitian) (a : ℝ) :
    a • (1 : Matrix (Fin k) (Fin k) ℝ) - A =
      (hA.eigenvectorUnitary : Matrix (Fin k) (Fin k) ℝ) *
        Matrix.diagonal (fun i => a - hA.eigenvalues i) *
        (hA.eigenvectorUnitary : Matrix (Fin k) (Fin k) ℝ)ᵀ := by
  let g := Unitary.conjStarAlgAut ℝ _ hA.eigenvectorUnitary
  have hdiag : a • (1 : Matrix (Fin k) (Fin k) ℝ) - Matrix.diagonal hA.eigenvalues =
      Matrix.diagonal (fun i => a - hA.eigenvalues i) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [Matrix.diagonal, smul_eq_mul]
    · simp [Matrix.diagonal, smul_eq_mul, hij]
  have hArepr : A = g (Matrix.diagonal hA.eigenvalues) := hA.spectral_theorem
  calc
    a • (1 : Matrix (Fin k) (Fin k) ℝ) - A =
        g (a • (1 : Matrix (Fin k) (Fin k) ℝ) - Matrix.diagonal hA.eigenvalues) := by
          calc
            _ = a • (1 : Matrix (Fin k) (Fin k) ℝ) - g (Matrix.diagonal hA.eigenvalues) :=
              congrArg (fun M => a • (1 : Matrix (Fin k) (Fin k) ℝ) - M) hArepr
            _ = g (a • (1 : Matrix (Fin k) (Fin k) ℝ) - Matrix.diagonal hA.eigenvalues) := by
              simp [g, map_sub, map_smul]
    _ = g (Matrix.diagonal (fun i => a - hA.eigenvalues i)) := by rw [hdiag]
    _ = _ := by
      simp [g, Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose,
        Matrix.conjTranspose_eq_transpose_of_trivial]

lemma shift_posSemidef {k : ℕ} (A : Matrix (Fin k) (Fin k) ℝ)
    (hA : A.IsHermitian) (a : ℝ) (hEigBound : ∀ i, hA.eigenvalues i ≤ a) :
    (a • (1 : Matrix (Fin k) (Fin k) ℝ) - A).PosSemidef := by
  rw [shift_spectral A hA a]
  have hd : (Matrix.diagonal (fun i => a - hA.eigenvalues i)).PosSemidef :=
    Matrix.PosSemidef.diagonal (fun i => sub_nonneg.mpr (hEigBound i))
  simpa [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
    using hd.mul_mul_conjTranspose_same
      (hA.eigenvectorUnitary : Matrix (Fin k) (Fin k) ℝ)

end
end SAP.P005a.WH.W2.P.T9_L1

open scoped Matrix

theorem SAP.P005a.WH.W2.T9_L1_proof : SAP.P005a.WH.W2.T9_L1 := by
  change SAP.P005a.WH.W2.spectralTraceTest
  intro k A hA
  constructor
  · have hdiag : (Matrix.diagonal (fun i => Real.exp (hA.eigenvalues i))).PosSemidef :=
      Matrix.PosSemidef.diagonal (fun i => le_of_lt (Real.exp_pos _))
    have hExp : NormedSpace.exp A =
        (hA.eigenvectorUnitary : Matrix (Fin k) (Fin k) ℝ) *
          Matrix.diagonal (fun i => Real.exp (hA.eigenvalues i)) *
          (hA.eigenvectorUnitary : Matrix (Fin k) (Fin k) ℝ)ᵀ := by
      simpa only [one_smul, one_mul] using SAP.P005a.WH.W2.P.T9_L1.exp_scaled_spectral A hA 1
    rw [hExp]
    simpa [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
      using hdiag.mul_mul_conjTranspose_same
        (hA.eigenvectorUnitary : Matrix (Fin k) (Fin k) ℝ)
  · intro a θ hθ hexists
    obtain ⟨v, hvunit, hvray⟩ := hexists
    have hexistsEigen : ∃ i, a < hA.eigenvalues i := by
      by_contra hnone
      have hall : ∀ i, hA.eigenvalues i ≤ a := by
        intro i
        by_contra hnot
        exact hnone ⟨i, lt_of_not_ge hnot⟩
      have hshift := SAP.P005a.WH.W2.P.T9_L1.shift_posSemidef A hA a hall
      have hq := hshift.dotProduct_mulVec_nonneg v
      have hqeq : star v ⬝ᵥ ((a • (1 : Matrix (Fin k) (Fin k) ℝ) - A) *ᵥ v) =
          a - SAP.P005a.WH.W2.quadratic A v := by
        have hvdot : v ⬝ᵥ v = 1 := by
          change (∑ i, v i * v i) = 1 at hvunit
          simpa [dotProduct] using hvunit
        calc
          star v ⬝ᵥ ((a • (1 : Matrix (Fin k) (Fin k) ℝ) - A) *ᵥ v) =
              v ⬝ᵥ ((a • (1 : Matrix (Fin k) (Fin k) ℝ)) *ᵥ v - A *ᵥ v) := by
                simp [star_trivial, Matrix.sub_mulVec, Matrix.smul_mulVec]
          _ = a • (v ⬝ᵥ v) - SAP.P005a.WH.W2.quadratic A v := by
                rw [dotProduct_sub, Matrix.smul_mulVec, Matrix.one_mulVec,
                  dotProduct_smul]
                simp [SAP.P005a.WH.W2.quadratic, SAP.P005a.dot, dotProduct]
          _ = a - SAP.P005a.WH.W2.quadratic A v := by rw [hvdot]; simp
      rw [hqeq] at hq
      linarith
    obtain ⟨i, hi⟩ := hexistsEigen
    have htrace : Matrix.trace (NormedSpace.exp (θ • A)) =
        ∑ j, Real.exp (θ * hA.eigenvalues j) := by
      rw [SAP.P005a.WH.W2.P.T9_L1.exp_scaled_spectral A hA θ]
      let U : Matrix (Fin k) (Fin k) ℝ := hA.eigenvectorUnitary
      have hUmul : U * Uᵀ = 1 := by
        simpa [U, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
          using Unitary.coe_mul_star_self hA.eigenvectorUnitary
      have hUunit : IsUnit U := isUnit_iff_exists_inv.mpr ⟨Uᵀ, hUmul⟩
      have hUdet : IsUnit U.det := Matrix.isUnit_iff_isUnit_det U |>.mp hUunit
      have hUinv : U⁻¹ = Uᵀ := by
        calc
          U⁻¹ = U⁻¹ * (U * Uᵀ) := by rw [hUmul, mul_one]
          _ = (U⁻¹ * U) * Uᵀ := by rw [mul_assoc]
          _ = Uᵀ := by rw [Matrix.nonsing_inv_mul U hUdet, one_mul]
      calc
        Matrix.trace (U * Matrix.diagonal (fun j => Real.exp (θ * hA.eigenvalues j)) * Uᵀ) =
            Matrix.trace (U * Matrix.diagonal (fun j => Real.exp (θ * hA.eigenvalues j)) * U⁻¹) := by
              rw [hUinv]
        _ = Matrix.trace (Matrix.diagonal (fun j => Real.exp (θ * hA.eigenvalues j))) :=
              Matrix.trace_conj hUunit _
        _ = ∑ j, Real.exp (θ * hA.eigenvalues j) := by simp [Matrix.trace_diagonal]
    unfold SAP.P005a.WH.W2.traceExp
    rw [htrace]
    apply le_trans (Real.exp_le_exp.mpr (le_of_lt (mul_lt_mul_of_pos_left hi hθ)))
    exact Finset.single_le_sum
      (s := (Finset.univ : Finset (Fin k)))
      (f := fun j => Real.exp (θ * hA.eigenvalues j))
      (fun j _ => le_of_lt (Real.exp_pos _)) (Finset.mem_univ i)
