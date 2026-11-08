import SAP.P001a.WH.W1.Leaves
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.Analysis.Matrix.Hermitian
import Mathlib.Analysis.CStarAlgebra.Matrix

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped RealInnerProductSpace

namespace SAP.P001a.WH.W1.P.T6_L4

lemma quadratic_eq_centered {K : ℕ} (G : Matrix (Fin K) (Fin K) ℝ)
    (v : Fin K → ℝ) (hv : (∑ k, (v k)^2) = 1) :
    (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin K) (G - 1)).reApplyInnerSelf
        (WithLp.toLp 2 v) =
      (∑ j, ∑ k, v j * G j k * v k) - 1 := by
  rw [ContinuousLinearMap.reApplyInnerSelf_apply, real_inner_comm,
    Matrix.inner_toEuclideanCLM]
  change dotProduct v (Matrix.mulVec (G - 1) v) = _
  simp [dotProduct, Matrix.mulVec, Finset.mul_sum, Finset.sum_sub_distrib, Matrix.one_apply,
    Matrix.sub_apply, mul_sub, sub_mul, mul_assoc]
  simpa [pow_two] using hv

lemma rayleigh_eq_abs_centered {K : ℕ} (G : Matrix (Fin K) (Fin K) ℝ)
    (v : Fin K → ℝ) (hv : (∑ k, (v k)^2) = 1) :
    |(Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin K) (G - 1)).rayleighQuotient
        (WithLp.toLp 2 v)| = |(∑ j, ∑ k, v j * G j k * v k) - 1| := by
  rw [ContinuousLinearMap.rayleighQuotient, quadratic_eq_centered G v hv]
  simp [EuclideanSpace.real_norm_sq_eq, hv]

end SAP.P001a.WH.W1.P.T6_L4

theorem SAP.P001a.WH.W1.T6_L4_proof : SAP.P001a.WH.W1.T6_L4 := by
  intro K hK G hG
  let D : Set ℝ := {r | ∃ v : Fin K → ℝ, (∑ k, (v k)^2) = 1 ∧
    r = |(∑ j, ∑ k, v j * G j k * v k) - 1|}
  let T : EuclideanSpace ℝ (Fin K) →L[ℝ] EuclideanSpace ℝ (Fin K) :=
    Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin K) (G - 1)
  have hA : (G - 1).IsSymm := by
    rw [Matrix.IsSymm] at hG ⊢
    simp [Matrix.transpose_sub, hG]
  have hHerm : (G - 1).IsHermitian := by
    exact Matrix.isHermitian_iff_isSymm.mpr hA
  have hT : T.IsSymmetric := by
    simpa [T, Matrix.coe_toEuclideanCLM_eq_toEuclideanLin, Module.End.one_eq_id] using
      (Matrix.isSymmetric_toEuclideanLin_iff (A := G - 1)).mpr hHerm
  have hD_nonempty : D.Nonempty := by
    let e : Fin K → ℝ := fun i => if i = ⟨0, hK⟩ then 1 else 0
    refine ⟨|(∑ j, ∑ k, e j * G j k * e k) - 1|, ?_⟩
    refine ⟨e, ?_, rfl⟩
    simp [e]
  have hD_bdd : BddAbove D := by
    refine ⟨‖T‖, ?_⟩
    rintro r ⟨v, hv, rfl⟩
    rw [← SAP.P001a.WH.W1.P.T6_L4.rayleigh_eq_abs_centered G v hv]
    exact T.rayleighQuotient_le_norm (WithLp.toLp 2 v)
  have hsup_le : sSup D ≤ ⨆ x : EuclideanSpace ℝ (Fin K), |T.rayleighQuotient x| := by
    apply csSup_le hD_nonempty
    rintro r ⟨v, hv, rfl⟩
    exact le_ciSup_of_le T.bddAbove_rayleighQuotient (WithLp.toLp 2 v)
      (le_of_eq (by simpa [T] using
        (SAP.P001a.WH.W1.P.T6_L4.rayleigh_eq_abs_centered G v hv).symm))
  have hzero_le : 0 ≤ sSup D := by
    rcases hD_nonempty with ⟨r, ⟨v, hv, rfl⟩⟩
    exact (abs_nonneg _).trans (le_csSup hD_bdd ⟨v, hv, rfl⟩)
  have hiSup_le : (⨆ x : EuclideanSpace ℝ (Fin K), |T.rayleighQuotient x|) ≤ sSup D := by
    refine ciSup_le fun x => ?_
    by_cases hx : x = 0
    · subst x
      simpa using hzero_le
    · let v : Fin K → ℝ := fun i => x i / ‖x‖
      have hnorm : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
      have hv : (∑ i, (v i)^2) = 1 := by
        change (∑ i, (x i / ‖x‖)^2) = 1
        calc
          (∑ i, (x i / ‖x‖)^2) = (∑ i, (x i)^2) / (‖x‖ ^ 2) := by
            simp_rw [div_pow]
            rw [← Finset.sum_div]
          _ = ‖x‖ ^ 2 / (‖x‖ ^ 2) := by rw [EuclideanSpace.real_norm_sq_eq]
          _ = 1 := div_self (pow_ne_zero 2 hnorm)
      have hxnormed : (‖x‖ : ℝ) • WithLp.toLp 2 v = x := by
        ext i
        calc
          ‖x‖ * (x.ofLp i * ‖x‖⁻¹) = (‖x‖ * ‖x‖⁻¹) * x.ofLp i := by ring
          _ = x.ofLp i := by rw [mul_inv_cancel₀ hnorm, one_mul]
      have hsmul := T.rayleigh_smul (WithLp.toLp 2 v) hnorm
      rw [hxnormed] at hsmul
      have hval : |T.rayleighQuotient (WithLp.toLp 2 v)| =
          |(∑ j, ∑ k, v j * G j k * v k) - 1| := by
        simpa [T] using SAP.P001a.WH.W1.P.T6_L4.rayleigh_eq_abs_centered G v hv
      have hmem : |T.rayleighQuotient (WithLp.toLp 2 v)| ∈ D := by
        rw [hval]
        exact ⟨v, hv, rfl⟩
      rw [hsmul]
      exact le_csSup hD_bdd hmem
  have hsup : sSup D = ⨆ x : EuclideanSpace ℝ (Fin K), |T.rayleighQuotient x| :=
    le_antisymm hsup_le hiSup_le
  calc
    gramDeviation G = sSup D := rfl
    _ = ⨆ x : EuclideanSpace ℝ (Fin K), |T.rayleighQuotient x| := hsup
    _ = ‖T‖ := (ContinuousLinearMap.norm_eq_iSup_rayleighQuotient T hT).symm
    _ = ‖(Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin K)) (G - 1)‖ := rfl
