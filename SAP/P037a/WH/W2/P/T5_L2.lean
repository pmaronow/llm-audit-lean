import SAP.P037a.WH.W2.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P037a.WH.W2.P.T5_L2

open SAP.P037a.WH.W2
open scoped BigOperators

def dInv (m : ℕ) (z : Fin (m+1) → ℝ) :
    (Fin (m+1) → ℝ) →L[ℝ] (Fin (m+1) → ℝ) := by
  letI : NormedSpace ℝ ℝ := NormedAlgebra.toNormedSpace ℝ
  exact ContinuousLinearMap.pi fun i => Fin.lastCases
    ((1 - ∑ j : Fin m, z j.castSucc) •
        (ContinuousLinearMap.proj (R := ℝ) (Fin.last m) :
          (Fin (m+1) → ℝ) →L[ℝ] ℝ) -
      z (Fin.last m) • ∑ j : Fin m,
        (ContinuousLinearMap.proj (R := ℝ) j.castSucc : (Fin (m+1) → ℝ) →L[ℝ] ℝ))
    (fun j => z (Fin.last m) •
        (ContinuousLinearMap.proj (R := ℝ) j.castSucc : (Fin (m+1) → ℝ) →L[ℝ] ℝ) +
      z j.castSucc • (ContinuousLinearMap.proj (R := ℝ) (Fin.last m) :
        (Fin (m+1) → ℝ) →L[ℝ] ℝ)) i

theorem hasFDerivAt_inverseNormalizationW2 (m : ℕ) (z : Fin (m+1) → ℝ) :
    HasFDerivAt (inverseNormalizationW2 m) (dInv m z) z := by
  change HasFDerivAt (fun x i => inverseNormalizationW2 m x i) (dInv m z) z
  unfold dInv
  rw [hasFDerivAt_pi]
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · have hs : HasFDerivAt (fun x : Fin (m+1) → ℝ => ∑ j : Fin m, x j.castSucc)
        (∑ j : Fin m, (ContinuousLinearMap.proj (R := ℝ) j.castSucc :
          (Fin (m+1) → ℝ) →L[ℝ] ℝ)) z := by
      simpa using (HasFDerivAt.fun_sum (u := Finset.univ)
        (A := fun (j : Fin m) (x : Fin (m+1) → ℝ) => x j.castSucc)
        (A' := fun j => (ContinuousLinearMap.proj (R := ℝ) j.castSucc :
          (Fin (m+1) → ℝ) →L[ℝ] ℝ))
        (by intro j hj; exact hasFDerivAt_apply j.castSucc z))
    have hq := (hasFDerivAt_const (1 : ℝ) z).sub hs
    have ht : HasFDerivAt (fun x : Fin (m+1) → ℝ => x (Fin.last m))
        (ContinuousLinearMap.proj (R := ℝ) (Fin.last m) :
          (Fin (m+1) → ℝ) →L[ℝ] ℝ) z := hasFDerivAt_apply (Fin.last m) z
    have hp := ht.mul hq
    have heq : (fun x : Fin (m+1) → ℝ =>
        x (Fin.last m) * (1 - ∑ j : Fin m, x j.castSucc)) =ᶠ[nhds z]
        ((fun x : Fin (m+1) → ℝ => x (Fin.last m)) *
          (fun x => 1 - ∑ j : Fin m, x j.castSucc)) := by
      filter_upwards [] with x
      rfl
    simpa [inverseNormalizationW2, headCoordinatesW2, appendSimplex, Fin.lastCases,
      sub_eq_add_neg, add_comm, add_left_comm, add_assoc, smul_neg] using
      hp.congr_of_eventuallyEq heq
  · have ht : HasFDerivAt (fun x : Fin (m+1) → ℝ => x (Fin.last m))
        (ContinuousLinearMap.proj (R := ℝ) (Fin.last m) :
          (Fin (m+1) → ℝ) →L[ℝ] ℝ) z := hasFDerivAt_apply (Fin.last m) z
    have hj : HasFDerivAt (fun x : Fin (m+1) → ℝ => x j.castSucc)
        (ContinuousLinearMap.proj (R := ℝ) j.castSucc :
          (Fin (m+1) → ℝ) →L[ℝ] ℝ) z := hasFDerivAt_apply j.castSucc z
    have hp := ht.mul hj
    have heq : (fun x : Fin (m+1) → ℝ => x (Fin.last m) * x j.castSucc) =ᶠ[nhds z]
        ((fun x : Fin (m+1) → ℝ => x (Fin.last m)) * (fun x => x j.castSucc)) := by
      filter_upwards [] with x
      rfl
    simpa [inverseNormalizationW2, headCoordinatesW2, appendSimplex, Fin.lastCases,
      add_comm, add_left_comm, add_assoc] using
      hp.congr_of_eventuallyEq heq

theorem dInv_entry₁₁ (m : ℕ) (z : Fin (m+1) → ℝ) (i j : Fin m) :
    LinearMap.toMatrix' (dInv m z).toLinearMap i.castSucc j.castSucc =
      if i = j then z (Fin.last m) else 0 := by
  simp [LinearMap.toMatrix'_apply, dInv, Pi.single_apply, eq_comm]

theorem dInv_entry₁₂ (m : ℕ) (z : Fin (m+1) → ℝ) (i : Fin m) :
    LinearMap.toMatrix' (dInv m z).toLinearMap i.castSucc (Fin.last m) = z i.castSucc := by
  simp [LinearMap.toMatrix'_apply, dInv, Pi.single_apply]

theorem dInv_entry₂₁ (m : ℕ) (z : Fin (m+1) → ℝ) (j : Fin m) :
    LinearMap.toMatrix' (dInv m z).toLinearMap (Fin.last m) j.castSucc =
      -z (Fin.last m) := by
  simp [LinearMap.toMatrix'_apply, dInv, Pi.single_apply]

theorem dInv_entry₂₂ (m : ℕ) (z : Fin (m+1) → ℝ) :
    LinearMap.toMatrix' (dInv m z).toLinearMap (Fin.last m) (Fin.last m) =
      1 - ∑ i : Fin m, z i.castSucc := by
  simp [LinearMap.toMatrix'_apply, dInv, Pi.single_apply]

theorem det_dInv (m : ℕ) (z : Fin (m+1) → ℝ) : (dInv m z).det = z (Fin.last m)^m := by
  let A : Matrix (Fin (m+1)) (Fin (m+1)) ℝ :=
    LinearMap.toMatrix' (dInv m z).toLinearMap
  let B := A.updateRow (Fin.last m)
    (fun j => ∑ i : Fin (m+1), A i j)
  have hBrow : (fun j => ∑ i : Fin (m+1), A i j) =
      (∑ i : Fin (m+1), A i) := by
    funext j
    simpa using (Finset.sum_apply j Finset.univ (fun i : Fin (m+1) => A i)).symm
  have hA11 (i j : Fin m) : A i.castSucc j.castSucc =
      if i = j then z (Fin.last m) else 0 := by
    exact dInv_entry₁₁ m z i j
  have hA12 (i : Fin m) : A i.castSucc (Fin.last m) = z i.castSucc :=
    dInv_entry₁₂ m z i
  have hA21 (j : Fin m) : A (Fin.last m) j.castSucc = -z (Fin.last m) :=
    dInv_entry₂₁ m z j
  have hA22 : A (Fin.last m) (Fin.last m) = 1 - ∑ i : Fin m, z i.castSucc :=
    dInv_entry₂₂ m z
  have hdetAB : B.det = A.det := by
    calc
      B.det = (A.updateRow (Fin.last m) (∑ i : Fin (m+1), A i)).det := by
        unfold B
        exact congrArg Matrix.det (congrArg (A.updateRow (Fin.last m)) hBrow)
      _ = A.det := by
        simpa using Matrix.det_updateRow_sum A (Fin.last m) (fun _ => (1 : ℝ))
  have hB11 (i j : Fin m) : B i.castSucc j.castSucc =
      if i = j then z (Fin.last m) else 0 := by
    simp [B, Matrix.updateRow_apply, hA11]
  have hB21 (j : Fin m) : B (Fin.last m) j.castSucc = 0 := by
    simp only [B, Matrix.updateRow_self]
    rw [Fin.sum_univ_castSucc]
    simp [hA11, hA21]
  have hB22 : B (Fin.last m) (Fin.last m) = 1 := by
    simp only [B, Matrix.updateRow_self]
    rw [Fin.sum_univ_castSucc]
    simp [hA12, hA22]
  have hminor : B.submatrix (Fin.succAbove (Fin.last m))
      (Fin.succAbove (Fin.last m)) =
      z (Fin.last m) • (1 : Matrix (Fin m) (Fin m) ℝ) := by
    ext i j
    simp [hB11, Fin.succAbove_last, Matrix.one_apply]
  have hminor' : B.submatrix Fin.castSucc Fin.castSucc =
      z (Fin.last m) • (1 : Matrix (Fin m) (Fin m) ℝ) := by
    simpa using hminor
  have hdetB : B.det = z (Fin.last m)^m := by
    rw [Matrix.det_succ_row B (Fin.last m), Fin.sum_univ_castSucc]
    simp only [hB21, hB22, mul_zero, zero_mul, add_zero, one_mul, Fin.succAbove_last]
    rw [hminor']
    simp [Matrix.det_smul]
  have hA : A.det = z (Fin.last m)^m := hdetAB.symm.trans hdetB
  have hlin : (dInv m z).det = A.det := by
    simp [A]
  exact hlin.trans hA

theorem inverseJacobianW2_proof : inverseJacobianW2 := by
  intro m z hz
  refine ⟨(hasFDerivAt_inverseNormalizationW2 m z).differentiableAt, ?_⟩
  have hfd : fderiv ℝ (inverseNormalizationW2 m) z = dInv m z :=
    (hasFDerivAt_inverseNormalizationW2 m z).fderiv
  rw [hfd, det_dInv]
  exact abs_of_pos (pow_pos hz.2 _)

end SAP.P037a.WH.W2.P.T5_L2

theorem SAP.P037a.WH.W2.T5_L2_proof : SAP.P037a.WH.W2.T5_L2 := by
  exact SAP.P037a.WH.W2.P.T5_L2.inverseJacobianW2_proof
