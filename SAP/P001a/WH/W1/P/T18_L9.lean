import SAP.P001a.WH.W1.Leaves
import AronowAudit.P001.Wave1.Gap.GLP0011B3
import AronowAudit.External.Causalean.Mathlib.Probability.Distributions.Gaussian.Standard

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators Classical Matrix MatrixOrder RealInnerProductSpace

noncomputable section

namespace SAP.P001a.WH.W1.P.T18_L9

lemma sqrtInv_facts {L : ℕ} (S : Matrix (Fin L) (Fin L) ℝ)
    (hS : S.PosSemidef) (hdet : IsUnit S.det) :
    ((CFC.sqrt S)⁻¹).transpose = (CFC.sqrt S)⁻¹ ∧
    (CFC.sqrt S)⁻¹ * S * ((CFC.sqrt S)⁻¹).transpose = 1 ∧
    (CFC.sqrt S)⁻¹ * (CFC.sqrt S)⁻¹ = S⁻¹ := by
  let B : Matrix (Fin L) (Fin L) ℝ := CFC.sqrt S
  let A : Matrix (Fin L) (Fin L) ℝ := B⁻¹
  have hBunit : IsUnit B := by
    apply (CFC.isUnit_sqrt_iff S hS.nonneg).2
    exact (Matrix.isUnit_iff_isUnit_det S).2 hdet
  have hBdet : IsUnit B.det := (Matrix.isUnit_iff_isUnit_det B).mp hBunit
  have hAB : A * B = 1 := by
    exact Matrix.nonsing_inv_mul B hBdet
  have hBA : B * A = 1 := by
    exact Matrix.mul_nonsing_inv B hBdet
  have hBsq : B * B = S := by
    dsimp [B]
    exact CFC.sqrt_mul_sqrt_self S hS.nonneg
  have hBself : IsSelfAdjoint B := by
    dsimp [B]
    exact (CFC.sqrt_nonneg S).isSelfAdjoint
  have hBherm : B.IsHermitian := Matrix.isHermitian_iff_isSelfAdjoint.mpr hBself
  have hBsymm : B.IsSymm := Matrix.isHermitian_iff_isSymm.mp hBherm
  have hBtranspose : B.transpose = B := by
    ext i j
    exact (Matrix.IsSymm.ext_iff.mp hBsymm) i j
  have hAtranspose : A.transpose = A := by
    dsimp [A]
    rw [Matrix.transpose_nonsing_inv, hBtranspose]
  have hA2S : (A * A) * S = 1 := by
    calc
      (A * A) * S = (A * A) * (B * B) := by rw [hBsq]
      _ = 1 := by
        calc
          (A * A) * (B * B) = A * (A * B) * B := by simp only [mul_assoc]
          _ = 1 := by simp [hAB]
  have hA2 : A * A = S⁻¹ := by
    calc
      A * A = (A * A) * (S * S⁻¹) := by
        rw [Matrix.mul_nonsing_inv S hdet, mul_one]
      _ = ((A * A) * S) * S⁻¹ := by simp only [mul_assoc]
      _ = S⁻¹ := by rw [hA2S, one_mul]
  refine ⟨?_, ?_, ?_⟩
  · exact hAtranspose
  · calc
      A * S * A.transpose = A * (B * B) * A := by rw [hBsq, hAtranspose]
      _ = 1 := by simp [mul_assoc, hAB, hBA]
  · exact hA2

lemma quad_eq_sqrtInv_normSq {L : ℕ} (S : Matrix (Fin L) (Fin L) ℝ)
    (hS : S.PosSemidef) (hdet : IsUnit S.det)
    (y : EuclideanSpace ℝ (Fin L)) :
    y.ofLp ⬝ᵥ S⁻¹.mulVec y.ofLp =
      ‖(Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S)⁻¹) y‖ ^ 2 := by
  obtain ⟨hAt, _hCov, hA2⟩ := sqrtInv_facts S hS hdet
  let A : Matrix (Fin L) (Fin L) ℝ := (CFC.sqrt S)⁻¹
  let x : Fin L → ℝ := y.ofLp
  have hvec : Matrix.vecMul (A.mulVec x) A = A.transpose.mulVec (A.mulVec x) := by
    ext i
    simp only [Matrix.vecMul, Matrix.mulVec, Matrix.transpose_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have hdot : (A.mulVec x) ⬝ᵥ (A.mulVec x) =
      x ⬝ᵥ (A.transpose * A).mulVec x := by
    calc
      (A.mulVec x) ⬝ᵥ (A.mulVec x) =
          Matrix.vecMul (A.mulVec x) A ⬝ᵥ x := Matrix.dotProduct_mulVec _ _ _
      _ = A.transpose.mulVec (A.mulVec x) ⬝ᵥ x := by rw [hvec]
      _ = x ⬝ᵥ A.transpose.mulVec (A.mulVec x) := by
        exact dotProduct_comm _ _
      _ = x ⬝ᵥ (A.transpose * A).mulVec x := by rw [← Matrix.mulVec_mulVec]
  have hnorm : ‖(Matrix.toEuclideanCLM (𝕜 := ℝ) A) y‖ ^ 2 =
      (A.mulVec x) ⬝ᵥ (A.mulVec x) := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp only [Matrix.ofLp_toEuclideanCLM]
    change ∑ i, (A.mulVec x i) ^ 2 =
      ∑ i, (A.mulVec x i) * (A.mulVec x i)
    exact Finset.sum_congr rfl fun i _ => by ring
  calc
    y.ofLp ⬝ᵥ S⁻¹.mulVec y.ofLp = x ⬝ᵥ (A.transpose * A).mulVec x := by
      dsimp [x]
      rw [hAt, hA2]
    _ = ‖(Matrix.toEuclideanCLM (𝕜 := ℝ) A) y‖ ^ 2 := by rw [← hdot, hnorm]

end SAP.P001a.WH.W1.P.T18_L9

theorem SAP.P001a.WH.W1.T18_L9_proof : SAP.P001a.WH.W1.T18_L9 := by
  classical
  intro p L hL V hV R hSdet
  have _hL := hL
  let S : Matrix (Fin L) (Fin L) ℝ := R * V * R.transpose
  have hS : S.PosSemidef := by
    dsimp [S]
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using hV.mul_mul_conjTranspose_same R
  let G : Measure (EuclideanSpace ℝ (Fin p)) :=
    multivariateGaussian (0 : EuclideanSpace ℝ (Fin p)) V
  let TR : EuclideanSpace ℝ (Fin p) →L[ℝ] EuclideanSpace ℝ (Fin L) :=
    AronowAudit.P001.Wave1.GLP0011B3.ProbabilityTheory.matrixToEuclideanCLMRect R
  let TS : EuclideanSpace ℝ (Fin L) →L[ℝ] EuclideanSpace ℝ (Fin L) :=
    Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S)⁻¹
  let q : EuclideanSpace ℝ (Fin L) → ℝ := fun y => y.ofLp ⬝ᵥ S⁻¹.mulVec y.ofLp
  let f : (Fin p → ℝ) → ℝ := fun z => (R.mulVec z) ⬝ᵥ S⁻¹.mulVec (R.mulVec z)
  have hqmeas : Measurable q := by
    dsimp [q]
    fun_prop
  have hTR : G.map TR = multivariateGaussian (0 : EuclideanSpace ℝ (Fin L)) S := by
    rw [AronowAudit.P001.Wave1.GLP0011B3.ProbabilityTheory.multivariateGaussian_map_rectangular
      R (0 : EuclideanSpace ℝ (Fin p)) hV]
    simp [S, AronowAudit.P001.Wave1.GLP0011B3.ProbabilityTheory.matrixToEuclideanCLMRect]
  have hcomp : (normalVectorLaw V).map f = (G.map TR).map q := by
    unfold normalVectorLaw
    change (Measure.map f (Measure.map (fun z : EuclideanSpace ℝ (Fin p) => fun j => z j) G)) =
      Measure.map q (Measure.map TR G)
    calc
      (Measure.map f (Measure.map (fun z : EuclideanSpace ℝ (Fin p) => fun j => z j) G)) =
          Measure.map (fun z : EuclideanSpace ℝ (Fin p) => f (fun j => z j)) G :=
            Measure.map_map (by fun_prop) (by fun_prop)
      _ = Measure.map (fun z : EuclideanSpace ℝ (Fin p) => q (TR z)) G := by
            refine Measure.map_congr (ae_of_all _ fun z => ?_)
            simp [f, q, TR,
              AronowAudit.P001.Wave1.GLP0011B3.ProbabilityTheory.ofLp_matrixToEuclideanCLMRect]
      _ = Measure.map q (Measure.map TR G) :=
            (Measure.map_map hqmeas TR.continuous.measurable).symm
  have hwhite : (multivariateGaussian (0 : EuclideanSpace ℝ (Fin L)) S).map TS =
      stdGaussian (EuclideanSpace ℝ (Fin L)) := by
    rw [ProbabilityTheory.multivariateGaussian_map_toEuclideanCLM
      (CFC.sqrt S)⁻¹ (0 : EuclideanSpace ℝ (Fin L)) hS]
    have hfacts := SAP.P001a.WH.W1.P.T18_L9.sqrtInv_facts S hS hSdet
    rcases hfacts with ⟨_hAt, hcov, _hA2⟩
    have hcov' : (CFC.sqrt S)⁻¹ * S * ((CFC.sqrt S)⁻¹).conjTranspose = 1 := by
      simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using hcov
    change multivariateGaussian
      (Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S)⁻¹ (0 : EuclideanSpace ℝ (Fin L)))
      ((CFC.sqrt S)⁻¹ * S * ((CFC.sqrt S)⁻¹).conjTranspose) =
        stdGaussian (EuclideanSpace ℝ (Fin L))
    calc
      multivariateGaussian
          (Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S)⁻¹ (0 : EuclideanSpace ℝ (Fin L)))
          ((CFC.sqrt S)⁻¹ * S * ((CFC.sqrt S)⁻¹).conjTranspose) =
        multivariateGaussian (0 : EuclideanSpace ℝ (Fin L)) 1 := by
          rw [hcov']
          simp
      _ = stdGaussian (EuclideanSpace ℝ (Fin L)) :=
        ProbabilityTheory.multivariateGaussian_zero_one
  have hquad : ∀ y : EuclideanSpace ℝ (Fin L), q y = ‖TS y‖ ^ 2 := by
    intro y
    simpa [q, TS] using
      SAP.P001a.WH.W1.P.T18_L9.quad_eq_sqrtInv_normSq S hS hSdet y
  calc
    (normalVectorLaw V).map f = (G.map TR).map q := hcomp
    _ = (multivariateGaussian (0 : EuclideanSpace ℝ (Fin L)) S).map
        (fun y => ‖TS y‖ ^ 2) := by
      rw [hTR]
      refine Measure.map_congr (ae_of_all _ fun y => ?_)
      exact hquad y
    _ = ((multivariateGaussian (0 : EuclideanSpace ℝ (Fin L)) S).map TS).map
        (fun y => ‖y‖ ^ 2) := by
      rw [Measure.map_map (by fun_prop) (by fun_prop)]
      rfl
    _ = wholeChiSquare L := by
      rw [hwhite]
      change (Causalean.Mathlib.stdGaussian (EuclideanSpace ℝ (Fin L))).map
          (fun y => ‖y‖ ^ 2) = wholeChiSquare L
      rw [Causalean.Mathlib.stdGaussian_map_normSq_eq_pi, finrank_euclideanSpace_fin]
      unfold wholeChiSquare
      rfl
