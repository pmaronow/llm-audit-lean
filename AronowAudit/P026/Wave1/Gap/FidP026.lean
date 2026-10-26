import AronowAudit.P026.P026_PaperScope
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

namespace AronowAudit.P026.Wave1
open scoped BigOperators
open AronowAudit.P026.PaperScope

/-- Adjoin the intercept used by the formula lm(Yd ~ X). -/
def designWithIntercept {I : Type*} (K : ℕ)
    (X : Matrix I (Fin K) ℝ) : Matrix I (Fin (K + 1)) ℝ :=
  fun i => Fin.cases (1 : ℝ) (X i)

/-- The coefficient-to-response map, with the Euclidean norm on responses. -/
noncomputable def olsDesignMap {I : Type*} [Fintype I] (K : ℕ)
    (V : Matrix I (Fin K) ℝ) :
    (Fin K → ℝ) →ₗ[ℝ] EuclideanSpace ℝ I :=
  ((EuclideanSpace.equiv I ℝ).symm.toLinearEquiv.toLinearMap).comp V.mulVecLin

/-- All response vectors attainable by the design, irrespective of rank. -/
noncomputable def olsColumnSpace {I : Type*} [Fintype I] (K : ℕ)
    (V : Matrix I (Fin K) ℝ) : Submodule ℝ (EuclideanSpace ℝ I) :=
  LinearMap.range (olsDesignMap K V)

/-- Ordinary unweighted least-squares fitted values. No coefficient is selected. -/
noncomputable def olsFitted {I : Type*} [Fintype I] (K : ℕ)
    (V : Matrix I (Fin K) ℝ) (y : I → ℝ) : I → ℝ :=
  (EuclideanSpace.equiv I ℝ)
    ((olsColumnSpace K V).starProjection ((EuclideanSpace.equiv I ℝ).symm y))

/-- A fitted vector lies in the column space and minimizes the residual sum of squares. -/
def IsLeastSquaresFitted {I : Type*} [Fintype I] (K : ℕ)
    (V : Matrix I (Fin K) ℝ) (y z : I → ℝ) : Prop :=
  (∃ β : Fin K → ℝ, V.mulVec β = z) ∧
  ∀ β : Fin K → ℝ,
    (∑ i, (y i - z i)^2) ≤ (∑ i, (y i - (V.mulVec β) i)^2)

private theorem T16_olsDesignMap_apply {I : Type*} [Fintype I]
    (K : ℕ) (V : Matrix I (Fin K) ℝ) (β : Fin K → ℝ) (i : I) :
    olsDesignMap K V β i = V.mulVec β i := rfl

/-- Pythagoras separates the optimal residual loss from the fitted-vector discrepancy. -/
private theorem T16_loss_decomposition {I : Type*} [Fintype I]
    (K : ℕ) (V : Matrix I (Fin K) ℝ) (y : I → ℝ) (β : Fin K → ℝ) :
    (∑ i, (y i - V.mulVec β i)^2) =
      (∑ i, (y i - olsFitted K V y i)^2) +
      (∑ i, (olsFitted K V y i - V.mulVec β i)^2) := by
  let C := olsColumnSpace K V
  let u := (EuclideanSpace.equiv I ℝ).symm y
  let p := C.starProjection u
  have hβ : olsDesignMap K V β ∈ C := ⟨β, rfl⟩
  have hp : p ∈ C := C.starProjection_apply_mem u
  have ho : inner ℝ (u - p) (p - olsDesignMap K V β) = 0 :=
    C.starProjection_inner_eq_zero u _ (C.sub_mem hp hβ)
  have h := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
    (u - p) (p - olsDesignMap K V β) ho
  have hadd : u - p + (p - olsDesignMap K V β) = u - olsDesignMap K V β := by
    abel
  rw [hadd] at h
  simpa only [← sq, EuclideanSpace.real_norm_sq_eq, PiLp.sub_apply,
    T16_olsDesignMap_apply, u, p, C, olsFitted, EuclideanSpace.equiv,
    PiLp.continuousLinearEquiv_apply, PiLp.continuousLinearEquiv_symm_apply,
    PiLp.toLp_apply] using h

/-- Projection is an attainable least-squares fit, and the fitted vector is unique. -/
theorem olsFitted_spec {I : Type*} [Fintype I]
    (K : ℕ) (V : Matrix I (Fin K) ℝ) (y : I → ℝ) :
    IsLeastSquaresFitted K V y (olsFitted K V y) ∧
    ∀ z : I → ℝ, IsLeastSquaresFitted K V y z → z = olsFitted K V y := by
  classical
  obtain ⟨β, hβ⟩ := (olsColumnSpace K V).starProjection_apply_mem
    ((EuclideanSpace.equiv I ℝ).symm y)
  have hfit : V.mulVec β = olsFitted K V y := by
    exact congrArg (EuclideanSpace.equiv I ℝ) hβ
  refine ⟨⟨⟨β, hfit⟩, ?_⟩, ?_⟩
  · intro γ
    have h := T16_loss_decomposition K V y γ
    have hn : 0 ≤ ∑ i, (olsFitted K V y i - V.mulVec γ i)^2 :=
      Finset.sum_nonneg fun _ _ => sq_nonneg _
    linarith
  · intro z hz
    obtain ⟨γ, hγ⟩ := hz.1
    have hmin := hz.2 β
    rw [hfit, ← hγ] at hmin
    have h := T16_loss_decomposition K V y γ
    have hzero : (∑ i, (olsFitted K V y i - V.mulVec γ i)^2) = 0 := by
      have hn : 0 ≤ ∑ i, (olsFitted K V y i - V.mulVec γ i)^2 :=
        Finset.sum_nonneg fun _ _ => sq_nonneg _
      linarith
    rw [← hγ]
    funext i
    have hi : (olsFitted K V y i - V.mulVec γ i)^2 ≤ 0 := by
      calc
        _ ≤ ∑ j, (olsFitted K V y j - V.mulVec γ j)^2 :=
          Finset.single_le_sum (fun j _ => sq_nonneg _) (Finset.mem_univ i)
        _ = 0 := hzero
    exact (sub_eq_zero.mp (sq_eq_zero_iff.mp (le_antisymm hi (sq_nonneg _)))).symm


/-- Convert the potential-outcome residual contrast to the observed-outcome residual contrast. -/
private theorem T16_generalized_observed_residual
    {Ω I : Type*} [Fintype Ω] [Fintype I] [DecidableEq I]
    (D : Design Ω I ℝ) (N : ℕ) (y1 y0 : I → ℝ) (f : Ω → I → ℝ) (w : Ω) :
    generalized D N y1 y0 f w =
      ((∑ i, indicator D true w i * (observed D y1 y0 w i - f w i) /
          marginal D true i) -
       (∑ i, indicator D false w i * (observed D y1 y0 w i - f w i) /
          marginal D false i)) / (N : ℝ) := by
  rw [generalized_residual]
  simp [ht, htTotal, mul_sub, observed_mask]

/-- T16(b) with an intercept and exact least-squares fitted values, without a rank restriction. -/
theorem all_unit_OLS_bias_T16_rank_unrestricted
    {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    (E : UnitExperiment I) (K : ℕ) (X : Matrix I (Fin K) ℝ)
    (y1 y0 : I → ℝ) :
    let V := designWithIntercept K X
    let f : (I → Bool) → I → ℝ :=
      fun w => olsFitted (K + 1) V (observed E.design y1 y0 w)
    (∀ w, IsLeastSquaresFitted (K + 1) V (observed E.design y1 y0 w) (f w)) ∧
    (∀ w,
      generalized E.design (Fintype.card I) y1 y0 f w =
        ((∑ i, indicator E.design true w i *
            (observed E.design y1 y0 w i - f w i) / marginal E.design true i) -
         (∑ i, indicator E.design false w i *
            (observed E.design y1 y0 w i - f w i) / marginal E.design false i)) /
          (Fintype.card I : ℝ)) ∧
    expectation E.design (generalized E.design (Fintype.card I) y1 y0 f) -
        ate (Fintype.card I) y1 y0 =
      -(∑ i, covariance E.design
          (fun w => indicator E.design true w i) (fun w => f w i) *
          (1 / marginal E.design true i + 1 / marginal E.design false i)) /
        (Fintype.card I : ℝ) := by
  dsimp only
  refine ⟨fun w => (olsFitted_spec (K + 1) _ _).1, ?_, ?_⟩
  · intro w
    exact T16_generalized_observed_residual E.design (Fintype.card I) y1 y0 _ w
  · exact generalized_bias_two_arm E.design E.probability E.marginals
      (Fintype.card I) Fintype.card_pos y1 y0 _


end AronowAudit.P026.Wave1
