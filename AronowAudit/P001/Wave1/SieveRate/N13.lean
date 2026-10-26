import AronowAudit.P001.Wave1.SieveRateBlueprint
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
import Mathlib.Probability.Moments.Variance

/-! A deterministic-design Gaussian law.  All integrals below are with respect
to the finite response product; no random inverse Gram matrix is integrated. -/

set_option autoImplicit false

namespace AronowAudit.P001.Wave1.SieveRate

open AronowAudit.P001 MeasureTheory ProbabilityTheory Filter Polynomial
open scoped BigOperators ENNReal NNReal Topology

noncomputable section

theorem n13_proof : N13 := by
  classical
  intro n K P hP w
  let A : Matrix (Fin K) (Fin K) ℝ := P.transpose * P
  let H : Matrix (Fin K) (Fin K) ℝ := A⁻¹
  let u : Fin K → ℝ := H.mulVec w
  let alpha : Fin n → ℝ := P.mulVec u
  have hAT : A.transpose = A := by
    simp [A, Matrix.transpose_mul]
  have hHT : H.transpose = H := by
    dsimp [H]
    rw [Matrix.transpose_nonsing_inv, hAT]
  have hAu : A.mulVec u = w := by
    change A.mulVec (A⁻¹.mulVec w) = w
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hP, Matrix.one_mulVec]
  have hscalar (y : Fin n → ℝ) : olsCoef P y ⬝ᵥ w = y ⬝ᵥ alpha := by
    change H.mulVec (P.transpose.mulVec y) ⬝ᵥ w = y ⬝ᵥ alpha
    calc
      H.mulVec (P.transpose.mulVec y) ⬝ᵥ w =
          w ⬝ᵥ H.mulVec (P.transpose.mulVec y) := dotProduct_comm _ _
      _ = w ⬝ᵥ H.transpose.mulVec (P.transpose.mulVec y) := by rw [hHT]
      _ = P.transpose.mulVec y ⬝ᵥ H.mulVec w :=
        Matrix.dotProduct_transpose_mulVec H w (P.transpose.mulVec y)
      _ = u ⬝ᵥ P.transpose.mulVec y := dotProduct_comm _ _
      _ = y ⬝ᵥ alpha := Matrix.dotProduct_transpose_mulVec P u y
  have hsquares : (∑ i : Fin n, alpha i ^ 2) = w ⬝ᵥ H.mulVec w := by
    calc
      (∑ i : Fin n, alpha i ^ 2) = alpha ⬝ᵥ alpha := by
        simp only [dotProduct, pow_two]
      _ = u ⬝ᵥ P.transpose.mulVec alpha :=
        (Matrix.dotProduct_transpose_mulVec P u alpha).symm
      _ = u ⬝ᵥ A.mulVec u := by
        dsimp [alpha, A]
        rw [Matrix.mulVec_mulVec]
      _ = u ⬝ᵥ w := by rw [hAu]
      _ = w ⬝ᵥ H.mulVec w := dotProduct_comm _ _
  have heval_map (i : Fin n) :
      (gaussVec n).map (fun y : Fin n → ℝ => y i) = gaussianReal 0 1 := by
    exact (measurePreserving_eval (fun _ : Fin n => gaussianReal 0 1) i).map_eq
  have hcoord (i : Fin n) : HasGaussianLaw (fun y : Fin n → ℝ => y i) (gaussVec n) := by
    refine ⟨(measurable_pi_apply i).aemeasurable, ?_⟩
    rw [heval_map i]
    infer_instance
  have hind : iIndepFun (fun i (y : Fin n → ℝ) => y i) (gaussVec n) := by
    exact iIndepFun_pi (fun _ : Fin n => measurable_id.aemeasurable)
  have hvec : HasGaussianLaw (fun y : Fin n → ℝ => y) (gaussVec n) := by
    exact hind.hasGaussianLaw hcoord
  let L : (Fin n → ℝ) →L[ℝ] ℝ :=
    ∑ i : Fin n, alpha i • (ContinuousLinearMap.proj i : (Fin n → ℝ) →L[ℝ] ℝ)
  have hL (y : Fin n → ℝ) : L y = y ⬝ᵥ alpha := by
    simp [L, dotProduct, mul_comm]
  have hgauss : HasGaussianLaw (fun y : Fin n → ℝ => y ⬝ᵥ alpha) (gaussVec n) := by
    have hg := hvec.map_fun L
    simpa only [hL] using hg
  have hmean_coord (i : Fin n) : (∫ y, y i ∂gaussVec n) = 0 := by
    have hm : (∫ z : ℝ, z ∂(gaussVec n).map (fun y : Fin n → ℝ => y i)) =
        ∫ y, y i ∂gaussVec n :=
      integral_map (measurable_pi_apply i).aemeasurable measurable_id.aestronglyMeasurable
    rw [heval_map i, integral_id_gaussianReal] at hm
    exact hm.symm
  have hmean : (∫ y, y ⬝ᵥ alpha ∂gaussVec n) = 0 := by
    simp only [dotProduct]
    rw [integral_finsetSum _ (fun i _ => (hcoord i).integrable.mul_const (alpha i))]
    simp only [integral_mul_const, hmean_coord, zero_mul, Finset.sum_const_zero]
  have hvariance : Var[fun y : Fin n → ℝ => y ⬝ᵥ alpha; gaussVec n] =
      ∑ i : Fin n, alpha i ^ 2 := by
    have hv := variance_sum_pi (μ := fun _ : Fin n => gaussianReal 0 1)
      (X := fun i (z : ℝ) => z * alpha i)
      (fun i => (memLp_id_gaussianReal (μ := 0) (v := 1) 2).mul_const (alpha i))
    have hsum : (∑ i : Fin n, fun y : Fin n → ℝ => y i * alpha i) =
        (fun y : Fin n → ℝ => y ⬝ᵥ alpha) := by
      funext y
      simp only [Finset.sum_apply, dotProduct]
    rw [hsum] at hv
    simpa only [gaussVec, variance_mul_const, variance_fun_id_gaussianReal,
      NNReal.coe_one, one_mul] using hv
  have hfun : (fun y => olsCoef P y ⬝ᵥ w) = (fun y : Fin n → ℝ => y ⬝ᵥ alpha) :=
    funext hscalar
  rw [hfun]
  have hlaw := hgauss.map_eq_gaussianReal
  rw [hmean, hvariance, hsquares] at hlaw
  exact hlaw

end

end AronowAudit.P001.Wave1.SieveRate
