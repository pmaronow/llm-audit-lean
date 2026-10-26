/-
Modified for llm-audit-lean: import paths adapted and declarations not used by this repository removed.
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# The χ²_d distribution as the law of the squared norm of a standard Gaussian

The chi-squared distribution with `d` degrees of freedom is *defined* here as the
law of `‖W‖²` where `W` is the standard `d`-dimensional Gaussian
(`Causalean/Mathlib/Probability/Distributions/Gaussian/Standard.lean`, `stdGaussian`).  This is the textbook
definition (sum of `d` independent squared standard normals) and is exactly the
target produced by whitening the multivariate-CLT Gaussian limit through a Wald
quadratic form.

The connection to the `Gamma(d/2, 1/2)` density (`ProbabilityTheory.gammaMeasure`)
is a separate, much deeper analytic fact and is *not* developed here; Mathlib has
no chi-squared distribution.

Key declarations:

* `chiSqDist d` — the χ²_d law on `ℝ`, `(stdGaussian (EuclideanSpace ℝ (Fin d))).map ‖·‖²`.
* `IsProbabilityMeasure (chiSqDist d)`.
* `stdGaussian_map_linearIsometryEquiv` — `stdGaussian` is invariant under linear
  isometry equivalences (proved via characteristic functions).
* `stdGaussian_map_normSq` — the law of `‖·‖²` under `stdGaussian E` depends only
  on `finrank E`, equalling `chiSqDist (finrank ℝ E)`.
-/

module
public import AronowAudit.External.Causalean.Stat.CLT.GaussianCharFunBridge
public import AronowAudit.External.Causalean.Mathlib.Probability.Distributions.Gaussian.Standard

/-! # Chi-Squared Distribution

This file defines the chi-squared distribution with $d$ degrees of freedom as
the law of the squared norm of a standard $d$-dimensional Gaussian vector. It
establishes invariance facts needed for Wald limit distributions.

The main declarations are `chiSqDist`, the probability-measure instance for
that law, `stdGaussian_map_linearIsometryEquiv`, the dimension-only identity
`stdGaussian_map_normSq`. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Complex Causalean.Mathlib
open scoped RealInnerProductSpace

namespace Causalean.Stat

local notation "stdGaussian" => Causalean.Mathlib.stdGaussian

/-- For [a nonnegative integer number of degrees of freedom](hyp:d), the
[chi-squared distribution](goal) is the probability law on the real line of
the squared Euclidean norm of a standard Gaussian vector with that many
coordinates. -/
noncomputable def chiSqDist (d : ℕ) : Measure ℝ :=
  (stdGaussian (EuclideanSpace ℝ (Fin d))).map (fun w => ‖w‖ ^ 2)

/-- For [every nonnegative integer number of degrees of freedom](hyp:d), the
[chi-squared distribution with that number of degrees of freedom is a probability law](goal). -/
instance (d : ℕ) : IsProbabilityMeasure (chiSqDist d) := by
  unfold chiSqDist
  infer_instance

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- **`stdGaussian` is invariant under linear isometry equivalences.**  Pushing
the standard Gaussian forward along an inner-product isometry yields the standard
Gaussian on the target.  Proved by matching characteristic functions: both sides
are centered Gaussians whose covariance form is the inner product (preserved by
the isometry). -/
theorem stdGaussian_map_linearIsometryEquiv
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]
    (ι : E ≃ₗᵢ[ℝ] F) :
    (stdGaussian E).map ι = stdGaussian F := by
  set L : E →L[ℝ] F := (ι : E →L[ℝ] F) with hL
  have hmapL : (stdGaussian E).map ι = (stdGaussian E).map L := rfl
  haveI : IsGaussian ((stdGaussian E).map L) := by
    rw [← hmapL]; exact isGaussian_map_equiv ι.toContinuousLinearEquiv
  -- mean of the pushforward is `0`
  have hmean_map : ∫ x, x ∂((stdGaussian E).map L) = 0 := by
    have hstep : ∫ x, x ∂((stdGaussian E).map L) = L (∫ x, x ∂(stdGaussian E)) := by
      rw [integral_map (by fun_prop) (by fun_prop)]
      exact ContinuousLinearMap.integral_comp_comm L IsGaussian.integrable_id
    rw [hstep, show ∫ x, x ∂(stdGaussian E) = 0 from integral_id_stdGaussian, map_zero]
  refine Measure.ext_of_charFun ?_
  funext t
  have hmemLp : MemLp id 2 (stdGaussian E) := IsGaussian.memLp_two_id
  have hcoveq : covarianceBilin ((stdGaussian E).map L) t t
      = covarianceBilin (stdGaussian F) t t := by
    rw [covarianceBilin_map hmemLp, ι.adjoint_eq_symm]
    simp only [Causalean.Mathlib.stdGaussian, ProbabilityTheory.covarianceBilin_stdGaussian]
    exact ι.symm.inner_map_map t t
  rw [hmapL, charFun_isGaussian_centered _ hmean_map t,
    charFun_isGaussian_centered _
      (show ∫ x, x ∂(stdGaussian F) = 0 from integral_id_stdGaussian) t, hcoveq]

/-- [The law of the squared norm under the standard Gaussian distribution on a
finite-dimensional real inner product space equals the chi-squared distribution
whose degrees of freedom is the space's dimension](goal). -/
theorem stdGaussian_map_normSq :
    (stdGaussian E).map (fun x => ‖x‖ ^ 2) = chiSqDist (Module.finrank ℝ E) := by
  classical
  set d := Module.finrank ℝ E with hd
  -- the standard orthonormal basis gives an isometry `E ≃ₗᵢ EuclideanSpace ℝ (Fin d)`
  set ι : E ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d) := (stdOrthonormalBasis ℝ E).repr with hι
  rw [chiSqDist, ← stdGaussian_map_linearIsometryEquiv ι,
    Measure.map_map (by fun_prop) (by fun_prop)]
  refine Measure.map_congr (ae_of_all _ fun x => ?_)
  simp only [Function.comp_apply]
  rw [ι.norm_map]


end Causalean.Stat
