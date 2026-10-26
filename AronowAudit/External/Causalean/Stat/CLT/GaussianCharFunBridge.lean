/-
Modified for llm-audit-lean: import paths adapted and declarations not used by this repository removed.
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Gaussian characteristic-function bridge for the multivariate CLT

A centered Gaussian limit can be specified by a target measure `Q` with
characteristic function
`charFun Q t = exp(−½ ∫⟪t,ψ⟫² dP)`.
At the current Mathlib pin the multivariate-Gaussian characteristic-function
formula is available as
`ProbabilityTheory.IsGaussian.charFun_eq'`
(`Mathlib/Probability/Distributions/Gaussian/CharFun.lean`):
`charFun μ t = exp(⟪t, μ[id]⟫·I − covarianceBilin μ t t / 2)`.

This file specializes the Gaussian characteristic-function formula to a centered
Gaussian measure `Q`.
-/

module
public import Mathlib.Probability.Distributions.Gaussian.CharFun

/-! # Gaussian Characteristic-Function Bridge

This file connects concrete centered Gaussian measures with the characteristic
function form used by the library's multivariate central-limit theorems. It
specializes the characteristic-function formula to measures with mean zero.

`charFun_isGaussian_centered` specializes the Mathlib Gaussian characteristic
function formula to centered Gaussian measures. -/

public section

open MeasureTheory ProbabilityTheory Complex
open scoped RealInnerProductSpace

namespace Causalean.Stat

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [CompleteSpace E]

/-- **Centered-Gaussian characteristic function.** For a Gaussian measure `Q` on `E` with
[mean zero](hyp:hmean), [its characteristic function at any point `t` equals
$\exp(-\tfrac12\,\mathrm{covarianceBilin}\ Q\ t\ t)$](goal).

    Specialisation of `IsGaussian.charFun_eq'` with `Q[id] = 0`. -/
theorem charFun_isGaussian_centered (Q : Measure E) [IsGaussian Q]
    (hmean : ∫ x, x ∂Q = 0) (t : E) :
    charFun Q t = Complex.exp (-(covarianceBilin Q t t : ℂ) / 2) := by
  rw [IsGaussian.charFun_eq']
  have h0 : (∫ x, id x ∂Q) = 0 := by simpa using hmean
  rw [h0, inner_zero_right, Complex.ofReal_zero]
  congr 1
  ring


end Causalean.Stat
