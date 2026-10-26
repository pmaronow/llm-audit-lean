/-
Upstream project: StatLean.
Modified for llm-audit-lean: import paths adapted and declarations not used by this repository removed.
-/
import AronowAudit.External.StatLean.AsymptoticStatistics.ForMathlib.LpSeminorm
import AronowAudit.External.StatLean.AsymptoticStatistics.ForMathlib.RnDerivSqrt
import AronowAudit.External.StatLean.AsymptoticStatistics.ForMathlib.L2
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Topology.Instances.ENNReal.Lemmas

/-!
# The `L²` norm and the integral of a square

For `f ∈ L²(μ)`, the norm is given by
`√(∫ f² dμ) = (eLpNorm f 2 μ).toReal`.

In the dominated QMD setting (van der Vaart §25.3, Lemma 25.14), a curve
`t ↦ Q_t` of probability measures dominated by a fixed σ-finite `μ` has
square-root residual
`‖√p_t − √p_0 − (t/2) g √p_0‖_{L²(μ)} / |t| → 0` as `t → 0`
along `𝓝[≠] 0`. Its consequences are square-integrability
`g · √p_0 ∈ L²(μ)` and mean zero `∫ g d(Q_0) = 0`.
The square-integrability argument uses the triangle inequality and the
unit norm of square-root probability densities. The mean-zero argument
uses Cauchy–Schwarz on the linear part of the residual and the affinity
bound `∫ √p_t √p_0 dμ ≤ 1`, with a two-sided sign argument.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

namespace AsymptoticStatistics.ForMathlib.QMDAnalytic

variable {Ω : Type*} [MeasurableSpace Ω]


/-- Bridge between the L²(μ) `eLpNorm` and the real-valued
`√(∫ f² dμ)` for `MemLp f 2 μ`. -/
lemma sqrt_integral_sq_eq_eLpNorm_toReal {μ : Measure Ω}
    {f : Ω → ℝ} (hf : MemLp f 2 μ) :
    Real.sqrt (∫ ω, f ω ^ 2 ∂μ) = (eLpNorm f 2 μ).toReal := by
  rw [hf.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
  -- Goal: √(∫ f²) = (ENNReal.ofReal ((∫ ‖f‖^2)^(1/2))).toReal
  have h2 : (2 : ℝ≥0∞).toReal = 2 := by norm_num
  -- Reduce `‖f‖^(2 : ℝ)` to `f^(2 : ℕ)` pointwise.
  have h_int_eq :
      (fun ω => ‖f ω‖ ^ (2 : ℝ≥0∞).toReal) = (fun ω => f ω ^ 2) := by
    funext ω
    rw [h2, Real.rpow_two, Real.norm_eq_abs, sq_abs]
  rw [h_int_eq]
  have h_int_nn : 0 ≤ ∫ ω, f ω ^ 2 ∂μ :=
    MeasureTheory.integral_nonneg (fun _ => sq_nonneg _)
  rw [ENNReal.toReal_ofReal (Real.rpow_nonneg h_int_nn _), h2,
      Real.sqrt_eq_rpow]
  norm_num








end AsymptoticStatistics.ForMathlib.QMDAnalytic
