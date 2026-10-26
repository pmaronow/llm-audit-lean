/-
Upstream project: StatLean.
Modified for llm-audit-lean: import paths adapted and declarations not used by this repository removed.
-/
import AronowAudit.External.StatLean.AsymptoticStatistics.Core.QMDPath
import AronowAudit.External.StatLean.AsymptoticStatistics.ForMathlib.QMDAnalytic
import AronowAudit.External.StatLean.AsymptoticStatistics.ParametricFamily.Defs
import AronowAudit.External.StatLean.AsymptoticStatistics.DQM.Defs
import AronowAudit.External.StatLean.AsymptoticStatistics.ParametricFamily.FisherInformation
import AronowAudit.External.StatLean.AsymptoticStatistics.LocalAsymptoticNormality.LANExpansion
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.Analysis.InnerProductSpace.EuclideanDist

/-!
# Quadratic-mean-differentiable paths and one-dimensional LAN

Imports for abstract quadratic-mean-differentiable paths and local asymptotic normality.

Reference: van der Vaart, *Asymptotic Statistics*, §25.3.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

namespace AsymptoticStatistics.LowerBounds.T6_FinDimLAN

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

namespace QMDPath

open AsymptoticStatistics.Core.Hilbert

/-- L²(γ.dominating)-membership of `√p_t` for any `t`.

For each `t`, `(γ.curve t)` is a probability measure absolutely continuous
w.r.t. `γ.dominating`, and `γ.dominating` is σ-finite. The conclusion is the
`RnDerivSqrt.memLp_sqrt_rnDeriv` Hellinger-type bound:
`‖√p_t‖²_{L²(γ.dominating)} = (γ.curve t)(univ) = 1`. -/
theorem memLp_sqrt_rnDeriv (γ : AsymptoticStatistics.Core.QMDPath.QMDPath P)
    (t : ℝ) :
    MemLp (fun ω => Real.sqrt ((γ.curve t).rnDeriv γ.dominating ω).toReal)
      2 γ.dominating := by
  have : IsProbabilityMeasure (γ.curve t) := γ.curve_isProbability t
  have : SigmaFinite γ.dominating := γ.dominating_sigmaFinite
  exact AsymptoticStatistics.ForMathlib.RnDerivSqrt.memLp_sqrt_rnDeriv
    (γ.curve_absContinuous t)








end QMDPath
end AsymptoticStatistics.LowerBounds.T6_FinDimLAN
