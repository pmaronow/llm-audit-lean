/-
Upstream project: StatLean.
Modified for llm-audit-lean: import paths adapted and declarations not used by this repository removed.
-/
import AronowAudit.External.StatLean.AsymptoticStatistics.ParametricFamily.Defs
import AronowAudit.External.StatLean.AsymptoticStatistics.DQM.Defs
import AronowAudit.External.StatLean.AsymptoticStatistics.ForMathlib.L2
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Consequences of Differentiability in Quadratic Mean (DQM)

Reference: van der Vaart, *Asymptotic Statistics*, Theorem 7.2.
-/

open MeasureTheory Asymptotics Filter Topology
open scoped RealInnerProductSpace ENNReal

namespace AsymptoticStatistics

variable {𝓧 : Type*} [MeasurableSpace 𝓧]
variable {Θ : Type*} [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ]


/-! ## DQM ⇒ asymptotic singular-mass control (vdV §7.3)

DQM gives an **asymptotic** bound: each per-factor singular set carries
`o(1/n)` probability mass. DQM does *not* imply common
support; this is asymptotic singular-mass control, not a derivation of common support from DQM.

The "probability mass" here is the density integral `∫_A p dμ` over the singular set `A`, NOT the
bare `μ`-volume `μ A` (DQM controls density integrals, not the dominating-measure volume; a
`μ`-volume statement would be FALSE on infinite-`μ` / small-density regions). -/


end AsymptoticStatistics
