/-
Modified for llm-audit-lean: import paths adapted and declarations not used by this repository removed.
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import AronowAudit.External.StatLean.AsymptoticStatistics.EmpiricalProcess.AbstractDonsker.PBridgeTight
import AronowAudit.External.StatLean.AsymptoticStatistics.EmpiricalProcess.AbstractDonsker.SufficiencyDiscretization
import AronowAudit.External.StatLean.AsymptoticStatistics.EmpiricalProcess.AbstractDonsker.NecessityTightness
import AronowAudit.External.StatLean.AsymptoticStatistics.EmpiricalProcess.Donsker
import AronowAudit.External.StatLean.AsymptoticStatistics.ForMathlib.WeakConvergence.Outer

/-!
# van der Vaart Theorem 18.14: abstract Donsker characterization

The abstract-Donsker property states that the empirical process `𝔾ₙ`, viewed as a
random element of `ℓ∞(F)`, converges weakly in the van der Vaart–Wellner outer sense
`⇝ₒ` to a tight `P`-Brownian-bridge law `G_P`. Van der Vaart's Theorem 18.14
(book p.261) characterizes this property by a marginal central limit theorem
and asymptotic equicontinuity.

Reference: van der Vaart, *Asymptotic Statistics* (Cambridge, 1998), Theorem
18.14 (book p.261), §19.2.
-/

namespace AsymptoticStatistics.EmpiricalProcess

open MeasureTheory Filter Topology AsymptoticStatistics
open scoped ENNReal NNReal

variable {Ω : Type*} [MeasurableSpace Ω]


end AsymptoticStatistics.EmpiricalProcess
