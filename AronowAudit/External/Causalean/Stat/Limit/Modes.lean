/-
Modified for llm-audit-lean: import paths adapted and declarations not used by this repository removed.
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
module
public import AronowAudit.External.Causalean.Stat.Coupling.Basic
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Topology.MetricSpace.Pseudo.Constructions


public import Mathlib.MeasureTheory.Function.ConvergenceInDistribution

/-!
# Modes of stochastic convergence

## Using Mathlib's results

Mathlib's `Mathlib.MeasureTheory.Function.ConvergenceInDistribution` already supplies
`MeasureTheory.TendstoInDistribution.continuous_comp` (continuous mapping),
`MeasureTheory.TendstoInDistribution.prodMk_of_tendstoInMeasure_const` and its additive and
multiplicative Slutsky corollaries, `MeasureTheory.tendstoInDistribution_of_tendstoInMeasure_sub`
(converging together), and `MeasureTheory.TendstoInMeasure.tendstoInDistribution`. The fixed-space
almost-sure-to-probability results remain in
`Mathlib.MeasureTheory.Function.ConvergenceInMeasure`.
-/

@[expose] public section

open Filter MeasureTheory Topology
open scoped BoundedContinuousFunction ENNReal NNReal Topology

namespace Causalean.Stat.Modes


end Causalean.Stat.Modes


namespace Causalean.Stat.Modes

open Filter MeasureTheory Topology
open scoped ENNReal

universe u v


end Causalean.Stat.Modes
