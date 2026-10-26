/-
Upstream project: StatLean.
Modified for llm-audit-lean: import paths adapted and declarations not used by this repository removed.
-/
import AronowAudit.External.StatLean.AsymptoticStatistics.EmpiricalProcess.SupMeasurability
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

/-!
# Pointwise measurability for empirical-process suprema

The van der Vaart–Wellner pointwise-measurability condition asks for a
countable subclass `F' ⊆ F` such that every `f ∈ F` is the pointwise limit
of a sequence drawn from `F'`, with a single integrable envelope `Φ`
dominating the whole class.

The whole-class equality of suprema follows from the per-function
approximating sequences via dominated convergence. Requiring equality of
suprema over every subset `S ⊆ F` would instead force the empirical process
to vanish at any `f ∈ F \ F'` by taking `S = {f}`.

The measurability argument uses dominated convergence for the integral
term and continuity of the finite sample sum along each approximating
sequence. The whole-class supremum then equals the supremum over the
countable subclass, whose measurability follows from countable suprema.
On a probability space, an `L²(P)` envelope is integrable, since `L²(P)`
is contained in `L¹(P)`.

Reference: van der Vaart & Wellner, *Weak Convergence and Empirical Processes*
(Springer, 1996), §2.3.3 (pointwise-measurable class); van der Vaart,
*Asymptotic Statistics* (Cambridge, 1998), §2.3.3 / §19 (measurability of
suprema via a countable pointwise-dense subclass).
-/

namespace AsymptoticStatistics.EmpiricalProcess

open MeasureTheory Filter Topology
open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]






variable {Ξ : Type*} [MeasurableSpace Ξ] {P : Measure Ω}





end AsymptoticStatistics.EmpiricalProcess
