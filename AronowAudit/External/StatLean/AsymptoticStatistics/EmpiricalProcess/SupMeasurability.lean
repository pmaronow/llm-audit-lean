/-
Upstream project: StatLean.
Modified for llm-audit-lean: import paths adapted and declarations not used by this repository removed.
-/
import AronowAudit.External.StatLean.AsymptoticStatistics.EmpiricalProcess.EmpiricalProcess
import AronowAudit.External.StatLean.AsymptoticStatistics.EmpiricalProcess.FunctionClass
import AronowAudit.External.StatLean.AsymptoticStatistics.EmpiricalProcess.Bracketing
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-!
# The affine-transformed empirical process and its per-index measurability

The chaining decomposition's right-hand side is a sum of `∫⁻` terms whose
B-link / TRUNC / raw integrands carry a supremum `⨆ f ∈ S` of
`ξ ↦ |𝔾ₙ(φ f)(ξ)|` over a sub-collection `S ⊆ F`, for a **pointwise-affine**
transform `φ f = (f − a) · b` with a fixed subtract `a : Ω → ℝ` and a fixed
multiplier `b : Ω → ℝ`.  All three shapes (raw: `a = 0, b = 1`; TRUNC:
`a = 0, b = 1{tail}`; B-link: `a = π_q i, b = 1{chainB i}`) are the same
functional `f ↦ |𝔾ₙ((f − a)·b)|`.

For fixed `f`, the map `ξ ↦ ofReal|𝔾ₙ((f − a)·b)(ξ)|` is measurable
whenever `f`, `a`, and `b` are measurable. Countable pointwise-dense
subclasses with an integrable envelope give measurability of the whole-class
supremum via dominated convergence.

Reference: van der Vaart, *Asymptotic Statistics* (Cambridge, 1998), §2.3.3
(measurability of suprema, `E*`); van der Vaart & Wellner, *Weak Convergence
and Empirical Processes* (Springer, 1996), §2.3.3 (pointwise-measurable class).
-/

namespace AsymptoticStatistics.EmpiricalProcess

open MeasureTheory
open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]




variable {Ξ : Type*} [MeasurableSpace Ξ] {P : Measure Ω}


end AsymptoticStatistics.EmpiricalProcess
