/-
Upstream project: StatLean.
Modified for llm-audit-lean: import paths adapted and declarations not used by this repository removed.
-/
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.MeasurableSpace.CountablyGenerated
import Mathlib.MeasureTheory.Measure.SeparableMeasure

/-!
# Measurable selection for random functions in a function class

Measurable selection concerns the measurability of the parameter-space event
`{ξ | fhat ξ ∈ F}`. A measurable surrogate replaces `fhat ξ` by a fixed
`f₀ ∈ F` outside that event, preserving joint measurability.

Van der Vaart–Wellner, Theorem 2.10.1, states that every L²(P)-norm-closed
admissible class measurably selects random functions.

The L² formulation uses the event `{ξ | ∃ f ∈ F, fhat ξ =ᵃᵉ[P] f}`.
For an a.e.-invariant class, this agrees with function-level membership.
The L² space is Polish under the countable-generation hypotheses used in
the Lp second-countability construction. A norm-closed subset of
`Lp ℝ 2 P` is Borel measurable. The canonical lift
`Φ ξ := if h : MemLp (fhat ξ) 2 P then MemLp.toLp (fhat ξ) h else 0`
uses the L²-locus `{ξ | MemLp (fhat ξ) 2 P}`; its measurability is obtained
via Fubini. In a second-countable Borel pseudometric target,
measurability of pointwise distances implies Borel measurability, by a
countable ball cover. Function-level L²-norm closedness transfers to the
Lp quotient using sequential closedness and convergence in `eLpNorm`.

Reference: Vaart–Wellner, *Weak Convergence and Empirical Processes*,
§2.10.1; see also van der Vaart, *Asymptotic Statistics*, §19.4 (the union
closure step in the proof of Theorem 19.23).
-/

open MeasureTheory Filter
open scoped ENNReal NNReal Topology

namespace AsymptoticStatistics.ForMathlib
namespace MeasurableSelection

variable {Ω : Type*} [MeasurableSpace Ω]





end MeasurableSelection
end AsymptoticStatistics.ForMathlib
