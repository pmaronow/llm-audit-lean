/-
Upstream project: StatLean.
Modified for llm-audit-lean: import paths adapted and declarations not used by this repository removed.
-/
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Analysis.Convex.Integral



/-!
# A Gaussian / sub-Gaussian maximal inequality

For a **finite** family `Z : ι → Ω → ℝ` of sub-Gaussian random variables, each
with proxy variance `≤ c` (`ProbabilityTheory.HasSubgaussianMGF (Z i) c μ`), the
expected maximum is controlled by `√(2 c · log(card))`:

* One-sided form:
    `∫ ω, ⨆ i, Z i ω ∂μ ≤ Real.sqrt (2 * c * Real.log (Fintype.card ι))`.
* Absolute-value form:
    `∫ ω, ⨆ i, |Z i ω| ∂μ ≤ Real.sqrt (2 * c * Real.log (2 * Fintype.card ι))`.

The classical **MGF / Jensen** argument (no layer-cake): for any
`λ > 0`, convexity of `exp` (Jensen, `ConvexOn.map_integral_le`) gives
`exp (λ · E[⨆ Z]) ≤ E[exp (λ · ⨆ Z)] ≤ ∑ᵢ mgf (Z i) λ ≤ card · exp (c λ²/2)`,
hence `E[⨆ Z] ≤ log(card)/λ + c λ /2`; optimising at `λ = √(2 log card / c)`
yields `√(2 c log card)`.  The absolute-value form follows by indexing the
doubled family `Z` and `-Z` over `ι ⊕ ι` (`|Z i| = max (Z i) (-Z i)`).
-/

open MeasureTheory Real Finset
open scoped ENNReal NNReal



namespace ProbabilityTheory




set_option linter.unusedFintypeInType false

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
variable {ι : Type*} [Fintype ι]


end ProbabilityTheory
