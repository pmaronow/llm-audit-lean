/-
Upstream project: StatLean.
Modified for llm-audit-lean: import paths adapted and declarations not used by this repository removed.
-/
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.Probability.CentralLimitTheorem
import Mathlib.Probability.CDF
import Mathlib.Probability.Distributions.Gaussian.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

/-!
# Berry–Esseen characteristic-function estimates

Imports for characteristic-function estimates in the Berry–Esseen theorem.

**Reference.** W. Feller, *An Introduction to Probability Theory and Its Applications*,
Vol. II, 2nd ed., Wiley, 1971, §XVI.3 (smoothing) and §XVI.5 (Berry–Esseen).
-/

open MeasureTheory ProbabilityTheory Filter Complex
open scoped Topology ENNReal NNReal Real

namespace StatLean.HypothesisTesting

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]






















end StatLean.HypothesisTesting
