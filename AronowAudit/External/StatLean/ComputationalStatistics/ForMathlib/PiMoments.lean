/-
Upstream project: StatLean.
Modified for llm-audit-lean: import paths adapted and declarations not used by this repository removed.
-/
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.StrongLaw
import Mathlib.Probability.ProductMeasure
import Mathlib.Probability.Independence.InfinitePi

/-!
# Moments and limits of coordinate averages under product measures

The first- and second-moment identities and the strong-law limit for the average
`x ↦ (1/n)·Σᵢ g(xᵢ)` of a function of the coordinates under the canonical i.i.d.
laws `Measure.pi (fun _ : Fin n => P)` and `Measure.infinitePi (fun _ : ℕ => P)`:

* `E[X̄] = μ`;
* `Var(X̄) = σ²/n`;
* the mean-squared error of the average is `σ²/n`;
* `X̄ₙ → μ` almost surely (SLLN transport).

**Reference.** James E. Gentle, *Elements of Computational Statistics*, Springer,
2002 (ISBN 0-387-95489-9), §2.2 (Monte Carlo estimation, eqs. (2.8)–(2.9), and
the law-of-large-numbers discussion on p. 53).

**Bibliographic comments.** The variance identity for sample means is classical
(Laplace); the almost-sure law of large numbers is Kolmogorov's (1933).
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology

namespace StatLean.ComputationalStatistics

variable {𝓧 : Type*} [MeasurableSpace 𝓧] {P : Measure 𝓧} [IsProbabilityMeasure P]
  {n : ℕ} {g : 𝓧 → ℝ}


end StatLean.ComputationalStatistics
