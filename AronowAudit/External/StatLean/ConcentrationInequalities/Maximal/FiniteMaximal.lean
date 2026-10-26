/-
Upstream project: StatLean.
Modified for llm-audit-lean: import paths adapted and declarations not used by this repository removed.
-/
import AronowAudit.External.StatLean.ConcentrationInequalities.SubGaussian.TailBounds
import Mathlib.Data.Fintype.Order
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
# Finite Maximal Inequality for Sub-Gaussian Variables

Let $X_1, \dots, X_d$ ($d \ge 1$) be (not necessarily independent) sub-Gaussian random
variables with variance proxy $\sigma^2$ and mean zero, $\mathbb{E}[X_j] = 0$ for every
$j$. Then:

* **Tail bound.** For every $t \ge 0$,
  $$\mathbb{P}\!\Big(\max_{1 \le j \le d} X_j > t\Big) \le d\, e^{-t^2/(2\sigma^2)}.$$
* **Expectation bound.** Under a probability measure,
  $$\mathbb{E}\!\Big[\max_{1 \le j \le d} X_j\Big] \le \sigma\sqrt{2\log d}.$$

The finite maximum can be written as the supremum
$\bigvee_{j} X_j$ over the index set $\{1, \dots, d\}$ (the supremum equals the
pointwise maximum once $d \ge 1$), and $\sigma$ is recovered as $\sqrt{\sigma^2}$.

**Boundary case.** The book states the tail bound for $t > 0$; the bound also allows
$t \ge 0$, which is strictly stronger. The book's high-probability form
"$\max_j X_j \le \sigma\sqrt{2\log(d/\delta)}$ with probability at least $1-\delta$" is
the same statement as the tail bound after substituting $\delta = d\,e^{-t^2/(2\sigma^2)}$.

**Reference.** Junwei Lu, *Big Data Analysis*, Springer Nature Switzerland, 2025
(ISBN 978-3-032-03160-0), Chapter 6 (Bernstein and Maximal Inequalities), §6.2,
Theorem 6.2 (Finite Maximal Inequality).
The expectation bound is the first display of the theorem; the tail bound is the union
bound established in its proof.

**Bibliographic comments.** This is a folklore result with no single seminal origin; it
is the prototype of the maximal-inequality-via-MGF argument. A standard modern
reference is S. Boucheron, G. Lugosi, and P. Massart, *Concentration Inequalities: A
Nonasymptotic Theory of Independence*, Oxford University Press, 2013, §2.5 (the maximal
inequality $\mathbb{E}[\max_j X_j] \le \sqrt{2v\log d}$ for sub-Gaussian variables with
variance factor $v$). The same bound appears in P. Massart, *Concentration Inequalities
and Model Selection*, Lecture Notes in Mathematics 1896, Springer, 2007. The argument
goes back to the classical Cramér–Chernoff method applied to the maximum and is not
attributable to a single research paper.
-/

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal NNReal

namespace StatLean.ConcentrationInequalities

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}










end StatLean.ConcentrationInequalities
