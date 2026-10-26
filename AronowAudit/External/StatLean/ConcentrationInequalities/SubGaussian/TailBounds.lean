/-
Upstream project: StatLean.
Modified for llm-audit-lean: import paths adapted and declarations not used by this repository removed.
-/
import AronowAudit.External.StatLean.ConcentrationInequalities.SubGaussian.Defs

/-!
# Two-Sided Tail Probability for Sub-Gaussian Random Variables

Let $X$ be a sub-Gaussian random variable with variance proxy $\sigma^2$ under a
measure $\mu$, and write $\mathbb{E}X = \int X \, d\mu$ for its mean. Then for
every $t \ge 0$:

* **One-sided (Chernoff) tail.** The right deviation satisfies
  $$\mu\bigl(\{t < X - \mathbb{E}X\}\bigr) \le \exp\!\Bigl(-\frac{t^2}{2\sigma^2}\Bigr).$$
  This is the right-tail step used inside the book's proof of the two-sided form.
* **Two-sided tail.** The absolute deviation satisfies
  $$\mu\bigl(\{t < |X - \mathbb{E}X|\}\bigr) \le 2\exp\!\Bigl(-\frac{t^2}{2\sigma^2}\Bigr).$$

**Added/changed hypotheses.** The book states both bounds for $t > 0$; we use the
weaker hypothesis $t \ge 0$, which yields a (formally) stronger statement (the
$t = 0$ case is trivially true). The strict inequality $t < \cdot$ on the event is
faithful to the book.

**Reference.** Junwei Lu, *Big Data Analysis*, Springer Nature Switzerland, 2025
(ISBN 978-3-032-03160-0). Chapter 4 (Concentration Inequalities),
§4.2 (Sub-Gaussian Random Variables), Theorem 4.5 (Two-Sided Tail Probability).

**Bibliographic comments.**
The two-sided sub-Gaussian tail bound is folklore: it follows immediately from
the defining moment-generating-function bound by an optimized Chernoff argument
and a union bound over the two tails, and has no single seminal origin. The
modern axiomatic theory of sub-Gaussian random variables — the equivalence of
the MGF bound, the tail bound, and the Orlicz-norm characterization — was
systematized by V. V. Buldygin and Yu. V. Kozachenko, "Sub-Gaussian random
variables," *Ukrainian Mathematical Journal* **32** (1980), 483–489. The
underlying technique traces to J.-P. Kahane's study of sub-Gaussian series and
ultimately to the Chernoff/Cramér large-deviation bound. Standard textbook
treatments include M. J. Wainwright, *High-Dimensional Statistics: A
Non-Asymptotic Viewpoint* (Cambridge University Press, 2019), §2.1, and
R. Vershynin, *High-Dimensional Probability* (Cambridge University Press, 2018),
§2.5.
-/

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal NNReal

namespace StatLean.ConcentrationInequalities

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}


end StatLean.ConcentrationInequalities
