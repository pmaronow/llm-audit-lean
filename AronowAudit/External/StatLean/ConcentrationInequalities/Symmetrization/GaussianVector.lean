/-
Upstream project: StatLean.
Modified for llm-audit-lean: import paths adapted and declarations not used by this repository removed.
-/
import AronowAudit.External.StatLean.ConcentrationInequalities.ForMathlib.GaussianAbsMoment
import AronowAudit.External.StatLean.ConcentrationInequalities.SubGaussian.Defs
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# The canonical standard Gaussian vector

The joint law of $N$ i.i.d. standard Gaussians $g_1, \dots, g_N \sim N(0,1)$,
realized as the product measure
$$ \bigl(N(0,1)\bigr)^{\otimes N}
   \quad\text{on } \mathrm{Fin}\,N \to \mathbb{R}, $$
with coordinate marginals given by measure-preserving
evaluations; coordinates are integrable, mean zero, with
$\mathbb{E}|g_i| = \sqrt{2/\pi}$; and each coordinate (and its negation) is
sub-Gaussian with variance proxy $1$.

**Reference.** Roman Vershynin, *High-Dimensional Probability*, 2nd ed.,
Cambridge University Press, §6.6 ($g_1,\dots,g_N$ i.i.d. $N(0,1)$, Lemma
6.6.2); the Gaussian-is-sub-Gaussian bridge is §2.5 (Example 2.5.8 with
$\sigma^2 = 1$).

**Bibliographic comments.** Gaussian multipliers as the comparison class for
Rademacher sums are classical Banach-space probability (Ledoux–Talagrand,
*Probability in Banach Spaces*, 1991, Ch. 4); the sub-Gaussian bridging facts
are standard.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace StatLean.ConcentrationInequalities

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}


end StatLean.ConcentrationInequalities
