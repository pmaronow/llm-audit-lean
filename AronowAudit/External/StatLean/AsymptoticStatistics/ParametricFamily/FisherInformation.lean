/-
Upstream project: StatLean.
Modified for llm-audit-lean: import paths adapted and declarations not used by this repository removed.
-/
import AronowAudit.External.StatLean.AsymptoticStatistics.ParametricFamily.Defs
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Fisher information (bilinear form)

For a parametric family $\{P_\theta\}$ with score function
$\dot\ell_\theta : \mathcal X \to \Theta$, the **Fisher information**
at $\theta$ is the symmetric bilinear form on the parameter space
$$ I_\theta(u, v) \;=\; P_\theta\bigl(\langle u,
\dot\ell_\theta\rangle\,\langle v, \dot\ell_\theta\rangle\bigr)
   \;=\; \int \langle u, \dot\ell_\theta(x)\rangle\,\langle
   v, \dot\ell_\theta(x)\rangle \, p_\theta(x)\,d\mu(x). $$
In a finite-dimensional basis this is the matrix
$I_\theta = P_\theta\,\dot\ell_\theta\,\dot\ell_\theta^{\mathsf T}$,
i.e. the expected outer product of the score under $P_\theta$.

**Reference.** A. W. van der Vaart, *Asymptotic Statistics*, Cambridge Series in Statistical and
Probabilistic Mathematics, Cambridge University Press, 1998. Chapter 7 (Local Asymptotic Normality),
§7.2, definition of the Fisher information matrix
$I_\theta = P_\theta\,\dot\ell_\theta\,\dot\ell_\theta^{\mathsf T}$
(score function $\dot\ell_\theta$ introduced in §5.5).

**Bibliographic comments.** The Fisher information originates with R. A. Fisher, "On the
mathematical foundations of theoretical statistics," *Philosophical Transactions of the Royal
Society of London, Series A*, vol. 222, pp. 309–368, 1922, where the "intrinsic accuracy" / amount
of information of a statistic is introduced (§§3–11), and is developed further in R. A. Fisher,
"Theory of statistical estimation," *Proceedings of the Cambridge Philosophical Society*, vol. 22,
pp. 700–725, 1925. The modern multivariate form as the expected outer product of the score,
$I_\theta = E_\theta[\dot\ell_\theta\dot\ell_\theta^{\mathsf T}]$,
is standard (van der Vaart §7.2).
-/

open MeasureTheory
open scoped RealInnerProductSpace

namespace AsymptoticStatistics

variable {𝓧 : Type*} [MeasurableSpace 𝓧]
variable {Θ : Type*} [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ]


end AsymptoticStatistics
