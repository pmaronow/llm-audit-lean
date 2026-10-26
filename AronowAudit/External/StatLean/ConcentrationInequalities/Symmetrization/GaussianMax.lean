/-
Upstream project: StatLean.
Modified for llm-audit-lean: import paths adapted and declarations not used by this repository removed.
-/
import AronowAudit.External.StatLean.ConcentrationInequalities.Symmetrization.GaussianVector
import AronowAudit.External.StatLean.ConcentrationInequalities.Maximal.FiniteMaximal
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Gaussian maximum bounds and the Pi norm

For $g_1, \dots, g_N$ i.i.d. standard Gaussians ($N \ge 1$),
$$ \mathbb{E}\,\max_{i \le N} |g_i| \;\le\; \sqrt{2 \log (2N)}, $$
equivalently $\mathbb{E}\,\|g\|_\infty \le \sqrt{2\log(2N)}$ for the Pi
sup-norm on $\mathrm{Fin}\,N \to \mathbb{R}$. This is the explicit-constant
replacement for the book's "$\mathbb{E}\|g\|_\infty \le C\sqrt{\log N}$"
(cited from Exercise 2.38(a)) in the lower bound of Lemma 6.6.2.

**Reference.** Roman Vershynin, *High-Dimensional Probability*, 2nd ed.,
Cambridge University Press, §6.6, p. 186 (in the proof of Lemma 6.6.2);
the underlying maximal inequality is §2.5, Exercise 2.38(a).

**Bibliographic comments.** The $\sqrt{2\log N}$ growth of Gaussian maxima is
classical extreme-value theory (Cramér, 1946); the sub-Gaussian
maximal-inequality route used here is the standard argument of
Boucheron–Lugosi–Massart, *Concentration Inequalities* (2013), §2.5.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace StatLean.ConcentrationInequalities

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- The `Fintype` Pi norm on `ι → ℝ` is the supremum of the coordinate
absolute values. -/
-- LEAN-ONLY: norm/ciSup bridge; via pi_norm_le_iff_of_nonneg + norm_le_pi_norm.
theorem pi_norm_eq_ciSup_abs {ι : Type*} [Fintype ι] [Nonempty ι] (v : ι → ℝ) :
    ‖v‖ = ⨆ i, |v i| := by
  apply le_antisymm
  · refine (pi_norm_le_iff_of_nonneg (Real.iSup_nonneg (fun i => abs_nonneg _))).mpr (fun i => ?_)
    rw [Real.norm_eq_abs]
    exact le_ciSup (Finite.bddAbove_range fun k => |v k|) i
  · exact ciSup_le (fun i => by rw [← Real.norm_eq_abs]; exact norm_le_pi_norm v i)


end StatLean.ConcentrationInequalities
