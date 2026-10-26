/-
Documentation corrected for llm-audit-lean.
Upstream project: StatLean.
Modified for llm-audit-lean: import paths adapted and declarations not used by this repository removed.
-/
import AronowAudit.External.StatLean.AsymptoticStatistics.EmpiricalProcess.Bracketing
import AronowAudit.External.StatLean.AsymptoticStatistics.EmpiricalProcess.FunctionClass
import Mathlib.Probability.StrongLaw
import Mathlib.Probability.IdentDistrib

/-!
# Glivenko–Cantelli classes via finite $L_1$-bracketing (Theorem 19.4)

A class $\mathcal F$ of measurable functions is **$P$-Glivenko–Cantelli** if, for
any i.i.d. sample $X_1, X_2, \dots$ drawn from $P$, the empirical-process
supremum deviation
$$\|\mathbb P_n - P\|_{\mathcal F} \;=\; \sup_{f \in \mathcal F}
  \Bigl| \tfrac1n \sum_{i=1}^n f(X_i) - \int f \, dP \Bigr|$$
converges to $0$ almost surely as $n \to \infty$.

The headline result is: *every class $\mathcal F$ of measurable functions whose
$L_1(P)$ bracketing numbers are finite — that is, $N_{[\,]}(\varepsilon,
\mathcal F, L_1(P)) < \infty$ for every $\varepsilon > 0$ — is
$P$-Glivenko–Cantelli.* Here a finite ε-bracketing cover means a finite collection
of brackets [lᵢ, uᵢ] with measurable, P-integrable endpoints, lᵢ ≤ uᵢ pointwise,
and ∫(uᵢ − lᵢ) dP < ε, such that every f ∈ ℱ lies pointwise in some bracket.

**Formalization scope.** This module imports the bracketing, function-class,
and strong-law infrastructure but currently declares no Glivenko–Cantelli
predicate or theorem. The result above describes the mathematical target.
In a Lean statement, `Integrable f P` entails almost-everywhere strong
measurability, not necessarily `Measurable f`. A measurable representative or
a separate measurability hypothesis is needed wherever pointwise measurability
is required.

**Reference.** A. W. van der Vaart, *Asymptotic Statistics*, Cambridge Series in
Statistical and Probabilistic Mathematics, Cambridge University Press, 1998,
Chapter 19 (Empirical Processes), §19.2 (Glivenko–Cantelli Theorems),
Theorem 19.4.

**Bibliographic comments.** The classical Glivenko–Cantelli theorem — uniform
a.s. convergence of the empirical distribution function to the true
distribution function — originates in two companion 1933 papers in the same
journal volume: V. Glivenko, "Sulla determinazione empirica delle leggi di
probabilità," *Giornale dell'Istituto Italiano degli Attuari* 4 (1933), 92–99
(the continuous case), and F. P. Cantelli, "Sulla determinazione empirica delle
leggi di probabilità," *Giornale dell'Istituto Italiano degli Attuari* 4 (1933),
421–424 (the general case). The abstract bracketing-entropy formulation
described above (van der Vaart's Theorem 19.4) is part of the modern theory of
empirical processes and is not attributable to a single seminal paper; it is
folklore in that literature, presented systematically in A. W. van der Vaart and
J. A. Wellner, *Weak Convergence and Empirical Processes*, Springer, 1996.
-/

namespace AsymptoticStatistics.EmpiricalProcess

open MeasureTheory Filter ENNReal
open scoped ENNReal Topology

variable {Ω : Type*} [MeasurableSpace Ω]



end AsymptoticStatistics.EmpiricalProcess
