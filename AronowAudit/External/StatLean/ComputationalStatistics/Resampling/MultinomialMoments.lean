/-
Upstream project: StatLean.
Modified for llm-audit-lean: import paths adapted and declarations not used by this repository removed.
-/
import AronowAudit.External.StatLean.ComputationalStatistics.Resampling.CategoricalCounts
import AronowAudit.External.StatLean.ComputationalStatistics.Core.EmpiricalMeasure
import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.Moments.Covariance

/-!
# Moments of multinomial category counts

First and second moments of the count vector `V_j = #{i | Aᵢ = j}` of `n`
i.i.d. `categorical q` draws:

* `E[V_j] = n·q_j`;
* `Var(V_j) = n·q_j·(1 − q_j)`;
* `Cov(V_j, V_k) = −n·q_j·q_k` for `j ≠ k`.

**Reference.** James E. Gentle, *Elements of Computational Statistics*, Springer,
2002 (ISBN 0-387-95489-9), ch. 4 p. 84 (the multinomial resampling vector);
moments are the classical multinomial moments.  (`ECS ch. 4`.)

**Proof formalization notes.**

* Each count is a sum of indicator functions of the independent coordinates,
  so the proofs are `iIndepFun_pi` + Bernoulli-moment algebra; no multinomial
  pmf manipulation is needed.
* Counts are `ℕ`-valued; the statements coerce to `ℝ`.

**Bibliographic comments.** Classical; see also Johnson–Kotz–Balakrishnan,
*Discrete Multivariate Distributions*, Wiley, 1997, ch. 35.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace StatLean.ComputationalStatistics

variable {m n : ℕ} {q : Fin m → ℝ}

/-! ### Coordinate indicators

Each count is the sum over the coordinates of the indicator that the coordinate
takes the value `j`; those indicators are independent (`iIndepFun_pi`) and
Bernoulli`(q j)`, which is all the moment computations need.
-/


end StatLean.ComputationalStatistics
