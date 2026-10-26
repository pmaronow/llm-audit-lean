/-
Upstream project: StatLean.
Modified for llm-audit-lean: import paths adapted and declarations not used by this repository removed.
-/
import AronowAudit.External.StatLean.ConcentrationInequalities.McDiarmid.DoobDecomposition

/-!
# McDiarmid's bounded-differences inequality

Let $X = (X_0, \dots, X_{n-1})$ be $n$ independent random variables and let
$f$ be a real-valued function satisfying the **bounded-differences condition**
with constants $c_0, \dots, c_{n-1} \ge 0$: changing the $k$-th coordinate of the
argument changes the value of $f$ by at most $c_k$, i.e.
$$\bigl|f(x) - f(x_{-k}, y)\bigr| \le c_k \quad\text{for all } x \text{ and all } y,$$
where $(x_{-k}, y)$ denotes $x$ with its $k$-th coordinate replaced by $y$. Then the
centered evaluation $f(X) - \mathbb{E}[f(X)]$ has the Gaussian-style upper tail, for
every $t \ge 0$,
$$\mathbb{P}\bigl(f(X) - \mathbb{E}[f(X)] > t\bigr) \le \exp\!\left(\frac{-2 t^2}{\sum_{k}
c_k^2}\right),$$ and the corresponding two-sided form
$$\mathbb{P}\bigl(\bigl|f(X) - \mathbb{E}[f(X)]\bigr| > t\bigr)
\le 2\,\exp\!\left(\frac{-2 t^2}{\sum_{k} c_k^2}\right).$$

The book states the bound for $t > 0$; the weaker hypothesis $t \ge 0$ also suffices
(the $t = 0$ case is trivial). The bounded-differences constants are taken nonnegative; this is a
harmless normalization, since a difference bound is vacuous for negative $c_k$.

**Reference.** Junwei Lu, *Big Data Analysis*, Springer Nature Switzerland, 2025
(ISBN 978-3-032-03160-0), Chapter 5 (Sub-exponential Random Variables), §5.1,
Theorem 5.1 (McDiarmid Inequality).

**Bibliographic comments.** The independent bounded-differences inequality is due to
C. McDiarmid, "On the method of bounded differences", in *Surveys in Combinatorics, 1989*
(J. Siemons, ed.), London Mathematical Society Lecture Note Series 141, Cambridge University
Press, 1989, pp. 148–188 (the inequality is stated there as Lemma (1.2)). The underlying
technique — controlling the Doob martingale of $f(X)$ via a martingale exponential bound —
goes back to W. Hoeffding, "Probability inequalities for sums of bounded random variables",
*Journal of the American Statistical Association* **58** (1963), 13–30, and to K. Azuma,
"Weighted sums of certain dependent random variables", *Tôhoku Mathematical Journal* **19**
(1967), 357–367; for this reason the result is often called the Azuma–Hoeffding bounded-
differences inequality.
-/

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal NNReal

namespace StatLean.ConcentrationInequalities

section McDiarmid

variable {n : ℕ} {Ω : Type*} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {β : Fin n → Type*} [(i : Fin n) → MeasurableSpace (β i)]
  -- LEAN-ONLY: standard-Borel coordinate spaces; threaded to `mgf_sub_expectation_le`.
  [∀ i, StandardBorelSpace (β i)] [∀ i, Nonempty (β i)]


end McDiarmid

end StatLean.ConcentrationInequalities
