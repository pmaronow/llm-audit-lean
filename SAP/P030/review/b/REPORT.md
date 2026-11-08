# P030 statement audit

All 15 targets are accepted: **11 correct_whole, 4 correct_restricted**. There are **0 issues**, **0 omissions**, and **0 false or vacuous Lean statements**. Severity counts: none 15, minor 0, major 0.

| Verdict | Count |
| --- | ---: |
| correct_whole | 11 |
| correct_restricted | 4 |
| restriction_inaccurate | 0 |
| not_faithful | 0 |
| vacuous | 0 |
| false | 0 |
| omission_ok | 0 |
| omission_questionable | 0 |

There are no non-`correct_*`/`omission_ok` items to list.

## Order and record assessment

`reading.md` was saved before opening `claims.json`. `claim-stage.json` was saved and parsed before opening `record.json`. No step-2 verdict was changed after the record was read. All Defs and Challenge parts were read; no Solution or Comparator was read or imported. The paper excerpts and canonical formal statements supplied in `claims.json` sufficed; no web search was needed.

The architect's decisions are supported for every target:

| Targets | Record decision | Assessment |
| --- | --- | --- |
| T1, T3, T6, T7, T11, T12, T13, T15 | whole | The complete canonical mathematical content is retained. |
| T9 | whole | The complete claim is retained; divisor invariance is correctly strengthened to every positive real divisor. |
| T10 | whole | The complete formal content is retained; the corrected finite sums also apply to arbitrary positive off-diagonal distance arrays. The claims explicitly exclude mean normalization from formal content. |
| T4 | refuted | The Lean theorem negates the false universal printed claim, as the canonical target requests. The five-unit counterexample lies within the paper's intended setting. |
| T2, T5 | restricted | The statement, record, and Challenge docstring agree on the omitted rank vectors, centered cross products, exact distance rank-square sums, and rational squared-correlation calculations/comparisons. The genuine null population, conditional law, exact correlations, positivity, order, rounding, and claimed p values or sizes remain. |
| T8 | restricted | All three counterexamples remain. The record and docstring accurately disclose omission of explicit rank vectors, centered cross products, the observed distance rank-square sum, separate covariance/variance values under the two divisors, and squared-correlation calculations/comparisons. |
| T14 | restricted | The only omitted explicit assertion from canonical parts (a)–(g) is the parenthetical outcome midrank vector (3/2,4,3,3/2), exactly as both record and docstring disclose. The actual adjacency schedule and observed-data reference calculation remain. |

Step 2 labels T9 and T10 `broader` because of the two valid strengthenings above; their final `correct_whole` verdicts mean that the full canonical claims are certified, with no missing part or added hypothesis. This does not revise the saved step-2 comparison. No target is omitted, so no omission justification is needed. The record's names of prior proof rows were treated only as metadata, not as evidence of statement correctness.

## Mathematical checks

The definitions use binary assignments, finite sets, real potential outcomes, compatible-assignment filtering, and support-relative nulls as claimed. The observed-data statistic uses only the fixed outcomes and assignment. Uniform laws really are uniform on the selected finite supports. Both inclusive tails count assignments, so equal statistic values keep their multiplicity. Average ranks use the stated tie convention, and their centered sums give the ordinary Spearman correlation when the variances are positive.

No contradiction or conclusion is hidden in a premise. The nonempty-support premises are satisfiable, including examples with nonempty fixed and variant subsets and nonzero direct effects. `FiniteLaw.total` forces a nonempty support even though the structure does not list nonemptiness separately. Unused mass-function values outside its support cannot affect a probability.

The explicit five- and ten-unit examples have a treated variant unit in every assignment used by a nearest-distance statistic, and every correlation denominator used in the claims is positive. T9 proves positive rank-square sums from its nonconstant-vector assumptions. T10 represents undefined ordinary division by an explicit partial quotient; its corrected sums exclude self and require positive off-diagonal distances. T13 guards each use of a conditional mean by a premise ensuring nonempty support. The natural subtraction in T11 has nonnegative intermediate results; T13's N−1 premise is under N≥2, and its expectation formulas subtract in the reals. No integral, limsup, or unbounded supremum convention is used. T12's maximum is a genuine greatest element of an explicitly nonempty finite set of attained levels together with zero.

The general tail claims follow by ordering the finite statistic values and summing their masses. The inclusive upper-tail identity accounts for ties, and the union bound gives the corrected level bounds. For uniform laws, the same cumulative counts give exactness at attainable levels and the greatest-attainable-level formula. T9 uses Cauchy-Schwarz and its equality case for nonzero centered ranks. T10's constant doubling ratio contradicts an exponential form; its divergence inequality uses positive square roots, while the exponential limit is ordinary continuity. T11 is finite disjoint additivity plus integer arithmetic. T13 follows from inclusion probabilities M/N, (M−1)/(N−1), and M/(N−1), followed by linearity. T15 follows by completing the square and identifying the closest feasible integers to half the controls.

## Validation artifacts and limits

`/home/ubuntu/sap/tools/sap-lean scratch/Check.lean` completed successfully with exit code 0. The file imports only `SAP.P030.Defs`, contains no `sorry`, and establishes nonempty original and conditional designs, the no-effect/no-interference examples, a four-assignment conditional design with nonzero direct effects, a valid nonuniform finite law with a zero-mass point, nonconstant rank vectors and exact positive rank-square sums, positive off-diagonal distances, and all three nonempty supports in the N=5,M=2 exposure example. `scratch/lean-check.log` is empty because the final compilation emitted no diagnostics. Lean checks ran sequentially through the required wrapper; `lake` was never run.

`python3 scratch/referee_checks.py` completed successfully. It independently reconstructs the five-unit example, all six table rows and tails, both printed-formula divisors, the ordering reversal, the weak-monotonicity example, and the actual illustrative observations. It additionally checks 7,260 finite-law instances, 6,696 nonconstant rank-vector pairs, 894 exposure/design/neighbor-set instances for N=2 through 7, and 150 positive-count maximization instances. Exact rational arithmetic is used except to check the printed decimal rounding of square-root correlations. Results are saved in `scratch/check-results.json`.

These scratch checks support the reading and rule out the identified convention and vacuity risks; they are not offered as replacement proofs of all universal Challenge statements. The audit judges statements and the declared restrictions, rather than certifying the Solution or Comparator.
