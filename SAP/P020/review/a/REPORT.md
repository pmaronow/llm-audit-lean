# P020 statement audit

17 targets audited: **13 `correct_whole`, 4 `correct_restricted`**. All other verdict counts are zero; severity counts are **17 none, 0 minor, 0 major**. There are no omissions or requested fixes.

No items received a verdict outside `correct_*` or `omission_ok`.

The architect's decisions agree with the independent claim-stage classifications. Each restricted theorem has an accurate disclosure in its Challenge docstring:

| Target | Disclosed restriction |
| --- | --- |
| P020-T3 | Omits the separately displayed scalar N=1 illustration. The universal negativity and exclusion results remain; their formal domain still allows N=1. An N=1 population cannot itself meet the standing two-arm cluster-design assumptions. |
| P020-T5 | Omits the intermediate equation-(29) expectation-of-sums and product-of-means chain. Both arm-total means and the corrected ATE expectation and bias remain unconditional. |
| P020-T14 | Omits the original-outcome expansion, derivative/first-order assertions and Appendix C algebraic rearrangements. Ratio-based optimum claims explicitly require positive size variance. |
| P020-T17 | Omits explicit certificates for the introductory strict growth conditions on total and both realized arm counts, and a joint coupling across population indices. All four marginal weak laws, pooled convergence and the exact replication/counterexample content remain. |

The blind reading was saved in `reading.md` before opening either JSON input. The independent comparisons were then saved in `claim-stage.json` before opening `record.json`. No step-2 verdict was changed after reading the record. No Solution or Comparator source was inspected.

Every SAP mathematical definition was expanded. The finite laws have nonnegative normalized finite weights; empty supports cannot satisfy normalization. Complete randomization ranges over every fixed-cardinality subset, and block/copy laws range over full Cartesian products. Cluster means use divisor M, as required. Positive arm counts and cluster sizes prevent division by zero in supported estimates; sample variance formulas require at least two clusters per arm; coefficient ratios are used with positive size variance; block and copy limits have nonempty index sets. Arbitrary cluster totals lose no individual-outcome cases: `scratch/Check.lean` constructs individual realizations for every allowed population. No extraneous hypothesis assumes the audited conclusion.

`scratch/Check.lean` compiled successfully with `/home/ubuntu/sap/tools/sap-lean`, importing only `SAP.P020.Defs`. It proves nonvacuity witnesses for the limiting premises, assignment admissibility, positive size variance, nonzero bias, a nonconstant sharp-null population, two-clusters-per-arm formulas, both distinct conservativeness branches, nonempty block/copy products and non-invariance premises. The compiler log is `scratch/lean-check.log`; its only messages are two stylistic linter warnings.

`python3 scratch/exact_audit.py` passed independent rational-arithmetic enumeration on 126 populations, with 2–7 clusters and every possible positive arm-count split, including equal-size, sharp-null and constant-total-effect cases. It also checked the numerical refutations, positive within-cluster scaling, two-block product moments and four copy-average means and 1/h variances. Results are in `scratch/check-results.json`. These finite checks support the mathematical review; they do not replace proofs of universal or asymptotic statements. The latter also have the expected elementary arguments: bias–variance decomposition and Markov's inequality, finite-sampling moments, completed squares, and bounded independent-copy averages followed by positive-denominator ratio convergence.

The printed logistic model, replication schemes and in-expectation variance interpretation were cross-checked against the [paper PDF](https://joelmidd.github.io/papers/MiddletonAronow_Cluster%20Randomized.pdf). The audit uses the canonical corrected statements where the target requests a repair, and the printed erroneous expressions where it requests a refutation.

`findings.json`, `claim-stage.json` and the auxiliary numerical-results JSON were parsed and checked with Python. `findings.json` has exactly one entry per target, with matching theorem names and all required fields.
