# P020 statement audit

17 targets: **13 correct_whole, 4 correct_restricted, 0 issues**. No target is
omitted. No statement was found false, vacuous, unfaithful, or inaccurately
restricted.

| Verdict | Count |
| --- | ---: |
| correct_whole | 13 |
| correct_restricted | 4 |
| restriction_inaccurate | 0 |
| not_faithful | 0 |
| vacuous | 0 |
| false | 0 |
| omission_ok | 0 |
| omission_questionable | 0 |

There are no non-`correct_*`/`omission_ok` items to list. All severities are
`none`; no statement or docstring fix is required.

## Blind-first order and record comparison

`reading.md` was saved after reading the Defs, Challenge, and relevant Mathlib
definitions, before opening `claims.json`. `claim-stage.json` was then saved
and parsed before opening `record.json`. Its independent classifications were
13 `whole` and four `narrower`. No step-2 verdict was changed after reading the
record. No Solution or Comparator source was read.

Each record entry names the corresponding Challenge theorem. The 13 `whole`
decisions agree with the retained mathematical content. The four `restricted`
decisions also agree, and their restriction strings match the Challenge
docstrings after whitespace normalization:

| Target | Disclosed restriction checked against the proposition |
| --- | --- |
| P020-T3 | Omits the separately evaluated N=1 illustration; keeps monotonicity, the raw-count bound, individual negativity, negative average and exclusion of 0.007. |
| P020-T5 | Omits the intermediate expectation-of-sums and product-of-means calculation in (29); keeps both total means and corrected ATE mean and bias. |
| P020-T14 | Omits the original-outcome expansion, derivatives, first-order equations and successive Appendix C rearrangements; retains the coefficient formulas, unique minima, actual variance formula, completed squares, comparison criteria and sign intervals on the positive-size-variance coefficient domain. |
| P020-T17 | Omits certificates for the introductory strict growth of total and realized arm counts, and a coupling across population indices; retains all four marginal weak laws, pooled convergence, ratio identity, exact replication identities, persistent nonzero bias and actual growing-size inconsistency. |

For T3 the omission concerns a standalone illustration, not an added N≥2
hypothesis: the universal analytic lemmas still specialize to N=1. An actual
randomized cluster design under the standing assumptions needs at least two
individuals. The docstring's stated reason for omitting that illustration is
therefore correct. No empirical conclusion about simulation code or plotted
results is asserted.

T14's positive-size-variance domain is explicit, including in the initial
docstring sentence. Thus the equal-size coefficient boundary is not claimed.
The retained unconditional design-variance moment formula does not divide by
size variance. T17's generic inconsistency conjunct is expressed for the
constant original law; its universal replication identities and the
definitional equality of the replicated laws transfer that result to the
actual within-cluster sequence. Its explicit efficiency example additionally
states failure of `WithinReplicationConsistent` itself.

## Definition and hypothesis checks

The SAP definitions expand into the intended finite population quantities:
cluster totals, individual-weighted ATE, individual difference in means,
cluster HT totals, and centered Des Raj totals. Population moments use divisor
M. Uniform subset laws give complete randomization with fixed cluster counts;
uniform laws on all block/copy assignment functions are full product laws and
therefore encode the required independence. Arbitrary real cluster outcome
or covariate totals have individual realizations because every cluster is
nonempty. The separate individual-outcome structure in T10 imposes exactly
the aggregation identities needed for its genuine individual sharp null.

No problematic totalization is used in an asserted statistical formula:

* `0 < mt < M` implies M≥2 and positive control count. Positive integer
  cluster sizes imply N>0 and positive realized individual counts in both
  supported arms. Natural subtraction in `controlCount` is therefore exact.
* A finite law's nonnegative weights and total weight one force nonempty
  support. All probability, covariance, MSE and expectation expressions are
  finite sums, so integrability and unbounded `limsup` conventions do not arise.
* The ratio lemma has positive v throughout the support, forcing E[v]>0.
  Off-support ratios and weights cannot affect any expectation.
* The combined variance estimator is used only with at least two clusters
  in each arm. The observed OLS witness has size variance 2/3, and the
  optimization conclusions explicitly require positive size variance.
* All averaged logistic populations have N>0, and 1+exp(x)>0. All asymptotic
  copy counts are h+1; all block results require a positive block count.

None of the substantive hypotheses assumes the conclusion. T2's comparator
condition is the canonical sufficient condition, with a simultaneous
nonzero-bias instance. T15's per-block conservative hypotheses are the natural
premises for aggregating conservative estimators; the actual block estimator
is not assumed conservative. The T16 disjunction uses cluster-total effects
and cluster counts, as specified in the canonical claim, and asserts an
expectation inequality rather than an assignmentwise inequality.

## Mathematical truth checks

The elementary finite-sum identities support the universal claims, separately
from the numerical checks. Expanding a square gives MSE = variance + bias²;
the positive-threshold event bound gives the stated Markov inequality. If
bias tends to b≠0, its square is eventually above b²/4, whereas a comparator
whose MSE tends to zero is eventually below b²/4. This gives the exact strict
comparison and the usual probability limit in T2.

Under the uniform fixed-size subset law, inclusion probabilities are t/M and,
for distinct clusters, t(t−1)/[M(M−1)]. These yield the total expectations,
HT variance components, ratio bias correction, and covariance correction for
an assignment-dependent coefficient. Centering preserves means; expansion
of the population moments yields every corrected T8 line. Completing the
quadratic gives the stated arm and common optima, and its curvature is
strictly positive on T14's domain. The T9 inequalities evaluate the actual
printed subscript and bracket expressions.

For T16, writing e_j=y1_j−y0_j, the excess of the mean null estimator over
actual HT variance is

* M² τ²/[N²(M−1)] if e_j=τ for every j;
* M²/[N²(M−1)] · [(mean e)²+(M−2)S(e)/(M−1)] if c=t.

Both are nonnegative for M≥2, including the M=2 boundary.

Each per-copy sum in T17 is finite and bounded. Under its actual product law,
the mean of h copies has the asserted expectation and variance Var(X)/h.
Chebyshev's bound gives all four marginal weak laws; positive limiting arm
sizes give the pooled ratio limit. Within-cluster replication cancels its
positive multiplier in the estimators and preserves the design law. The
explicit probability-one error then proves genuine inconsistency while
N=7h tends to infinity. No assertion needs a coupling across population
indices to define its marginal convergence in probability.

## Verification artifacts

`/home/ubuntu/sap/tools/sap-lean scratch/Check.lean` completed with exit code 0.
It imports only `SAP.P020.Defs` and contains no `sorry`. Its checks include:
nonempty finite-law support; positive general population denominators; a
four-cluster two-per-arm design with positive size variance; both distinct
T16 hypotheses; an actual individual sharp-null realization with nonzero
total variance; nonempty covariate, block and copy indices; T12's simultaneous
non-invariance hypotheses; and simultaneous T2 limit hypotheses. Equality of
the within-replicated and original design laws is checked by `rfl` for every
population. Only one Lean process ran at any time; `lake` was not run.

`python3 scratch/audit_exact.py` independently enumerates ordinary subsets
and products using rational arithmetic. It passed for all four named
counterexample populations, 63 additional complete-randomization designs,
315 coefficient/variance checks, 16 independent-copy marginal checks, and a
two-block product with nine assignments. The results are saved in
`scratch/audit_exact.json`. These are finite instance checks; the universal
identities and limit arguments were also assessed mathematically above.

Both requested JSON files were parsed and checked for one entry per target,
correct theorem names, and allowed verdict values using Python.
