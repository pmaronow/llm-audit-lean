# Referee report

All 15 targets have Challenge theorems. The decisions are correct on the supplied
statements: 4 whole claims and 11 accurately disclosed restrictions.

| Verdict | Count |
| --- | ---: |
| correct_whole | 4 |
| correct_restricted | 11 |
| restriction_inaccurate | 0 |
| not_faithful | 0 |
| vacuous | 0 |
| false | 0 |
| omission_ok | 0 |
| omission_questionable | 0 |

Severity counts: none 15; minor 0; major 0.

There are no non-`correct_*` findings and no omissions to adjudicate.

## Order and scope

`reading.md` was saved before opening `claims.json`; `claim-stage.json` was saved
before opening `record.json`. No stage-2 verdict was changed after reading the
record. The four whole claims are P004-T2, P004-T10, P004-T11 and P004-T13.
Each of their main canonical conclusions is present. Supporting proof suggestions
under `finite_lemmas` were distinguished from the canonical statement's conclusions.

The restrictions accepted in the other targets are:

| Target | Retained scope and disclosed losses |
| --- | --- |
| P004-T1 | Guarded failure of the printed IPW linearization and three weighted-square calculations. The entered arrays are expressly not identified as estimator coefficients or actual variances. The other numerical, moment, expansion and coverage certificates are omitted; the cyclic sequence is extended to all N. |
| P004-T3 | An actual constrained-MLE witness, variance guards and printed-SAH/actual-variance ratio limit 8/25. The spatial realization changes to counting measure at node points. Finite identities/comparisons and the other limit and coverage conclusions are omitted. |
| P004-T4 | Both weighting identities and the oracle covariance bound/expectation identity. All finite and asymptotic comparisons in clause (c) are omitted. |
| P004-T5 | The complete binary Euclidean-area Case B. Cases A and C and grid refinement are omitted; no empirical application effect is claimed. |
| P004-T6 | Integral aggregation through marginal means and effects, range/equal-mass results and scaling invariance. The two negative assertions and the empirical interpretation are omitted. |
| P004-T7 | The finite adjusted-order reversal and an eventual upper bound on guarded coverage. Exact limiting coverage and the listed auxiliary spectral, moment and asymptotic conclusions are omitted. Invalid draws are excluded from the coverage event; this is an unconditional probability of a conjunction. |
| P004-T8 | Finite capped variance ordering/inclusion and conservative coverage for supplied critical values at least the normal quantile. The universal Student-quantile comparison is omitted. Empty-arm draws satisfy the implication inside the asymptotic event. |
| P004-T9 | The actual boundary MLE, its maximizer conditions, the uniform 3/32 tail bound and failed score expansion. Separate numerical, derivative, moment and limit-law certificates are omitted. |
| P004-T12 | Eight-node Witnesses A and B, including a positive-probability draw array and actual exact rejection probability. The universal negative-statistic assertion, signed size and seventeen-node large-P witness are omitted. |
| P004-T14 | The two-node atomic Witness 2, sufficient to defeat every common weighting of its supported circle AMEs. The other witnesses and separate node-effect/mass-vector certificates are omitted. |
| P004-T15 | General point-effect integral identity, supported finite-shell decomposition/common positive weights, and the exact annular radial measure. The only-if/non-identifiability assertions and separate uniform-density comparison are omitted. Zero-mass shells are excluded as disclosed. |

The recorded restrictions agree with the Challenge docstrings, including line-wrap
hyphenation. `scratch/record-check.json` records that comparison. It checks textual
agreement; the substantive comparison is in the saved blind reading and claim-stage
reasons.

## Nonvacuity and mathematical checks

Every target's `nonvacuity` entry gives a concrete instance or an explicit reason.
In particular, the asymptotic assumptions in T2 and T8 are simultaneously
satisfiable with a positive variance floor: use singleton nodes (10i,0), counting
measure, assignment-independent alternating outcomes (-1)^i, p=1/2 and d=h=0.
For T2 add an intercept-only logistic model, truth 0, compact constraint [-1,1]
and its actual constrained MLE. The normalized Gram matrix is [1] and

    N Var(linearization) = 4(1 - mean(outcomes)^2) >= 3 for N >= 2.

For T8 the distance kernel is the identity, so identity eigenvectors and all-one
eigenvalues satisfy the spectral hypotheses. Homophily is zero in this example.
Thus the normal/coverage branches are instantiated as well as the preliminary
branches. T10 has the same genuine interior MLE instance.

`scratch/Check.lean` imports only the supplied Defs and compiled successfully with
`/home/ubuntu/sap/tools/sap-lean scratch/Check.lean`. It proves a nonempty,
positive-dimensional instance of **all finite T2 hypotheses**, uniform overlap,
nonempty treatment/control arms, a positive-mass well-defined spatial population,
finite T8 spectral/arm guards, and positive supported shell masses/common weights
for T15. Its log contains two cosmetic linter/deprecation warnings and no errors.
No Challenge stub is used. Only one Lean process ran at a time; no `lake` command
was run.

`scratch/arithmetic_checks.py` independently checks, using integers and rational
arithmetic:

* T1's three entered weighted squares.
* T3's actual fitted-IPW variances and printed-SAH expectations at N=32 and 64,
  by group-count enumeration; also the corrected N=32 raw-SAH expectation.
* T5's negative bin sum and positive area-weighted whole effect.
* T7's full twenty-node variances, adjustment traces and adjusted-order reversal.
* T9's sufficient negative-tail probability for N=1 through 500.
* T12's observed/resampled HT values and exact rejection size, approximately
  0.05549969550171698, strictly greater than 1/20.
* T14's zero supported-circle AMEs and disk/donut AME 1/6.

Results are saved in `scratch/arithmetic-results.json`. The general T9 tail bound
also follows from its Rademacher second/fourth moments as in the canonical claim;
the finite enumeration is an independent check, not a substitute for that argument.

The definitions were checked for material totalization conventions. Spatial
averages used in claims have positive finite mass and integrable outcomes;
propensity denominators are positive; singular finite matrices are guarded when
inverses matter, and the asymptotic information matrices are eventually
nonsingular. The Student parameters in T7 are positive on its guarded event.
The natural subtractions in T12's numerator stay in their intended ranges.
T15's radial density has positive denominator, and its supported-shell sums avoid
zero-shell means. No conclusion is assumed as a hypothesis, and empty types or
empty-arm conventions do not supply the claimed substantive results.

The full asymptotic propositions were assessed mathematically from the supplied
definitions and canonical statements; this statement audit does not certify their
Lean proofs. `findings.json` and `claim-stage.json` were parsed and checked with
Python against the 15 target IDs.
