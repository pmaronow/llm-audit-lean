# P026b statement audit

Audited all 12 targets and all 12 Challenge theorem stubs, in the required
order. The blind expansion was saved as `reading.md` before opening
`claims.json`. The comparison was saved as `claim-stage.json` before opening
`record.json`. No mathematical step-2 verdict changed after reading the
record. Claim notes and provenance rows were not treated as hypotheses.

| Verdict | Count |
| --- | ---: |
| correct_whole | 10 |
| correct_restricted | 1 |
| not_faithful | 1 |
| restriction_inaccurate | 0 |
| vacuous | 0 |
| false | 0 |
| omission_ok | 0 |
| omission_questionable | 0 |

Severity: 11 none, 1 minor, 0 major. The one adverse verdict concerns a
required docstring disclosure; the underlying theorem matches its canonical
mathematical claim. No target is omitted.

## P026-T15 — not_faithful, minor documentation defect

`SAP/P026b/Challenge/Part1.lean:17–19` gives the three-unit OLS example and
its expectation and bias, but does not identify the reading of the package
guidance that the example refutes. The task explicitly requires an
interpretation-based refutation's docstring to say which reading it
refutes. Here that reading is that calling `estate()` with `HT=TRUE`
preserves unbiased Horvitz–Thompson estimation when `X` is supplied.

The canonical counterexample itself is correct: every allocation has
positive probability, the displayed vectors are the unique OLS fitted
responses, the adjusted estimates are `(1/4, 1, 1/4)`, their expectation
is `1/2`, the ATE is `1`, and unadjusted HT is always `1`. The architect's
`whole` classification is right. The adverse finding is confined to the
separate documentation rule, and does not change the step-2 mathematical
comparison of `whole`.

Add this sentence to the docstring:

> This refutes the reading of the package help that estate() with HT=TRUE
> remains unbiased when covariates X are supplied.

A complete replacement docstring is provided in `findings.json`. The Lean
statement needs no change.

## Accepted restriction and refutations

T21 is correctly restricted. Clause (b) adds exactly `m` treated clusters
on every positive-weight allocation (`Defs/Part5.lean:38`). The canonical
formal-content clause lists the partition and the equal marginal
probabilities without this fixed-count condition. Both the record and
the Challenge docstring at lines 53–54 disclose the addition completely.
The restriction is proper: independent fair assignments on two clusters
have the required marginals with `M=2,m=1`, but support allocations with
zero or two treated clusters. A complete one-of-two design satisfies the
stronger hypotheses. The extra condition is unnecessary for the stated
cluster-scaled algebraic identity, but is an accurately disclosed
narrowing.

T17, T18 and T19 correctly refute assertions in their canonical printed
claims. T17's two-unit law has true HT variance `27/8` and expected printed
variance estimate `23/8`, under the sharp null and positive same-arm
joints. T18's XOR fit has covariance `1/4` despite each fitting input's
individual independence from the focal treatment. T19 need only disprove
the conjunction of printed table moments; the FE mean alone is outside
the claimed rounding interval. None of these three is merely a
refutation of an alternative reading of package guidance.

## Definition and nonvacuity checks

Expectations are finite sums under normalized nonnegative weights.
Positive marginals and nonempty unit types protect all universal ATE and
HT denominators. Natural subtractions occur with strict bounds on the
subtrahends. The printed variance estimator's epsilon convention matches
the canonical formula. The logistic likelihood uses probabilities
strictly between zero and one. Existence of its maximizers is a conclusion,
so the definition's fallback is not an assumption doing the work. The
OLS definition is ordinary Euclidean projection onto the actual column
space; no full-rank assumption has been added. Cluster totals use a
surjective partition map and actual unit and cluster counts.

Nonempty real unit and cluster probability laws, positive cluster
disagreement, complete-assignment examples, and the properness of T21's
restriction are checked in the scratch Lean files. Fixed zero predictions
instantiate every zero-covariance antecedent. The numerical and
refutation targets are closed assertions with explicit nonempty finite
populations, rather than implications with impossible hypotheses.

The table data and regression meanings were checked against Table 1 and
Section 7.1 of the [paper, pp. 147–148](https://joelmidd.github.io/papers/AronowMiddleton_A%20class%20of%20unbiased%20estimators.pdf#page=13).
In particular, the logistic predictions deliberately use the other
block's fitted coefficients. Independent enumeration recovers the exact
linear residual vector, FE mean approximately `-0.013987426269439`,
logistic ATE standard deviation `0.247091750594593`, and logistic variance
estimator standard deviation `0.012566702389965`. The decimal logistic
check supports the stated intervals; it is not itself a formal
enclosure or a replacement for the package's proof certification.

`scratch/numerical_audit.py` uses exact rational arithmetic for the finite
regression calculations and 75-digit decimal arithmetic for the logistic
score equations. Its saved results are in
`scratch/numerical-evidence.json`. Scratch proofs import only
`SAP.P026b.Defs`, with no use of Challenge stubs or source-formalization
proofs. No `lake` command was run, and at most two Lean processes were
active. JSON parsing and exact target coverage were checked with Python.

Final validation passed: `scratch/Nonvacuity.lean`,
`scratch/CountNonvacuity.lean`, and `scratch/Check.lean` each compiled
successfully with `/home/ubuntu/sap/tools/sap-lean`; the independent Python
audit also passed. Results are recorded in `scratch/validation.json`.
