# P023 statement audit

Audited all 12 targets in the required order: saved the blind expansion in
`reading.md`, saved the independent claim comparison in `claim-stage.json`,
then read `record.json`. No claim-stage verdict was changed after reading
the record.

| Verdict | Count |
| --- | ---: |
| correct_whole | 8 |
| correct_restricted | 4 |
| restriction_inaccurate | 0 |
| not_faithful | 0 |
| vacuous | 0 |
| false | 0 |
| omission_ok | 0 |
| omission_questionable | 0 |

Severity counts: **none 12; minor 0; major 0**. There are no adverse
findings or omitted targets. T10 and T12 correctly refute the canonical
printed readings; their negations are the intended audited statements.

The four restrictions are accurate and disclosed in both the Challenge
docstrings and the record:

- **T3:** omits the finite-tolerance event-probability inequality; adds
  positive close-window counts to the whole nonlocality component; adds
  the listed probability, degree, bandwidth and sample-design guards to
  the shared-consistency component.
- **T4:** adds sample-design guards for degree one, degree seven and RD;
  risk comparisons cover measurable predictors with integrable squared
  error. All population formulas and fit bounds remain present.
- **T5:** restricts risk comparisons to measurable predictors with
  integrable squared error. The explicit witness and complete changing-law
  family remain present.
- **T8:** adds RD admissibility and OLS admissibility at every fixed degree
  and every rate-qualified growing degree sequence. All population,
  sampling and degree-schedule-existence conclusions remain present.

The record's remaining whole/refuted decisions agree with the independent
reading. The unused rows listed there are supporting or redundant results;
they do not identify missing clauses of these target statements. There
are no target-level omitted decisions to assess.

Definitions were checked for mathematical domain problems. Under the used
hypotheses, residual variances and central RD denominators are positive;
observed-bin demeaning never divides by an empty bin's cardinality;
relevant integrals are integrable; approximation and risk extrema have
nonempty bounded domains in the required direction; and the growing-degree
Rayleigh infimum is a positive eigenvalue. The continuity counterexample
uses explicit tail inequalities and subsequential divergence, avoiding a
real limsup on an unbounded sequence. Sample-design guards control the
singular/empty events asymptotically. No hypothesis assumes the claimed
bias identity or consistency conclusion.

`scratch/Check.lean` compiled successfully using
`/home/ubuntu/sap/tools/sap-lean scratch/Check.lean`. It imports only the
definitions and proves concrete full-rank, positive-window,
coarsened-solution and pair-indexed nonvacuity instances.
`python3 scratch/audit_exact.py` passed independent exact rational checks
of both finite matrices, every stated finite weight and coefficient
change, both population projections and residual variances, tail shares,
sigmoid coefficients, the tight degree-seven amplification bounds, and
clustered-law normalization and moments at three positive parameters.

`findings.json` gives a substantive instance for each target. For the
universal sampling statements, uniform IID margins with bounded noise
give all design guards; the rate implies degrees grow slowly enough for
binomial concentration to establish full rank with probability tending
to one. The fixed-law counterexample and the full logarithmic asymptotic
were assessed mathematically, not independently reproved in Lean. This
audit judges statements and does not inspect Solution or Comparator
proofs. All output JSON files were checked with Python.
