# Statement audit of P045a

Audited all 16 Challenge theorem statements. The result is **1 correct whole
statement and 15 correct, disclosed restricted statements**. No architect
decision needs correction.

| Verdict | Count |
| --- | ---: |
| correct_whole | 1 |
| correct_restricted | 15 |
| restriction_inaccurate | 0 |
| not_faithful | 0 |
| vacuous | 0 |
| false | 0 |
| omission_ok | 0 |
| omission_questionable | 0 |

Severity: none 16, minor 0, major 0. There are no items outside the accepted
`correct_*` / `omission_ok` categories to report.

T8 retains the whole canonical finite counterexample. T1–T7 and T9–T16 retain
less than their canonical claims, and their Challenge docstrings and record
accurately identify the retained content and omissions. In particular, the
independent product laws and one-regime scope of T2 are disclosed; the
deterministic scope of T11 omits the stated uniform-sampling instance; and
T15 discloses its fixed six-group tract partition. No step-2 verdict was
changed after reading the record. There are no omitted targets.

The counterexamples assert the canonical witnesses and corrections, rather
than claiming those canonical assertions are false. T8's docstring correctly
identifies the universal monotonic-bias **reading** of the missing-tie guidance
as the proposition refuted by its witness.

## Order and evidence

1. `reading.md` was saved before opening `claims.json` or `record.json`.
   It expands all 16 proposition definitions and their underlying SAP
   definitions, with quantifier order, probability laws and arithmetic domains.
   Mathlib source inspection confirmed the meanings of finite subset selection,
   natural distance, graph extended distance, sorting and real infinite sums.
2. `claim-stage.json` was saved before opening `record.json`. It compares each
   theorem with the canonical `statement`, `definitions_needed` and standing
   assumptions. Audit-history notes and formalization row names were not used
   to add or remove canonical clauses.
3. The record was then compared against those saved assessments and the actual
   Challenge docstrings. Its 1 whole and 15 restricted decisions agree with them.

`scratch/Check.lean` imports only `SAP.P045a.Defs` and compiled successfully
with `/home/ubuntu/sap/tools/sap-lean scratch/Check.lean`. Its checks construct
a normalized full-support finite Design and a genuine Network, exhibit valid
first-stage and fixed-count domains and a nonconstant baseline, and construct
a completed greedy run on a disconnected graph. There are no proof holes in
that scratch file. The successful run emitted only a deprecation warning for
the Mathlib alias `ENat.coe_lt_top`. Two Lean processes were run sequentially;
`lake` was never run.

`python3 scratch/audit_checks.py` passed. Its independent exact-rational checks
cover the 512-outcome Bernoulli witness, all retained six-group numerical
variance examples, heterogeneous regular and singleton variance-bias examples,
the two-unit HT witnesses, all 64 triangle inputs, all 2,110 deletion/treatment
cases, all 45 pairs for both ten-vertex examples, the sampler laws, and all
20 tract selections. Detailed results are in `scratch/check-results.json`;
the target-specific nonvacuity evidence is also included in `findings.json`.
Finite examples check the universal identities on representative inputs;
their general forms were also reviewed mathematically.

## Arithmetic and domain checks

All conditional means interpreted probabilistically have positive event
probability. The fixed-count and regular variance formulas have nonempty arms
and the stipulated sample sizes. Off-support totalized expressions in the
finite sums have zero mass and do not change the estimators on their design
support. The singleton-drop estimator explicitly omits an undefined required
variance; its corrected counterpart returns `none`. Empty exposure HT cells
are genuine empty sums with positive individual exposure probabilities.

Every Hajek denominator in the deletion witness is positive. The sampler's
potentially infinite trace family is summable: after first center 0, each
repeat of 0 multiplies the mass by 1/4, and each of the three possible final
centers receives the convergent sum
`sum_(r>=0) 4^(-(r+2)) = 1/12`. Its treatment laws therefore use ordinary
convergent sums. Graph distances between disconnected vertices are infinity;
this convention supports the intended separation and covering conditions.

No hidden conclusion-as-hypothesis, inconsistent probability domain,
substantive use of division by zero, harmful natural subtraction, or empty
index type was found. The supplied Solution and Comparator were not read.
