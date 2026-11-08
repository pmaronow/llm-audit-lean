# Palomar statement audit: P061b

All 10 targets are accounted for. There are **8 correct_whole** findings
(including the faithful refutation T16), **2 correct_restricted** findings,
and **0 issues**. No target is omitted.

| Verdict | Count |
|---|---:|
| correct_whole | 8 |
| correct_restricted | 2 |
| restriction_inaccurate | 0 |
| not_faithful | 0 |
| vacuous | 0 |
| false | 0 |
| omission_ok | 0 |
| omission_questionable | 0 |

Severity counts: none 10, minor 0, major 0. There are no items outside
`correct_*` / `omission_ok` to list.

## Order and scope

[reading.md](reading.md) was saved before opening `claims.json` or
`record.json`. It expands every theorem's objects, quantifiers, hypotheses
and conclusion, including all referenced SAP definitions and the relevant
Mathlib summation, division and limit conventions.

[claim-stage.json](claim-stage.json) was saved before opening `record.json`.
It records seven direct whole matches, two narrower statements and one
different-polarity statement, T16. No claim-stage comparison was changed
after reading the record. Rows named in the record were treated only as
the architect's declarations; no Solution or external formalization was read.

The architect's seven `whole`, two `restricted` and one `refuted` decisions
agree with the independent assessment. In the final verdict vocabulary,
T16's correct complete refutation receives `correct_whole`. Its claim-stage
comparison remains `different`, since the Lean assertion negates the
canonical assertion rather than asserting it.

## Decisions requiring particular care

**T16.** The canonical statement and standing assumptions permit infinite
atomic support and unbounded outcomes without an integrability hypothesis.
Consequently the unqualified assertion of ordinary finite-mean HT
unbiasedness does fail. A separate Lean proof constructs N=1,
p(n)=2^(-n-1), constant exposure 0, and y(n)=2^(n+1). Its exposure
probability is 1, but every term in the estimator's first absolute moment
is 1. This refutes the canonical AEPO assertion itself. The theorem and
docstring correctly identify an existence failure; they do not claim an
inequality between two existing finite means. The first-moment conjunct
ensures the refutation does not rely on Mathlib assigning zero to a
nonsummable real `tsum`.

**T17.** The docstring and record accurately disclose both losses of scope:
all survey unbiasedness in clause (b), including a census, is omitted;
clause (c) covers the binary cube itself and does not cover larger feasible
sets with extra zero-mass interventions. Clause (a)'s equal-margin identity
is retained. The supplied `exposedMean` is correctly a fixed-denominator
sum, and the completely randomized instance has exactly the required fixed
count on support. Its natural subtraction N−n is positive because 0<n<N.

**T19.** The docstring and record accurately disclose omission of the quoted
claim that zero joint exposure probability precludes an unbiased estimator
of the corresponding product. No assertion about all estimators is
formalized. The retained joint-positive unbiased variance estimate,
conservative estimate and Young inequality match the claim. The two
variance-estimate definitions preserve ordered-pair multiplicities and
diagonals. The conservative estimate divides by a joint probability only
in its positive branch; a zero joint probability uses the printed marginal
square correction.

**T20.** Its first-moment assumptions are authorized by the canonical
`definitions_needed`: “Expectations are over the design distribution and
are assumed to exist (automatic for a finite support).” In particular, the
displayed cancellation includes each exposed-outcome and prediction
expectation. Ordinary finite real expectations require the corresponding
absolute moments. The exposed-prediction moment is already implied by the
full prediction moment. This assessment uses that canonical clause, not
the audit-history note. Calibration is the printed sufficient condition;
it does not assume unbiasedness of the adjusted estimator.

**Infinite designs and asymptotics.** In T12, T13, T18 and T19, constancy
of outcomes on the relevant supported exposure cells makes their moments
finite, despite arbitrary off-support outcomes. T18's d-only formulas
lose no cases from the bundled d/e positivity assumptions: take e=d.
T21 retains all three printed conditions and proves the full probability
limit along N+1, which traverses every positive population size. Under its
assumptions the usual bound is
P(|HT−AEPO|>ε) ≤ b_N c_N²/(N² ε²) → 0.
A nondegenerate family satisfying every hypothesis is given in
[findings.json](findings.json): independent binary assignments, own-coordinate
outcomes, b_N=N/4 and c_N=2. No empty index type drives the conclusion.

## Verification

`/home/ubuntu/sap/tools/sap-lean scratch/Check.lean` completed successfully.
[scratch/Check.lean](scratch/Check.lean) imports only Defs and independently
checks the infinite-support refutation, positive household margins, joint
positivity, a zero joint probability, finite moment hypotheses, calibration
without NURVA, and a normalized binary-cube fixed-count instance for T17.
The printed axioms for the checked declarations are only `propext`,
`Classical.choice` and `Quot.sound`; no `sorryAx` occurs.

`python3 scratch/enumerate.py` completed successfully using exact rational
arithmetic. [scratch/enumerate.py](scratch/enumerate.py) verifies the household
and hidden-version contrasts, variance identities and conservative slack
for three designs with signed outcomes, and completely randomized
experiments for N=2,…,6 and every 0<n<N with interfering outcomes. For the
missing-pair example, variance=25/4 and expected conservative estimate=13/2,
so slack=1/4.

These checks supplement statement inspection; they do not purport to
certify the supplied theorem stubs' proofs. Nonvacuity instances for every
target are recorded in [findings.json](findings.json).
