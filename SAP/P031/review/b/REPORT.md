# P031 statement audit

Audited all 11 canonical targets. Counts:

| Verdict | Count |
| --- | ---: |
| correct_whole | 9 |
| correct_restricted | 2 |
| restriction_inaccurate | 0 |
| not_faithful | 0 |
| vacuous | 0 |
| false | 0 |
| omission_ok | 0 |
| omission_questionable | 0 |

Severity counts: none 11, minor 0, major 0. No targets were omitted.
There are no non-`correct_*` findings.

## Record decisions and disclosed scope

All eleven record decisions are justified. Here `correct_whole` includes
the correct direct refutation recorded for T5; it does not assert that
the original positive large-sample conjunction is true.

P031-T5's canonical statement explicitly asserts that the other robust
estimators are asymptotically equivalent to HC2 and explicitly lists
normality as the only printed hypothesis. Its HR/HC2 counterexample
under a standardized normal limit therefore negates an asserted clause
of the canonical conjunction. The relative-error definition is the
ordinary first-order meaning relevant to transferring interval coverage.
The theorem need not falsify coverage separately to refute a conjunction
containing equivalence. Its docstring correctly discloses this limitation.
This is a direct refutation of an assertion, rather than merely a
counterexample to an optional reading of descriptive guidance. The
record's `refuted` label is appropriate.

The corresponding passages were checked against
[the paper, pp. 367–368](https://cyrussamii.com/wp-content/uploads/2013/08/samii_aronow_equivalencies_white.pdf#page=3).
No unprinted arm-growth or moment conditions were imported from its
bibliographic references.

P031-T6 correctly discloses the dropped contrasting coverage assurance
for Neyman and HC2. It retains both directions of scaled OLS/CE error
and a common standardized-normal undercoverage witness for every
positive critical value. The scale is explicitly allowed by the
canonical definitions.

P031-T7 proves the entire canonical counterexample itself, so `whole`
is the right decision even though that counterexample falsifies the
quoted original-covariance equality. T8 and T9 include every intermediate
equality of their corrected proof chains, not just their endpoints.

P031-T10 correctly discloses every dropped canonical clause: the
intermediate observed-vector/intercept/estimate/residual shift identities;
the exact finite-row variance and OLS formulas and the treated-sign
second-moment formula; and the N=8 enumeration calculations. Its three
fixed families, all prescribed moments, scaled limits, probability and
ratio limits, and population-level shift invariances remain present.
Dropping a CE limit is not a restriction of this target because the
canonical claim does not assert that limit.

P031-T11 includes all deterministic and conditional probability limits,
bounded-outcome sufficiency and exact shifts. It explicitly discloses
its centered arm sample-variance meaning of second-moment convergence.
The positive-denominator hypothesis belongs only to the ratio clause,
and the additional moment condition only to the probability clauses.

## Order and correction log

`reading.md` was saved before `claims.json` was opened, and the initial
`claim-stage.json` was saved before `record.json` was opened. The initial
stage is preserved in `scratch/claim-stage-initial.json`. No Solution or
Comparator files were read. Claim notes and `finite_lemmas` were not
used to add or remove canonical clauses.

One claim-stage reason was corrected for a specific misreading, not
because the record supplied new hypotheses: the initial T5 reason
treated the absence of formal definitions as if it removed the
canonical equivalence assertion. On rereading the canonical statement,
the sentence **“The other estimators are all asymptotically equivalent
to HC2”**, together with the final bracket stating that normality is the
only printed hypothesis, contradicts that initial concern. Undefined
formal notation does not erase an explicit mathematical assertion.
The concern about the `refuted` label and opening docstring was therefore
withdrawn. The corrected reason cites these exact clauses.

T5's `my_reading_vs_claim` remains `different` to record its logical
polarity: a counterexample/negation rather than the original positive
conjunction. Its final verdict is `correct_whole` because the architect's
direct refutation correctly addresses that canonical assertion. No other
claim-stage assessment was changed.

## Definitions and validation

The finite hypotheses imply at least two units in each arm, a nonempty
legal assignment set and positive denominators. Natural subtraction
does not admit invalid allocations. The inverse Gram matrix, leverage
and sandwich coefficient contractions match the two-column regression
definitions. All randomization expectations are actual finite uniform
averages, and true variance is variance about the actual expectation.
The normal CDF is Mathlib's genuine standard Gaussian CDF. Relative-error
events handle zero reference estimates without division by zero, and
coverage includes zero-width intervals. No hypothesis assumes its own
conclusion. No vacuity or mathematical falsehood was identified in a stub.

Validation completed:

* `/home/ubuntu/sap/tools/sap-lean scratch/Check.lean` passed. It imports
  only Defs, checks an admissible balanced assignment, a nonempty legal
  assignment space, the explicit unbalanced family, and its population
  growth. It uses no Challenge theorem or `sorry`.
* `python3 scratch/exact_checks.py` passed with exact rational arithmetic
  on 15 general populations / 426 assignments and six sign-family
  populations / 744 assignments: 1,170 assignments total. It checks
  the finite identities, randomization expectations and variances,
  counterexample numbers, expected-OLS formula, sign-family row
  formulas, and shifts by c=7,d=-5. Results are saved in
  `scratch/exact-checks.json`.
* These finite checks are examples, not universal proofs. Analytic
  nonvacuity witnesses for the asymptotic assertions are given below
  and in each target's `nonvacuity` field in `findings.json`.

## Asymptotic nonvacuity

For T5, take N=n+4, M=2, all y0=0, and
y1_i=Phi^{-1}((i+1/2)/N). These symmetric, distinct normal quantiles
have mean zero and variance tending to one. Two draws without
replacement converge jointly to independent standard normals, while
the exact treatment-mean variance tends to 1/2. Thus the standardized
normal-limit premise is satisfiable. On every assignment the control
residuals are zero and HR=HC2/2 with HC2>0. The relative-error event
at epsilon=1/4 therefore has probability one. All finite design
inequalities are satisfied. This gives a mathematical nonvacuity
argument independent of the imported formalization's proof.

For the other asymptotic targets, set N=4k, M=k, with half the signs
z_i=-1 and half +1, y0=z and y1=a*z+2, k=n+2. If r is the treated
sign mean, its control counterpart is -r/3, E[r]=0 and
E[r^2]=3/(N-1). The centered treatment estimator is (a+1/3)r, and

    N*trueVariance -> 3a^2+2a+1/3,
    N*OLS -> 4a^2/3+4 in probability.

The second limit follows from the exact expression

    N*OLS = N/(N-2) [4a^2/3+4 - (4a^2/3+4/9)r^2]

and Markov's inequality. Its expectation has the same limit. CE has
the same probability limit because CE=(N-2)/(N-1)*OLS. These
observations verify all three T10 witnesses and the nonzero denominators
of their ratios.

For T6, a=2 gives scaled true variance 49/3 and scaled OLS/CE limit
28/3; a=1/2 gives 25/12 and 13/3, respectively. The hypergeometric
normal limit for the treated sign count supplies standardized normality
for the first sequence. Its limiting coverage is
2*Phi(z*sqrt(4/7))-1, strictly below 2*Phi(z)-1 for every z>0.

For T11, a=1 gives p=1/4, v1=v0=c=1, a uniform outcome bound of 3,
and positive true scaled variance limit 16/3. Since r tends to zero
in probability and both arm sizes grow, the centered arm sample
variances converge to one. This exercises the boundedness and
positive-denominator branches, rather than merely a degenerate
zero-variance case.
