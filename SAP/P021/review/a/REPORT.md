# P021 statement referee report

Audited both targets. The blind reading was saved in `reading.md` before opening
`claims.json`. The independent comparison was saved in `claim-stage.json` before
opening `record.json`. No claim-stage verdict was changed after reading the record.

| Verdict | Count |
| --- | ---: |
| correct_whole | 1 |
| correct_restricted | 1 |
| restriction_inaccurate | 0 |
| not_faithful | 0 |
| vacuous | 0 |
| false | 0 |
| omission_ok | 0 |
| omission_questionable | 0 |
| Total | 2 |

Severity counts: none 2, minor 0, major 0. There are no adverse findings and no
omitted targets.

## P021-T1: correct_whole

`SAP.P021.T1` states the canonical probability-law formulation of Proposition 1
and all the requested identities in Eqs. (2)–(4). The positive-degree support
convention is part of the canonical standing assumptions and is stated in the
docstring. Ignorability is equality of conditional means with positive sampling
probability, exactly as required. No extra independence or sign assumptions occur.

The probability law makes the finite degree support nonempty. Bounded outcomes
and finite discrete degree/sample coordinates make the integrands integrable.
Ignorability gives positive sampled masses on all supported strata; summing
them gives a positive sample fraction. Bayes' rule then gives
`p_k=(rho/c)*(q_k/f(k))`, and summing gives the nonzero normalization `c/rho`.
Finite-stratum total expectation yields the displayed mean and cancellation
identities. Every substantive denominator is justified. The record's `whole`
decision is correct.

## P021-T2: correct_restricted

`SAP.P021.T2` retains consistency in probability and ordinary deterministic
convergence under the canonical common bounds, realized empirical convergence,
and limit-law conditions. It additionally requires nonempty samples almost
surely at every random stage and at every deterministic stage. Both the
docstring and the record accurately state the entire restriction.

This is a real restriction. For example, let the first one-unit population have
state `(Y,D,S)=(1,1,0)` and every later population have state `(1,1,1)`. Its joint
empirical laws converge to the all-sampled Dirac law, which satisfies both limit
conditions with `c=a=1`. An arbitrary estimator value at the first, empty sample
does not affect consistency. The canonical claim includes this sequence; the
formal theorem excludes it. Likewise, positive empty-sample probabilities can
tend to zero without ever being zero. The restriction is unnecessary for an
arbitrarily extended estimator, but it is accurately disclosed and permitted
by the task's correctness rule.

For truth of the retained statement, `SY/D` and `S/D` are bounded continuous
functions on the common compact state space. With `b=c*a`, the limit-law
conditions imply `b>0`, `E[S/D]=b`, and `E[SY/D]=b*E[Y]`. Empirical convergence
therefore gives convergence of the two normalized sums, and continuity of the
ratio at the nonzero limiting denominator gives each asserted conclusion. The
record's `restricted` decision is correct; there are no unrecorded reductions.

## Verification and nonvacuity

`/home/ubuntu/sap/tools/sap-lean scratch/Check.lean` completed with exit code 0
(two tactic-style lint warnings). It imports only `SAP.P021.Defs`, uses no
Challenge theorem or Solution, and verifies compactness, integrability of
continuous real functions against probability measures, and concrete models of
the hypotheses of both targets and both T2 branches. It also checks negative
scale/profile parameters.

`python3 scratch/finite_models.py` passed all exact rational assertions. Its
four-atom model has a null intermediate degree stratum, a negative scale, a
profile zero only on the null stratum, and positive sampling fractions strictly
below one. Its population mean and VH ratio are both `1/2`. Eight-unit empirical
populations, or growing repetitions of them, give the required convergent
sequences. Full instance details appear in `findings.json` and
`scratch/finite-model-results.json`.

No solution or comparator was inspected, no `lake` command was run, and all
output files were written within the working directory. The final JSON files
were parsed and checked against the target and theorem inventories with Python.
