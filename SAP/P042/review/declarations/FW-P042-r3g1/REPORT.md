# P042 declaration review

All five declarations are faithful at their recorded scope. T1 and T3 cover their
whole canonical claims; T2, T4 and T5 have accurate, disclosed restrictions.
No correction is needed.

The blind reading, including every closure declaration and junk-value convention,
was saved in [reading.md](reading.md) before opening the canonical claims.
[claim-stage.json](claim-stage.json) was saved before opening the record. Reading
the record required no change to the stage-2 conclusions. T5's stage-2 classification
as `different` records its negation of two positive formula assertions; its final
`faithful` verdict assesses the accurately disclosed partial refutation.

| Declaration | Recorded scope | Verdict | Severity |
|---|---|---|---|
| SAP.P042.T1 | whole | faithful | none |
| SAP.P042.T2 | restricted | faithful | none |
| SAP.P042.T3 | whole | faithful | none |
| SAP.P042.T4 | restricted | faithful | none |
| SAP.P042.T5 | restricted | faithful | none |

**T1.** `Defs/Part2.lean:21` and `Defs/Part4.lean:13` describe the actual
six-voter population and its 90 uniform allocations. The binomial expectation
is the product of three normalized count laws, so independence is built into
the construction. Every canonical moment, weight, variance ratio, coverage
event, sum and fraction is present. `Defs/WholeW1.lean:54` also includes the
actual Gaussian quantile and unchanged integer thresholds. The binomial law
with equal turnout probabilities admits the stated zero-effect realization;
the six-voter schedule explicitly states the individual sharp null.

**T2.** `Defs/Part6.lean:67` contains all eight general laws and the relevant
half-width identities. Its assumptions match the canonical mathematical setting.
Historical applications, covariance estimation, numerical recalculations and
editorial actions are accurately excluded in `Challenge/Part1.lean:22` and
the record. The fourth allocation label correctly permits unused units when
the three arm sizes sum to less than the population size.

**T3.** `Defs/WholeW1.lean:95` contains the exact fixed and DL calculations,
rounding discrepancies and agreement, actual quantile certificate, guarded
square-root-free equivalences and endpoint monotonicity. The claim is a calculation
on stipulated inputs; its docstring correctly avoids an inference about historical
intent or the program that generated the printed result.

**T4.** `Defs/Part7.lean:60` states the corrected rounding bins, positivity,
actual variance under the stipulated marginal variances and zero covariance,
and the alternative DL result. The canonical squared endpoint bounds follow
from the stated bins and exact positive gaps. The absent normal-quantile
enclosure and implementation actions are accurately disclosed at
`Challenge/Part1.lean:42`.

**T5.** The reading tested is: under H1/H2, with no covariance condition, the
variance of a precision pool is 1/W and that of a difference of disjoint
precision pools is 1/W_N+1/W_A. These are explicit subassertions of the canonical
statement's audit reading. For the compiled witnesses:

- The standard Gaussian is a probability measure on a standard Borel space;
  Z and both D_j=Z are Borel and square-integrable.
- J=2 and both marginal variances equal 1>0.
- Fixed precision weights are 1, hence normalized pool weights are 1/2.
  The actual pooled variance is 1, while 1/W=1/2.
- N={0}, A={1} are nonempty disjoint index sets, with within-pool weights 1.
  The difference is zero, with variance 0, while the proposed sum is 2.
- Neither tested formula imposes independence of the estimates or independent
  replicate assignments. Thus shared randomness violates no hypothesis.

`Defs/Part8.lean:13` states precisely these two negations. Its restricted
decision and `Challenge/Part1.lean:48` accurately avoid a refutation of the
historical empirical claims or a claim to reproduce their other clauses.

Validation: `/home/ubuntu/sap/tools/sap-lean scratch/Check.lean` passed without
errors or warnings and uses only Defs and Mathlib, with no Challenge theorem
or `sorry`. It supplies concrete nonvacuity data for every retained universal
law and both counterexamples. `scratch/Closure.lean` successfully printed all
81 generated closure proof declarations. `python3 scratch/numerical_checks.py`
passed the independent exact arithmetic checks; its floating Gaussian-CDF check
is only a cross-check, not a replacement for the certified quantile assertion.
No invalid denominator, infinite-variance conversion, empty-support mean or
default infimum affects an asserted statistical quantity. Findings and stage-2
JSON were parsed and checked against all five closure entries.
