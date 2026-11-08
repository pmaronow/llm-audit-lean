# Declaration review

All five declarations are faithful to their recorded scope. No current issues
were found. T29 is faithfully restricted; the other four state their whole
canonical claims.

| Declaration | Recorded scope | Verdict | Severity |
| --- | --- | --- | --- |
| SAP.P004b.T26 | whole | faithful | none |
| SAP.P004b.T27 | whole | faithful | none |
| SAP.P004b.T28 | whole | faithful | none |
| SAP.P004b.T29 | restricted | faithful | none |
| SAP.P004b.T30 | whole | faithful | none |

The [blind reading](reading.md) was saved before claims or review history were
opened. Every closure entry was read, including the 31 generated proof
declarations printed with Lean. [claim-stage.json](claim-stage.json) was saved
before opening the record. No claim-stage assessment changed after the record
was opened. Earlier issues and the architect's response were read between the
blind and record stages; historical scope tables were checked against the
current source, rather than treated as current statements.

T26 includes the exterior-tail conclusion, explicit auxiliary radius, liminf
and C6 consequences, and the interior-premise remark. Its forced-coordinate
means implement S3 even at Bernoulli endpoints.

T27 includes the full W1–W5 witness and genuine valid-interval coverage limits.
Both earlier issues concerned wording: the two current docstrings explicitly
identify the repaired quadratic-spacing reading. Both issues are fixed, as
recorded separately in `findings.json`. The canonical target is itself this
counterexample, so its whole decision is correct. The witness meets every
condition of the tested reading; degenerating variance is not a violation of
that reading's premises.

T28 independently defines the five-term V1, identifies its row sum, states
all three raw approximation errors and the bias bound, and requires the
variance lower bound only for conservative liminf coverage. Quantile guards
are conclusions; invalid intervals do not count as coverage. All-size positive
bandwidths are a harmless finite-prefix convention for a diverging sequence.

T29's docstring and record accurately disclose its population-center
specialization, stronger uniform spacing and bandwidth conditions, and the
omitted V1/V2 clauses and numerical checks. Its retained cross-arm algebra
and N^-2 mean-product scale match the corrected claim.

T30 derives positive support sizes, conditional uniformity and disjointness,
and the equal Bernoulli remainder laws. Its independent explicit linearization
formula prevents the augmented-class alias from substituting for the actual
claim. The wrong-fit difference and characterization, variance equality and
quantitative interaction remainder are all present.

Usual measure-theoretic conditions are treated as presupposed, as instructed.
Positive finite spatial masses and integrability exclude junk averages.
Strict propensities protect conditional denominators, while forced means
handle endpoints explicitly. Empty-sample conventions affect finite prefixes.
Real empty or unbounded suprema/infima have default zero, but all substantive
extrema here are genuine; Gaussian quantiles have levels in (0,1), and T26's
real liminf occurs together with convergence to zero. Negative-variance square
roots and zero-denominator statistics cannot manufacture the asserted coverage
or counterexample.

[nonvacuity.md](nonvacuity.md) gives the instances and full condition checks.
Both [finite Lean examples](scratch/Nonvacuity.lean) and
[spatial Lean examples](scratch/SpatialNonvacuity.lean) compile successfully
with `sap-lean`, without invoking the Challenge theorem stubs. The spatial
examples assemble every outer hypothesis of T26, T28 and T29. A separate
balanced deterministic planar sequence establishes mathematical nonvacuity of
T28's additional variance premise; its general variance calculation is not
claimed as a compiled proof. Independent exact rational enumeration checks
T27's finite witness formulas, T29's cross-arm identity and an interacting T30
variance-square example; [the output](scratch/finite-checks.json) records all
checks passing.

The review changes only review artifacts and scratch checks. The five source
declarations and their definitions were left unchanged.
