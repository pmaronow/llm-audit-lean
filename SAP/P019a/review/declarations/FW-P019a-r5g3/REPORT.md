# T11 review

`SAP.P019a.T11`: **faithful**, severity **none**. The record's `whole`
decision and the theorem's docstring accurately describe the statement.
The step-2 judgment is unchanged after reading the record.

The theorem states the corrected treatment-arm expectations, affirmative-response
conditional expectation, and affirmative-cell mean shift with the canonical
assumptions. It also gives the asymptotic Wald coverage in correction (c).
The canonical statement assigns no separate mathematical content to correction
(d), which the docstring describes accurately.

All entries of the dependency closure were read, including generated proof
declarations checked with Lean. The finite observation range expresses the fixed
list's bounded counts; the underlying probability space is arbitrary. The
sampling law is an actual iid product, and treatment independence concerns the
entire triple `(W,X,Y)`. The empirical estimator and its variance agree with the
published formula, including division by sample size. See the
[published paper, p. 49](https://alexandercoppock.com/aronow_etal_2015.pdf#page=7).

All population conditioning events are required to have positive probability.
Sample denominator failures are excluded by a domain whose probability tends
to one; fixed completions do not affect coverage. Quantiles are evaluated
strictly inside their ordinary domain. Measurability, integrability, finite
measure values, and nonnegative square-root arguments prevent junk-value
conventions from changing the assertion. No hypothesis encodes the conclusion.

`scratch/Nonvacuity.lean` compiled successfully. Its uniform eight-point model
has `J=1`, independent fair bits `W,X,Z`, `Y=X`, and `V=W+XZ`. It proves all
four standing assumptions and every additional positivity hypothesis used by
the separate clauses. Each conditioning cell has probability and conditional
variance `1/4`, and `mu=1/2`; `alpha=1/2` is admissible. Thus every implication
has a genuine jointly satisfiable premise.

`reading.md` was saved before reading the claim; `claim-stage.json` was saved
before reading the record. The audit used only the supplied unit sources,
permitted Mathlib sources, scratch compilation, and the paper.
