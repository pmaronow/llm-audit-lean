All five declarations are faithful within their recorded scope. No current
definition, hypothesis, junk-value or docstring defect was found. The blind
reading was saved in `reading.md` before the claims and prior review material
were opened; `claim-stage.json` was saved before `record.json` was read. No
step-2 conclusion changed at the record stage.

| Declaration | Canonical coverage | Record decision | Verdict / severity |
| --- | --- | --- | --- |
| `SAP.P027a.T6` | Narrower, with disclosed omissions | restricted | faithful / none |
| `SAP.P027a.T10` | Whole | whole | faithful / none |
| `SAP.P027a.T11` | Whole | whole | faithful / none |
| `SAP.P027a.T12` | Whole | whole | faithful / none |
| `SAP.P027a.T13` | Whole | whole | faithful / none |

T6 correctly states the finite phase estimators, corrections, comparisons,
bounds and guarded outcome-average ratio. Its omissions are accurately listed
at `SAP/P027a/Challenge/Part1.lean:35-43` and in the record. The integrability
antecedents are usual measure-theoretic conditions, so only the actual omitted
clauses justify the restricted scope.

T10's canonical assertion is the specified negative-bias witness against the
inference that positive sizes and the noisy model ensure conservativity for
each population. Its conditions are eight units, sample size two, positive
integer sizes in the offset-NB support, PPS feasibility, the specified ordered
uniform-start design, and the additive residual representation. The supplied
sizes, probabilities, intervals and outcomes meet each condition. All C1-C5
calculations and the perturbation bound are stated. The canonical note's
Gaussian event-probability discussion adds no clause. Both current docstrings
explicitly distinguish this inference from the literal proportional-outcome
assertion. The sole earlier issue is therefore fixed; this is recorded in
T10's `resolved` entry.

T11 averages the actual conditional sampling bias over errors with the fixed
size vector and design outside that average. It includes the full moment
identities, populationwise criterion, and positive-average versus negative
realization comparison. T12 includes the genuine positive-probability invalid
vector and every listed configuration. T13 includes the complete capped
ordered construction, certainty-unit example and independent full-vector
redraw recipe with its conditional output law. Neither counterexample is
mislabelled as a refutation of its own canonical assertion.

`scratch/Nonvacuity.lean` and `scratch/Support.lean` compiled successfully with
`sap-lean`; their final logs are empty. The checks construct all hypothesis
instances, exercise positive variance and positive model second-moment
guards, directly calculate the negative-bias and invalid-probability witnesses,
verify the six floor divisions, and prove positivity of every finite NB-vector
atom from the definitions. They do not invoke the Challenge theorem stubs.
All 85 generated closure proof declarations were also inspected. No `lake`
command was run, no more than two Lean processes ran concurrently, and no SAP
source was changed.
