# P016a declaration review

All five reviewed declarations are faithful to their recorded scope. No defects
were found in their statements, dependent definitions, or docstrings.

| Declaration | Canonical coverage | Recorded decision | Verdict | Severity |
| --- | --- | --- | --- | --- |
| SAP.P016a.T1 | Whole | whole | faithful | none |
| SAP.P016a.T2 | Whole | whole | faithful | none |
| SAP.P016a.T3 | Whole | whole | faithful | none |
| SAP.P016a.T4 | Narrower, accurately disclosed | restricted | faithful | none |
| SAP.P016a.T7 | Whole | whole | faithful | none |

`reading.md` was saved before reading the claims. Every closure entry was read,
including the 74 distinct generated proof declarations and the generated option
matchers. `claim-stage.json` was saved before reading the record. No claim-stage
judgment was changed after reading the record.

T1 includes both pairing covariances, both complete statistic tables, the tail
probabilities, and both design covariances. T2 includes every clause A–G, including
attainment and exact minimizers, fixed-size ordering, margin invariance, design
dependence, and the network and scalar-KS witnesses. T3 includes every finite
exposure, affine obstruction, regression minimum, determinant, and cutoff example.
T7 includes both genuine additive counterexamples and their corrected reference
probabilities. The `whole` labels concern the canonical counterexample assertions;
none is incorrectly labelled as refuting its own canonical assertion. T3's affine
obstructions concern ordinary centering and scaling of raw exposures and do not
assert impossibility for an unspecified arbitrary function.

T4's restriction is accurate (`record.json:64-66` and
`SAP/P016a/Challenge/Part1.lean:20-22`). It discloses the additional common-bank-count
assumption on the raw orientation identity and the two explicit positive-SD
assumptions. It also discloses omission of identification with the saved
10,000-assignment application bank, 500-draw directional application procedure,
projected maximum-p bounds, Figure 4's interpretation, and the released simulation
procedure as a whole. Its retained algebraic properties and doubled-tail witnesses
are correctly described. The narrower claim-stage result therefore remains
narrower while the final verdict is faithful to the declared restriction.

The [published paper](https://doi.org/10.1093/pan/mpw018) was consulted for the
printed procedure and model descriptions. The canonical `statement` and
`definitions_needed`, together with standing assumptions, governed coverage;
historical notes did not remove any clauses.

Validation used `/home/ubuntu/sap/tools/sap-lean`, with no `lake` invocation and at
most one Lean process at a time. `scratch/Nonvacuity.lean` compiled successfully
using only `SAP.P016a.Defs`, without relying on the Challenge stubs. In particular,
T4 has a nonempty model instance with positive exposure variance and two nonzero
coefficients; the eight-unit KS probability space has exactly 70 assignments.
`scratch/exact_checks.py` passed all independent exact-rational checks, including
the regression minima, determinants, and all 70 KS assignments. Results are in
`scratch/exact-results.json`.

Group means and conditional bank means have nonzero denominators in these uses;
standardization is protected by positive SD. Every least-squares infimum ranges
over a nonempty set bounded below by zero. Empty index types, totalized division,
and real square-root defaults do not supply any claimed witness or substantive
conclusion. Existing proof certification was taken as given, as requested.
