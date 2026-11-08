# P045a declaration review

All five declarations are **faithful**, with severity **none**, relative to
their recorded scope. No statement, definition, hypothesis, junk-value or
docstring defect was found.

| Declaration | Recorded scope | Assessment |
|---|---|---|
| `SAP.P045a.T6` | Restricted | Retains every mathematical event characterization and corrected/complement expectation formula, including threshold sufficiency. The omitted numerical example and software actions are disclosed. |
| `SAP.P045a.T7` | Whole | Covers all triangle-order, single-edge, asymmetry-count and exposure assertions, and the complete deletion output law for every stipulated probability. |
| `SAP.P045a.T8` | Whole | Uses the exact printed graph, independent uniform deletion/treatment law, outcomes, Hájek ratios and target. Includes every domain, count and numerical bias assertion. |
| `SAP.P045a.T9` | Restricted | Correctly retains the copying bounds, exposure implications, exact HT identities/sign and Hájek counterexample. The omitted separate matrix assertions and software/prose instructions are disclosed. |
| `SAP.P045a.T10` | Whole | Covers both complete centre and treatment laws, the retry calculation, partitions, separation failure and exhaustive repaired-net characterization. |

`reading.md` was saved before opening the canonical claims. Every supplied
closure declaration was read, including generated declarations printed in
`scratch/ClosurePrint.out`. `claim-stage.json` was saved before opening the
record. The record required no revision of those judgments.

The canonical T8 assertion is the explicit counterexample, which the theorem
establishes. Its docstring correctly identifies the *universal monotonic-bias
reading* being contradicted. The witness uses the required printed graph,
one uniformly treated unit, independent uniform undirected deletion, exact
probabilities and the stipulated positive-spillover outcomes. Every ratio is
defined. None of these items is incorrectly labelled `refuted` relative to
its canonical claim.

Real division by zero does not supply a claimed numerical result: all relevant
denominators are positive. The copying defaults are outside the matrix
coordinates under review. T10 includes summability for every terminal-length
series and both algorithms, excluding Mathlib's default zero for nonsummable
real sums. Natural subtraction is used at radius parameter 3, and the
singleton list fallback is protected by an actual singleton condition.

`/home/ubuntu/sap/tools/sap-lean scratch/Nonvacuity.lean` completed successfully
with no diagnostics. It imports only `SAP.P045a.Defs`, constructs nonconstant
T6 instances including threshold sufficiency, satisfies the T9 matrix and HT
hypotheses, and checks the concrete T7/T8/T10 witnesses.
`python3 scratch/enumerate.py` independently checked all 64 copying inputs,
all 2,110 Hájek cases, and both complete four-path laws using exact rational
arithmetic. The three biases are approximately 0.0200033290, 0.0091337422 and
-0.0012143920; their absolute values strictly decrease. Detailed exact outputs
are in `scratch/enumeration.json`.

`findings.json` contains the five original fingerprints and no adverse issues.
No source changes or fixes are needed.
