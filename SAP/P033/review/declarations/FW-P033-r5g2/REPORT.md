# Review of P033-T6 through P033-T10

All five declarations are **faithful**, with severity **none**. Their SAP
definitions express the stated mathematical notions, and no substantive extra
assumptions, vacuous premises, encoded conclusions, or active junk values were
found. The five `whole` decisions and the Challenge docstrings agree with the
canonical mathematical claims. No step-2 conclusion changed after reading the
record.

| Declaration | Review result |
| --- | --- |
| `SAP.P033.T6` | Includes the binary population and sample bounds, fixed stored-SE power bounds and roots, sample-size correction, both table changes, and t-ratio invariance. The stored SE remains a numerical premise. |
| `SAP.P033.T7` | Includes all linear, polynomial and Gaussian counterexamples and the genuine conditional over-rejection calculation. The product law preserves independence, and the conditioning event has positive probability. |
| `SAP.P033.T8` | Includes the conditional binomial law, equal-mass criterion, both monotonicity directions, finite-width bound, shrinking-window limit and expansion, and benchmark tails. Its optional local assumptions apply to the appropriate clauses. |
| `SAP.P033.T9` | Includes Gaussian rejection power, monotonicity, cluster-label counting, conditional SE-factor comparison, four ratios/overlaps and six table corrections. It does not assert validity of an arbitrary clustered variance approximation. |
| `SAP.P033.T10` | Includes the nonsignificant point to the right of the printed line, the reciprocal-line comparison, and the distinct variance/SD coordinates with identical t-ratios. |

T7 and T10 establish the canonical counterexample assertions, so their `whole`
labels are appropriate. T7 tests the finite-window inference from absence of
publication selection to equal side mass; it does not dispute Table 1's counts
or arithmetic or a shrinking-window limit. T10's second witness distinguishes
two readings of the standardizing phrase without claiming the phrase literally
commands division by variance. The printed readings and witness-condition
checks are recorded in `claim-stage.json`.

The blind reading, including all statement dependencies and totalization
conventions, was saved in `reading.md` before opening the claims.
`claim-stage.json` was saved before opening the record. All 114 distinct
generated auxiliary proofs were printed and read; they concern numeral types
and the ordinary real scalar action.

`/home/ubuntu/sap/tools/sap-lean scratch/Check.lean` completed with exit 0
(style/deprecation warnings only). It constructs a fair binary variable,
verifies the linear density and positive 19-study conditioning probability,
constructs a normalized density meeting T8's local assumptions, realizes the
Gaussian and overlapping-cluster premises, and independently proves the complete
T10 statement. It imports only the Definitions, and uses no Challenge theorem.
The independent arithmetic checks in `scratch/NumericCheck.py` also passed:
fraction calculations are exact; floating normal evaluations are diagnostics
and are not claimed as interval certificates. Full evidence is recorded in each
entry of `findings.json`.
