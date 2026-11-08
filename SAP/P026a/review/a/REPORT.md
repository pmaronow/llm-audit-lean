# Statement audit of P026a

All 12 targets pass within their declared scopes: **6 correct whole and 6 correct restricted**. No false, vacuous, unfaithful, inaccurately restricted, or omitted target was found.

| Verdict | Count |
| --- | ---: |
| `correct_whole` | 6 |
| `correct_restricted` | 6 |
| `restriction_inaccurate` | 0 |
| `not_faithful` | 0 |
| `vacuous` | 0 |
| `false` | 0 |
| `omission_ok` | 0 |
| `omission_questionable` | 0 |
| **Total** | **12** |

There are no non-`correct_*`/`omission_ok` findings to list. All severities are `none`; no statement or docstring fix is requested.

## Blindness and record assessment

`reading.md` was saved after reading all Defs and Challenge sources and tracing their finite-sum, vector, cardinality and field conventions into Mathlib, before opening `claims.json`. `claim-stage.json` was then saved before opening `record.json`. The stage-2 classifications remain unchanged: six whole and six narrower.

The architect's decisions agree with the independent assessment: T2, T3, T8, T10, T11 and T12 are whole; T1, T4, T5, T6, T7 and T9 are restricted. Each of the six restriction strings matches its Challenge docstring exactly. The restrictions describe the omissions found at stage 2 accurately and completely. There are no omitted targets; `rows_not_used` entries in the record concern proof rows, not additional canonical targets.

| Restricted target | Disclosed loss of coverage |
| --- | --- |
| T1 | Selected marginal/probability and pointwise numerical facts; literal [34] undefinedness is represented only by zero-denominator/numerator diagnostics. Covariance moments explicitly concern the zero-omitted continuation. |
| T4 | Exact full fitting sets, an explicit independence-failure probability comparison, three-unit marginal values, and the three-unit XOR fit's pointwise zero generalized estimate; its expectation remains. |
| T5 | Unbiased totals and ATE require assignment-vector independence for every unit. The weaker observed-response-vector premise and mixtures are omitted from that unbiasedness clause, while their individual independence/covariance conclusions remain. |
| T6 | The explicit prediction and residualized FE formulas are not identified as OLS fits or regression solutions. The numerical facts concern those formulas. |
| T7 | The OLS identification and blanket unchanged-column assertion are omitted; only the selected HT/prior moments and variance rounding are retained from the latter. |
| T9 | Explicit half-valued marginals, pointwise [34] values and the population arm-variance-bound equality to 28 are omitted. |

## Mathematical and computational checks

All expectations are finite weighted sums. Probability normalization and positive marginals are genuine assumptions or verified concrete properties. The population-size denominators use cardinalities of nonempty types. Surjective cluster maps give nonempty fibers, and the separation premise is the standing distinct-cluster assumption. No premise assumes a desired covariance, bias or equality.

The epsilon adjustment in [35] is the stated convention. The covariance continuation explicitly omits zero joints; support makes it coincide with [34] wherever the literal statistic is claimed. Positive-joint branches in the arm estimators use ordinary nonzero denominators. The unavailable cross-pair sum in T12 includes the diagonal. The squared rounding intervals are used only with positive rounding centers. The numerical design's natural-number subtraction is guarded by the branch where the unit index is at least four.

`scratch/Check.lean` was compiled successfully with `/home/ubuntu/sap/tools/sap-lean scratch/Check.lean`. It constructs a real law on two independent fair assignments and an identity cluster partition, proving normalization, positive marginals, separation, directed and same-arm support. It also proves mutual assignment independence and independence from a nonempty singleton fitting vector. Thus the general premises do not depend on empty populations or empty fitting data. The per-target `nonvacuity` fields give further explicit instances, including unavailable pairs and strict conservative bounds.

`python3 scratch/audit.py` passes. It independently enumerates the supplied rational laws, both XOR examples, the 90-assignment numerical population, residual vector, linear moments, FE intervals, selected HT/prior moments, and all six Appendix-E display values. It verifies FE denominator positivity exactly: the covariate sum of squares is 331/10 and the minimum treatment-residual sum of squares is 2710/993. A further 38 nondegenerate finite laws, including zero-weight allocations, missing joints and signed outcomes, satisfy the checked printed/repaired bias and positive-weight decomposition identities. These finite checks supplement the mathematical reading; they are not proofs of the universal theorems.

The supplied canonical transcriptions were the comparison standard. The [paper](https://d-nb.info/1363881582/34) was retrieved after the blind reading for context. No Solution or external formalization was read. Original Defs and Challenge files were left unchanged; no `lake` command was run, and Lean checks ran sequentially.

`claim-stage.json` and `findings.json` parse with Python; their target IDs and theorem names cover the 12 canonical targets exactly once.
