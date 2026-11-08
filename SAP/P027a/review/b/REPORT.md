Statement audit completed for all 11 targets: **1 correct_whole, 9 correct_restricted, 1 omission_ok**. No false, vacuous, unfaithful, inaccurately restricted, or questionably omitted target was found.

| Verdict | Count |
|---|---:|
| correct_whole | 1 |
| correct_restricted | 9 |
| restriction_inaccurate | 0 |
| not_faithful | 0 |
| vacuous | 0 |
| false | 0 |
| omission_ok | 1 |
| omission_questionable | 0 |

Severity counts: none 11, minor 0, major 0. There are no adverse items requiring a corrected statement or docstring.

| Target | Assessment of the architect's decision |
|---|---|
| T1 | Correctly restricted to the retained numerical witness and alternating-family identities; missing representations, comparisons, continuous-measure identification and explicit asymptotic assertions are disclosed. |
| T2 | Correctly restricted. Integrability antecedents, square-level calibration, omitted intermediate identities and finite nonvanishing/numerical assertions, and positive-size reindexing are disclosed. |
| T3 | Correctly restricted to the two explicit bias-increase witnesses and retained moments; missing detailed probability lists and samplewise numbers are disclosed. |
| T4 | Correctly restricted. Exact common-indicator fibers are distinguished from the general almost-sure preservation input; the missing squared-difference identity and reduction example are disclosed. |
| T5 | Correctly restricted to the rounded scalar violations and exact 120-unit calculations. It does not assert the full table-interpretation refutation or identify an implementation; this limit is explicit. |
| T6 | Correctly restricted to the finite periodic formulas and comparisons, with disclosed integrability premises and missing continuous-start, preservation, mean-scale and provenance assertions. |
| T9 | Omission is justified. The numerical statements do not identify the code or implementation that produced the table. The canonical text does not support labelling a printed qualitative sentence false merely because one interpretation fails. |
| T10 | Correctly restricted to a deterministic finite counterexample and neighborhood; support/model-event connections and other missing explicit subclaims are disclosed. |
| T11 | Correctly restricted. The averaged conditional design-bias formulas are faithful; added integrability and omission of the explicit realization comparison are disclosed. |
| T12 | Correctly whole. It includes the infeasible printed probabilities, normalized negative-binomial product law with finite moments and positive witness mass, and all six configurations. |
| T13 | Correctly restricted. Indicator integrability, omitted cap-map properties, construction identifications, conditional-redraw description and provenance are disclosed. |

The audit order was preserved: `reading.md` was saved before opening `claims.json`; `claim-stage.json` was saved and parsed before opening `record.json`. The record caused **no revisions** to the step-2 classifications. Each of the nine declared restrictions occurs verbatim, apart from whitespace, in its theorem docstring. Proof-row names in the record were not used as evidence of statement correctness.

The definitions preserve the ordered zero-pair convention, diagonal HT terms, exponent-2 correction, original-population mean divisor, and distinction between a ratio of outcome averages and a realized population's ratio. Positive-denominator guards are sufficient. No integral outside its stated or derivable integrability conditions, truncated subtraction, infinite-value conversion, unbounded limsup, empty-type device, or conclusion-assuming hypothesis was found. Finite atom representations lose no subset-law generality on a finite population.

Independent checks passed:

* `/home/ubuntu/sap/tools/sap-lean scratch/Nonvacuity.lean` — exit 0; imports only Defs. Checks include valid positive finite laws, a strict unequal-group branch, positive-variance independent-sign noise, nonzero calibration, positive total variance and systematic-indicator integrability.
* `python3 scratch/exact_checks.py` — exact rational enumeration passed for all finite numerical witnesses, the 120-unit calculations, rounded-table tolerances, all six infeasible vectors and the repaired PPS law. The T10 closed-box maximum is `-49/4`, safely below its stated bound `-13/4`.
* General identities were checked algebraically, including the negative squared-group-total bias, aggregation difference, centered-noise moments, both outcome-averaged ratios, negative-binomial normalization/moments, and systematic sample cardinality and marginal probabilities. Details and limits of these checks are in `scratch/verification.md`.

The estimator rendering and aggregation convention agree with the display and paragraph on printed p. 237 of the [published article](https://www150.statcan.gc.ca/n1/pub/12-001-x/2013001/article/11831-eng.pdf#page=9). The simulation model and table context were cross-checked against Section C and Table A3 of the [paper's supplement](https://cyrussamii.com/wp-content/uploads/2013/08/smj_suppl.pdf). The canonical statements and required definitions, rather than audit-history notes, determined the scope judgments.

`findings.json` contains one entry for every target, with individual nonvacuity evidence and confidence. Both output JSON files were parsed with Python and their coverage checked against the targets and theorem declarations.
