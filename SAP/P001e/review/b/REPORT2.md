# P001e — revision 2 delta review

All 19 targets remain accepted: **7 correct_whole and 12 correct_restricted**. There are no adverse findings, false statements, vacuous statements or omitted targets. All severities are `none`. Under the required findings schema, the seven `correct_whole` verdicts include the three successful refutations; the architect's decision counts are **4 whole, 12 restricted, 3 refuted, 0 omitted**.

## Earlier findings and their disposition

My first review contained no adverse findings or requested fixes. All 19 previous verdicts are retained in [findings2.json](findings2.json); there are no outstanding earlier requests to classify as partly fixed or not fixed. The architect's account correctly identifies this review as Referee B's review.

The other referee's reported **T91 disclosure finding is fixed**, fully. The revised [Challenge docstring](SAP/P001e/Challenge/Part1.lean) and record2.json explicitly disclose:

- A supplied potential-outcome family indexed by every real dose, with every coordinate measurable and integrable.
- Conditional independence of that entire supplied process and treatment given X, including unsupported-dose coordinates, which strengthens the canonical supported-process premise.
- Separate measurability and integrability of the observed diagonal Y(D).
- The retained countable-cell, positive-mass identification and contrast, and the omitted continuous-dose clause, its observed-CEF bridge and continuity argument, and the intermediate conditional potential mean given both X and D.

My earlier zero-extension discussion was too permissive about disclosure. Choosing zero outside the treatment support replaces the supplied family; it does not eliminate the premise on the family actually quantified in the theorem. The architect's distinction is correct. For example, with fair binary D and constant X, take Y(0)=Y(1)=0, Y(2)=D and all other coordinates zero. Every coordinate and the diagonal are measurable and integrable. The supported process is deterministic, while the full process reveals D at coordinate 2: its joint event with D=1 has probability 1/2, and the product of marginal probabilities is 1/4. The revised disclosure accurately covers this stronger premise. The existing [scratch scope witness](scratch/Check.lean) verifies the distinction in Lean.

This explanatory correction does not change the saved blind reading or the mathematical theorem. It creates no remaining defect in revision 2.

## Changes checked against the saved reading

I reread all six Defs parts, both import aggregators and every Challenge declaration against [reading.md](reading.md). I found no change in mathematical hypotheses, quantifier order, conclusions, shared definitions or fixed data. The changed coverage text is T91's docstring. A comparison of record.json and record2.json likewise identifies only the T91 restriction entry as changed; theorem names and decision labels are unchanged.

The four `whole` labels still cover the canonical formal clauses:

| Target | Coverage checked |
|---|---|
| T81 | Both hot-deck donors, all eight distances, the second donor and gap, completed values and mean 16/3. |
| T82 | An actual bounded conditional probability/mean version, uniqueness almost surely, the invalid-range equivalence, and the tautology describing the printed thresholds. |
| T88 | Both observable endpoint formulas, sharpness, unbiasedness for every positive sample size and consistency under observable iid sampling. |
| T95 | Both directions of nearest-neighbor matching, the corrected donor comparison and gap, both completed columns and means, and contrast 7/6. |

The three `refuted` labels continue to refute the specified printed readings:

| Target | Refutation checked |
|---|---|
| T84 | The actual unique finite logistic MLE gives probability 7/12 and estimates 3/7 and 5/12, differing by 1/84. Positive respondent and nonrespondent counts in every cell prevent an empty-cell explanation. |
| T90 | Deterministic zero and spike potential processes satisfy process independence and give the same observable law under positive-density uniform dose, but different effect means at the specified supported pairs, including the interior pair. |
| T92 | The original design with covariate 10 gives the stated nonsingular OLS fit. Evaluating the two printed tables at covariate 9 produces the exact discrepancy −253/4874, refuting precisely their literal equality. |

The twelve restricted targets remain T77–T80, T83, T85–T87, T89, T91, T93 and T94. Their retained and omitted content agrees with the saved claim-stage assessment. All twelve restriction strings in record2.json match their individual Challenge docstrings. T91's expanded text now expressly captures its full input assumptions. No continuous-dose result or equivalence between cylinder-process independence and a stronger evaluation-ready contract is credited.

## Junk values and nonvacuity

The mathematical premises are unchanged, so the earlier per-target witnesses remain applicable. I additionally compiled [Delta91.lean](scratch/Delta91.lean) against the refreshed Defs using `/home/ubuntu/sap/tools/sap-lean scratch/Delta91.lean`. It passed with no errors or admitted scratch proofs. This check proves all substantive T91 hypotheses jointly for fair Bool probability, constant Unit-valued X, binary D, Y(t,ω)=t, and distinct doses 0 and 1. In particular, it includes the full real-indexed independence and both separately required diagonal conditions. Both target cells have mass 1/2; no conditioning denominator vanishes.

The full process in this witness is a constant random element, while its observed diagonal is the nonconstant D. Thus the stronger disclosed assumptions are jointly satisfiable without an empty domain or an assumption of the identification conclusion.

For general T91 inputs, countability and measurable singletons make the cells legitimate measurable events. Positive target-dose masses protect the conditional means used on positive covariate cells; the standardized sum explicitly suppresses null covariate cells. Identification equates its remaining terms to potential-outcome cell integrals, whose total absolute contribution is bounded by E|Y(d)| or E|Y(d′)|. The real infinite sum therefore does not rely on the nonsummability fallback. Supplied integrability and measurable bounded indicators keep the integral and conditional-expectation fallback conventions inactive.

There are no new totalization or nonvacuity problems in the revised disclosure. No package source files were changed during this review. The previous findings, report and blind reading were preserved. Python parsed findings2.json and verified its schema, all 19 target identities, unique theorem names, verdict counts, field types and correspondence with record2.json.
