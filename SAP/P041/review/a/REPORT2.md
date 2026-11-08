# P041 delta review

Thirteen targets: twelve included theorems and one omission.

| Verdict | Count |
| --- | ---: |
| correct_whole | 5 |
| correct_restricted | 7 |
| restriction_inaccurate | 0 |
| not_faithful | 0 |
| vacuous | 0 |
| false | 0 |
| omission_ok | 1 |
| omission_questionable | 0 |

All thirteen severities are `none`. No unresolved or new statement defect was found. My earlier adverse finding is **fixed**: 1 fixed, 0 partly fixed, 0 not fixed.

## Earlier finding: T12 fixed

The previous minor finding concerned the opening falsity label in the T12 docstring. The replacement at `SAP/P041/Challenge/Part1.lean:69` removes that opening. It now explicitly identifies the reference-risk interpretation of “k% more likely ... than” as `100(p_comparison/p_reference - 1)`.

The distinction is correct. Canonical T12 already asserts the correctness of P1's symmetric arithmetic and P3's directions and diagnoses the three directional assertions as false in P2. The Lean theorem asserts P1/P3 and only the negation of the conjunction of the directional rounding assertions. It therefore proves a restricted portion of the canonical diagnosis. The revised docstring and `record2.json` both disclose the omitted exact directional equalities and the omitted three individual negations. They do not claim the stronger conjunction of individual failures or any quoted Cox/inferential conclusion.

The decision remains `restricted`, as it should. A `refuted` decision would confuse this canonical diagnosis with the reading being refuted. The revised description fixes the entire earlier finding without changing the proposition.

## Delta inventory and decisions

I reread all fourteen Defs parts, both root modules and the Challenge part and compared their mathematical content with `reading.md`. The shared definitions and all twelve proposition bodies retain the previously read objects, quantifier order, hypotheses, constants and conclusions. No mathematical theorem statement changed. The Challenge change is the T12 documentation; the record changes are T12's restriction wording and T13's omission rationale. All theorem names and decision values are retained.

| Target | Current result | Delta assessment |
| --- | --- | --- |
| T1 | correct_whole | Unchanged exponential laws, common hazard ratios, exact contrasts and four positive binomial expressions. |
| T2 | correct_restricted | Unchanged; omitted cited-only/causal/mechanism content, finer central values and specified exact countermodel contrasts remain disclosed. |
| T3 | correct_whole | Unchanged; includes every individual directional failure, corrected and symmetric roundings, and the general/exact gap identities. |
| T4 | correct_whole | Unchanged; includes the corrected percentages, precision bounds, separate alternative-count calculation and symmetric repair. |
| T5 | correct_whole | Unchanged; includes the six full cases, general and size-50 results, direct/slow effects and both boundary checks. |
| T6 | correct_whole | Unchanged; includes the general own-rank/own-treatment identity and the distinct protocol effects. |
| T7 | correct_restricted | Unchanged; omitted normal/Student-t and significance conclusions remain disclosed. |
| T8 | correct_restricted | Unchanged; retained Gaussian tiers and omitted finer p/z/quantile content remain accurately distinguished. |
| T9 | correct_restricted | Unchanged; retains the disclosed k<n condition and conditional design-statistic formulas. |
| T10 | correct_restricted | Unchanged; positive variance remains required and disclosed. |
| T11 | correct_restricted | Unchanged P1-only scope, with P2 and the central living-p rounding assertion excluded as disclosed. |
| T12 | correct_restricted | Earlier finding fully fixed by the reading-specific description and accurate restriction. |
| T13 | omission_ok | Revised rationale accurately recognizes its canonical mathematical content and existing T5/T6 coverage. |

No target is now labelled `refuted`. T1, T3 and T5 correctly remain `whole`: their canonical claims are themselves the specified countermodels/refutations, rather than the assertions challenged by those constructions. No audit-history note or `finite_lemmas` was used to remove canonical clauses.

## T13's revised omission rationale

My original verdict was `omission_ok`, qualified by the fact that the canonical implication is mathematically meaningful and already addressed by T5 and T6. The new rationale adopts that distinction. It no longer presents the canonical target as lacking an estimand: it expressly identifies the implemented expectation, planned expectation and direct effect, and cites the countermodel and sufficient condition.

The visible provenance remains `no_lean: true` in `claims.json`, no T13 theorem, and no target-specific credited rows in the record. I retain `omission_ok` on that evidence and the existing T5/T6 coverage. The no-Lean flag is packaging metadata; it does not erase any clause of the canonical claim. The external architect-brief and `work.json` references were not inspected or treated as additional referee instructions. Nothing in this omission certifies the actual study estimates biased or unbiased.

## Junk values, nonvacuity and validation

There are no changed mathematical hypotheses or definitions to invalidate the earlier nonvacuity evidence. The positive rounding rectangles, nonempty balanced sample spaces, full-rank example designs, positive degrees-of-freedom guard and positive-variance guard remain intact. The earlier witnesses and independent arithmetic checks therefore continue to apply.

For the revised T12 description I also independently proved the entire current `T12Statement` with `norm_num` in `scratch/AuditDeltaT12.lean`, importing only the supplied Defs. The check uses no Challenge/Solution theorem, assumption or `sorry`. It additionally verifies strict positivity of the three reference risks 52/150, 69/150, 32/100 and group sizes 150 and 100. Thus neither zero division nor a vacuous premise supports the revised description.

`/home/ubuntu/sap/tools/sap-lean scratch/AuditDeltaT12.lean` completed with exit code 0. No `lake` command was run. The earlier broader numerical checks were not repeated because their mathematical inputs are unchanged. This is a statement review; the architect's claims about Solution/comparator validation were not used as evidence of statement fidelity.

`findings2.json` was parsed with Python and checked for one object per canonical target, the original schema and allowed verdict/severity values, and agreement of theorem names with `record2.json`. The declared restriction strings were checked against the revised Challenge docstrings.
