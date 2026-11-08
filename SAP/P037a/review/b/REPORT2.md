Delta review: 15 targets; 8 correct whole, 5 correct restricted, and 2 justified omissions. The one adverse finding from my first review is fixed. There are no unresolved or new adverse findings.

| Verdict | Count |
| --- | ---: |
| `correct_whole` | 8 |
| `correct_restricted` | 5 |
| `restriction_inaccurate` | 0 |
| `not_faithful` | 0 |
| `vacuous` | 0 |
| `false` | 0 |
| `omission_ok` | 2 |
| `omission_questionable` | 0 |

| Earlier finding or revised passage | Status | Re-check |
| --- | --- | --- |
| My P037-T1 finding: missing interpretative scope | Fixed | The [revised T1 docstring](/home/ubuntu/sap/tasks/CHFID-P037a-b/SAP/P037a/Challenge/Part1.lean:7) explicitly challenges identification from randomization, an eligible-composition main effect and marginal average linearity alone. It says the witness violates the preferred qualified response restriction and preserves that model's separate interpretation. The omission of clause (v) remains explicit. |
| Other referee's P037-T12 scope finding, as reported by the architect | Fixed | The [revised T12 docstring](/home/ubuntu/sap/tasks/CHFID-P037a-b/SAP/P037a/Challenge/Part1.lean:58) identifies the exactly-64 reading challenged by its examples and correctly states that the literal upper bound remains true. |

I compared all nine current Defs parts, both root modules and the Challenge part with the mathematical expansion in `reading.md`. No change to a theorem's mathematical content was detected: objects, quantifiers, hypotheses, conclusions and shared definitions match the saved reading. The revised prose is confined to T1 and T12. Neither change adds a hypothesis or drops a conclusion. My original `reading.md`, `claim-stage.json`, `findings.json` and `REPORT.md` are preserved.

The revised T1 remains `restricted`: canonical clauses (i)–(iv), including the finite hierarchical law, both schedules, exact moments, unique expected-regression coefficients and mixture criterion, are retained; the repeated-block OLS limit (v) is omitted and disclosed. Its new scope sentences agree with the opening of the canonical statement. T12 remains `whole`: all five canonical clauses are present, including no ties, bounds, divisibility, monotonicity, endpoints, the three counts, the 521 threshold and five shares. Its corrected prose challenges an interpretation of the parenthesis rather than contradicting the canonical count assertion. Neither target warrants a `refuted` label or a false-printed-claim prefix.

`record2.json` equals the original `record.json` as parsed JSON. Its decisions remain appropriate: T1–T5 are restricted, T6–T13 are whole, and T14–T15 are omitted. T2–T5 still disclose the omitted conditional seed construction, Gaussian calculations and exponential/simplex construction clauses accurately, as detailed in `claim-stage.json`. The unchanged whole targets retain every canonical mathematical clause. T7 and T10 are whole because their canonical assertions already ask for counterexamples. T14's qualified empirical application and T15's actual significance status remain unsettled by the supplied formal statements, so both omissions remain justified. There are zero `refuted` decisions. The canonical statement, definitions_needed and standing assumptions govern these judgments; note and finite_lemmas supply no extra clauses or exemptions.

The changed docstrings introduce no new junk-value or nonvacuity problem. T1 still uses a genuine normalized law with 454 positive-mass states, a nonsingular expected Gram matrix and unequal causal/regression slopes. `scratch/DeltaCheck.lean` independently verifies that the displayed expected equations have no solution with composition coefficient zero, regardless of the nuisance coefficients. For T12 it verifies e(100)=40, e(200)=40 and e(375)=52, proves e(n)<=64 for every n<550, and checks the transition e(520)=60 to e(521)=64 and the endpoint e(550)=64. The interpolation branch still requires n>200, its divisor is 350, and every asserted share has a positive denominator. These checks support the new distinction between the two readings of the parenthesis.

Validation: `/home/ubuntu/sap/tools/sap-lean scratch/DeltaCheck.lean` and `/home/ubuntu/sap/tools/sap-lean scratch/Check.lean` both completed with exit code 0 and empty diagnostic logs (`scratch/delta-lean-check.log` and `scratch/nonvacuity2-lean-check.log`). The latter recompiles the earlier nonempty four-school row sequence, including uniform bounds and a strictly positive variance lower bound, against the refreshed Defs. These files import Defs and do not rely on the Challenge's sorry stubs. `findings2.json` was parsed with Python 3 and checked for the exact required fields, all 15 target IDs, the 13 current theorem names, allowed verdicts and consistent counts.
