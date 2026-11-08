Delta review: the one earlier adverse finding is **fixed**. No new problem was found in the revised package.

| Verdict | Count |
| --- | ---: |
| correct_whole | 1 |
| correct_restricted | 9 |
| restriction_inaccurate | 0 |
| not_faithful | 0 |
| vacuous | 0 |
| false | 0 |
| omission_ok | 1 |
| omission_questionable | 0 |

All 11 targets have severity `none`. Earlier adverse findings: fixed 1; partly fixed 0; not fixed 0. There are no remaining items requiring a fix.

**P027-T10: fixed.** The [revised restriction docstring](/home/ubuntu/sap/tasks/CHFID-P027a-a/SAP/P027a/Challenge/Part1.lean:84) now states that the continuous uniform-start measure on `[0,8)` and its induced four-atom sampling law are not identified explicitly. The T10 restriction in `record2.json` makes the same disclosure. This is exactly the missing distinction identified in the first review: the sampling-start law is separate from the size and outcome generators. The statement remains the correct finite witness described by [Random8Witness](/home/ubuntu/sap/tasks/CHFID-P027a-a/SAP/P027a/Defs/Part7.lean:72). Its verdict changes from `restriction_inaccurate` to `correct_restricted`; its mathematical content has not been enlarged.

I compared every revised Defs part and every theorem type with the saved [blind reading](/home/ubuntu/sap/tasks/CHFID-P027a-a/reading.md). No change in mathematical objects, quantifiers, hypotheses or conclusions was found. All ten theorem signatures and all eleven decisions are unchanged. The only changed record field is T10's restriction text. The corresponding Challenge change adds that disclosure; the other docstrings retain their previous scope. The architect's account of the earlier finding is accurate. I did not infer unchanged definitions merely from the architect's report, and did not inspect Solution or Comparator proofs.

| Target | Delta-review outcome |
| --- | --- |
| P027-T1 | Correctly restricted; unchanged finite witness and family, with the omitted measure identification, expansions and nonvanishing assertions still disclosed. |
| P027-T2 | Correctly restricted; unchanged uniform-start law, finite bias identities, moment formulas and calibrated limit, with added integrability and omitted calibration/conclusion clauses disclosed. |
| P027-T3 | Correctly restricted; both finite bias-increase witnesses retained, with omitted enumerations and moments disclosed. |
| P027-T4 | Correctly restricted; preservation on positive-weight atoms remains separate from the exact-fiber bias formulas, as disclosed. |
| P027-T5 | Correctly restricted; numerical incompatibility and the 120-unit witness retained, without claiming the omitted population/collection interpretation or implementation provenance. |
| P027-T6 | Correctly restricted; finite correction comparisons and the outcome-averaged ratio retained, with the continuous-start, mean-scale and provenance omissions disclosed. |
| P027-T9 | Omission remains acceptable. The formal reading overlaps T5/T6; the stronger implementation assertion remains uncertified without the simulation populations or code. |
| P027-T10 | Earlier finding fixed; now correctly restricted. |
| P027-T11 | Correctly restricted; conditional sampling variance is averaged over errors, with the integrability additions and omitted realized-population comparison disclosed. |
| P027-T12 | Correctly whole; all four canonical clauses remain represented. |
| P027-T13 | Correctly restricted; necessity, capped probabilities, the guarded systematic construction and repaired finite law retained, with omissions and added indicator integrability disclosed. |

T12's `whole` decision was rechecked against the canonical statement and definitions: the eight-unit printed probabilities and their excess, impossibility for an indicator sampling design, the specified normalized negative-binomial product law with finite moments and positive witness mass, and all six floor-based configuration witnesses remain asserted. Finite design atoms faithfully represent laws on subsets of a finite population. No audit-history note was used to remove a canonical clause.

There are no `refuted` decisions. The counterexample targets state their own canonical counterexamples or disclosed portions of them. T5's docstring identifies the after-totalling interpretation of the table, and does not claim that the printed passage itself is false. T9 is still omitted. These labels comply with the distinction between a canonical assertion and an interpretation of printed guidance.

No mathematical statement changed, so the prior nonvacuity and total-function checks continue to apply. T10 still has four positive weights, strictly positive marginal probabilities, population-size divisor 64, and no outcome integral; the disclosure adds no hypothesis. Its exact values remain `A=-16`, total variance `256/3`, expected HT variance estimator `208/3`, expected C2 estimator `352/3`, and mean-scale bias `-1/4`. The open-box upper bound remains `-16 + 48(2/8 + 1/64) = -13/4`. The other guards on divisions, finite moments, normalized measures, integrability and positive parameters are unchanged. No new empty-index, truncated-subtraction or totalized-integral issue was found.

Validation against the refreshed Defs: `/home/ubuntu/sap/tools/sap-lean scratch/Check.lean` completed successfully. It rechecks the positive finite designs, aggregation antecedent, moment-model and calibrated instances, and general integrability of systematic indicators. Its output is [round2-nonvacuity.log](/home/ubuntu/sap/tasks/CHFID-P027a-a/scratch/round2-nonvacuity.log). The unchanged exact-arithmetic evidence from the first round remains in [finite-audit.json](/home/ubuntu/sap/tasks/CHFID-P027a-a/scratch/finite-audit.json). Mechanical checks verify target/theorem coverage, all revised restrictions against their docstrings, the unchanged decisions and theorem signatures, and the absence of a `refuted` label; current source hashes are recorded in [delta-review.json](/home/ubuntu/sap/tasks/CHFID-P027a-a/scratch/delta-review.json). Both findings JSON files parse, and the original blind-reading SHA256 remains `8526bb53bc83cfc47a153b9c0473e29cb93350fc016109e8a365b4458f6ee336`.
