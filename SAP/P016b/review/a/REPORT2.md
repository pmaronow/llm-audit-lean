Delta review of all 10 targets against the saved blind `reading.md`, the supplied canonical claims, the revised Defs and Challenge files, `record2.json`, and `architect-report.md`.

| Verdict | Count |
| --- | ---: |
| correct_whole | 6 |
| correct_restricted | 3 |
| restriction_inaccurate | 1 |
| not_faithful | 0 |
| vacuous | 0 |
| false | 0 |
| omission_ok | 0 |
| omission_questionable | 0 |

The two earlier adverse findings resolve as **one fixed and one partly fixed**. One minor scope-description issue remains. I found no new mathematical problem.

| Target | Earlier finding | Resolution and revised verdict |
| --- | --- | --- |
| T12 | correct_restricted | Unchanged and acceptable; `correct_restricted`. The raw KS-value table remains the disclosed omission. |
| T13 | correct_restricted | Acceptable; `correct_restricted`. The revised wording correctly acknowledges that the complement characterization retains two-assignment fibers. The level and decimal omissions remain disclosed. |
| T14 | restriction_inaccurate | **Fixed**; `correct_whole`. The record is now whole with restriction null, and the docstring correctly describes positivity as inherited from T12(iii). |
| T15 | correct_whole | Unchanged and acceptable; `correct_whole`. |
| T16 | correct_restricted | Unchanged and acceptable; `correct_restricted`. Both positive-size guards remain disclosed. |
| T17 | correct_whole | Unchanged and acceptable; `correct_whole`. |
| T18 | correct_whole | Unchanged and acceptable; `correct_whole`. |
| T19 | restriction_inaccurate | **Partly fixed**; `restriction_inaccurate`, minor. The domain description is fixed; the remaining empirical-scope justification does not resolve the earlier finding. |
| T20 | correct_whole | Unchanged and acceptable; `correct_whole`. |
| T21 | correct_whole | Unchanged and acceptable; `correct_whole`. |

**Remaining issue: P016-T19, minor.** The revised docstring at `SAP/P016b/Challenge/Part1.lean:65` correctly treats positive half-size and the nonzero multiplier as existing mathematical domain conditions. It also now distinguishes recommendations to recompute powers or change the calibration objective. Those parts of the earlier finding are fixed.

The record still calls the target restricted because of empirical powers, their ordering, and the data-specific approximation `1.035312` in the quoted repair. However, the supplied canonical claim follows that quotation with an explicit “Mathematical content, with every hypothesis” block consisting of (a)–(f), all of which are formalized. Its note expressly says the simulated-data powers and mean-shift comparison “are not a target”. That remains the basis of the original reading.

The new justification in `record2.json` and `architect-report.md:147` invokes a brief rule giving the quoted statement precedence over diagnostic notes. **The supplied `brief.md` contains no such rule.** Its line 30 describes the `claim-stage.json` schema. The architect cites a brief in another workspace; that file is outside the permitted reading scope and was not accessed. The revision account does not establish a governing instruction or a canonical misreading that would overturn this finding. The issue is the scope label and its justification, not the truth of the Lean theorem.

Fix T19 by marking it `whole`, setting its restriction to null, and retaining the corrected explanation of the positive-half-size and nonzero-multiplier domains. Its docstring should describe the canonical exclusion of empirical material without presenting that exclusion as a loss of mathematical target content. Remove the unsupported precedence-rule justification from the account. Exact replacement text is in `findings2.json`.

The comparison with `reading.md` found **no changed mathematical statement**: all ten theorem types, quantifier orders, hypotheses, conclusions, and the SAP definitions they use retain the saved mathematical readings. The substantive revision is to the T13, T14 and T19 documentation and scope metadata. All six targets labelled whole were rechecked for their canonical clauses. No target is now labelled refuted or omitted; the existing counterexample targets still assert their canonical counterexamples.

The guards also remain intact. In T13, positive B and M=6435 protect probability denominators, the cutoff conditions prevent truncated exponents from changing the binomial formula, and the balanced finite design is nonempty. In T14 the probability-measure premise prevents infinite-measure real conversion, corrected tails divide by B+1, and the exact-law normalization rules out an empty probability space. In T19, m>0 and exactly m treated units make both central median indices valid and the treated discrepancy set nonempty, finite and bounded below; inverse comparisons have a nonzero multiplier, roots require a nonzero treated outcome, and the matching formula guards its denominator. No revised wording introduces a junk-value interpretation or a circular premise.

`/home/ubuntu/sap/tools/sap-lean scratch/RefereeChecks.lean` was run against the refreshed definitions and completed successfully. It checks nonempty groups, nonempty balanced designs, positive uniform weights, the explicit KS decreases, exchangeability of a concrete probability law, admissible network multipliers, and a nonempty bounded treated-discrepancy set. A uniformly random permutation of 0,...,B supplies the separate tie-free exchangeable instance. The prior exact enumeration and outward-rounded probability evidence remains applicable to the unchanged formulas and witness data; those computations were not needlessly repeated. Nonvacuity instances for every target are retained in `findings2.json`.

`findings2.json` parses, has exactly the required fields, and covers each canonical target once. The original reading and first-round output files, the supplied Lean sources, and both architect records were preserved.
