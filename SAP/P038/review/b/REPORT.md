# P038 statement audit

One target and one theorem were audited. The independent verdict is **correct_whole** for `P038-T1` / `SAP.P038.T1`.

| Verdict | Count |
| --- | ---: |
| correct_whole | 1 |
| correct_restricted | 0 |
| restriction_inaccurate | 0 |
| not_faithful | 0 |
| vacuous | 0 |
| false | 0 |
| omission_ok | 0 |
| omission_questionable | 0 |

Severity counts: none 1, minor 0, major 0. No item requires correction.

`reading.md` was saved before opening `claims.json` or `record.json`. It expands every SAP definition, lists every quantified block and hypothesis, and distinguishes the unconditional count/rounding conclusions from the conditional exact-tail-set conclusions. `claim-stage.json` was saved before opening `record.json`; its `whole` verdict was unchanged at the record stage.

All four mathematical clauses of the canonical corrected claim are present in `Defs/Part1.lean:40-79`. The finite sets contain precisely the nonzero integer weeks in the stated windows, with ordinary real division and strict outside-threshold comparisons. The windows used for proportions are positive. The additional exact-0.04 equivalence and repeated rounding bounds are valid consequences, and add no restriction. Extending a finite positive family to a function on all integers changes no mathematical content. The last block's positivity on the 100-week window is already in the canonical setup. Window monotonicity concerns counts and follows from finite-set inclusion; it does not assert monotonicity of proportions.

The canonical mathematical statement expressly assumes count two in clause (i) and the exact set `{-14,7}` in clauses (iii)-(iv). The latter determines the smaller-window count; count two alone would not determine it. The theorem preserves this distinction. It neither claims to establish the plotted observations nor selects which published output reflects the final data. This conditional scope is part of the target itself. The definition and theorem docstrings disclose it accurately. The record's decision `whole`, with no restriction or omission, is therefore correct.

The [paper's Methods, Fig. 1 caption, and footnote 2](https://pmc.ncbi.nlm.nih.gov/articles/PMC4944447/) support the supplied context: surrounding Tuesdays form the empirical reference distribution, the caption counts points outside the two thresholds, and the footnote prints election-hours values 0.04 and 0.06 at the two relevant windows. The formalization follows the canonical target's explicit interpretation of the windows and tie rule.

Nonvacuity and arithmetic checks compiled successfully with `/home/ubuntu/sap/tools/sap-lean scratch/Check.lean` (exit 0, no diagnostic output). The file imports only `SAP.P038.Defs` and contains no proof holes. At `R=117/100`, take the positive values `r(-14)=1/2`, `r(7)=3/2`, and `r(w)=1` otherwise. Lean verifies the exact tail sets and both conventions' numerical values, the reference-set cardinalities, threshold-tie exclusion, and rounding intervals. It also verifies every integer count from 0 through 50 against all four exact-value/rounding equivalences. These checks establish that the hypotheses are jointly satisfiable and test the definitions without using the Challenge theorem's stub.

The remaining general reasoning is direct: filtering a nested sequence of finite reference sets preserves inclusion; restricting `{-14,7}` to the 12-week reference set leaves `{7}`; the two conventions then give `1/24`, `2/50`, `2/25`, and `3/51`. The spacing between consecutive possible ordinary 25-week proportions is `1/50`, so exactly the specified counts lie in each rounding interval. No false, vacuous, or undisclosed restricted assertion was found.
