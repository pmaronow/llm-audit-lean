# P032 declaration review

Both declarations are faithful at their declared scope. No defects were found.

| Declaration | Against canonical claim | Recorded decision | Verdict | Severity |
| --- | --- | --- | --- | --- |
| SAP.P032.T8 | Narrower by exactly the disclosed two equalities | restricted | faithful | none |
| SAP.P032.T10 | Whole mathematical claim | whole | faithful | none |

T8 preserves the specified binary outcomes, logit fits, unadjusted cluster
components, completed-data decomposition values, five-imputation average, Rubin
term, pooled totals, negative discrepancy and inactive clipping. It omits exactly
the separate equalities with the two direct ordered-pair sums, as stated in
`SAP/P032/Challenge/Part1.lean:50` and `record.json:6`. This is an accurate
restriction. The component definitions include the correct nonincident singleton
clusters. Positive information, probabilities strictly between zero and one, and
five imputations exclude every relevant junk-value convention.

T10 includes all formal clauses (i)–(iv): unique bounded integer recovery using
the exact rational rounding tolerance, both threshold sets and counts, the
equality case, and every neighboring count and attained SER endpoint. All 22
printed inputs match the canonical data and the publisher's
[Supplementary Table A.2, p. A3](https://static.cambridge.org/content/id/urn:cambridge.org:id:article:S1047198723000268/resource/name/S1047198723000268sup001.pdf).
The natural-number witnesses encode precisely the nonnegative integer counts;
all denominators are positive. The docstring accurately describes this result.

The review followed the required order. `reading.md` was saved before opening
the claims; `claim-stage.json` was saved before opening the record. Every closure
entry was read, including generated proof declarations (78 distinct entries).
The record required no revision to the claim-stage judgments. Neither theorem
has external hypotheses, neither is a refutation-labelled claim, and neither
uses a placeholder or a definition that assumes its conclusion.

`scratch/Nonvacuity.lean` compiled successfully with
`/home/ubuntu/sap/tools/sap-lean scratch/Nonvacuity.lean`, with no diagnostics,
using only `SAP.P032.Defs`. It independently verifies the T8 witness and strict
pooling gap, plus T10's admissible witnesses and threshold sets.
`python3 scratch/ExactChecks.py` also passed: it checks both T8 direct sums and
exhaustively checks integer recovery and all counts for T10. Results are saved in
`scratch/exact-check-results.json`. Both required JSON output files were parsed
and checked for exactly the two requested declarations and matching fingerprints.
