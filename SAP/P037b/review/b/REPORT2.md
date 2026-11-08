# P037b — delta statement review

Reviewed all 15 targets, the revised Challenge, all three Defs parts,
`record2.json`, and `architect-report.md` against the saved `reading.md`,
`claim-stage.json`, and first-round findings.

| Verdict | Count |
| --- | ---: |
| correct_whole | 2 |
| correct_restricted | 11 |
| restriction_inaccurate | 0 |
| not_faithful | 0 |
| vacuous | 0 |
| false | 0 |
| omission_ok | 2 |
| omission_questionable | 0 |
| **Total** | **15** |

Severity: 15 none, 0 minor, 0 major. There are no outstanding findings.

## Earlier finding: fixed

The sole earlier issue was P037-T29's description of the omitted branch
assertions as “r=0/r≥1 error equalities.” It is **fully fixed** in
[Challenge/Part1.lean:50](/home/ubuntu/sap/tasks/CHFID-P037b-b/SAP/P037b/Challenge/Part1.lean:50),
the parsed T29 restriction in `record2.json`, and `architect-report.md`.
They now distinguish the equality at r=0 from the stronger lower bound

\[
|r/10000-p|\ge 1/10000-p>p\quad(r\ge1),\qquad p=1/127008.
\]

This matches canonical T29(iii). The retained theorem still states the common
error floor and strict half-probability floor, while disclosing the omitted
branch assertions accurately. Its verdict is now `correct_restricted`.

Earlier issue dispositions: **1 fixed, 0 partly fixed, 0 not fixed**. No other
target had an earlier issue. The architect's account of this finding agrees
with the actual revised files.

## Statement and label comparison

Rereading every definition and all 13 `TxxStatement` propositions found no
change in their mathematical objects, quantifiers, hypotheses or conclusions
relative to `reading.md`. Each Challenge declaration still asserts the
corresponding proposition without extra hypotheses. The mathematical scope
judgments from `claim-stage.json` remain unchanged: 2 whole, 11 narrower.

A field comparison of `record.json` and `record2.json` found only the T29
restriction text changed. All 15 decisions and theorem mappings agree.
Every revised restricted docstring matches its parsed `record2.json`
restriction exactly. No target is labelled `refuted`.

| Targets | Revised assessment |
| --- | --- |
| T25 | Whole: both network certificates, indegrees, quantiles, fixed directed-graph referents, counts, probability vectors, positivity and different inverse weights remain present. The docstring explicitly compares the nomination and either-direction rows. This is the canonical ambiguity witness. |
| T30 | Whole: canonical (a)–(e) remain covered by the binomial law and moments, finite grid and error floor, precision and simultaneous bounds, positivity-screen consequences, and actual blocked-avoidance formula with all four examples. |
| T29 | Restricted: the mathematical content is unchanged and the sole inaccurate omission description is corrected. |
| T18, T19, T20, T21, T22, T23, T24, T26, T31, T32 | Restricted: the propositions and their disclosed retained conclusions and omissions agree with the first-round review. |
| T16, T17 | Omission remains justified for the empirical table/procedure and headline-effect assertions. No separate interpretation or arithmetic fact is substituted for the canonical empirical claim. |

The canonical `statement`, `definitions_needed`, and standing assumptions
govern these judgments. Audit-history notes and `finite_lemmas` supply no
additional clauses or exemptions. The counterexample labels remain relative
to their canonical witness claims; the revision adds no claim that an
unspecified printed interpretation is itself false.

## Well-definedness and nonvacuity

The only theorem documentation change is T29's restriction prose, so it
introduces no new hypotheses or operations. Its assignment type remains the
two school flags times four genuine five-of-ten subset spaces, with positive
mass `1/(2*252^4)`. All four exposure probabilities remain strictly between
zero and one, including the rare probability `1/127008`. Its 10000-draw
product law, positive denominators and error-grid interpretation are unchanged.

The earlier per-target nonvacuity instances are retained in `findings2.json`.
They include full-rank OLS designs with nonzero residuals, genuine integrable
Rademacher moments, a positive finite design with all four audited exposures,
supported seed lists, and nonempty actual blocked school supports. The
previously compiled `scratch/RefereeCheck.lean` and 39 finite checks remain
applicable because the relevant definitions and propositions match the saved
reading. No additional Lean checks were needed for the prose correction.

The review found no new reliance on singular inverse values, integrals of
nonintegrable functions, zero denominators, truncated subtraction, empty
index types or contradictory hypotheses. T19's zero-block extension remains
irrelevant to its limit at infinity; T30's sample-size and subset conditions
still protect its combinatorial probabilities.

`findings2.json` was parsed with Python and checked for its exact schema,
unique coverage of all 15 canonical targets, theorem mappings, verdicts and
agreement with these counts. The first-round artifacts were preserved.
