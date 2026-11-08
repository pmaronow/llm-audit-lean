# Palomar statement referee report: P012a

Audited all 12 targets in `claims.json`, in the required order. The blind
mathematical reading was saved in [reading.md](reading.md), and the claim
comparison in [claim-stage.json](claim-stage.json), before opening `record.json`.
No step-2 verdict changed after reading the record.

| Verdict | Count |
|---|---:|
| correct_whole | 3 |
| correct_restricted | 9 |
| restriction_inaccurate | 0 |
| not_faithful | 0 |
| vacuous | 0 |
| false | 0 |
| omission_ok | 0 |
| omission_questionable | 0 |
| **Total** | **12** |

Severity counts: none 12; minor 0; major 0.

There are no items outside `correct_*` or `omission_ok`, and no fixes are
required. No target was omitted.

## Decisions and restrictions

| Target | Verdict | What is retained or disclosed |
|---|---|---|
| P012-T1 | correct_restricted | All four counterexamples and both fresh-trait choices are retained; exhaustive execution and detailed failure-mode descriptions, and dyad uniqueness, are disclosed omissions. |
| P012-T2 | correct_restricted | Preservation covers every execution of both corrected mechanisms; detailed intermediate branch and cleanup characterizations are disclosed omissions. |
| P012-T3 | correct_restricted | The compatible leaf witness, counts, quotient, both uniform bounds, integer equality cases, three violations and gaps remain; the polynomial certificate and separate denominator-positivity/leaf-degree assertions are disclosed omissions. |
| P012-T4 | correct_whole | Both lower-endpoint bounds, all numerical gaps, and the degree-discrepancy converse are covered, including rounding to four decimals. |
| P012-T5 | correct_restricted | The attained exact lower endpoint and its full stated domain remain; the assertion about information absent from the published paper is disclosed as omitted. |
| P012-T6 | correct_restricted | All sharp homophily bounds, attainment and denominator conditions remain; the one-pass computation claim is disclosed as omitted. |
| P012-T7 | correct_restricted | Susceptible-neighbour decomposition, fraction bounds, sharp preferential bounds and attainment remain; the one-pass computation claim is disclosed as omitted. |
| P012-T8 | correct_whole | The exact permitted starting graph produces the specified incompatible triangle and unchanged induced graph, refuting the proof step. |
| P012-T9 | correct_restricted | Existing cross edges, incompatible output and full degree/edge counts remain; the common-denominator assertion is disclosed as omitted. |
| P012-T10 | correct_restricted | Distinct compatible augmented and induced graphs and their shared-neighbour move remain; the fully specified private-leaf construction and its extra properties are disclosed as omitted. |
| P012-T11 | correct_restricted | Nonidentification, arbitrary other unsampled traits, the swap invariants, positive denominator formulas, both forms of (A1), and the exact instance remain; the separate supporting degree inequalities are disclosed as omitted. |
| P012-T12 | correct_whole | The two-recruit example gives the complete functional difference -5/12, different from both printed single-recruit expressions. |

The nine recorded restriction strings occur verbatim in their theorem
docstrings. Their contents accurately account for the missing assertions.
The three whole decisions agree with the blind comparison. Unused supporting
proof rows in the record are not omitted targets.

## Domain and truth checks

The definitions represent the supplied finite simple augmented graphs,
recruitment order, compatibility and functionals faithfully. Admissibility
prevents truncated spare-degree subtraction from changing a claimed value.
The option-valued functionals exclude their undefined cases. The susceptible
sets use the required just-before-time convention. Attained least/greatest
values encode the smallest containing interval; no assertion of a continuum
of attainable values is being substituted for Definition 4. No extra
hypothesis assumes the conclusion, and no empty index set establishes the
retained identification results.

Nonvacuity evidence is given separately for every target in
[findings.json](findings.json). In particular, the 527-subject hypotheses have
an explicit recruitment-forest and degree-vector instance. T4's converse
also has an explicit instance with actual lower endpoint -539551/767814,
within the specified rounding tolerance of -0.7027; its antecedent is
satisfiable despite its incompatible nomination graph.

The definitions-only Lean checks in [scratch/Check.lean](scratch/Check.lean)
compiled successfully with the authorized `sap-lean` command. They verify
actual compatible states and proposal inputs without importing Challenge
stubs. [scratch/ExactChecks.py](scratch/ExactChecks.py) passed all fixed
witness checks using exact integers and fractions, both large nonvacuity
fixtures, all 136503 integer edge-count triples, and all numerical gaps.
Detailed mathematical checks for the general statements and the recorded
restrictions are in [audit-notes.md](audit-notes.md).

The supplied source transcriptions were cross-checked against the
[published article](https://academic.oup.com/aje/article/187/1/153/3865631)
and its [official Web Appendix](https://oup.silverchair-cdn.com/oup/backfile/Content_public/Journal/aje/187/1/10.1093_aje_kwx208/6/kwx208supplement.pdf),
including the placement of line 22 and the cleanup and trait-choice rules.
The audit concerns these statements; it does not infer the unavailable
empirical code or data from the paper's printed pseudocode.
