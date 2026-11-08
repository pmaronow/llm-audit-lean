# Delta referee report

15 targets reviewed: 13 theorem stubs and 2 omissions.

| Verdict | Count |
|---|---:|
| correct_whole | 2 |
| correct_restricted | 11 |
| restriction_inaccurate | 0 |
| not_faithful | 0 |
| vacuous | 0 |
| false | 0 |
| omission_ok | 2 |
| omission_questionable | 0 |

Earlier findings: **1 fixed, 0 partly fixed, 0 not fixed**. New findings: **0**. No outstanding minor or major issues.

The earlier P037-T29 finding is fixed. The restriction in `SAP/P037b/Challenge/Part1.lean:50` and `record2.json` now separately names the error equality for r=0 and the stronger bound |r/10000−p|≥1/10000−p>p for r≥1, where p=1/127008. This exactly implements the correction requested in `findings.json` and agrees with canonical T29(iii). The unchanged Lean statement asserts the common nonstrict error floor and the strict half-p floor; the revised prose correctly discloses the omitted stronger branch assertions. T29 is now `correct_restricted`.

Both referees' T29 entries described in `architect-report.md` concern this same wording issue, and the synchronized correction addresses both. The architect accepts the finding, and its account agrees with the inspected docstring and revised record.

Comparison of all current theorem statements and their supporting SAP definitions with `reading.md` found no mathematical change: no changed objects, hypotheses, quantifiers, conclusions, numerical constants, or probability conventions. The changed theorem documentation is confined to T29. A structural comparison of `record.json` and `record2.json` found only the T29 restriction-text change; no target decision, theorem name, or credited-row list changed. All 11 revised restrictions match their actual Challenge docstrings.

| Targets | Delta and current assessment |
|---|---|
| T16, T17 | Remain omitted; the earlier omission judgments stand. The full empirical/procedural assertions are not established by the supplied formal objects. |
| T18, T19, T20, T21, T22 | Mathematical statements and disclosed restrictions match the blind reading; remain correct_restricted. |
| T23, T24, T26 | Mathematical statements and disclosed restrictions match the blind reading; remain correct_restricted. |
| T29 | Restriction wording fixed; mathematical statement unchanged; correct_restricted. |
| T31, T32 | Mathematical statements and disclosed restrictions match the blind reading; remain correct_restricted. |
| T25 | Remains correct_whole: both concrete network certificates, labels, probabilities, positivity and reciprocal-weight differences are represented. Its comparison is between nomination and either-direction rows, as its docstring says; it does not declare the ambiguous printed sentence false. |
| T30 | Remains correct_whole: canonical (a)–(e) are represented by the binomial law, moments, frequency grid/error floor, precision and simultaneous bounds, positivity-screen consequences, blocked-avoidance formula and all four examples. |

There are no `refuted` decisions in `record2.json`. The two whole labels are relative to the canonical assertions, not to stronger interpretations supplied by audit-history notes. The eleven restricted labels retain the same accurately disclosed omissions, with T29's disclosure now corrected. Neither `note` nor `finite_lemmas` was used to add or remove a canonical clause.

The wording revision creates no new undefined quantity or nonvacuity obligation. In particular, T29 still uses the actual finite four-block assignment space with positive masses, normalized total mass, p=1/127008>0 and fixed positive simulation size 10000. A concrete rare state selects {5,6,7,8,9} in each block with treatment=true. The previous denominator, integrability, full-rank, natural-subtraction and nonempty-screen checks remain applicable to the unchanged statements; per-target instances and reasons are retained in `findings2.json`.

The command `/home/ubuntu/sap/tools/sap-lean scratch/Check.lean` was rerun against the refreshed compiled Defs and completed with exit code 0 and no warnings or errors. It imports only `SAP.P037b.Defs` and checks the nondegenerate multiplier moments, full-rank regression designs, nonempty analysis population, supported seed sets and positive kept-group denominators. Round-1 exact enumeration evidence is preserved in `scratch/finite-checks.json`; unchanged formulas did not require a new enumeration. The original `reading.md`, `claim-stage.json`, `findings.json` and `REPORT.md` were preserved.

`findings2.json` contains exactly one object per canonical target and has been parsed and schema-checked with Python.
