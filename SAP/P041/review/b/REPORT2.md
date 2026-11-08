# P041 revision 2 delta review

Both earlier findings are fixed. No new statement, restriction, label, junk-value or nonvacuity issue was found.

| Verdict | Count |
|---|---:|
| correct_whole | 5 |
| correct_restricted | 7 |
| restriction_inaccurate | 0 |
| not_faithful | 0 |
| vacuous | 0 |
| false | 0 |
| omission_ok | 1 |
| omission_questionable | 0 |
| **Total** | **13** |

Severity: 13 none, 0 minor, 0 major. Earlier findings: 2 fixed, 0 partly fixed, 0 not fixed. There are no remaining items outside `correct_*` or `omission_ok`.

## Earlier findings

**T12 — fixed; now correct_restricted.** The opening at `SAP/P041/Challenge/Part1.lean:69` no longer says “The printed claim is false.” The next line explicitly identifies the reference-risk reading of “k% more likely ... than” as `100(p_comparison/p_reference - 1)`. The restriction paragraph accurately distinguishes the retained negated conjunction from the omitted exact directional values and conjunction of three individual negations. The revised record uses the same wording. The theorem supports part of the canonical diagnosis and remains `restricted`; it is correctly not labelled `refuted`.

**T13 — fixed by the requested alternative remedy; now omission_ok.** The earlier finding allowed either adding a suitably credited restricted theorem or explicitly identifying the missing credit as the remaining provenance obstacle. `record2.json:169` and `architect-report.md` take the latter route. They recognize the canonical mathematical implication and its three estimands, identify T5/T6 as covering the related counterexample and sufficient condition, and stop claiming that the canonical target lacks a mathematical estimand. The supplied `claims.json` has `no_lean: true`; the revised record continues to show no T13 theorem and no credited rows.

This accepts an explicitly disclosed packaging omission. T13 has not gained a theorem, and its canonical content has not been removed, refuted as an empirical assertion, or declared unformalizable. The architect cites a no-Lean rule in an external brief; that brief is outside the permitted review files and was not opened. The visible metadata, accurate cross-references and adoption of the earlier alternative remedy suffice to resolve this review finding without claiming independent verification of that external rule.

## Statements and labels checked

All fourteen Defs parts, the Defs root, Challenge part and Challenge root were reread. Every expanded theorem proposition and supporting definition still agrees with the corresponding section of the saved `reading.md`; no mathematical change was found. The changed theorem documentation is T12's. Comparing the two supplied records finds only changes to the T12 restriction and T13 omission rationale. The twelve theorem names, statement-definition references, decisions and credited-row lists are preserved.

| Target | Current decision | Delta and scope assessment |
|---|---|---|
| T1 | whole | Unchanged; full explicit exponential countermodel, survival formulas, ratios, contrasts and four positive binomial masses. |
| T2 | restricted | Unchanged; rounding-rectangle bounds, central p bounds, pooled contrasts and existential common-bias model retained; listed finer numbers and cited-only/causal claims omitted. |
| T3 | whole | Unchanged; all three individual directional failures, repairs, symmetric values and general positive-domain gap identity retained. |
| T4 | whole | Unchanged; all corrected percentages, rounding tolerances, separate 76-count variant and symmetric alternative retained. |
| T5 | whole | Unchanged; six-order table, general balanced law, size-50 instance, zero direct effects, slow schedule and both boundary checks retained. |
| T6 | whole | Unchanged; general rank/own-treatment identity, fixed-calendar specialization and direct/planned/implemented protocol separation retained. |
| T7 | restricted | Unchanged; exact cell fit and HC1 arithmetic retained; reference-distribution tails, critical values and significance conclusions explicitly omitted. |
| T8 | restricted | Unchanged; coarse uniform Wald bounds, Gaussian tiers and nested-cutoff distinction retained; finer numerical and quantile conclusions explicitly omitted. |
| T9 | restricted | Unchanged; positive degrees of freedom and nonsingularity retained; conditional sufficient-statistic formulas and supplied survival arithmetic remain disclosed. |
| T10 | restricted | Unchanged; positive variance retained for the reciprocal-SE/Wald clause; predictor/hazard identities, reciprocal bounds and illustration retained. |
| T11 | restricted | Unchanged; P1 numerical content retained and P2 inference/counterexample/comparison omitted; no central living-group rounding to 0.70 asserted. |
| T12 | restricted | Documentation corrected; P1 and P3 plus only the negation of the directional conjunction are accurately disclosed. |
| T13 | omitted | Rationale corrected; canonical content acknowledged, related T5/T6 coverage identified, target-specific credit remains absent. |

The five `whole` labels continue to cover their complete canonical mathematical assertions as read in round 1; none was weakened. Every `restricted` record entry matches its Challenge restriction paragraph. There are zero `refuted` decisions, so no interpretation has been newly mislabelled as contradicting the canonical assertion. The assessment uses the canonical statements, definitions and standing assumptions, without allowing audit-history notes to change their scope.

## Junk values, nonvacuity and verification

The revised disclosure introduces no new quantifier, hypothesis, domain, operator or numerical convention. T12 remains unconditional finite arithmetic: its reference risks are 52/150, 69/150 and 32/100, and its symmetric denominators are (75+52)/2, (92+69)/2 and (62+32)/2. All are strictly positive. Its conjunction is true without zero-division conventions, empty types or inconsistent premises.

`/home/ubuntu/sap/tools/sap-lean scratch/DeltaCheck.lean` completed with exit code 0 against the revised Defs. It directly proves the entire current T12Statement by exact arithmetic, verifies those six strict positivity facts, and confirms that the balanced m=2 sample space contains six assignments. It imports only Defs, not Challenge. The independently proved T12 check has dependencies `propext`, `Classical.choice` and `Quot.sound`, with no `sorryAx`; output is saved in `scratch/DeltaCheck.log`.

The unchanged statements retain the round-1 witnesses and domain checks: positive q parameters and hazards; inhabited, positive rounding rectangles; nonempty balanced laws with m>=1; nonzero percentage denominators; full-rank study designs with positive HC1 degrees of freedom; and a positive-variance reciprocal-SE witness. The T13 explanation refers to the same nonempty m=2 scrutiny construction already audited, with implemented expectation 1/6 versus planned expectation 0 and zero direct effects. No new data extraction or empirical causal conclusion is inferred.

The checks did not read Solution, Bridge or external formalization sources, did not follow the architect's links outside this working directory, and did not run `lake`. Only one Lean process ran. `findings2.json` parses and contains exactly one object per canonical target with the required schema. The original reading and first-round findings are preserved.
