# P009b delta review

All 17 revised targets are acceptable at their declared scope. **One substantive defect is fixed; none is partly fixed or remains unfixed.** There are no new statement, disclosure, nonvacuity, or labelling issues.

| `findings2.json` verdict | Count |
|---|---:|
| correct_whole | 8 |
| correct_restricted | 9 |
| restriction_inaccurate | 0 |
| not_faithful | 0 |
| vacuous | 0 |
| false | 0 |
| omission_ok | 0 |
| omission_questionable | 0 |
| **Total** | **17** |

The revised **record decisions** are separately **7 whole, 7 restricted, 3 refuted, 0 omitted**. All are justified. The requested JSON keeps the original verdict vocabulary: T19 is `correct_whole` because it covers the entire canonical counterexample, while its record decision is correctly `refuted`. T21 and T23 are `correct_restricted` because their refutations retain the explicitly disclosed exclusions. These JSON verdicts do not relabel any refutation as a `whole` record decision.

## Correction to my earlier T25 reading

The architect's account of the T25 defect is correct. My original `correct_whole` verdict was wrong for the old source. At `reading.md:33`, I read the old expression

```lean
(∑ r, estimates r-1)/(R:ℝ)
```

as an average of individual errors. Lean actually parses it as `((∑ r, estimates r) - 1) / R`. With every estimate equal to 1, it gives 1/2 at R=2 and 49999/50000 at R=50000. The R=1 sign-loss examples did not detect this mistake.

The revised `SAP/P009b/Defs/Part2.lean:82` explicitly uses `(∑ r, (estimates r - 1)) / (R : ℝ)`. This fixes the mathematical definition, not merely its description. The T25 docstring now gives the same formula. For positive R it equals the mean estimate minus 1; `reportedBias` is its absolute value. Thus the revised theorem covers both canonical formal-content clauses: the sample statistic and sign loss, and the full-interference population biases. My earlier audit files remain unchanged as the historical record; the current approval rests on the repaired source.

## Every earlier target finding

My earlier `findings.json` contained no open issue entries. The table rechecks all 17 target-level assessments, including the defect identified by the other referee and missed by me.

| Target | Earlier verdict | Revised decision | Recheck |
|---|---|---|---|
| T18 | correct_whole | whole | Retained; every count, zero-case, ratio, and bound clause remains present. No earlier repair requested. |
| T19 | correct_whole | refuted | Refutation label now correct; every counterexample fact remains present. |
| T20 | correct_restricted | restricted | Retained; all aggregate-chain and indicator-domain exclusions remain disclosed. |
| T21 | correct_restricted | refuted | Refutation label correct; aggregate-only scope and exclusion of convergence refutation remain disclosed. |
| T22 | correct_restricted | restricted | Retained; omitted covariance/regime clauses and added regularity/q ≥ 4 remain disclosed. |
| T23 | correct_restricted | refuted | Refutation label correct; integrability and all sampling-integral exclusions remain disclosed. |
| T24 | correct_restricted | restricted | Retained; the exact finite exception and empirical exclusions remain accurate. |
| T25 | correct_whole, erroneous for old source | whole | **Fixed**: per-replicate subtraction now matches the canonical statistic. No residual issue. |
| T26 | correct_restricted | restricted | Retained; supplied-exponent scope and omitted maximal-order/special-probability clauses remain disclosed. |
| T27 | correct_restricted | restricted | Retained; supplied-minimizer scope and omitted existence/exponential-limit/heavy-atom clauses remain disclosed. |
| T28 | correct_whole | whole | Retained; mean, finite centering, eventual distance, and sequence clauses are present. |
| T29 | correct_restricted | restricted | Retained; natural powers and the full numerical chain remain accurately described. |
| T30 | correct_whole | whole | Retained; both estimator identities and equality-or-zero characterizations are present. |
| T31 | correct_whole | whole | Retained; finite CDF and all-threshold convergence clauses are present. |
| T32 | correct_whole | whole | Retained; updates, flip specialization, both integer crossings, and opposite-flip identity are present. |
| T33 | correct_whole | whole | Retained; every corrected distinct-unit spillover, reciprocal-product, source-mean, and B1 clause is present. |
| T34 | correct_restricted | restricted | Retained; both first-moment links and the separate weighted proof chain remain explicitly excluded. |

Inspection of every revised Defs part against the saved reading found no further mathematical change. The substantive change is the shared T25 statistic. The other changed theorem descriptions are the refutation prefixes for T19, T21, and T23. Their mathematical propositions are unchanged. All nine non-null restriction texts, including those attached to the two partial refutations, still appear verbatim in their respective Challenge docstrings and accurately describe the actual omissions and additions.

## Refutations address the printed assertions

**T19:** The specified six-unit outcome schedule gives d_01=0, e_01=1, and witness count 3, with all individual witness and interference certificates retained. This contradicts the printed indicator-equals-count equality. It does not refute the final inequality of Lemma A7. Interference is defined on the full outcome cube and is independent of the assignment law; the same schedule can also be supplied with the paired law, so using a fair law to state the graph certificate does not evade the printed paired-design setting.

**T21:** The specified model gives B2=1/3 instead of the printed 2/3, and exact normalized expected gap −1/6 instead of −1/2. Its source baseline −1/4 is the paper's simplifying hypothesis for this illustration. The restriction correctly limits the refutation to exact evaluations, leaves out individual covariance certificates, and expressly does not refute the asymptotic convergence display. The revised false-claim prefix does not broaden that scope.

**T23:** The retained sampling integrals give signed bias −1 for both estimators and designs. At the included sample size n=100, squared bias is 1 while averaged design variance is 29/150 under complete randomization and 84151/515100 under paired randomization. These provide the complete-interference exception to the printed blanket negligibility claim. In this model each fixed-baseline design mean is zero and EATE is one, as also stated by the unchanged T24; consequently the joint sampling/assignment variance agrees with averaged design variance. That mathematical connection justifies the printed-reading refutation; a separate joint-space variance identity is not exported by T23, consistently with its restriction. The theorem does not contradict a result assuming restricted interference.

## Ordinary values, nonvacuity, and checks

T25's replication count is strictly positive in its universal caption clause. No division-by-zero value is used. The revised statistic is zero for R=2 and R=50000 with all estimates 1; constant estimates 0 and 2 have signed errors −1 and +1 for every positive R and equal reported magnitudes. The nonconstant array (0,2) at R=2 also gives zero error. Its unchanged population hypotheses have the concrete two-unit balanced-design instance from the earlier review.

The relabelled T19 and T21 assertions have no theorem hypotheses; their concrete finite normalized laws, nonempty index sets, and positive relevant conditional probabilities are unchanged. T23 retains positive even sizes, genuine complete and adjacent-rank paired designs, and explicit integrability of every one of its twelve sampling integrands. For example n=2 admits the constant swap pairing for every covariate vector and polynomial integrands on the bounded uniform support. Every positive even size, including n=100, admits a measurable sorted adjacent pairing and integrable bounded design quantities. Thus the refutation is not confined to an empty or unattainable hypothesis family. Per-target nonvacuity explanations are in `findings2.json`.

I independently compiled `scratch/DeltaCheck.lean` with `/home/ubuntu/sap/tools/sap-lean`; the final run exited successfully, with no diagnostics in `scratch/delta-check.log`. It imports only `SAP.P009b.Defs`. Definitional equalities verify both the old parse and the revised summand. The file also proves the general constant-estimate formulas and checks the R=2, R=50000, mixed-estimate, sign-loss, and mean-minus-one examples above. Symbolic finite-sum formulas avoid expanding a 50,000-element enumeration. No `lake` command was used, and at most one Lean process ran at a time.

The architect's claims about proof transports and fresh external certification were not treated as evidence of statement fidelity; no Bridge, Solution, or Comparator files were inspected. The revised decision/disclosure checks and Python validation confirm exactly one `findings2.json` object for each of the 17 canonical targets, unchanged theorem names, the original required schema and verdict values, and parseable JSON. There are no outstanding items requiring a statement or docstring fix.
