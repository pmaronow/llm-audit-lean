# P011b delta referee report

**14 targets: 10 correct_whole, 4 correct_restricted, 0 adverse findings, 0 omissions.** All severities are `none`.

| Verdict | Count |
| --- | ---: |
| correct_whole | 10 |
| correct_restricted | 4 |
| restriction_inaccurate | 0 |
| not_faithful | 0 |
| vacuous | 0 |
| false | 0 |
| omission_ok | 0 |
| omission_questionable | 0 |

The revised architect decisions are **6 whole, 3 restricted, 5 refuted**. All are justified. The findings schema has no separate success verdict for a refutation: `correct_whole` means the full canonical counterexample is stated, while `correct_restricted` means a correct counterexample retains disclosed scope limitations. Thus T15 remains `correct_restricted` in `findings2.json` despite its valid `refuted` decision. T18, T20, T23 and T26 are `correct_whole` for their canonical counterexample targets. No finding certifies the false printed assertion itself.

## Disposition of earlier findings

My first `findings.json` reported no adverse issues. The accepted scope reductions in T15, T16, T19 and T24 have been retained, not repaired away. Their disclosures remain accurate. No previously reported defect is partly fixed or not fixed.

The architect report identifies two T18 objections from the other referee. **Both are fixed.** My earlier whole-coverage assessment overlooked the missing link between the numerical arithmetic identity and the partially repaired moment expression. The old `reading.md` accurately recorded only an arithmetic equality at this point; it did not identify an exported repaired-expression equality. The revised statement now supplies that link explicitly. This corrects my earlier assessment of the old version; the current whole-counterexample assessment is justified by the additions.

| Target | Earlier finding | Revised decision | Delta disposition |
| --- | --- | --- | --- |
| T15 | correct_restricted | refuted | Mathematical content and disclosed omissions retained; new refutation label valid. |
| T16 | correct_restricted | restricted | Scaling domain and complete omission list retained; no fix required. |
| T17 | correct_whole | whole | All moment-domain expansion clauses retained; no fix required. |
| T18 | correct_whole | refuted | Both subsequently identified gaps fixed: named repaired expression and its value/comparison now exported; docstring accurate. |
| T19 | correct_restricted | restricted | Positive-variance domain and all disclosed omissions retained; no fix required. |
| T20 | correct_whole | refuted | Full sign certificate and universal negation retained; new refutation label valid. |
| T21 | correct_whole | whole | Finite-moment domain, variance/correlation identities and path witness retained; no fix required. |
| T22 | correct_whole | whole | All graph/program correspondence clauses retained; no fix required. |
| T23 | correct_whole | refuted | Both witnesses and unique optimum retained; new refutation label valid. |
| T24 | correct_restricted | restricted | Only formal content (i) retained; every omitted clause remains disclosed. |
| T25 | correct_whole | whole | All five denominator-correction clauses retained; no fix required. |
| T26 | correct_whole | refuted | Three finite witnesses and positive-probability realization retained; new refutation label valid. |
| T27 | correct_whole | whole | Finite maximum, sharp oracle bound and all program clauses retained; no fix required. |
| T28 | correct_whole | whole | Both inequalities and sufficient cap-attainment equality retained; no fix required. |

## Actual mathematical delta: T18

Reading all ten revised definition parts and the Challenge against `reading.md` found one mathematical change: `cwBracketOnlyRepair` is added in `Defs/Part4.lean`, and `T18Statement` in `Defs/Part7.lean` adds

- `cwBracketOnlyRepair = -70`;
- `cwActualCovariance ≠ cwBracketOnlyRepair`.

The earlier T18 core and actual-covariance correspondence are retained. The other 13 theorem statements, including their hypotheses and the definitions governing their meaning, match the earlier reading. Challenge documentation changes for T15, T18, T20, T23 and T26 accompany their new refutation labels.

For the existing constant witness, write E for expectation, B for the weighted sample mean, F for the correctly weighted fourth-moment block, J for `printedBracket`, and P=E[Y0 Y1]E[Y2 Y3]. The new definition is

`cwBracketOnlyRepair = F - (J + (2*3*4*5 - 1)*P)`.

Expanding J shows that adding 119P changes exactly the leading bracket coefficient from 1 to 120. Its remaining fifteen terms retain their printed coefficients, including the fifth term missing theta_i. Removing the original outside factor 120 and making this leading-coefficient change is precisely the opening-bracket move in canonical T18(d). It does not silently make the other coefficient repair.

Under the Dirac law Y=(1,1,1,1), B=7/2, F=9/16, J=-775/16 and P=1. Thus the moved bracket is 1129/16, and its resulting expression is -70. The actual covariance is 0. The revised type explicitly states this value and disagreement, so the former numerical-link gap is fully fixed. The T18 docstring now describes conclusions actually exported, fixing the second objection as well.

`/home/ubuntu/sap/tools/sap-lean scratch/DeltaCheck.lean` passed with exit status 0 and no diagnostics; its output is preserved in `scratch/delta-lean.log`. It imports only `SAP.P011b.Defs`. It independently checks the generic coefficient transformation, the actual named definition, integrability of every real-valued Dirac moment, the value -70, genuine Mathlib covariance 0, their inequality, and projection of both new clauses from the revised statement. It uses no Challenge theorem or Solution proof.

The changed expression introduces no new premise. Its sample size is the fixed positive number four, its law has total mass one, and all its moments exist. The sample-mean denominator is four; there is no division by a zero variance, nonintegrable integral default, unbounded extremum, or empty index doing the work. Degeneracy is appropriate for refuting the claimed finite covariance identity, which does not assume Scaling or positive limiting variance.

## Revised labels and disclosures

All five refutation docstrings begin with `The printed claim is false:`. The counterexamples refute the actual printed readings:

- **T15:** The lower star family satisfies Scaling and valid graph constraints; the unique compatible graph is the oracle. Its scaled variance is 27/128, but its scaled raw estimator tends to 3/16, and the stated underestimation probability tends to one. This contradicts the printed maximal-estimator conservativeness assertion. The refutation uses that variance claim, so the disclosed clipped-coverage convention does not substitute a different assertion for the one refuted. Its regression, conditional-law, design and mean-offset omissions remain disclosed.
- **T18:** Actual covariance zero disagrees with the literal first printed expression 9/4 and literal final expansion 93009/16. The newly linked bracket-only expression also differs, while the fully corrected expression is zero.
- **T20:** For independent fair signs satisfying the standing assumptions, the exact strict inside-event probabilities tend to one. The statement explicitly negates the printed universal assertion that those probabilities tend to zero. The strict event, all three exact finite probabilities and the nonvacuous family certificate are retained.
- **T23:** The literal data-dependent nonzero-product rule chooses an infeasible triangle under degree-one caps, and loses a forced zero-coefficient edge in the second example. These are failures of the printed decision-variable rule, with a nonempty feasible optimization problem and unique optimum independently specified.
- **T26:** The supplied source-level helper formulas and the paper formulas give different exact values on the stated data. The first vector occurs with probability 1/27 in the admissible three-point family. This refutes the printed implementation assertion on the mathematical source-formula scope of the canonical target; it does not claim execution of the external package.

The six `whole` decisions still state every canonical clause: T17 has corrected weighted/raw moments and the constant-centering expansion on their respective existence domains; T21 has the variance identity, correlation bound, pointwise auxiliary bound and path example; T22 has the bijection, objective/degree/constraint correspondence, optimizer equivalence, value factor and variable count; T25 has all five helper-correction clauses; T27 has feasibility, finite attainment, sharp oracle domination and every program characterization, including T22; T28 has both bounds and the stated sufficient equality condition.

The three `restricted` decisions remain exact: T16 adds Scaling even to the finite identities and discloses its omitted mean/coefficient identities, raw criteria, corollary, estimator shifts/specializations and perturbation bound; T19 discloses its omitted factor-ratio identity, equal-mean specialization and insufficiency assertion on the canonical positive-variance domain; T24 discloses the omitted data tuple, homoskedasticity index, statistical/scope and typography clauses. T15 retains its fourth scope disclosure despite the refutation classification. All four restriction strings in `record2.json` match the Challenge docstrings exactly.

The unchanged nonvacuity instances in `findings.json` and `scratch/nonvacuity.md` remain applicable: both star laws are nonconstant probability laws; the independent-sign intercept family meets every T16 hypothesis and its conditional design bounds and meets T19 with common variance one at every size; the graph witnesses use three vertices and actual feasible edges; and all helper denominators are positive. No newly added hypothesis weakens any of these examples.

## Outstanding items

There are no current non-`correct_*` / non-`omission_ok` items, no requested fixes, and no omitted targets. The two T18 objections discussed in the architect report are fixed; zero are partly fixed or not fixed. `findings2.json` contains one object per canonical target and has been parsed and schema-checked with Python.
