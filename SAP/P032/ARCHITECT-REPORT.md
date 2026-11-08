P032 packages all 12 targets for *Dyadic Clustering in International Relations*. Every listed Challenge has a proved Solution theorem; there are no open glue tasks.

| Decision | Count | Targets |
|---|---:|---|
| whole | 9 | T1, T2, T3, T4, T5, T6, T7, T10, T12 |
| restricted | 3 | T8, T9, T11 |
| refuted | 0 | None |
| omitted | 0 | None |

The restrictions are:

- **P032-T8:** Omits the separate equalities between the two completed-data decomposition values and direct ordered-pair covariance sums. It retains the specified data and closed-form logit fits, all components, both decomposition values, their five-imputation mean, Rubin terms, both pooled totals, the coefficient and negative gap, positivity, and inactive scalar clipping.
- **P032-T9:** Adds nonzero-denominator hypotheses for every `Gi i`, `GD`, and `n` in the asylike coefficient formula. This excludes division at zero. It retains the pooling identities, exact gap, DCR weight sum, unadjusted commutation, coefficient formula and nonzero example, and repair. The canonical fixed-sample, fixed-factor and common-estimate setting remains explicit in the definitions.
- **P032-T11:** Retains the unadjusted OLS residual matrix decomposition with full column rank, all occurring members, common residuals, and outsider-singleton member masks. It does not separately assert the equivalent pointwise coefficient identity, conventional multiway-cluster equivalence, software computability, square-root rule for standard errors, or eigenvalue clipping. This conservatively distinguishes the exported display from the additional mathematics quoted around it.

No targets are omitted. T5 establishes the canonical assertion that all four universal lower-bound readings fail: weak and strict population orderings, expected residual-variance ordering, and relative probability-limit ordering. Its decision is `whole`, and its docstring explicitly identifies these as the validators' readings of the quoted passages. The counterexample targets T1, T3 and T6 also establish their counterexample canonical claims, so their decisions are `whole`.

The definitions follow the single shared-module route: [Defs.lean](/home/ubuntu/sap/wt/ARCH-P032/SAP/P032/Defs.lean) imports nine Mathlib-only parts, and both sides import those compiled definitions. All scores, masks, covariance sums, finite distributions, fits and tables have SAP names. Observation-pair sums are ordered. The numerical data use zero-based labels; the table documentation identifies the four threshold studies.

The bridges are entirely structural or assembly glue:

- [Bridge/Part1.lean](/home/ubuntu/sap/wt/ARCH-P032/SAP/P032/Bridge/Part1.lean) converts the dyad and finite-distribution structures by preserving every field. The basic formula equalities are reflexive. Reverse dyad conversion transports the four universal assertions used in T5's refutation, without adding premises.
- [Bridge/Part2.lean](/home/ubuntu/sap/wt/ARCH-P032/SAP/P032/Bridge/Part2.lean) instantiates the existing intercept-fit certificate and simplifies the one-column contrast weights. It transports the existing replication formulas and limits. Limits use `m+1` blocks and ordinary filter composition, so every variance denominator is positive. The one-block six-edge expectation and its reversed ordering follow by arithmetic from the exported moments.
- [Bridge/Part3.lean](/home/ubuntu/sap/wt/ARCH-P032/SAP/P032/Bridge/Part3.lean) matches the survival-record and study-table projections by finite cases followed by reflexivity. Rewriting those correspondences transports the existing Cox fit, risk sets, scores, components and discrepancy, and the existing table-recovery and counting results. It does not recompute those results.
- [Solution.lean](/home/ubuntu/sap/wt/ARCH-P032/SAP/P032/Solution.lean) assembles the exported conclusions. Its remaining steps are specialization, conjunction, equality transport, interpretation of the existing coefficient identity, and elementary algebra or arithmetic on exported facts. Positive scalar covariances are fixed by clipping because their eigenvalue is the scalar itself.

T2 uses the arbitrary-probability-space OLS variance declaration with square-integrable centered errors. The reviewed `narrower` finite-support declaration is not substituted for it. The sign witnesses reuse the explicit bounded models from T1. T4's noncoincidence witness comes from T3, and T7's concrete matrix certificates come from T6; these cross-target dependencies are recorded separately in the manifest. Spectra in T1 are stated by explicit complete eigenbasis certificates, preserving the exact eigenvalues and multiplicities.

The canonical limit clauses in T1 and T5 are retained despite the conflicting `asymptotic=false` metadata. The statements follow those clauses rather than the diagnostic flag.

All Defs parts and root, Bridge parts and root, Challenge part and root, and Solution were compiled in dependency order with `/home/ubuntu/sap/tools/sap-lean`. [PrintAxioms.lean](/home/ubuntu/sap/wt/ARCH-P032/scratch/PrintAxioms.lean) imports only Solution and checks every theorem. Each report lists exactly `propext`, `Classical.choice`, and `Quot.sound`; see [axioms.log](/home/ubuntu/sap/wt/ARCH-P032/scratch/axioms.log). The [compile log](/home/ubuntu/sap/wt/ARCH-P032/scratch/compile.log) excludes the expected warnings about the required Challenge stubs.

[manifest.json](/home/ubuntu/sap/wt/ARCH-P032/SAP/P032/manifest.json) and [comparator.json](/home/ubuntu/sap/wt/ARCH-P032/SAP/P032/comparator.json) parse successfully. Each SAP file is within 300 lines. The Challenge and Solution theorem signatures match, and the source/import checks enforce the shared-definition boundary. Existing project files were not edited.

Full Comparator certification has not been run here: no Palomar Comparator, `con-ron`, or `nanoda_bin` executable was found on PATH. The configuration supplies the requested modules, all twelve theorem names, empty explicit definition list, permitted foundations, and external-kernel commands. Compilation and foundation checks are complete; external certification remains a runner step, with no open proof work.

The statements concern the canonical finite constructions and mathematical operations. They do not certify a Stata or R execution, a survival-model reanalysis, or the original empirical significance tests. The logit fit uses the canonical supplied closed-form formula. No assumptions or new mathematical proofs were taken from reviewers' suggested repairs.

## Revision 2: referee findings and responses

I checked both [referee A's findings](/home/ubuntu/sap/wt/ARCH-P032/referees/round1/a/findings.json) and [referee B's findings](/home/ubuntu/sap/wt/ARCH-P032/referees/round1/b/findings.json) against the canonical statements, definitions needed and standing assumptions. Both reports identify the same two T5 issues; I agree with both and have no disputed findings.

1. **T5 decision, raised by A and B:** Changed `refuted` to `whole`, keeping `restriction: null`. The [canonical statement](/home/ubuntu/sap/wt/ARCH-P032/work.json:1888) itself concludes “Each form is false: P032-T1.” The four negations in [T5Statement](/home/ubuntu/sap/wt/ARCH-P032/SAP/P032/Defs/Part7.lean:163) establish that assertion. This conclusion uses the canonical statement itself, not its historical note.
2. **T5 docstring scope, raised by A and B:** Replaced the blanket printed-claim verdict with an explicit description of the validators' four unrestricted readings: weak and strict population bounds, residual-estimator expectation bound, and relative probability-limit bound. The revised [docstring](/home/ubuntu/sap/wt/ARCH-P032/SAP/P032/Challenge/Part1.lean:30) says those readings fail. The [existing proof](/home/ubuntu/sap/wt/ARCH-P032/SAP/P032/Solution.lean:106) already proves exactly those four negations through structural transport; no proposition or proof changed.

The remaining findings in each report confirm the following statements and decisions. I retained them after checking their scope and disclosed restrictions:

| Target | A and B findings | Response |
|---|---|---|
| T1 | correct_whole | Retained all six model constructions, replication existence, finite formulas and both limits. |
| T2 | correct_whole | Retained the general square-integrable OLS comparison, sign equivalences, PSD criteria and sign witnesses. |
| T3 | correct_whole | Retained the complete Cox fit and both substitution discrepancies. |
| T4 | correct_whole | Retained the decomposition, exhaustive coefficients, subject-id discrepancies and scaling formula. |
| T6 | correct_whole | Retained the fitted OLS example, negative contrast and failed diagonal gate. |
| T7 | correct_whole | Retained clipping, fixed-point and gate criteria, and the concrete rank-one example. |
| T8 | correct_restricted | Retained the explicitly disclosed omission of the two direct ordered-pair equalities. |
| T9 | correct_restricted | Retained the explicitly disclosed nonzero count-denominator guards. |
| T10 | correct_whole | Retained unique numerator recovery, both thresholds and all neighboring counts. |
| T11 | correct_restricted | Retained the matrix decomposition and the full existing list of omitted assertions. |
| T12 | correct_whole | Retained the finite-variance identities and all strict and equality sign cases. |

The comparator configuration now lists the same twelve theorem names in numerical order. Its modules, shared-definition policy, permitted foundations and kernel commands are unchanged. Revision 2 recompiles all seventeen SAP Lean modules in dependency order and reruns all twelve foundation reports. [validation.json](/home/ubuntu/sap/wt/ARCH-P032/scratch/validation.json) records the checks, including identical theorem signatures on both sides and unchanged definitions and Solution proofs.

## Whole versions (new proofs)

- **P032-T9 (`SAP.P032.T9`):** Switched to `SAP.P032.T9WholeStatement` with decision `whole` and proof `SAP.P032.WH.W1.T9_whole`. The Challenge stub is in `SAP/P032/Challenge/Part1.lean`; the proof is used in `SAP/P032/Solution.lean`, and the updated decision and statement are recorded in `SAP/P032/manifest.json`. The whole statement is defined in `SAP/P032/Defs/WholeW1.lean`, assembled in `SAP/P032/WH/W1/Leaves.lean`, and exported by `SAP/P032/WH/W1/Proofs/T9.lean`. The four donor declarations used by the assembly are already recorded in `rows_used`.
  Removed restriction: “In the asylike coefficient formula, additionally requires every member-cluster denominator Gi i, the repeated-dyad denominator GD, and the record-count denominator n to be nonzero. These guards exclude totalized division at zero; the other canonical clauses are retained.” This supersedes the T9 restriction recorded above; all other targets retain their existing statements, proofs, and decisions.
