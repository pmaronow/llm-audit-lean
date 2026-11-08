P023 packages “A Note on Close Elections and Regression Analysis of the Party Incumbency Advantage” (2014), DOI 10.1515/spp-2014-0003.

The decisions are **10 whole, 1 restricted, 1 refuted, 0 omitted**. All 12 Challenge theorems have Solution proofs; there are no open glue tasks.

| Target | Decision | Content |
| --- | --- | --- |
| P023-T1 | whole | All six-election linear-witness assertions, explicit window and difference of close outcomes, and localization of RD and coarsened coefficients. |
| P023-T2 | whole | All sixteen-election degree-seven witness assertions, including every nonzero weight, explicit window, and close-outcome difference. |
| P023-T3 | whole | Complete finite weights, localization, moments, nonlocality, population illustrations, fixed-tolerance probability bound and shared consistency. |
| P023-T4 | whole | Complete uniform clipped-linear family, fixed-degree and RD sampling limits, residual formulas and finite or infinite predictor-risk comparisons. |
| P023-T5 | whole | Complete clustered-density family, moments and coefficients, vanishing zero-polynomial approximation error, and all measurable-predictor risk comparisons. |
| P023-T6 | whole | Fixed uniform law, sharp logarithmic amplification and norm, one fixed continuous mean, increasing-degree divergence, zero RD limit, and universal exclusion of Lipschitz functions with the prescribed growing bias. |
| P023-T7 | whole | Population and finite residual identities, both bias bounds and tolerance criteria, exact specification, and uniform constants. |
| P023-T8 | whole | Complete corrected Proposition 2, including all population, fixed-degree, RD and growing-degree conclusions without additional sample-admissibility premises. |
| P023-T9 | whole | Corrected pair-indexed partition, demeaning, positive denominator, and localized FWL ratio. |
| P023-T10 | refuted | Negation of universal localization for positive-degree polynomial vote-share controls, together with valid coarsened localization. |
| P023-T11 | restricted | Positive party counts and Proposition 1 equality under Conditions 1–3; omits the printed necessity remark about Condition 1. |
| P023-T12 | whole | Complete refutation of the adopted fixed-law, all-sufficiently-large-fixed-degrees reading of Proposition 2; no unconditional verdict on its undefined printed guidance. |

The current snapshot includes the whole-version statements and proofs listed below, which were already present at the start of round 4. Round 4 changed four explanatory docstrings; round 5 updates T11's two docstrings and coverage label. Every mathematical declaration and proof is preserved. Shared Mathlib-only definitions include `Defs/WholeW1.lean` as well as the earlier Defs parts. The Solution imports the existing whole proof modules. All 21 current SAP Lean modules, including the supplied W2 files, are rebuilt in dependency order, followed by the twelve-theorem dependency audit.

## Earlier packaging notes (historical)

The following notes record the earlier restricted snapshot. The current table above and the existing whole-version section below supersede those restrictions.

P023-T3 omits the separate fixed-tolerance probability inequality of clause (f). Its credited shared-consistency row exports the limiting implication. Although the source module has a supporting inequality, that inequality is not one of the credited rows, so it is not promoted into the Challenge. Positive winner and loser counts in the close window are additionally required for the nonlocality component, so its RD comparison has two existing means. The shared-consistency component also requires a probability law, degree at least one, positive bandwidths, and vanishing probabilities of singular polynomial designs and empty RD sides. All other mathematical components (a)–(e) and the shared-consistency implication are retained.

P023-T4 adds vanishing probabilities of singular sample designs at degrees one and seven, and of an empty winner or loser RD window, to its sampling component. Prediction-risk comparisons also require measurable predictors with integrable squared error. All population conclusions are retained under those guards: the statement includes both residual variances, symmetry and formulas, all coefficient and RD formulas and limits, the predictor's membership in the regression span, exact risks and risk improvements, the numerical relative improvement bound, and the limit of the improvement bound.

P023-T5 restricts the prediction-risk comparisons to measurable predictors with integrable squared error. This excludes the junk real-integral value of a predictor with undefined finite risk; no statement about arbitrary non-integrable predictors is included. The rest of the witness and family clauses are retained in full.

P023-T8 adds vanishing probabilities of empty RD sides and singular sample designs at every fixed degree and every growing-degree schedule satisfying the stated rate. No conclusion (a)–(g) is dropped; existence of admissible degree schedules remains a conclusion. The new guards are explicit assumptions, not additional results claimed from the credited rows.

P023-T11 retains the sufficient-conditions equality in full and omits the auxiliary statement in the canonical definitions that Condition 1 is necessary for an RD estimate to exist. The printed half-open window can contain one winner and one loser without a strictly interior positive-margin observation. The theorem does not claim necessity.

There are no omitted targets. P023-T1, T2, T4, T5 and T6 are canonical counterexample assertions, so proving those witnesses is not classified as refuting their canonical claims. P023-T10 refutes the positive printed data-localization assertion, and its docstring begins with the required false-claim wording. P023-T12 completely refutes the adopted fixed-law reading specified in the canonical definitions. Its `whole` label records complete coverage of that interpretation-specific refutation; the docstring makes no unconditional declaration that the undefined printed guidance is false.

The definition route uses only ordinary Mathlib objects and shared declarations under `SAP.P023`. All data and statement definitions are compiled once in `Defs/Part1.lean` through `Defs/Part6.lean`. Challenge parts import only `SAP.P023.Defs`; the Solution imports the Defs and Bridge roots. No project declaration is recreated under its original fully qualified name.

The bridges need no structure adapters. Finite designs, normal equations, epsilon-selected coefficients and projections, bin relations, probability laws, integrals, sample functions, and regularity predicates have the same bodies as their project counterparts. Direct applications in `Bridge.lean` check these correspondences by definitional equality, including proof irrelevance for finite-index bounds. The four guarded components introduce the extra hypotheses and apply the original theorem. The revised T10 bridge instantiates its universal at degree one and extracts the existing linear witness's sign, bandwidth, full-rank, exact-model, bounded-outcome and nonlocality assertions; no new regression proof is added. The continuity bridge only transports the existing witness: its coefficient-growth clause follows from its exported FWL equality, and its unbounded-tail clause follows by selecting a sufficiently late term of its exported diverging subsequence. Continuity of the shifted mean follows by adding a constant. The additional T6 universal non-Lipschitz clause is transported directly from the existing generic helper `tc11_growing_bias_not_lipschitz`; no analytic argument is recreated.

Existing rows credited elsewhere in this same unit are used explicitly where needed. T1 and T3 use T10's coarsened-localization row. T4 uses T3's identical uniform-law result for both residual variances. T7 uses T3's `corrected_finite_polynomial_weights` row to supply the residual treatment-moment equality and arbitrary-outcome FWL identity missing from T7's own finite-bias row. Thus the finite-sample coverage gap recorded for T7 is filled by an already credited declaration, without a new mathematical argument. T10 now uses T1's complete degree-one counterexample rather than the original broader negation whose degree range includes zero. These cross-target uses appear in the manifest.

The Solution adds only conjunction, instantiation, definitional transport, finite-sum substitution for agreement on the close window, exact arithmetic on the explicit witness data, and one-line algebra for the simple predictor and vanishing improvement scales. It adds no statistical or approximation proof. The separate numerical and other supporting rows not needed independently are listed with reasons in the manifest.

The sample functions retain the source's extensions at empty windows or singular designs. For the positive sampling claims in T3, T4 and T8, `RDAdmissible` and `OLSAdmissible` explicitly require the probabilities of these exceptional branches to vanish. These guards implement the requested exclusion of nonexistent sample quantities in asymptotic interpretations; they are why those targets are restricted. The exact refutation T12 retains the selected universal printed reading, including its source's total sample conventions. Its existing proof contradicts the population-bias tolerance under a constructed uniform law and supplies the sampling premises; it does not obtain the contradiction from an empty window or singular design.

For finite RD assertions, positive counts are hypotheses or follow from Condition 1 and the two-party condition; the explicit witnesses have one close winner and one close loser. Demeaning queries only the bin containing an actual observation. Population RD windows have positive finite mass in their stated ranges under the uniform, positive-density clustered, or repaired locally dominated laws. Residual divisions use full-rank designs or positive definite population moments. Bounded conditional means, compactly supported probability laws, and explicit integrability premises keep the integrals and approximation extrema meaningful. Risk comparisons with arbitrary predictors require integrability of their squared errors. No causal interpretation or external-validity theorem is asserted.

Every SAP source has the two required implicit-variable options, and every package file is under 300 lines. Both JSON files parse, account for exactly the 12 assigned targets, and name the same 12 theorems as Challenge and Solution. All Lean modules were compiled in dependency order with `sap-lean`; the final dependency audit is `scratch/P023AxiomCheck.lean`. Each proved theorem uses exactly `propext`, `Classical.choice`, and `Quot.sound`.

The current Palomar configuration in `SAP/P023/comparator.json` lists the same twelve theorem names and kernel settings. The deposited [Comparator receipt](SAP/P023/verification/comparator-result.json), stamped `20261104T181805Z`, and [kernel log](SAP/P023/verification/comparator.log) record all-three-kernel acceptance of the supplied W2 mathematical statements. Round 5 changes documentation and the manifest coverage annotation only. The receipt is preserved; no fresh Comparator run is claimed for these changes. All 21 current modules are rebuilt and all twelve permitted-dependency checks are rerun.


## Round 1 referee findings and revision 2 responses

This section records the earlier review and revision 2 decisions. The current T11 and T12 classifications and the completed T6 scope are updated in the declaration-review sections below.

I checked both referees' findings against the canonical targets and the expanded definitions. [Referee A's findings](referees/round1/a/findings.json) approve all twelve statements; [Referee B's findings](referees/round1/b/findings.json) identify one major scope gap in T10 and approve the other eleven. The table records every target-level finding from each report. Here “full” denotes a referee's `correct_whole` coverage verdict; T10 and T12 remain classified `refuted`, as required for positive printed assertions that are disproved.

| Target | Referee A | Referee B | Response |
| --- | --- | --- | --- |
| P023-T1 | full | full | Retained the complete concrete witness, localization consequences, and `whole` decision. |
| P023-T2 | full | full | Retained the complete degree-seven witness, nonzero weights, and `whole` decision. |
| P023-T3 | restricted | restricted | Retained the documented probability-inequality omission and all count and sample guards. |
| P023-T4 | restricted | restricted | Retained the population clauses and disclosed sampling and finite-risk guards. |
| P023-T5 | restricted | restricted | Retained the complete family and the disclosed finite-risk predictor domain. |
| P023-T6 | full | full | Retained the logarithmic rate, fixed witness, explicit unbounded tails, RD limit, and failure of a Lipschitz bound. |
| P023-T7 | full | full | Retained every clause, including the finite FWL statements supplied by the credited T3 row. |
| P023-T8 | restricted | restricted | Retained all conclusions and the disclosed fixed- and growing-degree sample guards. |
| P023-T9 | full | full | Retained the pair-indexed partition and positive-denominator localized ratio. |
| P023-T10 | full | not faithful, major | Accepted B's scope objection; required `1 ≤ J` inside the negated universal and proved it using the existing degree-one witness. |
| P023-T11 | full | full | Retained the printed coarsened regression's all-solutions equality. |
| P023-T12 | full | full | Retained the exact selected printed-reading refutation and the `refuted` decision. |

Referee B's T10 finding is correct. The [canonical T10 claim](/home/ubuntu/sap/wt/ARCH-P023/work.json:1075) concerns adequate vote-share controls; the original negation also ranged over degree zero, whose design contains only an intercept and party indicator. Negating that larger universal is weaker and does not itself locate a failure among positive-degree controlled regressions. This is the issue documented in [B's report](/home/ubuntu/sap/wt/ARCH-P023/referees/round1/b/REPORT.md:7). I disagree with A's approval of that previous T10 scope: [A's own blind reading](/home/ubuntu/sap/wt/ARCH-P023/referees/round1/a/reading.md:423) explicitly notes that J was not assumed positive, while the canonical claim requires a vote-share control.

The revised [definition](/home/ubuntu/sap/wt/ARCH-P023/SAP/P023/Defs/Part4.lean:194) requires `1 ≤ J` before the other premises of the universal being negated. Its [bridge](/home/ubuntu/sap/wt/ARCH-P023/SAP/P023/Bridge.lean:100) uses the already credited `linear_counterexample` at J=1: it extracts the existing full rank, exact fitted model, strictly bounded outcomes and failure of localization. The fitted-value premise is discharged by rewriting with the exported exact-model equality. All steps are instantiation, conjunction elimination, exact arithmetic or definitional transport. The Challenge docstring now expressly says positive-degree vote-share controls and states the positive-count domain of the coarsened comparison. The manifest records the degree-one witness as used and the broader original refutation row as not used. The theorem remains `SAP.P023.T10`, and no target has been weakened or left open.

Revision 2 rebuilds all eleven SAP Lean modules in dependency order and reruns the twelve declarations in `scratch/P023AxiomCheck.lean`. Both JSON files, the unchanged theorem-name list, shared statement definitions, required implicit-variable options, source line limits and proof dependencies are rechecked. Counts remain **6 whole, 4 restricted, 2 refuted, 0 omitted**, with **12 proved and no open glue tasks**. A fresh external Comparator receipt is still required for this revised snapshot.


## Declaration review round 1

This section preserves the round 1 response. Its T12 labelling disagreement is superseded by the accepted correction in declaration review round 2 below.

The two deposited findings files contain the same two entries. I used the T11 entry from [T11/r1g3/findings.json](fw/round1/T11/r1g3/findings.json) and the T12 entry from [T12/r1g3/findings.json](fw/round1/T12/r1g3/findings.json), and checked each against `work.json`, the operative brief, and the Lean definitions. Both mathematical statements and proofs remain unchanged; no shared definition changes in this round.

| Declaration and finding | Assessment and action |
| --- | --- |
| T11, label_wrong/minor: missing necessity assertion | Accepted. Changed `whole` to `restricted` and added the exact omission to the Challenge docstring and manifest. The theorem retains the complete equality under Conditions 1–3. |
| T11, missing disclosure and endpoint counterexample | Accepted. The disclosure explicitly omits the auxiliary necessity remark. I independently checked the suggested boundary data; no false necessity assertion is added. |
| T12, label_wrong/minor: relabel the reading refutation `whole` | Disagreed with the proposed relabelling under the operative brief, for the cited reasons below. Retained `refuted`; documented the decision in the manifest. |
| T12, opening overstates an interpretation-specific result | Clarified the scope immediately after the required opening: the docstring now spells out the adopted fixed-law reading and the order of tolerance, degree threshold and fixed-degree limit. Retained the opening required for `refuted`. |
| T12, moment guards described as printed | Accepted. The docstring identifies finite second moments and nondegenerate population moments as additional formal assumptions. It no longer attributes those guards to the printed Appendix B text. |

For T11 the necessity sentence really is part of [the canonical definitions](/home/ubuntu/sap/wt/ARCH-P023/work.json:1153), so the historical note about sufficiency cannot remove it from the coverage accounting. With k=1/2, margins (-1/4,1/2), indicators (0,1), and outcomes (0,2), both observations lie in (-k,k], both denominators equal one, and the RD difference equals two. Condition 1 fails because it requires a positive margin strictly less than k. This directly confirms the reviewer's reason for omitting the necessity statement. The existing Proposition 1 theorem remains correct and proved. The docstring and manifest now carry the same precise restriction.

For T12 I disagree with the requested `whole` classification and removal of the required false-claim opening. The operative [decision rule](/home/ubuntu/sap/wt/ARCH-P023/brief.md:52) assigns `refuted` when the canonical claim is a positive assertion disproved by the formalization; it explicitly allows “the negation of the printed assertion under its printed reading.” Its exception for `whole` concerns targets whose canonical claims are themselves refutations. [T12's canonical statement](/home/ubuntu/sap/wt/ARCH-P023/work.json:1217) is the positive Proposition 2, and [its canonical definitions](/home/ubuntu/sap/wt/ARCH-P023/work.json:1218) select the fixed-law interpretation. Thus the theorem negates the selected reading of this positive printed assertion, which is precisely the operative `refuted` case. It does not establish the positive proposition, and the canonical claim is not itself a negation. The undefined approximation terminology makes the scope qualification essential; it does not turn this positive canonical claim into a canonical refutation target. Accordingly, the docstring now states the complete adopted reading and distinguishes added formal guards, while retaining the required label and opening. The stronger guards are premises inside the universal being refuted; the supplied negation therefore gives a counterexample satisfying them, rather than assuming away a failed printed premise.

The [definition of PrintedPropositionTwo](/home/ubuntu/sap/wt/ARCH-P023/SAP/P023/Defs/Part5.lean:13), every `T<n>Statement`, the eleven-module import graph, and all Solution proofs are unchanged. Only the T11 and T12 explanatory docstrings and manifest annotations changed. `comparator.json` was regenerated and checked with the same twelve fully qualified names. The full dependency-order rebuild and all twelve `#print axioms` checks pass; every proved declaration still uses exactly `propext`, `Classical.choice`, and `Quot.sound`. JSON parsing, restriction disclosures, required implicit-variable options and source line limits are checked again. Round 1 counts were **5 whole, 5 restricted, 2 refuted, 0 omitted**, with **12 proved and no open glue tasks**.


## Declaration review round 2

I reviewed the T12 entry in [the round 2 findings](fw/round2/T12/r2g1/findings.json), the [review report](fw/round2/T12/r2g1/REPORT.md), the complete blind reading, and the unchanged canonical target and definition closure. The file also repeats T11's accepted status; its only open declaration is T12.

| Finding | Assessment and action |
| --- | --- |
| T12, label_wrong/minor: interpretation refutation still labelled `refuted` | Accepted. Changed the manifest decision to `whole` for complete coverage of the adopted fixed-law reading's refutation. The exact mathematical negation remains unchanged. |
| T12, unconditional false-printed-claim opening | Accepted. Removed that opening. The docstring now starts with the target and paper location, followed by the adopted-reading description and its full tolerance/threshold/fixed-degree quantifier scope. |
| T12, earlier moment-provenance issue | Already fixed and retained. The docstring still identifies the moment guards as additional formal assumptions. |
| T11, faithful/no severity; prior two issues fixed | Retained the `restricted` decision and exact omission of the auxiliary Condition 1 necessity remark. |

The decisive scope evidence is [the canonical definitions for T12](/home/ubuntu/sap/wt/ARCH-P023/work.json:1218): the paper does not define its approximation terminology, and the fixed-law tolerance/threshold/fixed-degree formula is the validators' adopted reading. The [formal definition](/home/ubuntu/sap/wt/ARCH-P023/SAP/P023/Defs/Part5.lean:13) and [T12 statement](/home/ubuntu/sap/wt/ARCH-P023/SAP/P023/Defs/Part6.lean:70) negate exactly that adopted formula. I accept the reviewer's scope distinction under the current requirement that `refuted` contradict the printed assertion. My earlier argument focused on the polarity of the chosen formula; it did not justify the unqualified opening about undefined printed guidance. That round 1 labelling response is superseded. `Whole` now means that the theorem covers the complete adopted-reading refutation; it does not mean the positive proposition has been proved. No clause is dropped from that reading refutation, and its moment and sampling premises stay explicit.

No shared definition, theorem statement, fully qualified theorem name, proof, or module import changed. The package changes are the T12 explanatory docstring and its manifest decision and annotations. `comparator.json` is regenerated and checked with the same twelve names and kernel settings. All eleven SAP Lean modules are recompiled with `sap-lean` in dependency order, followed by `scratch/P023AxiomCheck.lean`. All twelve declarations remain proved and use exactly `propext`, `Classical.choice`, and `Quot.sound`; there are no open glue tasks. Both JSON files parse, restriction docstrings match their manifest entries, both implicit-variable options remain present, and all package files stay under 300 lines. The current counts are **6 whole, 5 restricted, 1 refuted, 0 omitted**.


## Declaration review round 3

I checked the T6 entry in [the round 3 findings](fw/round3/T6/r3g3/findings.json), its [report](fw/round3/T6/r3g3/REPORT.md), and the blind reading against the canonical clause and the existing source declarations. The finding is correct: non-Lipschitzness inside one existential does not itself state that every function satisfying the counterexample conditions is non-Lipschitz.

| Finding | Assessment and action |
| --- | --- |
| T6, label_wrong/minor: clause (v)'s universal quantifier is absent | Accepted. Added `NoLipschitzContinuityCounterexample` and conjoined it to `T6Statement`, restoring the full universal clause without removing any previous conclusion. |
| T6, `whole` label and docstring did not disclose that gap | Fixed by restoring the clause. Retained `whole` with no restriction; the docstring now explicitly describes every qualifying function. |
| T7, T8, T9 and T10, faithful/no severity | The same findings file contains these accepted entries. Their statements, proofs and labels are unchanged. |

The [canonical T6 statement](/home/ubuntu/sap/wt/ARCH-P023/work.json:556) says no such h is Lipschitz, so clause (v) applies universally. The existing project already proves precisely the needed exclusion in [tc11_growing_bias_not_lipschitz](/home/ubuntu/sap/wt/ARCH-P023/AronowAudit/P023/Wave1/Lib/PopulationContinuityTailC.lean:59): for every real function h and strictly increasing degree sequence, the inequalities T_(degrees(m)) h ≥ m/4 for all m≥1 imply absence of a Lipschitz constant on [-1,1]. That exported helper is also used by the source proof of the original selected witness. It is not a new theorem or an additional premise.

The SAP proposition quantifies over every h and increasing degree sequence with continuity on [-1,1], h(0)=0, the bound |h|≤1/12, and the prescribed bias growth; its conclusion rules out every real Lipschitz constant on that interval. The [new bridge](/home/ubuntu/sap/wt/ARCH-P023/SAP/P023/Bridge.lean:80) simply introduces the data and applies the source helper. The helper needs even fewer hypotheses, so the continuity, cutoff and size assumptions are unused by this direct application. The Solution adds that result as one conjunction component. No bounded-bias estimate, growth contradiction, approximation proof, or other mathematics is reproduced.

Only `T6Statement` is strengthened, and only `SAP.P023.T6` refers to it. The new proposition is separate from `ContinuityWitness`; no previously shared statistical definition or any other target statement changes. The definition remains Mathlib-only in `Defs/Part6.lean`, imported by both Challenge and Solution. The manifest records the direct helper under `supporting_declarations`, alongside the unchanged credited rows, and the Comparator configuration retains all twelve fully qualified names. A fresh external certificate is required for strengthened T6.

All eleven SAP modules are recompiled in dependency order with `sap-lean`, then all twelve checks in `scratch/P023AxiomCheck.lean` are rerun. Every theorem remains proved with only `propext`, `Classical.choice`, and `Quot.sound`, and there are no open glue tasks. Both JSON files parse; the common statements, exact restriction disclosures, required implicit-variable options and 300-line limits are checked. Counts remain **6 whole, 5 restricted, 1 refuted, 0 omitted**.


## Whole versions (new proofs)

The following targets now use the proved whole statements. Their previous restrictions are removed; P023-T11 is classified `refuted` because its whole version includes the counterexample to the necessity assertion. Earlier sections record the previous snapshots.

- **P023-T3** (`whole`): Challenge [`SAP/P023/Challenge/Part1.lean`](SAP/P023/Challenge/Part1.lean); whole statement [`SAP/P023/Defs/WholeW1.lean`](SAP/P023/Defs/WholeW1.lean); proved leaves [`SAP/P023/WH/W1/Leaves.lean`](SAP/P023/WH/W1/Leaves.lean); whole proof [`SAP/P023/WH/W1/Proofs/T3.lean`](SAP/P023/WH/W1/Proofs/T3.lean); solution [`SAP/P023/Solution.lean`](SAP/P023/Solution.lean). Removed restriction: Omits the separate fixed-tolerance event-probability inequality in clause (f). Adds positive close-window winner and loser counts to the nonlocality component. The shared-consistency component additionally requires a probability law, degree at least one, positive bandwidths, and vanishing probabilities of singular OLS designs and empty RD sides.

- **P023-T4** (`whole`): Challenge [`SAP/P023/Challenge/Part1.lean`](SAP/P023/Challenge/Part1.lean); whole statement [`SAP/P023/Defs/WholeW1.lean`](SAP/P023/Defs/WholeW1.lean); proved leaves [`SAP/P023/WH/W1/Leaves.lean`](SAP/P023/WH/W1/Leaves.lean); whole proof [`SAP/P023/WH/W1/Proofs/T4.lean`](SAP/P023/WH/W1/Proofs/T4.lean); solution [`SAP/P023/Solution.lean`](SAP/P023/Solution.lean). Removed restriction: Adds vanishing probabilities of singular degree-one and degree-seven sample designs and empty RD sides to the sampling component. Prediction-risk comparisons cover measurable predictors with integrable squared error. All population conclusions are retained under these guards.

- **P023-T5** (`whole`): Challenge [`SAP/P023/Challenge/Part1.lean`](SAP/P023/Challenge/Part1.lean); whole statement [`SAP/P023/Defs/WholeW1.lean`](SAP/P023/Defs/WholeW1.lean); proved leaves [`SAP/P023/WH/W1/Leaves.lean`](SAP/P023/WH/W1/Leaves.lean); whole proof [`SAP/P023/WH/W1/Proofs/T5.lean`](SAP/P023/WH/W1/Proofs/T5.lean); solution [`SAP/P023/Solution.lean`](SAP/P023/Solution.lean). Removed restriction: Prediction-risk comparisons cover measurable predictors with integrable squared error. All remaining witness and family clauses are retained.

- **P023-T8** (`whole`): Challenge [`SAP/P023/Challenge/Part1.lean`](SAP/P023/Challenge/Part1.lean); whole statement [`SAP/P023/Defs/WholeW1.lean`](SAP/P023/Defs/WholeW1.lean); proved leaves [`SAP/P023/WH/W1/Leaves.lean`](SAP/P023/WH/W1/Leaves.lean); whole proof [`SAP/P023/WH/W1/Proofs/T8.lean`](SAP/P023/WH/W1/Proofs/T8.lean); solution [`SAP/P023/Solution.lean`](SAP/P023/Solution.lean). Removed restriction: Adds vanishing probabilities of empty RD sides and singular sample designs, for every fixed degree and every growing-degree schedule satisfying the stated rate. All population and sampling conclusions are retained.

- **P023-T11** (`refuted`): Challenge [`SAP/P023/Challenge/Part1.lean`](SAP/P023/Challenge/Part1.lean); whole statement [`SAP/P023/Defs/WholeW1.lean`](SAP/P023/Defs/WholeW1.lean); proved leaves [`SAP/P023/WH/W1/Leaves.lean`](SAP/P023/WH/W1/Leaves.lean); whole proof [`SAP/P023/WH/W1/Proofs/T11.lean`](SAP/P023/WH/W1/Proofs/T11.lean); solution [`SAP/P023/Solution.lean`](SAP/P023/Solution.lean). Removed restriction: Retains the exact Proposition 1 identity under Conditions 1–3; omits the auxiliary remark in definitions_needed that Condition 1 is necessary for existence of the RD estimate.


## Declaration review round 4

I used the T4 entry from [T4/r5g1/findings.json](fw/round4/T4/r5g1/findings.json) and the T5 entry from [T5/r5g1/findings.json](fw/round4/T5/r5g1/findings.json), reading their reports and blind expansions and checking the actual canonical claims and definitions. Both findings are correct. Each appeared in two docstrings: the Challenge declaration and its shared whole-statement definition.

| Finding | Assessment and action |
| --- | --- |
| T4, not_faithful/minor: conditional mean called odd | Accepted. Corrected the Challenge and `T4WholeStatement` docstrings to describe a continuous Lipschitz conditional mean whose centered part is odd. The positive amplitude and positive width domain and zero cutoff jump remain explicit. |
| T5, not_faithful/minor: conditional means called odd | Accepted. Corrected the Challenge and `T5WholeStatement` docstrings to describe continuous Lipschitz conditional means with odd centered parts and zero cutoff jumps. All coefficient, moment, approximation and risk descriptions remain intact. |
| Repeated definition-docstring findings | Fixed in `Defs/WholeW1.lean` for both T4 and T5, as well as in `Challenge/Part1.lean`; no repetition of the incorrect odd-mean wording remains. |

The [canonical T4 clause (i)](/home/ubuntu/sap/wt/ARCH-P023/work.json:314) assigns oddness to h_eta and defines the conditional mean as 1/2+h_eta. [SigmoidPopulation](/home/ubuntu/sap/wt/ARCH-P023/SAP/P023/Defs/Part3.lean:151) already states h_eta(0)=0, h_eta(-x)=-h_eta(x), and that shifted conditional mean. The [canonical T5 clause (i)](/home/ubuntu/sap/wt/ARCH-P023/work.json:457) and [ClusteredPopulation](/home/ubuntu/sap/wt/ARCH-P023/SAP/P023/Defs/Part4.lean:13) make the same distinction for the clustered h. Consequently each conditional mean is 1/2 at zero, which excludes oddness about zero. The corrected descriptions attribute symmetry to exactly the functions that the existing statements prove odd. No mathematical correction or new proof is needed.

The already supplied whole versions and their existing proofs are preserved. The manifest keeps T4 and T5 `whole`, with no restriction, and records the docstring corrections. Every other target decision is preserved. `comparator.json` is regenerated with the same twelve fully qualified theorem names, empty explicit definition list, permitted proof dependencies and kernel settings. A comment-free source comparison confirms that every Lean declaration body, theorem statement, proof and import is unchanged; editing a definition's docstring has not changed the definition used by any other theorem.

All 18 SAP modules, including the whole-statement definitions, leaves and five whole-proof modules, are recompiled with `sap-lean` in dependency order. The twelve checks in `scratch/P023AxiomCheck.lean` are rerun, and every theorem remains proved using exactly `propext`, `Classical.choice`, and `Quot.sound`. Both JSON files parse; theorem names and statements agree between Challenge and Solution; required implicit-variable options and 300-line file limits are checked. Counts are **10 whole, 0 restricted, 2 refuted, 0 omitted**, with **12 proved and no open glue tasks**.

## Whole versions (new proofs)

This section records the incoming W2 switch. Its T11 coverage label is corrected in declaration review round 5 below; the W2 theorem itself is preserved.

- **P023-T11** (`whole`): Challenge [`SAP/P023/Challenge/Part1.lean`](SAP/P023/Challenge/Part1.lean) now states `SAP.P023.T11WholeStatement_W2` from [`SAP/P023/Defs/WholeW2.lean`](SAP/P023/Defs/WholeW2.lean). The blueprint [`SAP/P023/WH/W2/Leaves.lean`](SAP/P023/WH/W2/Leaves.lean) assembles positive party counts and the printed-design Proposition 1 identity; [`SAP/P023/WH/W2/Proofs/T11.lean`](SAP/P023/WH/W2/Proofs/T11.lean) exports `SAP.P023.WH.W2.T11_whole`, now used in [`SAP/P023/Solution.lean`](SAP/P023/Solution.lean). The entry in [`SAP/P023/manifest.json`](SAP/P023/manifest.json) records the whole statement and adds `AronowAudit.P023.close_counts_positive` and `SAP.P023.Bridge.propositionOne` to `rows_used`.

The historical T11 restriction was: “Retains the exact Proposition 1 identity under Conditions 1–3; omits the auxiliary remark in definitions_needed that Condition 1 is necessary for existence of the RD estimate.” The incoming manifest already had `restriction: null` and classified the W1 statement as `refuted`. This switch follows `switch.json`: the W2 whole statement covers Proposition 1 under Conditions 1–3, derives both positive party counts, and has no restriction. It supersedes the earlier T11 classification and description above.

No other Solution proof uses `SAP.P023.T11`; no dependent proof repairs are needed. All other target statements, docstrings, proofs and manifest entries are unchanged.

Validation: `python3 /home/ubuntu/sap/tools/rebuild_sap.py . P023` rebuilt all 21 modules from scratch and passed the forbidden-token scan. The scratch file `/tmp/P023-switch-axioms.lean`, importing `SAP.P023.Solution`, reports exactly `propext`, `Classical.choice`, and `Quot.sound` for `SAP.P023.T11`. Lean processes ran sequentially; no `lake` command was run.


## Declaration review round 5

I reviewed both independent T11 entries: [r7g3/findings.json](fw/round5/T11/r7g3/findings.json) and [opus-o3/findings.json](fw/round5/T11/opus-o3/findings.json), together with their reports and blind readings. Both correctly describe the current finite estimator identity and establish meaningful instances. They differ only on whether the omitted necessity remark counts toward canonical coverage.

| Finding | Assessment and action |
| --- | --- |
| r7g3: T11 label_wrong/minor because necessity is omitted | Accepted. Changed T11 from `whole` to `restricted`; the manifest and both target docstrings now state the exact omission. The W2 theorem and proof remain unchanged. |
| opus-o3: T11 faithful/none, with no disclosure needed for the necessity remark | Agreed about mathematical fidelity of the estimator identity; disagreed with the coverage conclusion for the cited reason below. The same valid identity is retained with the narrower coverage label. |

The [canonical T11 definitions](/home/ubuntu/sap/wt/ARCH-P023/work.json:1153) explicitly include the printed statement that Condition 1 is necessary for an RD estimate to exist. The [precedence rule](/home/ubuntu/sap/wt/ARCH-P023/brief.md:30) makes the canonical claim controlling and treats historical notes as diagnostic; the [clause-completeness rule](/home/ubuntu/sap/wt/ARCH-P023/brief.md:58) requires an omitted clause to be disclosed. Calling the remark a clarity note in audit history, as the opus-o3 report does, does not remove that sentence from the supplied canonical object. Thus I accept r7g3's scope assessment and disagree with opus-o3's assertion that no disclosure is required. The current W2 statement assumes Condition 1 and derives positive counts and equality; it does not assert necessity. The manifest already acknowledged that omission before this round, so the previous `whole` label was inconsistent with its own description.

The omission is appropriate: at bandwidth 1/2, margins (-1/4,1/2), binary indicators (0,1), and outcomes (3,5), both close-window counts equal one and the RD difference is two, but Condition 1 has no positive-margin witness strictly below the bandwidth. This is an ordinary endpoint case of the printed half-open window, not a division-by-zero value. No false necessity clause is added, and no new counterexample proof is introduced in this round.

Both [the Challenge docstring](/home/ubuntu/sap/wt/ARCH-P023/SAP/P023/Challenge/Part1.lean) and [the W2 statement-definition docstring](/home/ubuntu/sap/wt/ARCH-P023/SAP/P023/Defs/WholeW2.lean) now say: “States the estimator-equality result under Conditions 1–3; omits the printed remark that Condition 1 is necessary for an RD estimate to exist.” I also removed their reference to assumed measure-theoretic conditions: the actual theorem is finite and has no such extra premises. Its name `T11WholeStatement_W2` is preserved for compatibility and does not determine the manifest's coverage label.

No shared definition body, theorem statement, fully qualified theorem name, proof, or import changes. A comment-free source comparison verifies that every Lean declaration is unchanged. `comparator.json` is regenerated with the same twelve names and kernel settings. All 21 SAP modules are recompiled with `sap-lean` in dependency order, followed by every declaration in `scratch/P023AxiomCheck.lean`; all twelve remain proved with exactly `propext`, `Classical.choice`, and `Quot.sound`. Both JSON files parse, the two T11 disclosures match the manifest restriction, and implicit-variable options and 300-line limits are checked. Current counts are **10 whole, 1 restricted, 1 refuted, 0 omitted**, with **12 proved and no open glue tasks**.
