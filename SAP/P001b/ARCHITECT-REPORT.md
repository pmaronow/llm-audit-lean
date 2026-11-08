# P001b packaging report

Work: *Foundations of Agnostic Statistics* (2019). Scope: exactly P001-T20 through P001-T38, as listed in `work.json`.

## Decisions

| Decision | Count |
|---|---:|
| whole | 14 |
| restricted | 1 |
| refuted | 4 |
| omitted | 0 |
| Total | 19 |

All 19 listed theorems are proved, with no open glue tasks. Current counts are 14 whole, 1 restricted, 4 refuted, and 0 omitted. Round 6 accepts all three T22 findings under the explicit author decision of 2026-11-04: measurable response sections are presupposed usual conditions, and labels depend on claim coverage rather than proof provenance. T22 is whole with no restriction. The earlier review sections record historical decisions; the round-6 ruling supersedes their T22 scope conclusions and earlier donor-status classification rules. Round 7 clarifies that T36 retains only the canonical density and extended-integral facts, without refuting an identity whose real slice integral is presupposed finite.

## Restrictions and refutation scope

- **P001-T25:** Retains only counterexample (a), the constant-zero one-atom law. Omits counterexample (b), the Bernoulli law with masses two thirds and one third and its printed-sum value one third.

- **P001-T31:** Retains the specified recursive fat-Cantor set, its measure one half, the normalized subtype probability law, its density, literal range and positive-density support, and exclusion of every nondegenerate interval. Omits the removed-length geometric-series calculation and the quantitative bounds on the lengths of the stage components.

- **P001-T34:** Retains only counterexample (a), the normalized density on (0,1) times (-1,0), with event mass one and printed iterated integral zero. Omits counterexample (b), the independent uniform law on [-1,1] squared and the values three eighths and one eighth.

- **P001-T36:** Retains real analyticity (and hence smoothness), strict positivity, integrability, total mass one, the infinite nonnegative slice integral at zero, and integrability of every nonzero slice. Omits boundedness; the logistic slice formula and its separate normalization; the joint CDF and everywhere mixed-derivative assertions; the limiting value of the zero-slice integrand; positivity of the nonzero slice integrals; and the marginal CDF assertion of no finite derivative at zero. States only these density and extended-integral facts; it does not establish a refutation of the pointwise marginal-PDF identity under the usual assumption that its real slice integral exists finitely.

## Omitted targets and open glue

None. Every assigned target has one Challenge stub and one proved Solution theorem.

## Definitions and bridges

The shared-definition route is used throughout. `Defs/Part1.lean` supplies ordinary finite-weight probabilities and density predicates; Part2 supplies the concrete witnesses; Parts3–4 supply the original statement predicates. The supplied `Defs/WholeW1.lean` and `Defs/WholeW2.lean` contain the extended predicates now used for T20, T22, T26, T27, T30, and T37. Their imports remain Mathlib and earlier Defs only. Challenge and Solution use the same compiled definition modules, so their statement definitions have one origin.

`Bridge.lean` imports the project. Its ordinary real probabilities, density predicates, CDFs, finite means, conditional means, concrete atom weights, dyadic series, uniform functions, rectangle density, smooth slice density, and printed bivariate formula agree by reflexivity.

Three structural adapters need more than reflexivity:

- `asFiniteLaw` bundles supplied nonnegative normalized weights into the project structure. It proves no additional property.
- `finiteProbability_eq` splits on membership to equate the two finite sums irrespective of the chosen decision instance. `finiteConditionalIndependence_eq` expands the factorization definitions and rewrites those finite probabilities.
- `cantorInterval_eq` uses structural induction on the list of left/right choices. The stage and intersection identities then simplify. `cantor_facts` transports a proposition depending on the set along its equality, moving the subtype and its comapped measure together.

The finite-support converse in T20 instantiates the existing finite bound on the marginal-support subtype. Remaining glue consists of conjunctions, instantiation, set logic, finite arithmetic, elementary algebra, and consequences of the exported facts. T34 guards its ordinary integral by explicit integrability, obtained from its exported nonzero total integral.

## Reuse across assigned targets

- T22 reuses the electorate witness, the measurable-response declaration exactly as stated, and the unconditional discrete ATE proof. Together they cover all three clauses under the author's presupposed usual conditions. The donor row's historical wrong-credit status does not change that claim-relative classification.
- T32 uses T31 only to supply a concrete continuous probability-space input to its credited complete-correction row. Thus its interval-free-range existence assertion is unconditional.
- T37 retains every finite nonnegative marginal version and its CDF, with its supplied assembly removing the former global measurability premise from the independently quantified normalization branch.
- T38 instantiates the T32 atomlessness theorem to exclude any density for the zero combination. Its positive-variance exclusion and both endpoint witnesses come from its own credited rows.

## Validation

All Defs parts and root, Bridge, both Challenge parts and root, and Solution compiled with `/home/ubuntu/sap/tools/sap-lean` in dependency order. The proof audit in `scratch/Axioms.lean` printed dependencies for every Solution theorem: each uses exactly `propext`, `Classical.choice`, and `Quot.sound`.

`manifest.json` and `comparator.json` are parsed and checked for the exact target set and theorem list. Every SAP Lean file has at most 300 lines and sets both implicit-variable options immediately after its imports.

Compiled statement-type comparison is recorded in `scratch/challenge-types.log` and `scratch/solution-types.log`. The check compares the full Lean expression and universe-parameter representations for each of the 19 theorem types.

## Limits and concerns

The current claim-relative rule is enforced. T22 uses the response-function declaration only for its exact measurable-section statement; those premises are presupposed usual conditions under the round-6 author decision. Its identification branch uses the existing unconditional discrete ATE proof, with no universal literature proposition added. The supplied T37 version has no global Borel premise on its slice-normalization branch.

No infinite slice is converted to a real value. T36 states an extended nonnegative integral equal to infinity; its zero slice lies outside the finite-real slice domain, and the theorem establishes no failure of the identity on that domain. Conditional means are evaluated on the two explicitly positive treatment cells and the constant-covariate cell; arbitrary density means or zero-denominator conditional means are not asserted. T38 explicitly exports the zero denominators in the ordinary printed expression, separately from the values of its total real-division extension.

The orchestrator supplied a successful prior-snapshot Comparator result in [verification/comparator-result.json](SAP/P001b/verification/comparator-result.json) and its [kernel log](SAP/P001b/verification/comparator.log): all 19 targets were accepted by the default Lean, con-ron, and nanoda kernels. Before revision 2, every recorded source/configuration hash matched this worktree; the check is in `scratch/revision2-baseline.json`. That record remains evidence for its original snapshot. The current declaration-review revision preserves the supplied round-2 statement definitions and Solution proofs; that supplied snapshot already includes the extended versions described below, which postdate the original certificate. The Comparator configuration is regenerated with the same 19 names and kernel settings. Fresh local recompilation, statement-type comparison, and dependency checks are recorded below; a fresh external-kernel run is not claimed.

## Referee round 1 findings and revision 2 actions

Both complete finding lists were checked against the canonical claims and the shared statements: [referee A](referees/round1/a/findings.json), [referee B](referees/round1/b/findings.json), and their [A report](referees/round1/a/REPORT.md) and [B report](referees/round1/b/REPORT.md). No mathematical finding is rejected. The classification changes below apply revision 2's new refutation rule, including where the earlier reports accepted the old labels.

| Target | A verdict | B verdict | Action |
|---|---|---|---|
| T20 | correct_restricted | correct_restricted | Kept the statement and its three disclosed omissions. |
| T21 | correct_whole | correct_whole | Revision 2 relabelled refuted; declaration review below corrects this to whole and names the interpretation. |
| T22 | correct_restricted | correct_restricted | Kept only corrected clause (i); omissions (ii) and (iii) remain explicit. |
| T23 | correct_whole | correct_whole | Kept all corrected probability and gloss clauses. |
| T24 | correct_whole | correct_whole | Kept total probability, the partition repair, positivity guards, and arithmetic example. |
| T25 | correct_restricted | correct_restricted | Relabelled refuted; kept the disclosed omission of the second witness. |
| T26 | correct_restricted | correct_restricted | Kept the missing-mass identities and disclosed die-specialization omission. |
| T27 | correct_restricted | correct_restricted | Revision 2 relabelled refuted; declaration review below restores restricted and names the interpretation. |
| T28 | correct_whole | correct_whole | Kept the countable and finite CDF clauses and all six die evaluations. |
| T29 | correct_whole | correct_whole | Relabelled refuted; kept all three density versions and both endpoint quotient failures. |
| T30 | correct_restricted | correct_restricted | Kept the continuous correction and disclosed discrete-factorization omission. |
| T31 | correct_restricted | correct_restricted | Relabelled refuted; kept the omissions of the removed-length sum and stage-length bounds. |
| T32 | correct_whole | correct_whole | Kept atomlessness, both uncountability assertions, and unconditional interval-free-range existence. |
| T33 | correct_whole | correct_whole | Kept the true pointwise algebraic generalization. |
| T34 | correct_restricted | correct_restricted | Relabelled refuted; kept the omission of the second rectangle witness. |
| T35 | correct_whole | correct_whole | Kept the corrected event, decomposition, and exact equality criterion. |
| T36 | restriction_inaccurate | correct_restricted | Revision 2 disclosed real analyticity and relabelled refuted; round 2 below corrects the label to restricted. |
| T37 | correct_restricted | correct_restricted | Kept Borel measurability solely on the conditional-normalization branch. |
| T38 | correct_whole | correct_whole | Revision 2 relabelled refuted; round 2 below restores whole. |

A's two T36 issues were checked separately. First, the retained `ContDiff` order is indeed the analytic order: Mathlib's [notation explanation](/home/ubuntu/sal/deps/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean:91), [definition](/home/ubuntu/sal/deps/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean:1068), and [analyticity equivalence](/home/ubuntu/sal/deps/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean:1196) identify the literal outer top with omega. The [credited existing declaration](AronowAudit/P001/Wave1/Gap/GLP0013B1.lean:247) already proves exactly this order for the explicit density. Second, the old prose disclosed only smoothness. T36's one-sentence description, scope text, manifest restriction, and this report now explicitly retain real analyticity and hence smoothness. All existing omissions are preserved. No theorem or proof is added to establish stronger regularity. Referee B's observation that analyticity entails smoothness is correct; A's exact-disclosure objection still applies. The revised descriptions state the stronger property explicitly.

Revision 2 initially applied the refuted label to eight counterexample targets. Declaration review round 1 corrects the interpretation-specific cases: T21 is whole and T27 is restricted. Their docstrings identify the precise readings rather than asserting unqualified falsity of the printed prose. At that stage six items retained false-claim openings. Round 2 below further corrects T36 and T38 relative to their canonical counterexample assertions. T25, T31, T34, and T36 retain their witness-scope disclosures; T27 retains its restriction disclosure. T22 remains restricted because its canonical target is the corrected assertion, of which the information-premise counterexample is just clause (i).

The finite-probability and integral checks were repeated during review: probability measures make every `toReal` argument finite; T20 and T24 guard their ratios by positive cell masses; T21 supplies the positive treatment and constant-covariate cell masses; T26 assumes summability; T27 has positive summable normalized weights; all arbitrary density means and triangle integrals carry integrability through the density predicates; and T37 requires an integrable selected slice with a strictly positive real integral. T36's divergent slice remains an extended nonnegative integral. T38's endpoint totalization is part of the explicitly stated counterexample, with separate zero-denominator certificates. Neither referee identified a missing guard, and independent inspection found no additional hypothesis needed.

Revision 2 verification completed: all 10 Lean modules rebuilt in dependency order, all 19 Solution dependency reports contain exactly the permitted three axioms, and all 19 compiled Challenge/Solution type expressions and universe parameters match. Both JSON files parse with the exact target set and theorem list. The definition and Solution source hashes and all theorem headers match the pre-revision baseline; every SAP file is within the 300-line limit. Results are recorded in `scratch/revision2-validation.json`; there are no open glue tasks.

## Declaration review round 1

Both open findings are accepted. Each contains a decision issue and a docstring issue; all four are addressed without altering any shared definition, statement, bridge, or Solution proof. The current counts above supersede revision 2's historical counts.

| Declaration | Finding | Action |
|---|---|---|
| T21 | label_wrong/minor: the canonical target already specifies the complete counterexample to the information implication. | Changed decision from refuted to whole, with restriction null. Checked every recorded four-atom-model clause against `T21Statement`. |
| T21 | The unconditional false-claim opening obscures the distinction between information in X and in (X,D). | Replaced it with the reviewer’s precise interpretation: complete coding in (X_i,D_i), no personal acquaintance, and conditional independence given X_i. |
| T27 | label_wrong/minor: the target concerns the local-constancy reading and the current theorem omits witness details. | Changed decision from refuted to restricted. Preserved the full existing restriction text, including all omitted clauses. |
| T27 | The false-claim opening does not identify that reading. | Replaced it with the local-constancy interpretation at every non-jump point and the continuity/nonconstancy witness at one third. Restored the Restricted prefix. |

T21 was checked against the [declaration finding](fw/round1/T21/a/findings.json), its [report](fw/round1/T21/a/REPORT.md), the [canonical statement](work.json:123), and [T21Statement](SAP/P001b/Defs/Part3.lean:28). The canonical “What is refuted” passage explicitly uses the recorded pair (X,D). In the [fixed gender and leaflet definitions](SAP/P001b/Defs/Part1.lean:54), X is constant while displayed D takes both values. Consequently, the result must name that reading; it does not establish that constant X alone records displayed gender or that ignorability fails in the actual Swiss data. The theorem covers the entire supplied counterexample, including vote counts, bounds, positive conditioning masses, factorization failure, conditional means, and average effect. Its whole label is relative to that canonical counterexample.

T27 was checked against its entry in the [multi-declaration finding file](fw/round1/T27/r1g1/findings.json), its [report](fw/round1/T27/r1g1/REPORT.md), the [canonical “read as” statement](work.json:545), and [T27Statement](SAP/P001b/Defs/Part3.lean:105). The theorem asserts a normalized positive countable dyadic law, strict increase, continuity at one third, and failure of local constancy there. Its statement still omits the per-level geometric-series identity, injectivity and exact range description, and separate zero-point-mass assertion. These remain in the manifest and docstring restriction. The other entries in that finding file (T25, T26, T28, T29) have no open issues and remain unchanged.

The mathematical statements already have the necessary probability, summability, integrability, and positive-denominator guards. The reviewers identify no mathematical or junk-value defect in either declaration, and inspection of their definition closures agrees. No additional proof, assumption, or shared-definition change is needed. The Comparator configuration is regenerated for the same 19 fully qualified theorem names and the same permitted dependencies and kernels.

Declaration review round 1 verification completed: all 10 Lean modules rebuilt in dependency order with `sap-lean`; every one of the 19 Solution theorems again reports exactly `propext`, `Classical.choice`, and `Quot.sound`; and all 19 compiled Challenge/Solution types and universe parameters match. Both configuration files parse with the exact target set and theorem names. Source hashes confirm that only the two Challenge docstrings changed among Lean files; every definition, statement, bridge, and Solution proof is unchanged. All SAP files satisfy the 300-line limit and both implicit-variable settings. The build log is `scratch/declaration-round1-build.log`, and the consolidated result is `scratch/declaration-round1-validation.json`. There are no open glue tasks; no fresh external-kernel run is claimed.

## Supplied extended proof versions

The following six targets were switched to supplied extended statements and proofs
between declaration review rounds 1 and 2. Each Challenge retains its stub; each
Solution theorem directly uses its supplied `_whole` theorem. That switch recorded
13 whole and 6 refuted. Current classifications and disclosures above and in the
round-6 section supersede that historical classification. T22 is whole under the
author's presupposed measurable-response convention.

- **P001-T37 (`SAP.P001b.T37`):** switched to `SAP.P001b.T37WholeStatement`
  using `SAP.P001b.WH.W1.T37_whole` in `SAP/P001b/Solution.lean`.
  Files: `SAP/P001b/Challenge/Part2.lean`, `SAP/P001b/Defs/WholeW1.lean`, `SAP/P001b/WH/W1/Leaves.lean`, `SAP/P001b/WH/W1/Proofs/T37.lean`.
  Old restriction removed: Adds global Borel measurability only to the conditional-slice normalization clause, as required by the narrower credited declaration. The marginal finiteness and all finite nonnegative almost-everywhere versions remain unrestricted by Borel measurability. No conditional kernel or disintegration identity is asserted.

- **P001-T20 (`SAP.P001b.T20`):** switched to `SAP.P001b.T20WholeStatement`
  using `SAP.P001b.WH.W1.T20_whole` in `SAP/P001b/Solution.lean`.
  Files: `SAP/P001b/Challenge/Part1.lean`, `SAP/P001b/Defs/WholeW1.lean`, `SAP/P001b/WH/W1/Leaves.lean`, `SAP/P001b/WH/W1/P/T20_L1V2.lean`, `SAP/P001b/WH/W1/P/T20_L2V2.lean`, `SAP/P001b/WH/W1/P/T20_L3V2.lean`, `SAP/P001b/WH/W1/Proofs/T20.lean`.
  Old restriction removed: States the overlap/pointwise-positivity equivalence, uniform-positivity implication, and finite-marginal-support converse for nonnegative joint arm masses. Omits clause (i), the two conditional arm-support identities and their normalization bridge; clause (v), the infinite-support counterexample; and a probability-space formulation for nondiscrete covariates.

- **P001-T22 (`SAP.P001b.T22`):** switched to `SAP.P001b.T22WholeStatement`
  using `SAP.P001b.WH.W1.T22_whole` in `SAP/P001b/Solution.lean`.
  Files: `SAP/P001b/Challenge/Part1.lean`, `SAP/P001b/Defs/WholeW1.lean`, `SAP/P001b/WH/W1/Leaves.lean`, `SAP/P001b/WH/W1/P/T22_L1V2.lean`, `SAP/P001b/WH/W1/P/T22_L2V2.lean`, `SAP/P001b/WH/W1/Proofs/T22.lean`.
  Old restriction removed: Retains only clause (i), the fully coded constant-covariate electorate counterexample, using the usable T21 witness. Omits clause (ii), the description-only functional-response implication, and clause (iii), the discrete ATE identification formula. The credited identification declaration requires an additional universal literature premise that is not assumed here; the other credited row is wrong_credit and is not used.

- **P001-T26 (`SAP.P001b.T26`):** switched to `SAP.P001b.T26WholeStatement`
  using `SAP.P001b.WH.W1.T26_whole` in `SAP/P001b/Solution.lean`.
  Files: `SAP/P001b/Challenge/Part1.lean`, `SAP/P001b/Defs/WholeW1.lean`, `SAP/P001b/WH/W1/Leaves.lean`, `SAP/P001b/WH/W1/P/T26_L1.lean`, `SAP/P001b/WH/W1/Proofs/T26.lean`.
  Old restriction removed: Retains clauses (i) and (ii), the corrected integer lower-tail sum, missing-mass identity, and equality criterion. Omits clause (iii), the fair-die specialization and its values three sixths and one half.

- **P001-T27 (`SAP.P001b.T27`):** switched to `SAP.P001b.T27WholeStatement`
  using `SAP.P001b.WH.W1.T27_whole` in `SAP/P001b/Solution.lean`.
  Files: `SAP/P001b/Challenge/Part1.lean`, `SAP/P001b/Defs/WholeW1.lean`, `SAP/P001b/WH/W1/Leaves.lean`, `SAP/P001b/WH/W1/P/T27_L1.lean`, `SAP/P001b/WH/W1/P/T27_L2.lean`, `SAP/P001b/WH/W1/Proofs/T27.lean`.
  Old restriction removed: Retains the explicit positive normalized dyadic atom weights, countable range, strict increase on (0,1), continuity at one third, and failure of local constancy there. Omits the per-level geometric-series identity, injectivity and exact identification of the range with the dyadic rationals in (0,1), and the separate zero point-mass assertion at one third.

- **P001-T30 (`SAP.P001b.T30`):** switched to `SAP.P001b.T30WholeStatement`
  using `SAP.P001b.WH.W2.T30_whole` in `SAP/P001b/Solution.lean`.
  Files: `SAP/P001b/Challenge/Part2.lean`, `SAP/P001b/Defs/WholeW2.lean`, `SAP/P001b/WH/W2/Leaves.lean`, `SAP/P001b/WH/W2/P/T30_L1.lean`, `SAP/P001b/WH/W2/P/T30_L2.lean`, `SAP/P001b/WH/W2/Proofs/T30.lean`.
  Old restriction removed: Retains all univariate correction clauses, joint almost-everywhere uniqueness, the uniform mixed-derivative boundary counterexample, the product CDF on the unit square, and the continuous density/product-law equivalence. Omits the separate assertion that discrete PMF factorization remains pointwise.

The supplied switch left the other Solution proofs independent of the six old
statements. Round 2 preserves all mathematical content of that supplied snapshot.
The internal proof-support module layout is adjusted below solely for the file limit.

Validation: `python3 /home/ubuntu/sap/tools/rebuild_sap.py . P001b` rebuilt all
30 unit modules from scratch and passed the forbidden-token scan. The scratch
file `scratch/whole-switch-axioms.lean` imports `SAP.P001b.Solution` and runs
`#print axioms` for all six switched theorems; each reports exactly `propext`,
`Classical.choice`, and `Quot.sound`. Compilation used one Lean process at a
time; no `lake` command was run. Per-target results are in `switched.json`.

## Declaration review round 2

Both open findings are accepted. The two report directories contain matching multi-declaration findings; each target's own entry was checked: [T36 finding](fw/round2/T36/r5g4/findings.json), [T36 report](fw/round2/T36/r5g4/REPORT.md), [T38 finding](fw/round2/T38/r5g4/findings.json), and [T38 report](fw/round2/T38/r5g4/REPORT.md).

| Declaration | Finding | Action |
|---|---|---|
| T36 | label_wrong/minor: the canonical target asserts the infinite-slice counterexample, while the theorem states a disclosed subset. | Changed refuted to restricted. Kept the existing restriction verbatim, including analyticity and every omitted clause. The docstring now introduces the canonical counterexample to finite marginalization at every y. |
| T38 | label_wrong/minor: the canonical target already asserts the zero normal combination and both endpoint singularities. | Changed refuted to whole with restriction null. The docstring now names the canonical counterexamples to the two quoted source assertions. Both components remain stated. |

For T36, the [canonical assertion](work.json:1128) includes extra boundedness, integration, limit and CDF properties. [T36Statement](SAP/P001b/Defs/Part4.lean:79) retains analyticity, strict positivity, joint integrability and unit mass, an infinite extended nonnegative slice at zero, and integrability of all nonzero slices. It establishes part of the canonical counterexample rather than refuting that counterexample. Its complete existing omission list is still accurate, so no mathematical clause is restored. The [credited declaration](AronowAudit/P001/Wave1/Gap/GLP0013B1.lean:247) already proves exactly the retained conjunction.

For T38, the [canonical assertion](work.json:1266) itself states both counterexamples. [T38Statement](SAP/P001b/Defs/Part4.lean:98) contains the unit atom, exclusion of every density and positive-variance normal law, the zero-coefficient identity, both admissible correlation endpoints, and both vanishing formula denominators. Its auxiliary zero-valued formula and zero-integral assertions concern the documented total real-division extension. The separate denominator identities certify the singular ordinary expression. All canonical counterexample clauses are present, so whole is appropriate and restriction stays null. No positive-variance normal law is assumed for the zero combination.

The round-2 clarification for wrong-credit declarations also applies to the supplied T22 extension. Its [statement](SAP/P001b/Defs/WholeW1.lean:175) requires both response sections to be measurable in its second conjunct. The [canonical clause (ii)](work.json:199) requires only a fixed response whose compositions are random variables. The [project declaration](AronowAudit/P001/P001_Foundations.lean:1604) proves exactly the stronger-premise statement and its final review status is wrong_credit for the unqualified component. It is now used only for its own statement, as expressly permitted in this update. T22 is relabelled restricted; the docstring and manifest disclose both added measurability hypotheses and the omitted unqualified implication. The counterexample and discrete ATE branches remain. The manifest also removes the contradictory entry that listed this used row as unused, and corrects the unused conditional-row explanation: the supplied proof uses the unconditional discrete ATE declaration, so identification is retained.

All shared Challenge definitions, theorem types, and Solution proof bodies are preserved. To enforce the 300-line rule on the supplied snapshot, the 524-line internal proof-support module `WH/W1/Leaves.lean` is divided into `Leaves/Part1.lean` and `Leaves/Part2.lean`, with a short import root; the declaration text and proof bodies are unchanged. The 307-line `WH/W1/P/T22_L1V2.lean` is reduced below the limit by removing blank lines only. Every new module sets both implicit-variable options. The identity of the moved text is recorded in `scratch/declaration-round2-layout.json`; no shared definition under Defs is edited, and no mathematics is added.

Declaration review round 2 verification completed: all 32 Lean modules rebuilt with `sap-lean` in dependency order using one Lean process. All 19 Solution theorems again report exactly `propext`, `Classical.choice`, and `Quot.sound`, and all 19 compiled Challenge/Solution type expressions and universe parameters match. Both JSON files parse with the exact target set and theorem list. Hash checks confirm unchanged Defs modules, unchanged theorem types and Solution source, verbatim preservation of the split proof-support text, and blank-line-only formatting of the overlength leaf proof. Every SAP file is at most 295 lines and every Lean module sets both implicit-variable options. Results are recorded in `scratch/declaration-round2-validation.json`, the ordered build in `scratch/declaration-round2-build-order.json`, and the compiler output in `scratch/declaration-round2-build.log`. All 19 theorems remain proved, with no open glue tasks; a fresh external-kernel run is not claimed.

## Declaration review round 3

The T22 label_wrong/minor finding is **not accepted**. Its two issues were checked separately against the canonical text, standing definitions, existing Lean statement, and the explicit rule repeated in the current update. T22 remains restricted with its current disclosure; all 19 statements and proofs remain unchanged.

| Finding | Decision and action |
|---|---|
| T22 decision is allegedly too narrow because section measurability is already implicit in the claim. | Disagree. The standing definition requires the composed outcomes to be random variables, while this theorem requires measurable response sections on the covariate space. The current wrong-credit rule expressly classifies this use as restricted. |
| T22's Restricted sentence allegedly excludes only cases outside the author's reading. | Disagree. The supplied canonical reading does not impose section measurability. Kept the exact restriction; revised the opening description to state the section hypotheses directly, avoiding the misleading suggestion that the canonical claim already includes them as “usual” conditions. |

The [finding](fw/round3/T22/r6g1/findings.json) and [report](fw/round3/T22/r6g1/REPORT.md) assert an express rule making ordinary measure conditions whole. That rule is not present in the supplied operative brief. Instead, [the brief's precedence rule](brief.md:30) makes the canonical claim authoritative, and [its restricted rule](brief.md:47) includes statements proved only under extra hypotheses. More specifically, the [round-3 update](revise-fw3.md:12) expressly says that a wrong-credit declaration may be used for its exact statement and “the target is then restricted.” The current Solution uses that precise declaration for the measurable-response branch.

The [standing Definition 1.2.2](work.json:45) says that g is a function of X when g composed with X is a random variable. This is measurability on the original sample space. It does not require g itself to be measurable on the covariate space. The [canonical T22(ii)](work.json:199) uses this fixed-function formulation. In contrast, [T22WholeStatement](SAP/P001b/Defs/WholeW1.lean:183) and the [credited declaration](AronowAudit/P001/P001_Foundations.lean:1607) separately assume that both response sections are measurable on the covariate space. Measurability of the compositions alone does not imply those premises, nor does it automatically identify the outcomes as measurable with respect to the sigma-field generated by X on arbitrary probability spaces.

This is also the exact distinction recorded by the final row review: [the status](work.json:262) is wrong_credit, [the specific missed hypothesis](work.json:270) is section measurability, and [the recorded excluded setting](work.json:278) explains why it is substantive for the unqualified implication. Those diagnostics corroborate the direct comparison; they are not used to introduce new mathematical assumptions. The new review's measurable-section examples show that the current statement has admissible instances, but they do not supply the missing unqualified assertion.

All three canonical components are represented, but component (ii) still has stronger premises. The full counterexample and discrete identification conclusions remain; the unqualified description-only implication remains outside the theorem. Relabelling whole and deleting the restriction would therefore overstate its coverage under the current canonical claim and explicit wrong-credit rule. No new proof is attempted. The name `T22WholeStatement` is retained to preserve the shared definition and does not determine the manifest decision. Its existing documentation describing “usual” conditions cannot change the canonical target's scope.

The other entries in the multi-declaration findings file, T20, T21, T23, and T24, have no open findings and remain unchanged. Both JSON configurations are regenerated with the same 19 theorem names, decisions, permitted dependencies, and kernel settings. The only Lean-source edit is the clarifying T22 Challenge docstring; no shared definition or proof is edited.

Declaration review round 3 verification completed: all 32 Lean modules rebuilt in dependency order with `sap-lean`, and all 19 Solution theorems again report exactly `propext`, `Classical.choice`, and `Quot.sound`. All 19 compiled Challenge/Solution types and universe parameters match. Both JSON files parse with the exact target and theorem lists. Hash checks confirm that the only Lean edit was the T22 Challenge docstring; definitions, theorem types, bridges, and proofs are unchanged. Every SAP file remains within 300 lines and every Lean module sets both implicit-variable options. Results are in `scratch/declaration-round3-validation.json` and `scratch/declaration-round3-build.log`. There are no open glue tasks. The T22 classification finding remains explicitly disputed for the reasons and citations above; no fresh external-kernel run is claimed.

## Declaration review round 4

The sole open declaration finding, T22 label_wrong/minor, is **not accepted** after checking both reported issues anew. The [round-4 findings](fw/round4/T22/r7g1/findings.json:31) and [report](fw/round4/T22/r7g1/REPORT.md) posit an explicit author convention requiring measurable response functions and whole status for usual measure-theoretic conditions. Neither the supplied canonical claim nor the operative brief contains that convention. This is a disagreement about the supplied scope rules, not about the validity of the existing Lean theorem.

| Finding | Decision and action |
|---|---|
| T22's restricted decision is allegedly wrong because response-section measurability is already presupposed. | Disagree. Retained restricted and the exact restriction in the manifest. Canonical clause (ii) and the standing definition require random-variable compositions, whereas the Lean statement separately requires measurable sections. The current update also expressly requires restricted status for this use of a wrong-credit row. |
| T22's Restricted sentence allegedly omits only cases outside the author's current reading. | Disagree. Retained the Challenge docstring, which states the two section premises and discloses the excluded cases. The cited author convention is not among the supplied assumptions, so removing this disclosure would overstate coverage. |

The controlling citations are the [canonical-precedence rule](brief.md:30), the [extra-hypothesis classification rule](brief.md:47), and the explicit [round-4 wrong-credit instruction](revise-fw4.md:12): the row may be used for its own statement, but “the target is then `restricted`.” This instruction is repeated in the current update, rather than merely appearing in historical review metadata.

Independently of that status rule, [Definition 1.2.2 in the standing assumptions](work.json:45) defines a function of X by requiring its composition with X to be a random variable. The [canonical clause (ii)](work.json:199) specifies a fixed response function without requiring measurable sections on the covariate space. In contrast, [the shared statement](SAP/P001b/Defs/WholeW1.lean:183) and [its existing donor](AronowAudit/P001/P001_Foundations.lean:1607) explicitly require both sections to be measurable. The original-space measurability of a composition does not in general supply these codomain hypotheses. The [row's final status](work.json:262) and [recorded scope difference](work.json:270) corroborate this direct comparison. No diagnostic note is treated as an instruction or as a new premise.

All three components are present, but clause (ii) remains conditional on stronger assumptions. The review's admissible measurable-section examples establish nonvacuity, not coverage of the excluded cases. Its suggested replacement would leave the theorem valid while misclassifying its coverage under the supplied canonical text and current wrong-credit instruction. No mathematical repair is attempted. The other entries in the same findings file, T20, T21, T23, and T24, are faithful and have no open issues.

The manifest and Comparator configuration are regenerated with the same decisions, disclosures, 19 theorem names, permitted dependencies, and kernel settings. No Lean source is changed: all shared definitions, statements, bridges, and Solution proofs retain their exact source hashes.

Declaration review round 4 verification completed: all 32 Lean modules rebuilt in dependency order with `sap-lean`, using one Lean process. Fresh `#print axioms` output for all 19 Solution theorems contains exactly `propext`, `Classical.choice`, and `Quot.sound`. All 19 compiled Challenge/Solution type expressions and universe parameters match. Both JSON files parse and have the exact target and theorem lists. Source hashes confirm that no Lean file changed, every SAP file remains within 300 lines, and every Lean module sets both implicit-variable options. The results are in `scratch/declaration-round4-validation.json`, the ordered build is in `scratch/declaration-round4-build-order.json`, and compiler output is in `scratch/declaration-round4-build.log` and `scratch/axioms.log`. All 19 theorems remain proved with no open glue tasks. The T22 finding remains disputed with the citations above; no fresh external-kernel run is claimed.

## Third-rung revision (Opus)

Historical action: retained T22 as restricted under the composition-only reading and the then-explicit wrong-credit instruction, and clarified its two docstrings. Definition bodies, statements, bridges, and proofs were unchanged. The round-6 author decision supersedes this T22 classification and scope disclosure.

The detailed prior account is preserved in [the pre-round-6 report](scratch/declaration-round6-report-before.md:232). Its 32-module rebuild, 19 axiom checks, and type comparisons passed; the logs remain in `scratch/opus-rung-build.log` and `scratch/opus-rung-validation.json`. The original counts were 13 whole, 2 restricted, 4 refuted, and 0 omitted, with all 19 theorems proved.

## Declaration review round 5

Checked the T22 findings from [r8g1](fw/round5/T22/r8g1/findings.json) and [r9g1](fw/round5/T22/r9g1/findings.json), and the T30 findings from [r9g3](fw/round5/T30/r9g3/findings.json). T30's two documentation findings were accepted. T22's classification and scope findings were disputed under the instructions supplied at that stage; the following historical conclusions are superseded by the explicit round-6 author decision.

| Finding | Decision and action |
|---|---|
| T22: restricted label allegedly treats an implicit measurability condition as substantive (both reports). | Disagree; retained restricted and the exact manifest restriction. The current wrong-credit rule expressly requires this classification, and the canonical composition-only definition does not require response-section measurability. |
| T22: Challenge restriction paragraph allegedly excludes only cases outside the author convention (both reports). | Disagree; retained its explicit account of all three clauses and the precise extra premises. The supplied canonical claim and standing definitions contain no such author convention. |
| T22: shared statement docstring allegedly mislabels section measurability as added (r9g1). | Disagree; retained the comparison with canonical clause (ii). The two section premises are separate hypotheses in the existing Lean statement. |
| T30: Challenge docstring attributes nonnegative derivatives to PDF versions. | Accepted; it now explicitly says that the CDF has a nonnegative derivative wherever it is differentiable. PDF versions are described as equal to that derivative almost everywhere and integrating to one. |
| T30: shared statement docstring repeats the attribution. | Accepted; applied the same correction. The [canonical clause (ii)](work.json:743) and [Lean statement](SAP/P001b/Defs/WholeW2.lean:57) both differentiate the CDF. No derivatives of PDF versions are asserted. |

For T22, [Definition 1.2.2](work.json:45) requires the compositions to be random variables; [canonical clause (ii)](work.json:199) specifies a fixed function. The [Lean premises](SAP/P001b/Defs/WholeW1.lean:185) separately require both response sections to be measurable on the covariate space. Composition measurability does not supply those premises in general. The [current round-5 instruction](revise-fw5.md:13) explicitly says that using a wrong-credit row for its own statement makes the target restricted; the [row status](work.json:262) remains wrong_credit. This is a current instruction, as well as a mathematical scope difference under the [canonical-precedence rule](brief.md:30) and [extra-hypothesis rule](brief.md:47). The reports' measurable-section examples establish admissible instances but do not establish the unqualified implication. The prior third-rung account supplies further detail.

Only the T30 doc comments in Challenge/Part2.lean and Defs/WholeW2.lean change. Every definition body, theorem statement, bridge, and proof remains unchanged, including all shared definitions used by other targets. T30 stays whole. Both JSON files are regenerated with the same 19 theorem names, decisions, restrictions, dependencies, and kernel settings.

Round-5 verification completed: all 32 SAP Lean modules rebuilt in dependency order with `sap-lean`, one process at a time. Fresh `#print axioms` output for all 19 Solution theorems lists exactly `propext`, `Classical.choice`, and `Quot.sound`. All 19 compiled Challenge/Solution types and universe parameters match each other and the pre-edit snapshot. Both JSON files parse; source comparisons confirm that only the two T30 doc comments changed. Every SAP file remains within 300 lines (maximum 295), and every Lean module sets both implicit-variable options. Logs and results: `scratch/declaration-round5-build.log`, `scratch/axioms.log`, and `scratch/declaration-round5-validation.json`. No open glue tasks remain; no fresh external-kernel run is claimed.

## Declaration review round 6

All three T22 findings in [r10g1's findings](fw/round6/T22/r10g1/findings.json) and [report](fw/round6/T22/r10g1/REPORT.md) are accepted under the explicit author decision of 2026-11-04. The [current label rule](revise-fw6.md:13) makes coverage decisive regardless of donor provenance, and the [usual-condition rule](revise-fw6.md:14) expressly presupposes measurable response sections. These instructions supersede the earlier wrong-credit classification rule and composition-only scope reading used in the historical sections above.

| Finding | Action |
|---|---|
| T22 is incorrectly labelled restricted for response-section measurability. | Changed the manifest decision to whole and restriction to null. The current statement contains all three canonical clauses under the presupposed usual conditions. |
| T22's Challenge restriction paragraph excludes cases outside the author's reading. | Removed it. The docstring now says that the usual measure-theoretic conditions are assumed, names measurable response sections and integrability where expectations occur, and states all three clauses in full. |
| T22's shared statement docstring calls section measurability an added, non-usual hypothesis. | Replaced that scope description with the same usual-condition convention and complete three-clause description. The definition body remains unchanged. |

Checked every clause of [the canonical assertion](work.json:199) against [T22WholeStatement](SAP/P001b/Defs/WholeW1.lean:179): clause (i) includes the complete T21 electorate witness, response representation, constant covariates and positivity; clause (ii) is the fixed measurable-response conditional-independence implication; clause (iii) gives the discrete ATE identity with both summable population-weighted observed-arm means, under explicit conditional independence and uniform positivity. Those last two assumptions remain substantive premises of that canonical clause. The theorem's broader arbitrary-measurable-space formulation includes the author's Borel setting. No clause is dropped, and no mathematical premise or conclusion is changed.

Also checked the four retained refutations against their printed settings under [the current reading rule](revise-fw6.md:15). T25's one-atom law at zero is integer-valued; T29's uniform density versions are genuine nonnegative integral PDFs; T31's closed fat-Cantor subtype carries the stated Borel probability law and integral PDF; and T34's normalized negative-rectangle density gives jointly continuous coordinates and a measurable printed event. None of these printed claims requires an additional independence assumption, nonnegative outcomes, or strictly positive integer values that its witness violates. Their labels and disclosed witness omissions remain unchanged. T36 stays restricted for its listed substantive omissions.

Only T22's two doc comments change among Lean sources. All shared definition bodies, theorem statements, bridges, Solution proofs, theorem names, and credited-row uses are unchanged. The manifest changes only T22's decision and restriction. The Comparator configuration is regenerated with the same 19 names and kernel settings. Current counts are 14 whole, 1 restricted, 4 refuted, and 0 omitted; all 19 theorems remain proved, with no open glue tasks.

Round-6 verification completed: all 32 SAP Lean modules rebuilt in dependency order with `sap-lean`, using one Lean process. Fresh `#print axioms` output for all 19 Solution theorems lists exactly `propext`, `Classical.choice`, and `Quot.sound`. All 19 compiled Challenge/Solution types and universe parameters match each other and the pre-edit snapshot. Both JSON files parse with the exact target and theorem lists. Source comparisons confirm unchanged definition bodies, statements, bridges, and proofs; only the two T22 doc comments changed. Every SAP file remains within 300 lines (maximum 297), and every Lean module sets both implicit-variable options. Results and logs are in `scratch/declaration-round6-validation.json`, `scratch/declaration-round6-build.log`, and `scratch/axioms.log`. All three findings are resolved, with no open glue tasks. No fresh external-kernel run is claimed.

## Declaration review round 7

Checked the T36 entry in [r11g4's findings](fw/round7/T36/r11g4/findings.json) and [report](fw/round7/T36/r11g4/REPORT.md), and only the P001-T36 entry of the multi-target [refutation recheck](fw/round7/T36/refcheck-base-b1/refcheck.json). They assess different readings of the zero-slice conclusion.

| Finding | Decision and action |
|---|---|
| T36 faithful/none: the specified density facts and omissions match the canonical example. | Agree. Kept the positive Lean statement, existing proof, restricted label, and every listed omission. |
| T36 not_faithful/major, weaker_reading: the infinite zero slice violates the finite-existence premise of a real pointwise marginalization identity. | Accept the domain objection and correct the prose. Removed the introduction claiming a counterexample to finite marginalization at every y. The Challenge docstring, manifest restriction, and current report now explicitly disclose that these facts establish no refutation on the assumed finite-real domain. |

The [current existence convention](revise-fw7.md:15) and [refutation rule](revise-fw7.md:16) apply: a divergent extended integral cannot witness a failed equality between defined finite real quantities. The zero-slice equality in [T36Statement](SAP/P001b/Defs/Part4.lean:82) is an extended nonnegative integral equal to infinity. It is never used as a finite real marginal value, and no finite slice integral at zero is assumed or assigned a totalized real value. No inconsistent finite-existence hypothesis is added to retain a purported refutation.

I do not accept a broader conclusion that the positive Lean assertion itself must be discarded. The [canonical target is a counterexample package](work.json:1125), and [its explicit assertions](work.json:1128) include this very function, joint normalization, divergence at zero, and finite nonzero slices. The [retained conjunction](SAP/P001b/Defs/Part4.lean:79) states precisely a disclosed subset of those assertions, proved by [the existing donor](AronowAudit/P001/Wave1/Gap/GLP0013B1.lean:247). These are facts of the canonical example, rather than unrelated helper lemmas. They remain a defensible restricted statement while the refutation of the identity under the task's finite-existence reading is not established. No new counterexample, finite-slice identity, or marginal derivative argument is supplied.

The only Lean edit is the T36 Challenge docstring. No shared definition, theorem type, bridge, or proof changes. The manifest changes only T36's restriction disclosure; the Comparator configuration is regenerated with the same 19 theorem names and kernel settings. Counts remain 14 whole, 1 restricted, 4 refuted, and 0 omitted; all 19 theorems remain proved, with no open glue tasks.

Round-7 verification completed: all 32 SAP Lean modules rebuilt in dependency order with `sap-lean`, using one Lean process. Fresh `#print axioms` output for all 19 Solution theorems lists exactly `propext`, `Classical.choice`, and `Quot.sound`. All 19 compiled Challenge/Solution types and universe parameters match each other and the pre-edit snapshot. Both JSON files parse with the exact target and theorem lists. Source checks confirm that only the T36 Challenge doc comment changed; all shared definition sources and proofs are unchanged. Every SAP file remains within 300 lines (maximum 297), and every Lean module sets both implicit-variable options. Results and logs are in `scratch/declaration-round7-validation.json`, `scratch/declaration-round7-build.log`, and `scratch/axioms.log`. There are no open glue tasks. The domain objection is addressed; the broader faithfulness disagreement is explained and cited above. No fresh external-kernel run is claimed.
