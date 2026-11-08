P008a packages exactly P008-T1 through P008-T14. P008b is outside this unit.

| Decision | Targets |
| --- | ---: |
| whole | 8 |
| restricted | 6 |
| refuted | 0 |
| omitted | 0 |

All 14 Challenge statements have matching proved Solution theorems and retain their fully qualified names. There are no open glue tasks and no omitted targets.

The canonical statement, definitions_needed and standing assumptions govern scope. Audit notes and finite_lemmas are not premises and do not remove clauses. The six counterexample targets already assert the respective counterexamples or reading failures; the retained theorems agree with those assertions. They are therefore whole or restricted, rather than refuted, under the clarified decision rule. No theorem contradicts its canonical statement's own assertion.

| Restricted target | Exact limitation relative to the canonical claim |
| --- | --- |
| P008-T1 | Retains the explicitly labelled 121-node observation and its within-count swap, both normalized supports, and both directions of the four-node tail discrepancy. Does not quantify over every initial 60-treated observed assignment or assert the existence of a relabelling that puts it into the recorded observation form. |
| P008-T2 | The spatial cumulative-test component is confined to Euclidean circles in a measurable whole field, with integrability for every assignment on every evaluated circle; positive finite circle mass and nonempty arms on the positive-probability conditional support make its averages and ratios meaningful. Imputability is asserted for the cumulative statistic on that support, rather than separately for each circle mean. The documentary seven-lottery design, its identification with a particular conditional reference law, and the empirical significance/withdrawal conclusions are not formalized. General finite-law calibration, conditioning, Bernoulli-given-count uniformity and both directions of the four-node law discrepancy are retained. |
| P008-T4 | Retains complementation, the one-third inclusive-tail lower bound for every linear contrast functional, the mass and level obstruction for every nonempty rejection set, general exact calibration, the IID sampled-permutation bound, and the sum 7.996 of the displayed estimates. Omits the reconstructed unrounded observed statistic 7.99649 and its asserted rounded value 8.00, the six reconstructed cumulative statistics and their exact observed p-value 1/3. The interpolated-percentile counterexample is not repeated in this theorem; it is stated in T3. |
| P008-T6 | The weighted-contrast, OLS weight/residual and sandwich-to-score-HAC identities hold for every nonnegative cutoff and general distance array when both arm counts are at least one; no off-diagonal separation premise restricts that representation. Only the HC0 specialization requires a zero diagonal and every off-diagonal distance to exceed the cutoff. Retains the reconstructed toy-node cutoff and interval equalities, the additive-score covariance formula, the diagonal/off-diagonal variance decomposition and exact cutoff condition. The geometric sufficient bound remains restricted to the Euclidean plane, a measurable whole field and coefficient integrands vanishing beyond the effect range on the whole plane, with positive finite circle masses. Omits the numerical smallest-distance approximation 1.4295... and reproduction of the ten printed interval pairs to three decimals. Also omits the canonical warning that cutoff c = r need not suffice; the counterexample referenced as P008-T5 is not asserted by this declaration. |
| P008-T8 | The fixed-radius spatial-risk component requires Euclidean circles and a measurable whole field; positive finite circle masses and integrability of exactly the positive-weight one-node overrides make the averages meaningful. Retains the generic convex-mixture probability bounds and identity, bounds against any common lower and upper effect bounds, equal-weight and constant-effect algebra, the -4 binary example, sorted finite-sample rescaling, the three reported values divided by four, and the comparisons -0.0321 < -0.0304 and -0.008025 < -0.0076. Does not explicitly state finite minimum/maximum values or a separate order-statistic characterization beyond the type-7 formula on a sorted sample, and does not construct the joint node/radius/point sampling probability space. The -4 example uses the labelled counting model of T7 and does not assert its planar realization. The numbers -0.0304, -0.0321 and 0.0336 enter only as supplied rational constants: omits the identification of -0.0321 as the actual observed sum and of -0.0304 and 0.0336 as the actual 0.025 and 0.975 sharp-null permutation percentiles of the summed AMR statistic on the stated 1-2.5 km window and grid, and hence the empirical assertion that the observed sum lies below the lower reference quantile (only the numerical comparison is stated). Also omits the specification of the actual application grid and unit weights, the identification of the actual equal-radius mean estimate with -321/40000 = -0.008025 (printed as approximately -0.0080, a 0.8 percentage-point reduction) or with the normalized sampling target, and any certification that the divided values are reconstructed permutation outputs; only exact division by four and comparison are established. |
| P008-T11 | Retains the exact sums of the displayed five and eight estimates, the full rounding envelope for the five estimates, the exclusion of a displayed sum 12.38, and the strict comparison with every number displayed as 7.97. Omits the identification of the actual unrounded cumulative effect as 7.99649 and its corrected display as 8.00; the rounding envelope alone does not establish that actual display. The kept empirical permutation percentiles -7.97 and 7.97 are not certified as outputs. |

## Definitions, bridges and proof scope

The route is shared Mathlib-only SAP definitions. Defs/Part1–Part4 contain finite laws, circles, estimators and explicit examples; Part5–Part8 contain the fourteen statement definitions. Challenge and Solution import the same compiled Defs modules. Project declarations are not copied under their project names.

| Bridge group | Correspondence and proof |
| --- | --- |
| toLaw; mass_eq, expect_eq, prob_eq, cov_eq, var_eq | The adapter keeps the mass function, nonnegativity and total mass. Each equality is rfl. |
| uniform_eq, conditional_eq, tail_eq, bernoulli_eq | Uniform and conditional masses, inclusive tails and Bernoulli product masses have identical bodies; rfl or Iff.rfl. |
| toModel; circle_eq, circle_measure_eq, circle_mass_eq, average_eq, circle_outcome_eq | The adapter keeps the field, nodes, node membership, measure and outcomes; all correspondences are rfl. |
| marginal_eq, amr_eq, risk_eq | The marginal sums and normalized averages agree after the two adapters; rfl. |
| rectangle_eq, bandwidth_model_eq | The concrete spatial witnesses have identical data after toModel; rfl, using proof irrelevance for validity fields. |
| line_distance | Existing AronowAudit.P008.line_embedding_distance gives the Euclidean distance of the rational x-axis embedding. |

Solution proofs instantiate existing declarations, assemble their conclusions and transport through these correspondences. Other glue is finite arithmetic on exported values, substitution of mean differences, and finite-sum algebra. T6 splits the exported covariance sum into diagonal and off-diagonal terms; no new probabilistic or geometric argument is introduced. T14 uses finite real mean data directly and rewrites the given node-effect definitions, avoiding unnecessary integrability conditions on unused spatial schedules.

Earlier referee rounds changed decisions, docstrings and documentation; the later whole versions of T7, T9 and T10 are described below. The certification repair changes only the T7_L5 proof implementation, without changing shared definitions or theorem statements. Positive finite circle masses, required integrability, positive conditional-event probability and nonempty arms guard the uses of averages and ratios. Conditional spatial imputability is restricted to that support. Finite quantiles use nonempty samples and valid levels; the rescaling clause assumes sorted observations and a positive divisor. T6's geometric integrands vanish on the relevant circles, so their averages do not depend on the nonintegrable branch.

T5 concerns finite linearization variances. Its canonical statement itself marks the limiting-variance consequence as not required of a formalization; no audit note is needed to exclude that optional assertion. The earlier T7 version was confined to indexed cells; the current whole version includes its planar realization, finite circle measures and sampling identities. T11 certifies the rounded table arithmetic, not the actual reconstructed unrounded statistic.

## Round 1 findings retained in the revision

Referee A's T6 separation-scope finding was accepted and fixed: the matrix representation now requires only a nonnegative cutoff and both arms, while the zero-diagonal and separation hypotheses occur only inside the HC0 specialization. The proof is direct use of [matrix_hac_reduction](/home/ubuntu/sap/wt/ARCH-P008a/AronowAudit/P008/P008_Audit.lean:1101), [hajek_weighted_contrast](/home/ubuntu/sap/wt/ARCH-P008a/AronowAudit/P008/P008_Audit.lean:1151) and the exported HC0 results. Both round-two referees confirm the repair. Referee B's round-two report withdraws its earlier acceptance of the old disclosure. Other round-one scope limitations remain unless superseded below.

The preceding round applied refuted labels and printed-falsity openings too broadly. The clarified canonical-assertion rule supersedes those labels; the final decisions and present docstrings above govern.

## Round 2 referee findings and actions

Both supplied findings.json and REPORT.md files were checked against work.json and the actual theorem definitions. No round-two reading.md files are present in this worktree; the supplied round-two reports and their descriptions of the saved readings provide the review evidence. The mathematical sources were inspected directly.

| Target | Referee A | Referee B | Action after independent check |
| --- | --- | --- | --- |
| P008-T1 | correct_restricted | correct_restricted | Kept the fixed-observation restriction and mathematical statement; restored restricted under the canonical-assertion rule and named the identification reading. |
| P008-T2 | correct_restricted | correct_restricted | Accepted both assessments; restrictions, statement and proof retained. |
| P008-T3 | correct_whole | correct_whole | Kept the complete spatial counterexample; whole because this proves the canonical counterexample assertion rather than contradicting it. |
| P008-T4 | correct_restricted | correct_restricted | Accepted both assessments; empirical reconstruction omissions remain explicit. |
| P008-T5 | not_faithful | not_faithful | Accepted both attribution findings; restored whole, identified outcome-range sufficiency as the false reading, and removed the printed-falsity opening. |
| P008-T6 | correct_restricted | correct_restricted | Accepted both confirmations of the earlier scope repair; restricted geometry and numerical omissions retained. |
| P008-T7 | not_faithful | correct_restricted | Accepted A's missing-spatial-realization finding; restored restricted and removed the printed-falsity opening. B's refuted acceptance is rejected below. |
| P008-T8 | correct_restricted | correct_restricted | Accepted both assessments; spatial assumptions, absent sampling construction and other omissions remain explicit. |
| P008-T9 | not_faithful | not_faithful | Accepted both attribution findings; restored restricted and described failure of the archived computational reading without falsifying the article's cutoff instruction. |
| P008-T10 | correct_restricted | correct_restricted | Accepted both assessments; strict-positivity omission retained. |
| P008-T11 | correct_whole | correct_whole | Relabelled restricted after checking the complete canonical statement; both whole assessments omit its actual 7.99649/8.00 correction. |
| P008-T12 | correct_whole | correct_whole | Kept all exact grid/output incompatibility facts; whole because these are the canonical assertion. |
| P008-T13 | correct_whole | correct_whole | Accepted both assessments; whole exact-grid statement retained. |
| P008-T14 | correct_whole | correct_whole | Accepted both assessments; whole corrected identity, equality characterization and numerical witness retained. |

T5: both referees are right about the attribution error. The canonical [statement](/home/ubuntu/sap/wt/ARCH-P008a/work.json:581) expressly identifies the outcome-range reading. The theorem's covariance 1/4 at node distance 2 shows why cutoff 1 fails to cover contribution dependence, so it cannot contradict guidance whose premise is absence of dependence beyond the cutoff. A's proposed continuation with a refuted decision is superseded by the clarified rule; B's whole classification matches the complete required finite counterexample. The docstring identifies that reading and states that printed-interval coverage is not established.

T7: A is right, and I disagree with B's acceptance of refuted. The canonical [statement](/home/ubuntu/sap/wt/ARCH-P008a/work.json:1248), items 1–3 and 7, requires a single planar field, geometric circles and outcomes at their centres. [Defs/Part4.lean](/home/ubuntu/sap/wt/ARCH-P008a/SAP/P008a/Defs/Part4.lean:50) supplies indexed cells and means, not that realization. B's [report](/home/ubuntu/sap/wt/ARCH-P008a/referees/round2/b/REPORT.md:106) relies on permission in the audit note to check the counting components. That note cannot remove the geometric clauses. The limited counting statement remains proved and is explicitly restricted.

T9: both attribution findings are accepted. The canonical [statement](/home/ubuntu/sap/wt/ARCH-P008a/work.json:1734) distinguishes the article's cutoff instruction from the archived cutoff-plus-position computation and describes its refutation as a computational one. The theorem establishes that model's grid dependence and its incompatibility with the positive printed width. It neither contradicts the article's dependence-cutoff guidance nor proves that a printed interval was produced by this model. No historical note is used to change those assertions. The canonical counterexample is retained with its intermediate-vector/kernel omissions, hence restricted.

T11: I disagree with both whole verdicts ([A](/home/ubuntu/sap/wt/ARCH-P008a/referees/round2/a/findings.json:109), [B](/home/ubuntu/sap/wt/ARCH-P008a/referees/round2/b/findings.json:107)). The canonical [statement](/home/ubuntu/sap/wt/ARCH-P008a/work.json:2036) includes the corrected actual cumulative effect 8.00 and unrounded reconstruction 7.99649. The two credited [declarations](/home/ubuntu/sap/wt/ARCH-P008a/AronowAudit/P008/P008_Audit.lean:245) establish printed sums and a rounding box, without identifying that actual effect. The box crosses the 7.995 rounding boundary; for example the five displayed numbers each decreased by 1/2000 satisfy the hypotheses and sum to 7.9935. Thus it does not force the actual display 8.00. Restricting is required even though the exact arithmetic clauses (a)–(c) are all present. The empirical percentile outputs kept by the correction are also not certified.

T1, T3 and T12: the earlier false-claim openings are removed as well. Their canonical statements explicitly assert the respective counterexamples or grid incompatibility ([T1](/home/ubuntu/sap/wt/ARCH-P008a/work.json:46), [T3](/home/ubuntu/sap/wt/ARCH-P008a/work.json:262), [T12](/home/ubuntu/sap/wt/ARCH-P008a/work.json:2099)). The theorems agree with those assertions. Referees accepted their mathematical content, but accepting refuted labels for agreement with a canonical counterexample is incompatible with the latest decision rule in [revise-ref2.md](/home/ubuntu/sap/wt/ARCH-P008a/revise-ref2.md:25). T1 remains restricted to its labelled observation; T3 and T12 are whole.

## Validation

All Defs parts and root, Bridge, Challenge part and root, Solution and scratch/Axioms.lean are rebuilt with /home/ubuntu/sap/tools/sap-lean in dependency order. All 14 dependency printouts contain only propext, Classical.choice and Quot.sound. The manifest and comparator configuration parse, cover precisely the assigned targets and retain every theorem name. Row partitions, Challenge/Solution signatures, imports, implicit-variable options, file lengths and docstring restrictions are checked again. Every SAP source file has at most 300 lines. There are no open proofs.

The supplied [Comparator result](/home/ubuntu/sap/wt/ARCH-P008a/SAP/P008a/verification/comparator-result.json) certifies all fourteen theorems for its recorded earlier snapshot. It predates the T6 scope repair and is historical evidence. This round changes no theorem type or proof relative to that repair; the rebuilt current package and comparator.json are ready for renewed external certification.

## Third-rung revision (Opus)

Open items after round 3: P008-T8 (referee a, `restriction_inaccurate`, minor) and P008-T8 (referee b, `restriction_inaccurate`, major). Both concern the same disclosure gap.

**Verdict: both referees are right.** The canonical [statement](work.json:1479) of P008-T8 opens with corrected text that is part of the claim, not an audit note: "For the unscaled sum of AMR estimates at the evaluated distances in the 1-2.5 km window, the 0.025 and 0.975 percentiles of the sharp-null permutation distribution are -0.0304 and 0.0336, respectively, and the observed sum is -0.0321. The observed sum lies below the lower reference quantile. Specify the actual grid and unit weights. [...] An equally weighted mean over the four radii indicated by Figure 8 would instead be approximately -0.0080, or a 0.8 percentage-point reduction for that explicitly normalized sampling target, with every permutation value divided by four as well." Formal clause (c) ends: "With m = 4 the printed values become -0.0304/4 = -19/2500 = -0.0076, -0.0321/4 = -321/40000 = -0.008025 and 0.0336/4 = 21/2500 = 0.0084, and -0.008025 < -0.0076 as -0.0321 < -0.0304."

The Lean statement ([Defs/Part7.lean](SAP/P008a/Defs/Part7.lean), `SAP.P008a.T8Statement`) contained, as its numerical conjunct, only

```
(-19 / 625 : ℝ) / 4 = -19 / 2500 ∧ (-321 / 10000 : ℝ) / 4 = -321 / 40000 ∧
(21 / 625 : ℝ) / 4 = 21 / 2500 ∧ (-321 / 40000 : ℝ) < -19 / 2500
```

and no empirical sample, permutation distribution, observed statistic or application grid. These constants could equally come from any other source. The generic `quantile7` rescaling conjunct holds for every sorted sample and does not single out the application's sample. So the theorem does not establish that -0.0304 and 0.0336 are the actual percentiles, that -0.0321 is the actual observed sum, or that it lies below the actual lower reference quantile. It also does not specify the actual grid and weights, and it does not identify the actual equal-radius estimate. The previous restriction said only that "the three reported values divided by four" are retained. That describes the arithmetic, but it does not disclose that the corrected text's identification of those values was dropped. Under referee-fix rule 1 (clause completeness), this omission must be listed.

**Changes.**

1. Restriction disclosure: the existing T8 restriction paragraph is kept and extended, in both the Challenge docstring ([Challenge/Part1.lean](SAP/P008a/Challenge/Part1.lean), `SAP.P008a.T8`) and `manifest.json`. The extension says that -0.0304, -0.0321 and 0.0336 enter only as supplied rational constants. It lists as omitted: the identification of -0.0321 as the actual observed sum; the identification of -0.0304 and 0.0336 as the actual 0.025/0.975 sharp-null permutation percentiles on the 1-2.5 km window and grid; the resulting empirical assertion that the observed sum lies below the lower reference quantile; the specification of the actual grid and unit weights; the identification of the actual equal-radius mean estimate with -321/40000 = -0.008025 (printed as approximately -0.0080, 0.8 percentage points) or with the normalized sampling target; and any certification that the divided values are reconstructed permutation outputs. This covers both referees' suggested wordings.
2. Clause restored by glue: the explicit comparison in clause (c), "as -0.0321 < -0.0304", was not stated (only its quotient by four was). It is now the conjunct `(-321 / 10000 : ℝ) < -19 / 625`, appended inside the numerical block of `T8Statement`. Its Solution proof is `by norm_num`, which is one-line arithmetic on constants. The four project conjuncts are still taken from `AronowAudit.P008.reported_values_divided_by_four`. The statement only gains a true numerical conjunct; no other conjunct changed. The docstring says that only the numerical comparison is stated, not the empirical quantile assertion.
3. Decision: T8 stays `restricted`. It is not `refuted`: nothing in the formalization contradicts the canonical assertion. It is not `whole`, because of the omissions above and the spatial-hypothesis, extremum, order-statistic, sampling-space and planar-realization omissions already disclosed.

No other target changed. Every other theorem keeps its statement, proof and fully qualified name. The round-3 referees found no other adverse items.

**Rebuild.** Defs Part1-Part8, Defs root, Bridge, Challenge Part1 and root, Solution and scratch/Axioms.lean were recompiled with /home/ubuntu/sap/tools/sap-lean in dependency order (log: scratch/opus-build.log). All 14 theorems print only `propext`, `Classical.choice` and `Quot.sound`. Proof placeholders appear only in Challenge stubs. No forbidden token appears elsewhere, and every SAP file starts with both implicit-variable options. `manifest.json` and `comparator.json` parse. `comparator.json` is unchanged: same 14 theorem names, no definition names, same permitted axioms and kernels. The stored Comparator result in SAP/P008a/verification predates this change (T8Statement gained a conjunct), so it is historical and the package needs fresh certification.

Counts after this revision: whole 5, restricted 9, refuted 0, omitted 0.


## Declaration review round 1

| Declaration | Finding | Action |
| --- | --- | --- |
| SAP.P008a.T6 (P008-T6) | restriction_inaccurate, minor; fingerprint 552f8b919e3e286d | Accepted. Added the missing omission to the Challenge docstring, manifest restriction and restriction table above. T6 remains restricted and proved. |

The [reviewer finding](/home/ubuntu/sap/wt/ARCH-P008a/fw/round1/T6/r1g2/findings.json:3) is correct. The canonical [T6 statement](/home/ubuntu/sap/wt/ARCH-P008a/work.json:929), part (d), asserts both the sufficient bound and the warning that a cutoff c = r need not suffice. [T6Statement](/home/ubuntu/sap/wt/ARCH-P008a/SAP/P008a/Defs/Part6.lean:135) concludes only that the coefficient average vanishes for far pairs under d + r ≤ c. It does not assert the failure example at c = r. The separate T5 declaration supplies that counterexample in this unit, but does not include it in T6's own statement.

The disclosure now adds: "Also omits the canonical warning that cutoff c = r need not suffice; the counterexample referenced as P008-T5 is not asserted by this declaration." No shared definition, theorem type or proof was changed. The same review file's T7–T10 entries are faithful with no open items and require no changes. All existing T8 revisions are preserved.

All Defs parts and root, Bridge, Challenge part and root, Solution and the scratch dependency-print file are recompiled with sap-lean in dependency order. All fourteen theorem names remain proved with only propext, Classical.choice and Quot.sound. The JSON files, exact restriction disclosure, implicit-variable options, permitted imports and file lengths are checked again. comparator.json is revalidated for the same fourteen theorems; its configuration is unchanged. Earlier external certification remains historical; this documentation repair adds no mathematical change to the reviewed statements.

Counts: whole 5, restricted 9, refuted 0, omitted 0; proved 14, open glue 0.


## Whole versions (new proofs)

The following switches supersede the earlier restricted versions of these three targets.

- **P008-T9 (`SAP.P008a.T9`)** is now `whole` with type `SAP.P008a.T9WholeStatement`. Files: `SAP/P008a/Challenge/Part1.lean`, `SAP/P008a/Solution.lean`, `SAP/P008a/manifest.json`, `SAP/P008a/Defs/WholeW1.lean`, `SAP/P008a/WH/W1/Common.lean`, `SAP/P008a/WH/W1/Leaves.lean`, `SAP/P008a/WH/W1/Proofs/T9.lean`, and `SAP/P008a/WH/W1/P/T9_L1.lean`.

  Old restriction now removed: Establishes a counterexample to the reading that the transcribed archived cutoff-plus-position rule implements the physical-cutoff specification, not to the article's instruction to cover contribution dependence. Retains the complete spatial construction with genuine circle integrals, identical data at radius 1/5 on both grids, its score vector, variances 1 and 1/2 at the two positions, and the reconstructed toy sixth-row zero-variance/positive-width incompatibility. Omits the explicitly displayed least-squares coefficient, residual and contrast-weight vectors and the two entry-by-entry kernel masks.

- **P008-T10 (`SAP.P008a.T10`)** is now `whole` with type `SAP.P008a.T10WholeStatement`. Files: `SAP/P008a/Challenge/Part1.lean`, `SAP/P008a/Solution.lean`, `SAP/P008a/manifest.json`, `SAP/P008a/Defs/WholeW1.lean`, `SAP/P008a/WH/W1/Common.lean`, `SAP/P008a/WH/W1/Leaves.lean`, `SAP/P008a/WH/W1/Proofs/T10.lean`, and `SAP/P008a/WH/W1/P/T10_L1.lean`.

  Old restriction now removed: Retains invariance for general distance arrays with both arms present, the all-pairs score-sum square and zero identity, variance 1 on both example grids, the reconstructed toy HC0 identity and its equality to cutoff zero, and the archived sixth-row zero variance. Omits the strict-positivity characterization when some residual is nonzero.

- **P008-T7 (`SAP.P008a.T7`)** is now `whole` with type `SAP.P008a.T7WholeStatement`. Files: `SAP/P008a/Challenge/Part1.lean`, `SAP/P008a/Solution.lean`, `SAP/P008a/manifest.json`, `SAP/P008a/Defs/WholeW1.lean`, `SAP/P008a/WH/W1/Common.lean`, `SAP/P008a/WH/W1/Leaves.lean`, `SAP/P008a/WH/W1/Proofs/T7.lean`, and `SAP/P008a/WH/W1/P/T7_L1.lean`, `SAP/P008a/WH/W1/P/T7_L2.lean`, `SAP/P008a/WH/W1/P/T7_L3.lean`, `SAP/P008a/WH/W1/P/T7_L4.lean`, `SAP/P008a/WH/W1/P/T7_L5.lean`, `SAP/P008a/WH/W1/P/T7_L6.lean`.

  Old restriction now removed: Retains both binary-outcome examples on labelled sets of 40000 points for each node and radius: the Bernoulli design, exact means, effects, observed estimates, normalized probabilities, all normalized radius weightings and the impossible probability difference -4. Omits the specified planar centres and radii as geometric objects, the rational-direction construction and its norm/distinctness/separation proofs, the planar field size 640004, the geometric identification and cardinality of its circles, and the outcomes at the four centres. The theorem establishes the finite counting model, not its claimed planar realization.

Validation: `python3 /home/ubuntu/sap/tools/rebuild_sap.py . P008a` rebuilt all 27 modules from scratch with a clean token scan. `scratch/P008aSwitchedAxioms.lean` imports `SAP.P008a.Solution`; `#print axioms` for T9, T10 and T7 reports only `propext`, `Classical.choice` and `Quot.sound` for each theorem.

## Strict certification repair

The supplied strict run failed only in con-ron, at `SAP.P008a.WH.W1.T7_L5_proof` (fold position 38088): the checker exhausted its weak-head reduction fuel. Nanoda and Lean accepted that snapshot. The failure artifact is preserved in scratch/certification-failure-before.json.

The concrete proof simplified the mass and integral expressions directly over `RiskCell = Fin 40000`. The repair factors the same finite Dirac-sum calculations into `dirac_sum_total`, `dirac_sum_integrable` and `dirac_sum_integral` in [T7_L5.lean](SAP/P008a/WH/W1/P/T7_L5.lean). Their index set is a variable. The proofs only instantiate Mathlib's finite measure-sum, Dirac integrability and Dirac integral rules and use finite-sum congruence. T7_L5 then specializes those facts and explicitly rewrites the cardinality using `Finset.card_univ` and `Fintype.card_fin`. This avoids simplifying the concrete 40,000-term expressions inside the leaf proof. It introduces no new mathematical argument.

All fourteen theorem names and statements, including the whole versions of T7, T9 and T10 already present at the start of this repair, are unchanged. Defs, Bridge, Challenge, the assemblies and Solution are byte-for-byte unchanged. No assumptions were added and no statement was weakened. The current counts are whole 8, restricted 6, refuted 0, omitted 0; proved 14, open glue 0. The earlier counts and referee discussions describe earlier snapshots.

The manifest now records the three factored proof helpers. Existing supporting declarations for the whole versions are recorded separately from the credited work.json rows; the credited rows and their use decisions are unchanged. The JSON is compacted to remain within the file-length limit. comparator.json is revalidated with the same fourteen names, permitted dependencies and three-kernel commands; no kernel fuel or verification setting is changed.

Validation: all 27 SAP modules and scratch/Axioms.lean rebuilt successfully with sap-lean in dependency order. Every one of the fourteen dependency printouts lists only propext, Classical.choice and Quot.sound. Manifest coverage, credited-row partitions, matching Challenge/Solution statements, required options and imports, restrictions, and the 300-line limits pass scratch/verify_package.py. Only WH/W1/P/T7_L5.lean differs among the Lean sources from the supplied failed snapshot.

The fresh strict command `python3 /home/ubuntu/sap/tools/run_comparator.py . P008a` was attempted after the local rebuild, but stopped before rebuilding or running a kernel: `OSError: [Errno 30] Read-only file system` while creating `/home/ubuntu/sap/cert/P008a-20261104T160350Z`. Its output is in scratch/certification-repair-comparator.log. Standalone checker executables were not available on PATH or at the tested local tool paths. Therefore con-ron acceptance of the repaired snapshot is unconfirmed. The supplied failed comparator-result.json remains historical evidence of the preceding snapshot; it is not replaced by a success claim. [repair-status.json](SAP/P008a/verification/repair-status.json) records the current local checks and the environmental block. A strict rerun remains necessary in the orchestrator environment that can write its certification directory.
