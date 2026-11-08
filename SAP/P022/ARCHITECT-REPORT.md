P022 — *Sharp bounds on the variance in randomized experiments*.

**10 whole, 6 restricted, 2 refuted, 0 omitted; 18 proved, 0 open glue.** All theorem names remain `SAP.P022.T1` through `SAP.P022.T18`. Project sources, `work.json`, the brief, and referee files were not edited.

All five negative-result docstrings begin “The printed claim is false:”. T1, T7 and T9 remain partial statements of their canonical counterexample descriptions and are labelled restricted under the [clause-completeness rule](brief.md#L49); their restriction fields enumerate the unstated facts. T5 and T18 are labelled refuted under the [refutation rule](brief.md#L45). No negative result is labelled whole. T5 includes the general equality characterization as well as its explicit counterexample. T18 now asserts the existence of an admissible sequence for which the joint conclusion of printed Lemma 2 fails, even allowing the integer functions to be chosen for that sequence; this contradicts the printed assertion without imposing a uniform-in-sequence reading.

## Restrictions and omissions

- **P022-T1 (restricted)**: Retains only witness A's conditions 1–3, population and sampled CDF distances equal to one, infinite scaled-tail limsups, and failure of Lemma 2. Omits A's explicit boundedness/condition-4 assertion, its individual CDF and left-CDF values at zero and at the displayed moving threshold, the finite probability-one and N-times-probability identities, and the partition proof-step assertion. Omits all of witness B: the perturbed four-corner population, its boundedness and nonsingular limiting law, its conditions 1–3 and CDF-distance assertions, and its probability-one and divergent-tail assertions.
- **P022-T6 (restricted)**: The limit conclusion chooses K1, K0 and the constant after the sequence, parameters, epsilon1 and xi are fixed, and asserts only their displayed tail bounds and identities; it does not assert positivity or monotonicity of those selected K functions, dependence only on the limiting law, or a minimization result. The earlier six rate bounds and Lemma 2 conclusions remain explicit hypotheses, as in canonical parts (c)–(d). The finite reciprocal CDF-threshold implication additionally requires C > 0; the remaining finite statements still allow C = 0. The separate lower-endpoint allocation is not asserted.
- **P022-T7 (restricted)**: Retains the four-corner conditions 1–3, atom-left convergence, bounded outcomes, and the two infinite scaled-tail limsups. Omits the zero-threshold finite probability-one identities, the N=4r moment/covariance/variance and decomposition calculations, the displayed 51200/(N delta^2) bound and centered-error limit, convergence of the scaled absolute error to 1/2, convergence of its threshold probabilities to one, and convergence of the scaled probability sequence to infinity.
- **P022-T9 (restricted)**: Retains the all-ones negative-output example and both endpoint discrepancy formulas under the cell-width condition. Omits the separate assignment-by-assignment observed-data/effect assertions, marginal variance/covariance and partition/selected-value/weight calculations, the explicit shifted-weight-sum identity, and the translation-invariance comparison.
- **P022-T10 (restricted)**: Retains the fixed-observed-sample identity and limit, and the actual-variance limit under uniformly bounded marginal variances and eventual fixed arm sizes. Drops the exact finite-N remainder identity for actual randomization variance, the (0,1) sample formulas and numerical examples, and any assertion about execution of the R branch.
- **P022-T17 (restricted)**: Drops Remark 4's narrowest-Wald-interval assertion. Adds explicit integrability of the first and second coordinate moments, centered squares and centered product for every compatible law, a nonempty covariance image bounded above and below, positivity of the limiting upper bound, and positivity of every finite estimated upper variance. The coverage assertion also requires the normal critical-value set to be nonempty and bounded below. Retains the CLT, gamma range, actual-variance limit, and guarded coverage limit/lower bound.

No target is omitted and no glue task remains open. Whole targets are T2, T3, T4, T8, T11, T12, T13, T14, T15 and T16.

## Referee findings and actions

Each entry with issues in either findings file was checked against `work.json` and the Lean declarations. Referee suggestions were treated as diagnostic advice. The current brief’s classification and clause-completeness rules govern the corrections.

| Referee finding | Assessment and action |
| --- | --- |
| A, T18 | Accepted the polarity objection. T18 is labelled refuted and its docstring starts with the required sentence. Declaration review round 1 subsequently identified a quantifier defect in the first repair; the current statement asserts a sequence-specific failure, as detailed below. |
| B, T18 | Same polarity correction. The current explicit existence of a sequence-specific failure contradicts the affirmative printed lemma. See [the refutation rule](brief.md#L45) and the round 1 correction below. |
| A, T1 | Accepted all coverage observations. The statement still contains witness A’s hypotheses, exact distance-one facts and infinite limsups. The docstring and manifest enumerate the missing individual CDF/left-limit and finite-probability assertions, the boundedness/condition-4 and partition assertions, and all of witness B. |
| B, T1 | Accepted the missing second-witness and left-limit/UI observations. These are now explicitly disclosed and the decision is restricted. See [the canonical witnesses](work.json#L1433). |
| A, T5 | Accepted the missing equality characterization and restored it. The corrected CDF-variance formula gives the positive coefficient times G(1−G); cancellation and elementary arithmetic give equality with the quarter-factor expression exactly when G=1/2. The six unordered treatment groups are also recorded by the binomial count. |
| B, T5 | Same restoration, over every valid Design, outcome vector and threshold. Valid designs imply m<N. This uses the existing usable T4 row, `AronowAudit.P022.Wave1.cdf_variance_corrected_proof`, as additional support for the ancillary canonical clause. See [that clause](work.json#L619). |
| A, T7 | Accepted: infinite limsup does not assert convergence in probability, probability tending to one, or sequence divergence. The restriction now lists all missing finite calculations, the displayed rate, and each stronger limit. B accepted whole coverage, but its reading also records only the infinite limsup; the explicit canonical stronger limits therefore require this disclosure. See [the canonical T7 text](work.json#L1806). |
| A, T9 | Accepted: neither the shifted-weight-sum identity nor the translation comparison is a conclusion of the retained theorem. The separate witness calculations and these two omitted assertions are now listed. B’s whole verdict does not remove these canonical clauses. Restoring a general translation theorem would require an argument beyond the selected discrepancy facts, so it was not added. See [the canonical T9 text](work.json#L776). |
| A, T17 | Disagree with the suggested whole label. The governing canonical statement explicitly includes the narrowest-Wald-interval assertion; the note excluding it is diagnostic history under the stated precedence rule. The credited row contains CLT and coverage conclusions but no optimality conclusion. T17 remains restricted, with the new existence guards also disclosed. See [the canonical statement](work.json#L1329), [the precedence rule](brief.md#L23), and [the credited row](AronowAudit/P022/Wave1/Gap/TailBCorollaryCoverage.lean#L199). |
| B, T17 report prose | Disagree for the same cited reason. Although B’s findings entry has no issues, its report also recommends whole coverage based on the note; the canonical statement and precedence rule govern instead. |

The other soundness and nonvacuity observations were accepted. No retained mathematical statement was replaced by an unproved assertion. The missing witnesses, stronger limits, translation result and optimality result were not supplied with new mathematics.

## Declaration review round 1

Accepted the T18 `label_wrong/major` finding and all three issues in its entry in [the declaration findings](fw/round1/T18/r2g1/findings.json); the other declarations in that file have no open findings. The previous negative statement concerned a common pair of integer functions chosen before all sequences and allocation parameters. Its negation alone did not contradict the sequencewise assertion in [the canonical claim](work.json#L362). The earlier report's assertion that this preserved the printed quantifier order was incorrect.

| Finding | Action |
| --- | --- |
| T18Statement: integer functions quantified before all sequences | Replaced only `T18Statement` by `∃ S H θ ρ, Conditions123 S H θ ρ ∧ ¬ Lemma2Conclusions S H θ ρ`. The joint conclusion includes both uniform-convergence assertions and existence of positive nonincreasing integer functions satisfying both tail bounds, chosen after the sequence and parameters. Its failure for an admissible sequence refutes the printed assertion regardless of whether that assertion further restricts the functions' dependence. |
| T18 docstring: unqualified falsity unsupported by the previous quantifier order | Replaced the explanation of the uniform reading with the explicit sentence that a sequence satisfying conditions 1–3 has a failing joint conclusion. The required “The printed claim is false:” prefix now describes the stronger statement actually proved. |
| T18 metadata: `refuted` with no restriction overstated the previous statement | Retained `refuted` and a null restriction for the repaired sequence-specific counterexample. The existing credited [negation of the sequencewise universal assertion](AronowAudit/P022/Wave1/PrintedLemma2.lean#L9) supplies it by classical quantifier duality alone, through the existing Bridge. No new counterexample construction or analytic proof was used. |

Only `SAP.P022.T18Statement` changed among shared definitions. It is used only by T18; all other target types and shared definition bodies were checked against the pre-review exports and remain identical. `Lemma2Conclusions` and the statistical definitions did not change. All theorem names and decisions remain the same; the Comparator module names and theorem list therefore remain unchanged.

## Existence and valid-domain checks

- T6’s finite reciprocal CDF-threshold implication now requires C>0, so its denominator 8NC² is nonzero. The decomposition, probability budget and absolute integral bound still include C=0. The conditional asymptotic part already required C>0, positive xi and eta, valid allocation fractions, and positive tolerance allocations.
- T8’s variance-substitution display is now restricted to ambient N≥m+k, the standing population domain. Its previously stronger but extraneous instances N=0 or N=1 are removed. This does not drop a canonical valid-design clause.
- T10’s fixed-sample limit now uses the cofinal valid sizes N=r+(m+k), and its fixed-arm part states m,k≥2 explicitly. These are the canonical sample-size conditions and eliminate invalid finite prefixes and zero sample-size divisions.
- T17 explicitly assumes `LawFunctionalsDefined H`, positivity of the limiting upper bound and every finite estimated upper variance. The definition requires proper first/second coordinate and centered integrals for every compatible law and a nonempty covariance image bounded above and below. Its coverage clause additionally assumes `NormalCriticalDefined alpha`, ruling out an empty or lower-unbounded critical-value set. The original theorem’s positive gamma together with the finite-variance guard makes every studentizing denominator positive.
- T15 establishes the required moment integrability as part of its conclusion; it does not merely use totalized moments of arbitrary non-integrable laws. Nonemptiness and boundedness of its compatible-law extrema are justified in the existing L2 coupling proof, including its attained endpoints; see [QuantileBridge](AronowAudit/Shared/MapTailB/QuantileBridge.lean#L226) and [the population L2 consequence](AronowAudit/P022/Wave1/Gap/TailBBoundConsistency.lean#L109).
- Finite empirical couplings in T13 have the actual finite-support marginals, hence proper coordinate and product integrals; this is supplied by the existing [N6–N7 components](AronowAudit/P022/Wave1/SharpBoundsBlueprint.lean#L165). Finite quantile integrands in the other targets are bounded step functions with positive sample sizes. Probability laws rule out `toReal` of infinite mass, and CDF-distance ranges are nonempty and bounded. T11’s variances and multiplier are positive; T12’s finite set is nonempty and its square-root arguments are nonnegative.

These guards were added under revision 2’s junk-value rule, not from repair notes or assumed cited theorems. They only weaken the relevant implications. The intentional numerical incompatibility in T12 and the permitted zero-threshold refutation in T7 remain genuine claims, not accidental empty statistical domains.

## SAP definitions and bridges

The single SAP definition route remains in use. Defs parts import only Mathlib and earlier Defs parts; Challenge imports only `SAP.P022.Defs`. Every target type is a shared `T<k>Statement` constant. No original-name copy or Orig module remains. Every SAP Lean module begins after its imports with both `set_option autoImplicit false` and `set_option relaxedAutoImplicit false`.

Bridge/Part1 contains inverse adapters for Design, ExperimentSequence and the two endpoint constructors. Design/sequence inverses and projections are `rfl`; endpoint identities use the two constructor cases. Bridge/Part2 proves the numerical, integral, CDF, probability and limiting-law correspondences by `rfl`, with endpoint cases where necessary. Bridge/Part3 transports the existing credited contracts through these adapters. Bridge/Part4 adds only the elementary equality characterization derived from the existing CDF variance formula. The new existence predicates are ordinary Mathlib propositions, used as explicit hypotheses in the Solution; no unproved analytic theorem is assumed.

The Solution uses those bridges and the existing declarations. Its additional operations are conjunction, instantiation, logical transport (including T18's classical quantifier duality), the cofinal natural-number shift, and elementary arithmetic. `rows_used` names the original usable declarations, including the explicitly recorded cross-target support for T5; `rows_not_used` explains which credited constituents are not separately invoked.

## Verification

All package modules were compiled with `/home/ubuntu/sap/tools/sap-lean` in dependency order. The ordered run checks 16 modules including `scratch/AxiomCheck.lean`, which prints the dependencies of all 18 Solution theorems. Every theorem uses only `propext`, `Classical.choice` and `Quot.sound`; the current output is in `scratch/final-build.log`.

The raw Challenge/Solution check passes for all 18 theorem types and 267 shared SAP declarations, comparing types, universe parameters and definition bodies without normalization, proof erasure or binder renaming. Its summary is `scratch/exact-check.json`; the executable exports are `scratch/ExactChallenge.lean` and `scratch/ExactSolution.lean`. Both JSON files parse, theorem lists agree, and all package source and metadata files have at most 300 lines.

The Comparator configuration retains the same module names and all 18 theorem names. Full external-kernel certification has not been rerun here; the raw constant check and Lean proofs pass. No three-kernel certification result is asserted.

## Whole versions (new proofs)

The five switches below supersede the earlier restricted classifications in this report. Each now has the decision from `switch.json` (`whole`), a null restriction, and a proved whole statement.

### P022-T7

`SAP.P022.T7 : SAP.P022.T7WholeStatement` is proved by `SAP.P022.WH.W1.T7_whole`.

Files: `SAP/P022/Challenge/Part1.lean`, `SAP/P022/Solution.lean`, `SAP/P022/manifest.json`, `SAP/P022/Defs/WholeW1.lean`, `SAP/P022/WH/W1/Support.lean`, `SAP/P022/WH/W1/Leaves.lean`, `SAP/P022/WH/W1/P/T7_L1.lean`, `SAP/P022/WH/W1/P/T7_L2.lean`, `SAP/P022/WH/W1/P/T7_L3.lean`, `SAP/P022/WH/W1/P/T7_L4.lean`, `SAP/P022/WH/W1/Proofs/T7.lean`.

Removed restriction (previous manifest text): Retains the four-corner conditions 1–3, atom-left convergence, bounded outcomes, and the two infinite scaled-tail limsups. Omits the zero-threshold finite probability-one identities, the N=4r moment/covariance/variance and decomposition calculations, the displayed 51200/(N delta^2) bound and centered-error limit, convergence of the scaled absolute error to 1/2, convergence of its threshold probabilities to one, and convergence of the scaled probability sequence to infinity.

### P022-T9

`SAP.P022.T9 : SAP.P022.T9WholeStatement` is proved by `SAP.P022.WH.W1.T9_whole`.

Files: `SAP/P022/Challenge/Part1.lean`, `SAP/P022/Solution.lean`, `SAP/P022/manifest.json`, `SAP/P022/Defs/WholeW1.lean`, `SAP/P022/WH/W1/Support.lean`, `SAP/P022/WH/W1/Leaves.lean`, `SAP/P022/WH/W1/P/T9_L1.lean`, `SAP/P022/WH/W1/P/T9_L2.lean`, `SAP/P022/WH/W1/Proofs/T9.lean`.

Removed restriction (previous manifest text): Retains the all-ones negative-output example and both endpoint discrepancy formulas under the cell-width condition. Omits the separate assignment-by-assignment observed-data/effect assertions, marginal variance/covariance and partition/selected-value/weight calculations, the explicit shifted-weight-sum identity, and the translation-invariance comparison.

### P022-T17

`SAP.P022.T17 : SAP.P022.T17WholeStatement` is proved by `SAP.P022.WH.W1.T17_whole`.

Files: `SAP/P022/Challenge/Part1.lean`, `SAP/P022/Solution.lean`, `SAP/P022/manifest.json`, `SAP/P022/Defs/WholeW1.lean`, `SAP/P022/WH/W1/Support.lean`, `SAP/P022/WH/W1/Leaves.lean`, `SAP/P022/WH/W1/P/T17_L1.lean`, `SAP/P022/WH/W1/P/T17_L2.lean`, `SAP/P022/WH/W1/P/T17_L3.lean`, `SAP/P022/WH/W1/P/T17_L4.lean`, `SAP/P022/WH/W1/P/T17_L5.lean`, `SAP/P022/WH/W1/P/T17_L6.lean`, `SAP/P022/WH/W1/P/T17_L7.lean`, `SAP/P022/WH/W1/Proofs/T17.lean`.

Removed restriction (previous manifest text): Drops Remark 4's narrowest-Wald-interval assertion. Adds explicit integrability of the first and second coordinate moments, centered squares and centered product for every compatible law, a nonempty covariance image bounded above and below, positivity of the limiting upper bound, and positivity of every finite estimated upper variance. The coverage assertion also requires the normal critical-value set to be nonempty and bounded below. Retains the CLT, gamma range, actual-variance limit, and guarded coverage limit/lower bound.

### P022-T1

`SAP.P022.T1 : SAP.P022.T1WholeStatement` is proved by `SAP.P022.WH.W1.T1_whole`.

Files: `SAP/P022/Challenge/Part1.lean`, `SAP/P022/Solution.lean`, `SAP/P022/manifest.json`, `SAP/P022/Defs/WholeW1.lean`, `SAP/P022/WH/W1/Support.lean`, `SAP/P022/WH/W1/Leaves.lean`, `SAP/P022/WH/W1/P/T1_L1.lean`, `SAP/P022/WH/W1/P/T1_L2.lean`, `SAP/P022/WH/W1/P/T1_L3.lean`, `SAP/P022/WH/W1/P/T1_L4.lean`, `SAP/P022/WH/W1/Proofs/T1.lean`.

Removed restriction (previous manifest text): Retains only witness A's conditions 1–3, population and sampled CDF distances equal to one, infinite scaled-tail limsups, and failure of Lemma 2. Omits A's explicit boundedness/condition-4 assertion, its individual CDF and left-CDF values at zero and at the displayed moving threshold, the finite probability-one and N-times-probability identities, and the partition proof-step assertion. Omits all of witness B: the perturbed four-corner population, its boundedness and nonsingular limiting law, its conditions 1–3 and CDF-distance assertions, and its probability-one and divergent-tail assertions.

### P022-T6

`SAP.P022.T6 : SAP.P022.T6WholeStatement` is proved by `SAP.P022.WH.W1.T6_whole`.

Files: `SAP/P022/Challenge/Part1.lean`, `SAP/P022/Solution.lean`, `SAP/P022/manifest.json`, `SAP/P022/Defs/WholeW1.lean`, `SAP/P022/WH/W1/Support.lean`, `SAP/P022/WH/W1/Leaves.lean`, `SAP/P022/WH/W1/P/T6_L1.lean`, `SAP/P022/WH/W1/P/T6_L2.lean`, `SAP/P022/WH/W1/P/T6_L3.lean`, `SAP/P022/WH/W1/P/T6_L4.lean`, `SAP/P022/WH/W1/P/T6_L5.lean`, `SAP/P022/WH/W1/P/T6_L6.lean`, `SAP/P022/WH/W1/P/T6_L7.lean`, `SAP/P022/WH/W1/Proofs/T6.lean`.

Removed restriction (previous manifest text): The limit conclusion chooses K1, K0 and the constant after the sequence, parameters, epsilon1 and xi are fixed, and asserts only their displayed tail bounds and identities; it does not assert positivity or monotonicity of those selected K functions, dependence only on the limiting law, or a minimization result. The earlier six rate bounds and Lemma 2 conclusions remain explicit hypotheses, as in canonical parts (c)–(d). The finite reciprocal CDF-threshold implication additionally requires C > 0; the remaining finite statements still allow C = 0. The separate lower-endpoint allocation is not asserted.

Dependent proof repairs: none. The other Solution proofs do not reference any switched theorem; their statements, docstrings, proofs and manifest entries are unchanged.

Verification for these switches: `python3 /home/ubuntu/sap/tools/rebuild_sap.py . P022` rebuilt all 47 modules from scratch; the forbidden-token scan was clean. `scratch/P022WholeAxiomCheck.lean` imports `SAP.P022.Solution` and prints the axioms of all five switched theorems. Each uses exactly `propext`, `Classical.choice` and `Quot.sound`; all 97 declaration checks for their `rows_used` entries also passed. Output is in `scratch/P022WholeAxiomCheck.log`. Lean ran sequentially, and no `lake` command was run. Results are recorded in `switched.json`.
