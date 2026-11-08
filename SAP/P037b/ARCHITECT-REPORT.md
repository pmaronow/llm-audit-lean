P037b packages only the 15 targets in work.json for “Changing Climates of Conflict: A Social Network Experiment in 56 Schools” (PNAS 113(3):566–571, DOI 10.1073/pnas.1514483113).

| Decision | Targets |
| --- | ---: |
| whole | 3 |
| restricted | 10 |
| refuted | 0 |
| omitted | 2 |

All 13 non-omitted statements have Solution proofs. There are no open glue tasks. The three whole targets are P037-T25 (both complete synthetic network certificates), P037-T29 (the complete fixed-simulation rare-exposure witness), and P037-T30 (the finite Monte Carlo law, grid, error bounds, positivity-screen consequences and blocked-exposure formula with its four examples).

The restricted statements have the following exact differences from their canonical claims:

- **P037-T18**: Retains the residual-multiplier covariance, leverage facts, homoskedastic HC0 shortfall, and positive-norm weighted-row algebra. Omits identification with the released R procedure, the second expanded Gram-inverse sandwich expression and coefficient standard-error/normal-Wald formulas in (a), and identification of the abstract row factor with the expected-to-true coefficient variance ratio.
- **P037-T23**: Retains the six-group inverse, normal-equation, residual-magnitude and HC0 certificates; both predicted means; all named variances and their comparisons; and the centered-fit certificates. Omits an explicit rank-3 assertion, the predicted-difference and variance-decomposition equations, the separate control-residual mean and sample-variance certificates, and the square-root interval-width conclusion or identification of released plotting code.
- **P037-T24**: Retains the algebraic prediction rows and mean difference, the symmetric-covariance decomposition/equality criterion, and same-sample full-rank recentering of coefficients, predictions, residuals and HC0 variance. Omits the normal-reference interval endpoints in (b), examples realizing both variance orderings in (c), the residual-control-band failure and concrete certificate in (e),(f), the explicit identification of the centered variance with a prediction quadratic form, and verification of the released plotting routines.
- **P037-T19**: Retains constant effects pointwise and averaged over every nonempty subset, assignment-dependent kept sets, the complete six-assignment table, finite expectations, profiling crossproducts, and the probability limit of the explicitly defined weighted block ratio. Omits identification of that ratio as the OLS treatment coefficient in a general regression on block indicators.
- **P037-T20**: States only the finite inverse-probability identities (a),(b) and the same-side threshold sufficient condition in (c). Omits the sharp-null specialization, the referenced T19 counterexample and conditional inclusion probabilities in (d), and verification of the released scripts, data counts and reporting descriptions.
- **P037-T21**: Retains both exact local probability vectors, their raw exposure histograms, probability sums and positivity/cutoff comparisons, two supported seed/nonseed realizations, and the supported 10000-draw frequency witness. Omits the separate conditional mass 1/924 assertions for those two selections and the complete analysis-set membership-change assertion in W2(vii), including its outcome, baseline, school and simulated-frequency masks.
- **P037-T22**: Retains the population equality, all stated screen inclusions and nonseed containment, scalar cutoff nondegeneracy, seed-exclusion lower bound, and integer-threshold/reciprocal bound. Omits the coordinatewise zero-probability implication in (b), strict-inclusion examples in (c), the binomial law in (d), randomness of the joint four-cutoff or full outcome-specific analysis set in (d),(e), and the fitted-prediction average and denominator in (f); no code execution or empirical count is certified.
- **P037-T31**: Retains actual 56-school support cardinalities and one pair probability for uniform 28-of-56 and 2-of-4 laws, the eight-school support witness and exact uncentered second-moment examples in both directions, and the general zero-mean/second-moment formula conditional on half school marginals. Omits the 56-school support inclusion and block-respecting probability, their exact ratio, universal school marginals/pairs/covariances, the complete eight-school pair-law family and explicit 34-state count, explicit zero means identifying the eight-school second moments as variances, and identification of the two 56-school outcome examples with their actual design variances.
- **P037-T32**: Retains the blocked mass definition and its normalization/support count, general uniform-selection marginal/pair formulas, and the school-local mixture identity for normalized nonnegative school and seed masses. Omits explicit independence of the blocked components, the numerical specializations in (b), the control-versus-other-exposure specializations and explicit equality of exposure probabilities/populations/estimands under the two school laws in (c), the joint control-exposure/variance comparisons in (d), and certification of the released-sampler repair.
- **P037-T26**: Retains Boolean union-graph properties and the two count decompositions, the scalar equal-label criterion and pointwise implications, and normalized positive-weight scalar probability inequalities with strictness. Omits the graph-instantiated subset-count inequalities, the all-supported-assignments reciprocal-possible-seed sufficient condition in (d), referenced concrete examples in (f), and verification of the released-script and Fig. S5 descriptions; probability comparisons are stated for scalar counts satisfying r ≤ c and q ≤ b.

The omitted targets are:

- **P037-T16**: no Lean rows are credited to this target. The printed tables and procedural descriptions are not established here. A separate target about the weight-law error belongs to another unit and is not substituted for this claim.
- **P037-T17**: no Lean rows are credited to this target. The printed empirical reduction statements are not established here. Arithmetic for a separate correction target is not substituted for this headline claim.

The package uses the shared-Defs route. Defs/Part1–Part3 import Mathlib and earlier Defs parts only; every project notion has a distinct SAP.P037b name. Both Challenge and Solution import the identical compiled Defs modules. Challenge imports no project or Bridge module. The root Challenge module imports only its Challenge part. Each SAP Lean file sets both implicit-variable options immediately after its imports.

Finite student and school indices are zero based; index j represents printed student or school j+1 in the named synthetic examples. Fin 5 exposure labels are C=0, S=1, NI=2, I=3, D=4. The treated-nonseed Fin 3 labels used for the network comparisons are S=0, NI=1, I=2. Referents are fixed from the directed nomination graph under both peer readings. The six rows of the band example have multiplicities 14,14,7,7,7,7 and represent 56 observations; they are not six equally weighted observations.

Bridge.toProject copies the mass, positivity proof and unit-total proof from the SAP ProbabilityDesign record into the project record. Bridge.probability_correspondence and Bridge.expectation_correspondence are reflexive equalities of the corresponding finite sums. Other renamed definitions agree by reduction of their bodies; no separate mathematical equivalence is assumed.

| Bridge theorem | Glue used |
| --- | --- |
| T18_correspondence | Conjoin and instantiate the four credited covariance, leverage, shortfall and row-factor statements. |
| T19_correspondence | Conjoin the finite counterexample, existing limit and crossproduct statements; simplify the mean of the exported constant effect over a nonempty finite set. |
| T20_correspondence | Adapt ProbabilityDesign and apply the two credited finite identity and threshold statements. |
| T21_correspondence | Conjoin the two credited witnesses and their existing count lemmas; evaluate the probability sums and cutoff arithmetic. |
| T22_correspondence | Adapt ProbabilityDesign and instantiate exactly the exported inclusions, scalar cutoff, seed-exclusion and integer-rule statements. |
| T23_correspondence | Conjoin the three existing grouped-fit, variance-value and centered-refit certificates. |
| T24_correspondence | Conjoin the existing prediction-row algebra, symmetric quadratic identity and centered-refit statement. |
| T25_correspondence | Apply the credited two-network theorem and its existing indegree and histogram lemmas; reduce the fixed graph rows and singleton counts, and evaluate arithmetic on the exported probabilities. |
| T26_correspondence | Conjoin the existing graph, count, equal-label and scalar mass-comparison statements; require unit-total masses for probability interpretation. |
| T29_correspondence | Conjoin the actual four-block design certificate with its existing relative/control arithmetic. |
| T30_correspondence | Adapt ProbabilityDesign and conjoin the existing law, simultaneous bound, blocked formula and four numerical specializations. The frequency grid is the filtered hit-count bound. The error floor instantiates the credited resolution row. The zero-probability consequence instantiates the existing law. The all-four inclusion is a projection of the existing inclusion statement. Existence of a missed truly positive focal student follows by logic from the exported strictly positive zero-hit probability of the T29 design. |
| T31_correspondence | Conjoin the actual sampler counterexample and existing finite second-moment formula. |
| T32_correspondence | Conjoin the existing school-law and local-mixture statements; require nonnegative normalized school and within-school masses. |

The extra supporting declarations used for T21, T25 and T30 are recorded separately in the manifest. The reviewed narrower row for T22 is used only for its exported inclusions, including when that inclusion is reused for T30. Its missing coordinatewise conclusion is not inferred from those inclusions. T30 instead obtains the coordinatewise zero-frequency conclusion from its credited Monte Carlo law.

Full compilation uses /home/ubuntu/sap/tools/sap-lean in dependency order: Defs parts and root, Bridge part and root, Challenge part and root, Solution, and scratch/P037bAxioms.lean. The foundation inspection prints all 13 proved theorem names and reports exactly propext, Classical.choice and Quot.sound for each. Manifest and comparator configuration parsing, target/row/theorem consistency, import restrictions, file-size limits and the forbidden-token check are verified separately.

Two distinctions in T22 matter: the four indirect exposure probabilities need not sum to one when direct exposure is possible, and positive seed probability alone does not make the whole analysis mask nonconstant, since another mask may exclude the student under every assignment. The packaged inclusions and exclusion bound avoid both overstatements. The eight-school quantities in T31 are explicitly the exported raw second moments; no missing actual-law zero-mean assertion is silently added to call them variances.

All empirical code/data descriptions remain external source context; these theorems do not claim to have executed the released scripts or reconstructed the original analysis. Positive masses and unit totals give genuine finite probability laws. Positive simulation sizes, feasible seed sample sizes, full-rank OLS hypotheses and positive row norms exclude the relevant undefined-quantity branches. The block-ratio limit concerns growing positive block counts; its total-function extension at zero blocks carries no regression interpretation.

The supplied [Comparator result](SAP/P037b/verification/comparator-result.json) records acceptance of the pre-revision snapshot stamped 20261103T231805Z by the Comparator and all three kernels. Every supplied snapshot source hash matched before revision 2. This revision changes only the T29 restriction prose, report and metadata; every Lean definition, theorem statement and proof is unchanged. The original verification result is preserved as a record of that snapshot. All nine SAP modules and the foundation inspection were recompiled for revision 2; no new external-kernel run is claimed.

## Revision 2 referee findings

Both round-1 reports were checked against the canonical statement, definitions_needed and standing assumptions. The audit-history note and finite_lemmas were not treated as clauses. Both referees report the same single minor wording finding, on T29; no finding is rejected.

- **Referee a, P037-T29 — accepted and fixed.** Its [finding](referees/round1/a/findings.json) correctly distinguishes the exact error equality at r=0 from the stronger lower bound for r≥1. Canonical T29(iii) in [work.json](work.json) states |r/10000-p| ≥ 1/10000-p > p for r≥1, with p=1/127008. The retained [T29Statement](SAP/P037b/Defs/Part2.lean) states the common error floor and strict half-p floor but does not separately state those branch assertions. The docstring, manifest restriction and report now name the omitted equality and lower bound separately.
- **Referee b, P037-T29 — accepted and fixed.** Its [finding](referees/round1/b/findings.json) identifies the same inaccurate plural wording. The same synchronized correction addresses it. T29 remains restricted; its fully qualified name, proposition, proof, credited rows and permitted foundations are unchanged.

Every per-target referee finding is accounted for below. The two T29 entries above are the only entries with nonempty issues; the other entries support the existing decisions.

| Target | Referee a | Referee b | Disposition |
| --- | --- | --- | --- |
| P037-T16 | omission_ok | omission_ok | Retained omitted; no issue reported. |
| P037-T17 | omission_ok | omission_ok | Retained omitted; no issue reported. |
| P037-T18 | correct_restricted | correct_restricted | Retained restricted; no issue reported. |
| P037-T23 | correct_restricted | correct_restricted | Retained restricted; no issue reported. |
| P037-T24 | correct_restricted | correct_restricted | Retained restricted; no issue reported. |
| P037-T19 | correct_restricted | correct_restricted | Retained restricted; no issue reported. |
| P037-T20 | correct_restricted | correct_restricted | Retained restricted; no issue reported. |
| P037-T21 | correct_restricted | correct_restricted | Retained restricted; no issue reported. |
| P037-T22 | correct_restricted | correct_restricted | Retained restricted; no issue reported. |
| P037-T29 | restriction_inaccurate | restriction_inaccurate | Corrected restriction wording; retained restricted scope. |
| P037-T30 | correct_whole | correct_whole | Retained whole; no issue reported. |
| P037-T31 | correct_restricted | correct_restricted | Retained restricted; no issue reported. |
| P037-T32 | correct_restricted | correct_restricted | Retained restricted; no issue reported. |
| P037-T25 | correct_whole | correct_whole | Retained whole; no issue reported. |
| P037-T26 | correct_restricted | correct_restricted | Retained restricted; no issue reported. |

Revision 2 validation: all 13 theorem names and their complete propositions and proofs match the pre-revision package; all 15 target decisions remain unchanged. comparator.json was regenerated with the same modules, theorem names, permitted foundations and kernel commands. Both required JSON files parse. Full dependency-order compilation and foundation inspection passed; every proved theorem uses exactly propext, Classical.choice and Quot.sound. The source/import, file-size, restriction-consistency and forbidden-token checks also passed. There are no open glue tasks.

## Whole versions (new proofs)

**P037-T29 (`SAP.P037b.T29`)** is now whole, with statement
`SAP.P037b.T29WholeStatement` and Solution proof
`SAP.P037b.WH.W1.T29_whole`. This supersedes the earlier restricted
description of T29; the package now has 3 whole, 10 restricted and 2 omitted targets.

- Updated Challenge stub and docstring: `SAP/P037b/Challenge/Part1.lean`.
- Updated Solution type, proof and import: `SAP/P037b/Solution.lean`.
- Whole statement: `SAP/P037b/Defs/WholeW1.lean`.
- Blueprint and proved leaf: `SAP/P037b/WH/W1/Leaves.lean` and `SAP/P037b/WH/W1/P/T29_L1.lean`.
- Generated whole theorem: `SAP/P037b/WH/W1/Proofs/T29.lean`.
- Updated target metadata and credited declarations: `SAP/P037b/manifest.json`.

**Old restriction removed:** Retains the actual four-block seed law, exact positive exposure probabilities, the universal frequency-error floor, independent-draw expected hit count, zero-hit probability and centered second moment, the zero-hit probability bounds, and relative/control variance arithmetic. Omits the event-specific two-block counts and named unique avoiding state in (i), the explicit probability-sum equation, the complete binomial distribution in (iv), the separate error equality for r=0 and the stronger error bound |r/10000-p| ≥ 1/10000-p > p for r≥1 (where p=1/127008), and an explicit relative-standard-error inequality above 3.5.

**Dependent proof repairs:** None. No other Solution proof refers to `SAP.P037b.T29`.

**Validation:** `python3 /home/ubuntu/sap/tools/rebuild_sap.py . P037b` rebuilt all 17 modules from scratch and passed the token scan. The scratch file `/tmp/SW-P037b-switched-axioms.lean` imports `SAP.P037b.Solution`; `#print axioms SAP.P037b.T29` reports exactly `propext`, `Classical.choice` and `Quot.sound`. Import and scope checks passed.

## Declaration review round 1

The [r4g2 findings for SAP.P037b.T29](fw/round1/T29/r4g2/findings.json) contain two valid minor wording issues. Both are accepted. The canonical independent-draw clause explicitly concerns Var(r/10000), and the formal statement already uses `iidVarianceW1 rareAssignmentMass 10000 (frequencyW1 E)`. No mathematical correction or new proof is needed.

- **Challenge docstring — fixed.** The sentence formerly made the count the subject of the variance clause. It now states separately that the count has the binomial law, expected count 625/7938, and zero-hit probability between .9 and .95, while the school-exposure frequency (count divided by 10000) has variance 127007/161310320640000, relative variance 127007/10000, and relative standard error above 3.5. See [Challenge/Part1.lean](SAP/P037b/Challenge/Part1.lean).
- **Shared statement docstring — fixed.** The duplicate prose on `T29WholeStatement` now uses the same corrected wording. Its body is unchanged. `frequencyW1` divides the hit count by the number of draws, and `iidVarianceW1` centers at its actual product-law expectation; see [Defs/WholeW1.lean](SAP/P037b/Defs/WholeW1.lean). With p=1/127008, exact rational arithmetic gives count variance 79379375/1008189504 and frequency variance 127007/161310320640000, a ratio of 10000².

The present whole T29 theorem and all other theorem names, statements, proof bodies and decision labels are preserved. No shared definition body was changed. The prior `WH/W1/Leaves.lean` exceeded the 300-line limit; it is now 295 lines after compacting comments, blank lines and expression continuations. All noncomment mathematical tokens in every Lean module match the pre-revision files.

The manifest records both corrections while retaining T29 as whole and proved. comparator.json was regenerated with the same modules, theorem list, permitted foundations and external-kernel commands. The earlier package-generation script predates the whole-T29 switch and was not rerun. All current SAP modules, including the previously supplied whole-proof modules, are compiled in import order with sap-lean; all 13 exported theorem foundations are inspected again. The retained Comparator artifact certifies its recorded earlier snapshot; this declaration review does not claim a new external-kernel run.

Declaration review validation passed: all 17 SAP modules compiled in dependency order, and the scratch foundation inspection printed all 13 exported theorem names with exactly `propext`, `Classical.choice` and `Quot.sound`. The validation also checked both JSON files, identical Challenge/Solution types, unchanged mathematical tokens, the synchronized docstrings, all required implicit-variable options, the 300-line limit and forbidden tokens. Results are recorded in `scratch/P037b-declaration-round1-compile.json` and `scratch/P037b-declaration-round1-validation.json`. There are no open glue tasks.

## Whole versions (new proofs)

**P037-T22 (`SAP.P037b.T22`)** is now whole, with Challenge and Solution type
`SAP.P037b.T22WholeStatement_W2` and Solution proof
`SAP.P037b.WH.W2.T22_whole`. This supersedes the earlier restricted
description of T22; the package now has 4 whole, 9 restricted and 2 omitted targets.

- Updated Challenge stub and docstring: `SAP/P037b/Challenge/Part1.lean`.
- Updated Solution type, proof and Proofs import: `SAP/P037b/Solution.lean`.
- Existing Mathlib-only whole statement: `SAP/P037b/Defs/WholeW2.lean`.
- Existing blueprint and proved leaves: `SAP/P037b/WH/W2/Leaves.lean`,
  `SAP/P037b/WH/W2/P/T22_L1.lean` and `SAP/P037b/WH/W2/P/T22_L2.lean`.
- Existing generated whole theorem: `SAP/P037b/WH/W2/Proofs/T22.lean`.
- Updated target metadata and credited declarations: `SAP/P037b/manifest.json`.
- Switch result: `switched.json`.

**Old restriction removed:** Retains the population equality, all stated screen inclusions and nonseed containment, scalar cutoff nondegeneracy, seed-exclusion lower bound, and integer-threshold/reciprocal bound. Omits the coordinatewise zero-probability implication in (b), strict-inclusion examples in (c), the binomial law in (d), randomness of the joint four-cutoff or full outcome-specific analysis set in (d),(e), and the fitted-prediction average and denominator in (f); no code execution or empirical count is certified.

**Dependent proof repairs:** None. No other Solution proof refers to
`SAP.P037b.T22`; all other theorem statements, docstrings, proofs and manifest
entries are unchanged.

**Validation:** `python3 /home/ubuntu/sap/tools/rebuild_sap.py . P037b` rebuilt
all 22 modules from scratch and passed the token scan. The scratch file
`/tmp/SW-P037b-T22-switch-k6eyodw_/Axioms.lean` imports
`SAP.P037b.Solution`; `#print axioms SAP.P037b.T22` reports exactly `propext`,
`Classical.choice` and `Quot.sound`. Exact Challenge/Solution types, the new
docstring, import restrictions, manifest fields and preservation of every other
target and all existing definition/proof sources passed the scope checks.
