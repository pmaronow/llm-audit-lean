Unit P026b packages exactly P026-T13 through P026-T24 from *A Class of Unbiased Estimators of the Average Treatment Effect in Randomized Experiments* (2013), DOI 10.1515/jci-2012-0009. Targets belonging to P026a are excluded.

| Decision | Count | Targets |
| --- | ---: | --- |
| whole | 8 | T13, T14, T15, T16, T20, T22, T23, T24 |
| restricted | 1 | T21 |
| refuted | 3 | T17, T18, T19 |
| omitted | 0 | None |

All 12 listed theorems are proved. There are no open glue tasks, and every proof plan is null. Every credited row used here has final status `ok`. The manifest accounts for every row, including unused duplicates and helpers.

T21 is restricted in clause (b): every assignment of positive probability must treat exactly m clusters. The canonical formal-content paragraph lists the partition and equal marginal probabilities; the credited cluster theorem additionally requires the fixed count. The Challenge states that additional hypothesis explicitly. All three clauses remain: the complete-unit result, the cluster formula and unbiasedness, and the unequal-cluster bias example. The canonical opening quotation itself describes fixed-count cluster sampling, but the broader formal-content paragraph is not silently repaired. No other target is restricted, and none is omitted.

T15 is whole: its canonical claim supplies a counterexample to the specified reading of package guidance, namely that estate() with HT=TRUE preserves unbiased estimation when covariates X are supplied. The Challenge docstring now names that reading explicitly. T17–T19 have positive canonical assertions, so their decisions are refuted. T17 includes both the universal support/conservativeness refutation and the separate footnote 9 counterexample. T18 supplies the fitting-input premises and a nonzero covariance that defeats the printed general rule. T19 negates a necessary collection of the printed moment assertions, which refutes their joint correctness; it does not classify every table entry individually. Its statement also certifies positive FE residual norms and unique logistic maxima to exclude invalid fitting branches.

The shared-definition and Bridge route is used throughout. The six Defs parts import only Mathlib and earlier Defs parts. Both theorem modules import the same compiled SAP definitions. Neither the Challenge nor any definition in its statement closure imports the project.

The Bridges are glue:

- Design, UnitExperiment and ClusterExperiment adapters preserve every field. Design weights, assignments, actual population counts, cluster totals, and all finite-sum moment and estimator definitions agree by reduction. The explicit equalities in Bridge/Part1 and the numerical design equalities in Bridge/Part2 use `rfl`.
- Arbitrary prediction arrays are encoded into the existing PredictionRule interface using an enumeration of the finite population, coordinate covariates, and a fitted vector containing the array values. `encoded_values` reduces the coordinate sum with `simp`. This adds no condition on predictions or their dependence on assignment.
- The observed residual contrast follows from the existing generalized-residual theorem and observed/potential-outcome masking identity, followed by distribution of multiplication over subtraction.
- The SAP OLS map, column space, projection and minimization predicate have the same bodies as the project notions. Their identification is definitional. For T15, the existing inverse-Gram theorem is instantiated at the three-unit intercept-and-covariate matrix, whose Gram matrix is [[3,3],[3,5]] with determinant 6. Exact matrix arithmetic identifies the rational fitted vectors, interpreted in the reals, with the OLS projection. The existing OLS specification supplies minimization and uniqueness. No least-squares argument is reproved.
- The Logit rounding glue expands a square and uses existing expectation addition, subtraction, constant and scalar identities. The exported unbiasedness facts make both mean squared errors equal the corresponding variances. Interval arithmetic then gives all ten corrected rounded entries and excludes all six erroneous printed entries.

Existing supporting declarations used beyond the selected aggregate rows include the OLS specification and inverse formula; the selected-logistic-coefficient maximizer and real-table probability facts; the FE normal-equation certificate for positive residual norms; covariance with a constant; and finite-expectation linearity. The fixed-prediction arm-total conclusions in T22 also instantiate the existing generalized-unbiasedness theorem. No paper theorem, independence condition, asymptotic result or additional substantive premise was introduced as an assumption.

The numerical counterexamples use exact rational arithmetic. T15 explicitly identifies the real least-squares fits of those rational responses. Unit means use the actual nonzero population cardinality; marginals are positive in every general estimator statement. The unequal-cluster example certifies both realized arm sizes are positive. The logistic theorem asserts existence and uniqueness and certifies that the selected coefficients maximize the likelihood, excluding the fallback selection branch. Equation [30] is retained without a directed cross-support hypothesis.

Validation completed:

- All six Defs parts and Defs root, both Bridge parts and Bridge root, the Challenge part and root, and Solution compiled with the specified sap-lean command in dependency order.
- `scratch/Axioms.lean` printed the dependencies of every proved theorem. Each has exactly `propext`, `Classical.choice`, and `Quot.sound`; results are in `scratch/axioms.log` and the manifest.
- `scratch/IdentityCheck.lean` loaded the two theorem modules separately. All 12 theorem types are structurally identical, as are the types and bodies of all 142 SAP declarations reachable from those statements. No project declaration occurs in that statement closure. Results are in `scratch/identity.log`.
- Both JSON files parse. The target and theorem lists match the 12 unit targets, every credited row is accounted for, every SAP file has at most 300 lines, and the required implicit-variable options and import boundaries were checked. Incomplete-proof markers occur only in the required Challenge stubs.

The comparator configuration retains the requested permitted dependencies and external kernel commands. The supplied [pre-revision Comparator result](SAP/P026b/verification/comparator-result.json) records acceptance of all 12 theorems by the Comparator and all three kernels. That result certifies its recorded snapshot. Revision 2 changes only the T15 docstring and review metadata; all definitions, theorem types and Solution proofs match that snapshot. This revision reruns local compilation, dependency printing and structural identity checking; it does not claim a fresh external-kernel run.


## Referee round 1 findings and revision 2

I checked each finding in [referee A's findings](referees/round1/a/findings.json) and [referee B's findings](referees/round1/b/findings.json) against the target's canonical `statement`, `definitions_needed` and standing assumptions in [work.json](work.json), then expanded the corresponding SAP definitions. Neither notes nor historical suggested fixes were used to add or remove clauses. The table accounts for all 24 findings. There are no disagreements with either referee.

| Target | Referee A | Referee B | Check and disposition |
| --- | --- | --- | --- |
| T13 | correct_whole | correct_whole | Accepted both: [T13Statement](SAP/P026b/Defs/Part3.lean:38) contains both arm-total covariance identities and the bias identity for arbitrary prediction arrays. Retained whole. |
| T14 | correct_whole | correct_whole | Accepted both: [T14Statement](SAP/P026b/Defs/Part4.lean:49), its core facts and column definitions retain both unique finite maxima, coefficient bounds, moment intervals, both RMSEs, all ten rounded entries and all six failures. Retained whole. |
| T15 | correct_whole | not_faithful (minor) | Accepted A's mathematical assessment and B's docstring correction. Added the precise package-help reading to the [Challenge docstring](SAP/P026b/Challenge/Part1.lean:17). The complete fitted-vector and bias example in [T15Statement](SAP/P026b/Defs/Part3.lean:78) is unchanged; retained whole and recorded the reading in the manifest. |
| T16 | correct_whole | correct_whole | Accepted both: [T16Statement](SAP/P026b/Defs/Part3.lean:96) covers fixed predictions, intercept-inclusive OLS without a rank restriction, its bias identity, both sufficient conditions and the T15 witness. Retained whole. |
| T17 | correct_whole | correct_whole | Accepted both: [T17Statement](SAP/P026b/Defs/Part4.lean:60) refutes the canonical universal assertion and separately gives the sharp-null footnote failure. Retained refuted. |
| T18 | correct_whole | correct_whole | Accepted both: [T18Statement](SAP/P026b/Defs/Part4.lean:73) states the fitting-input pairwise independence and nonzero covariance that contradict the canonical general rule. Retained refuted. |
| T19 | correct_whole | correct_whole | Accepted both: [T19Statement](SAP/P026b/Defs/Part4.lean:81) negates a necessary collection of the printed moments while certifying the regression denominators and logistic maxima. Retained refuted. |
| T20 | correct_whole | correct_whole | Accepted both: [T20Statement](SAP/P026b/Defs/Part5.lean:12) retains observed/potential equality, both total expectations and the ATE expectation under arbitrary assignment dependence. Retained whole. |
| T21 | correct_restricted | correct_restricted | Accepted both: [T21Statement](SAP/P026b/Defs/Part5.lean:22) adds the supported fixed-cluster-count hypothesis in clause (b); equal marginals alone do not imply it. All three clauses remain. Retained restricted with the existing precise disclosure. |
| T22 | correct_whole | correct_whole | Accepted both: [T22Statement](SAP/P026b/Defs/Part5.lean:54) retains both unbiased totals, unbiased ATE, fixed-prediction special case and the assignmentwise adjustment identity. Retained whole. |
| T23 | correct_whole | correct_whole | Accepted both: [T23Statement](SAP/P026b/Defs/Part5.lean:73) retains the affine formula, the equality characterization, a supported failure example and generalized invariance. Retained whole. |
| T24 | correct_whole | correct_whole | Accepted both: [T24Statement](SAP/P026b/Defs/Part6.lean:12) retains residual equivalence, the fixed-prediction variance formula, both arm variances and all three covariance forms including zero directed joints. Retained whole. |

The referees' `correct_whole` verdict vocabulary describes adequate mathematical coverage of a refutation as well as of a positive theorem. It does not require replacing the manifest's `refuted` decisions for T17–T19. Their canonical statements assert the contradicted general rule or moment claims. T15 instead concerns a stated reading of guidance, which is now disclosed without the false-printed-claim prefix. Its canonical opening sentence supplies that exact scope; no broader assertion about the package help is made.

I also rechecked the conditions excluding undefined statistical quantities: finite sums have finite real or rational entries, nonempty universal populations give positive N, positive marginals protect inverse weights, strict count inequalities protect natural differences, and the explicit unequal-cluster arm sizes are positive. The logistic existence and maximizer conclusions exclude the fallback coefficient branch; the FE norm conclusion excludes division by zero. The ordinary finite-dimensional OLS projection defines fitted values at every rank. Both implicit-variable options remain immediately after imports in every SAP Lean file. No new hypotheses, definitions, theorem clauses or mathematical proofs were required by the revision.

Revision 2 validation is recorded in [the build log](scratch/revision2-compile.log), [the dependency log](scratch/revision2-axioms.log), [the identity-check log](scratch/revision2-identity.log) and [the validation summary](scratch/revision2-validation.json). All 13 package modules were rebuilt in dependency order; every listed theorem remains proved with the permitted dependencies. The manifest and Comparator configuration were refreshed and parsed, all rows and theorem names remain accounted for, and the source limits and required options were rechecked. There are no open glue tasks.


## Whole versions (new proofs)

P026-T21 (`SAP.P026b.T21`) is now whole. This supersedes the earlier T21 restriction and decision recorded above.

- [Challenge/Part1.lean](SAP/P026b/Challenge/Part1.lean) now states `SAP.P026b.T21WholeStatement`, imports [Defs/WholeW1.lean](SAP/P026b/Defs/WholeW1.lean), and uses the supplied whole-version docstring while retaining `:= by sorry`.
- [Solution.lean](SAP/P026b/Solution.lean) imports [WH/W1/Proofs/T21.lean](SAP/P026b/WH/W1/Proofs/T21.lean) and proves T21 directly with `SAP.P026b.WH.W1.T21_whole`. Its existing blueprint [WH/W1/Leaves.lean](SAP/P026b/WH/W1/Leaves.lean) and proved leaf [WH/W1/P/T21_L1.lean](SAP/P026b/WH/W1/P/T21_L1.lean) establish the count-free cluster contrast, unbiasedness, and explicit real four-unit witness. These supporting files are unchanged.
- [manifest.json](SAP/P026b/manifest.json) records `whole`, a null restriction, the whole statement, `proved`, and adds the project declarations used by the new proof to `rows_used`. Every other target entry is unchanged.

Old restriction now removed: “Clause (b) additionally requires that every supported assignment treats exactly m clusters. The canonical formal-content paragraph lists only the partition and equal marginal probabilities; the existing credited cluster theorem also requires the fixed count. All clauses (a)-(c) are retained under that restriction.” The whole cluster clause uses the specified treatment and control marginals without requiring a fixed number of treated clusters on support.

No other Solution proof uses T21, so no dependent proof repairs were needed. All other theorem statements, docstrings, and proofs are unchanged.

Validation: `python3 /home/ubuntu/sap/tools/rebuild_sap.py . P026b` rebuilt all 17 unit modules from scratch and passed the token scan; see [whole-rebuild.log](scratch/whole-rebuild.log). [WholeAxioms.lean](scratch/WholeAxioms.lean) imports only `SAP.P026b.Solution` and runs `#print axioms SAP.P026b.T21`; [whole-axioms.log](scratch/whole-axioms.log) reports exactly `propext`, `Classical.choice`, and `Quot.sound`. The rebuild and axiom check ran sequentially using `sap-lean`, without running `lake`. Switch results are recorded in [switched.json](switched.json).
