Work P026a packages only P026-T1 through P026-T12 from `work.json`.
The paper is *A Class of Unbiased Estimators of the Average Treatment Effect
in Randomized Experiments* (2013), DOI 10.1515/jci-2012-0009.

Decisions: 6 whole, 6 restricted, 0 refuted, 0 omitted.
Proofs: 12 proved, 0 open glue tasks. No proof plans remain outstanding.
The canonical counterexample targets already assert refutations, so their
decisions are restricted rather than the separate `refuted` category.

| Target | Decision | Statement definition |
| --- | --- | --- |
| P026-T1 | restricted | `SAP.P026a.T1Statement` |
| P026-T2 | whole | `SAP.P026a.T2Statement` |
| P026-T3 | whole | `SAP.P026a.T3Statement` |
| P026-T4 | restricted | `SAP.P026a.T4Statement` |
| P026-T5 | restricted | `SAP.P026a.T5Statement` |
| P026-T6 | restricted | `SAP.P026a.T6Statement` |
| P026-T7 | restricted | `SAP.P026a.T7Statement` |
| P026-T8 | whole | `SAP.P026a.T8Statement` |
| P026-T9 | restricted | `SAP.P026a.T9Statement` |
| P026-T10 | whole | `SAP.P026a.T10Statement` |
| P026-T11 | whole | `SAP.P026a.T11Statement` |
| P026-T12 | whole | `SAP.P026a.T12Statement` |

Restrictions, with no omitted targets:

- **P026-T1**: Retain both explicit designs and the exported support, HT, printed-variance and covariance-continuation facts. Omit A's exact marginal vector, exact disagreement and same-arm probabilities, and pointwise covariance-continuation values; omit B's exact marginal vector, probability minima, and grouped pointwise HT and printed-variance values. Literal equation [34] is diagnosed by its zero directed denominator (and A's zero numerator), without a partial-valued undefinedness assertion; its covariance moments refer explicitly to the zero-omitted continuation.

- **P026-T4**: Retain both the six-unit and three-unit witnesses, their exported joint-cell, prediction, covariance, total and expectation facts. Omit the exact full fitting-set characterizations in A(ii), the explicit independence-failure probability comparison in A(iii), the three-unit marginal values, and B(i)'s pointwise zero generalized estimate; B(i)'s zero expectation is retained.

- **P026-T5**: Retain both independence conclusions in (a), the vector composition rule in (c), the additive prediction result in (d), and both examples in (e). In (b), unbiased totals and ATE are asserted only when every unit is independent of its fitting assignment vector. Omit unbiasedness under the weaker observed-outcome-vector premise and mixtures of the two premises across units.

- **P026-T6**: Retain the exact moments, residual vector, denominator positivity and rounding refutations for the specified opposite-block prediction and residualized FE formulas. Omit the separate assertions in A and B identifying those formulas as OLS fits or regression solutions; no least-squares optimality assertion is stated.

- **P026-T7**: Retain (a)-(c) and the selected HT and G (Prior) moments and variance rounding in (d). Omit (d)'s blanket assertion that all columns without X remain unchanged: no IPW or FE column entries, or HT/G (Prior) variance-estimator SE/RMSE entries 0.037 and 0.020, are asserted. The numerical statements use the specified prediction and residualized coefficient formulas; their identification as OLS fits or regression solutions is not stated.

- **P026-T9**: Retain the six printed-display values, its expectation -42, covariance and covariance bound -28, equation [34] continuation's expectation -28, true treatment-total variance 28, and exported support facts. Omit the explicit marginal values 1/2, equation [34]'s six pointwise values, and the population arm-variance-bound equality to 28.

The shared-definition route is used throughout. `Defs/Part1.lean` through
`Part4.lean` introduce SAP-named finite assignment designs, weighted sums,
variance and covariance expressions, the numerical populations, and the
unit and cluster records. `Part5.lean` through `Part16.lean` give the twelve
claim statements. They import only Mathlib and earlier Defs parts. Both
Challenge and Solution import the single compiled `SAP.P026a.Defs` root.
No project declarations are reintroduced under their project names.

`Bridge/Part1.lean` supplies these correspondences:

- `toAuditDesign`, `toAuditUnit`, and `toAuditCluster` preserve the data and
  proof fields. The design and cluster-total correspondences are `rfl`.
- `covariance_continuation_eq` identifies the explicit zero-omission guard
  with the project's total field formula. Splitting the zero-joint condition
  leaves a zero term or the identical expression. `repaired_covariance_eq`
  transports that equality through the directed-pair correction.
- `linear_residual_eq` uses the last conjunct of `table_linear_fits` to
  identify the actual sums of printed outcomes minus the specified linear
  predictions with the already certified rational residual vector.
- `full_support_arm_eq` simplifies the arm estimator to equation [31]
  under the stated same-arm support. It uses the existing
  `VarianceCompletion.zeroSum_of_positive` and simplifies the positive-joint
  guards and the printed epsilon. It supplies no new variance calculation.

`Bridge/Part2.lean` and `Part3.lean` assemble the paper clauses from the
usable rows. Other glue consists of these structural or arithmetic steps:

- T2 and T3 distribute fixed residual subtraction through finite cluster
  sums and use `generalized_residual`. The universally quantified outcome
  formulas therefore apply to all fixed residuals, including the sharp-null
  characterization, with the generalized contrast explicitly identified.
  T2 also records the directed-support failure and both exact biases of its
  nonconstant sharp-null witness using the existing certificates.
- T8 obtains the unconditional covariance lower-bound inequality from the
  exported exact gap and the nonnegativity of squares. T9 specializes the
  same exported gap to equal potential outcomes and obtains the covariance
  bound -28 from the exported covariance value. This is the quantity named
  by the refuted Appendix E assertion.
- T10 transports both arm equalities through subtraction and division for
  the ATE contrast. Its intermediate display steps replace unit indicators
  and marginals by their cluster values on each fiber and distribute scalar
  multiplication and division through the existing finite sums. The main
  aggregation equality is the credited project theorem.
- T11 specializes the existing unbiasedness conclusion through
  `full_support_arm_eq`. Both arms, the exact unavailable-pair bound gap,
  unbiased estimation of the bound, conservativeness, and the positive-support
  equality are stated.
- T12 retains the intermediate covariance sums of equation [21], using
  `ht_covariance_full_T12` and `sum_diagonal_off`, followed by scalar algebra.
  Equations [20], [22], both expressions of [23], and the complete corrected
  [24] are also stated. Its two `wrong_credit` numerical table rows are not
  used for this target.

The probability records permit zero-weight assignments and arbitrary
assignment dependence. A cluster record includes a surjective fixed unit
partition. Nonempty unit populations make every population-size denominator
positive. Positive treatment and control marginals are fields of `UnitLaw`.
The distinct-cluster premise is the standing convention from `work.json`;
no extra joint-support premise is imposed in T2, T11 or T12. T3 and the
observable covariance-estimator clauses of T8 use precisely the directed
support required by their canonical claims.

The covariance counterexample moments use an explicitly zero-omitted
continuation. They do not assign a meaning to literal equation [34] at a
zero directed denominator. The repaired covariance definition also omits
those terms explicitly. The numerical regression formulas use the project's explicit
normal-equation expressions; the Challenge includes positivity of both the
covariate norm and every treatment residual norm. Linear residuals are
computed from the supplied printed data and prediction formulas, with the
existing residual certificate supplying the correspondence. T6 and T7 do not
state an identification of these formulas as OLS solutions or minimizers; this
additional restriction keeps the statistical statements independent of that
identification. All numerical
models use exact rational arithmetic. Standard-deviation rounding and RMSE
comparison are expressed through squared quantities with positive rounding
endpoints, which is equivalent to the stated square-root comparisons.

Every Defs part and root, Bridge part and root, Challenge part and root, and
Solution compiled with `/home/ubuntu/sap/tools/sap-lean`. The dependency audit
in `scratch/P026aAxioms.lean` reports exactly `propext`, `Classical.choice`, and
`Quot.sound` for each of the twelve Solution theorems; its output is saved in
`scratch/P026aAxioms.log`. The separate-environment checks in `scratch/P026aChallengeTypes.lean` and
`scratch/P026aSolutionTypes.lean` produced identical theorem type expressions
and universe-parameter lists for all twelve theorems, saved in
`scratch/theorem-types.log`. Both JSON files parse. Target and row accounting,
exclusion of wrong-credit rows, the two implicit-variable options, source
restrictions, and the 300-line ceiling have been checked. Existing project
files are unchanged.

The comparator configuration lists all twelve theorems, no separately named
definitions, and the requested three-kernel policy. The supplied
[comparator result](SAP/P026a/verification/comparator-result.json) records
acceptance of all twelve theorems by all three kernels for the pre-review
snapshot dated 2026-11-03. Its recorded hash of `Defs/Part7.lean` precedes the
round-1 repair below, so that certificate does not certify the revised T3.
The current PATH provides neither the comparator nor the two external
kernels; a fresh external certification of the revised snapshot remains.

## Declaration review round 1

- **SAP.P026a.T3 — label_wrong / minor: accepted and fixed.** The
  [finding](fw/round1/T3/r2g1/findings.json) correctly identified the omitted
  nonimplication clause in the canonical claim
  ([work.json:412](/home/ubuntu/sap/wt/ARCH-P026a/work.json:412)). Assuming
  directed support for the estimator conclusions did not state that the
  standing assumptions fail to imply it. A separate T1 theorem did not fill
  that omission in T3's own statement.
- Added a final existential conjunct to `T3Statement`: a real-valued
  two-cluster finite assignment design is a normalized probability law,
  has positive marginals and separated indicators, and fails directed
  support. The witness has three equiprobable allocations, 00, 01 and 11;
  the omitted allocation 10 has probability zero. This is the original
  two-singleton-cluster example, expressed on its three positive-probability
  states rather than as a law on all four binary vectors.
- `Bridge.target3` transports the weights and indicators from
  [asymmetric_real_certificate](AronowAudit/P026/P026_Refutations.lean:15),
  projects its probability, marginal and separation facts, and contradicts
  directed support at the already certified zero joint (0,1). This is
  existential introduction, definitional transport and propositional glue;
  it adds no probability calculation or new mathematical argument.
- T3's Challenge docstring now names the nonimplication. Its `whole` label
  and theorem name `SAP.P026a.T3` are retained. The manifest records the
  certificate as a supporting declaration. The comparator configuration was
  regenerated and checked: the same twelve theorem names, shared-definition
  route, permitted axioms and external-kernel settings still apply.
- Only `T3Statement` changed in Defs. No common probability, estimator or
  population definition changed, and no other target statement refers to
  `T3Statement`; only T3's declaration closure needs renewed scope review.
  Every theorem nevertheless receives the required full rebuild and
  dependency audit. Other decisions and restrictions remain unchanged:
  6 whole, 6 restricted, 0 refuted, 0 omitted; 12 proved, 0 open glue tasks.

Round-1 validation completed successfully: all 24 SAP modules and three
scratch checks rebuilt in dependency order with `sap-lean` (exit 0).
All twelve rerun dependency audits report exactly the three permitted
axioms; see `scratch/P026aRound1Axioms.log`. Separate Challenge and Solution
environments again produced identical theorem types and universe parameters
for all twelve names; see `scratch/P026aRound1Types.log`. Both JSON files
parse, their target and row accounting agrees with `work.json`, and every
SAP Lean file retains both implicit-variable options and stays below 300
lines. Only the three Lean files listed above changed. The revised T3
statement requires fresh declaration review and external certification.

## Whole versions (new proofs)

The six targets below now use their proved whole statements. This section
supersedes the earlier restrictions and decision counts for these targets:
all twelve targets are now whole and proved. The other six targets retain
their existing statements, docstrings, proofs and manifest entries.

Each Challenge stub remains `:= by sorry` and imports only the permitted
Defs modules. Each Solution declaration uses the named `_whole` theorem
from its imported Proofs module. Solution imports no Challenge module.

- **P026-T9 (`SAP.P026a.T9`)**: `SAP.P026a.T9WholeStatement`,
  proved by `SAP.P026a.WH.W1.T9_whole`.
  Files: `SAP/P026a/Challenge/Part1.lean`, `SAP/P026a/Solution.lean`, `SAP/P026a/manifest.json`, `SAP/P026a/Defs/WholeW1.lean`, `SAP/P026a/WH/W1/Leaves.lean`, `SAP/P026a/WH/W1/Proofs/T9.lean`.
  Old restriction now removed: Retain the six printed-display values, its expectation -42, covariance and covariance bound -28, equation [34] continuation's expectation -28, true treatment-total variance 28, and exported support facts. Omit the explicit marginal values 1/2, equation [34]'s six pointwise values, and the population arm-variance-bound equality to 28.

- **P026-T1 (`SAP.P026a.T1`)**: `SAP.P026a.T1WholeStatement`,
  proved by `SAP.P026a.WH.W1.T1_whole`.
  Files: `SAP/P026a/Challenge/Part1.lean`, `SAP/P026a/Solution.lean`, `SAP/P026a/manifest.json`, `SAP/P026a/Defs/WholeW1.lean`, `SAP/P026a/WH/W1/Leaves.lean`, `SAP/P026a/WH/W1/P/T1_L1.lean`, `SAP/P026a/WH/W1/P/T1_L2.lean`, `SAP/P026a/WH/W1/Proofs/T1.lean`.
  Old restriction now removed: Retain both explicit designs and the exported support, HT, printed-variance and covariance-continuation facts. Omit A's exact marginal vector, exact disagreement and same-arm probabilities, and pointwise covariance-continuation values; omit B's exact marginal vector, probability minima, and grouped pointwise HT and printed-variance values. Literal equation [34] is diagnosed by its zero directed denominator (and A's zero numerator), without a partial-valued undefinedness assertion; its covariance moments refer explicitly to the zero-omitted continuation.

- **P026-T4 (`SAP.P026a.T4`)**: `SAP.P026a.T4WholeStatement`,
  proved by `SAP.P026a.WH.W1.T4_whole`.
  Files: `SAP/P026a/Challenge/Part1.lean`, `SAP/P026a/Solution.lean`, `SAP/P026a/manifest.json`, `SAP/P026a/Defs/WholeW1.lean`, `SAP/P026a/WH/W1/Leaves.lean`, `SAP/P026a/WH/W1/P/T4_L1.lean`, `SAP/P026a/WH/W1/Proofs/T4.lean`.
  Old restriction now removed: Retain both the six-unit and three-unit witnesses, their exported joint-cell, prediction, covariance, total and expectation facts. Omit the exact full fitting-set characterizations in A(ii), the explicit independence-failure probability comparison in A(iii), the three-unit marginal values, and B(i)'s pointwise zero generalized estimate; B(i)'s zero expectation is retained.

- **P026-T5 (`SAP.P026a.T5`)**: `SAP.P026a.T5WholeStatement`,
  proved by `SAP.P026a.WH.W1.T5_whole`.
  Files: `SAP/P026a/Challenge/Part1.lean`, `SAP/P026a/Solution.lean`, `SAP/P026a/manifest.json`, `SAP/P026a/Defs/WholeW1.lean`, `SAP/P026a/WH/W1/Leaves.lean`, `SAP/P026a/WH/W1/Proofs/T5.lean`.
  Old restriction now removed: Retain both independence conclusions in (a), the vector composition rule in (c), the additive prediction result in (d), and both examples in (e). In (b), unbiased totals and ATE are asserted only when every unit is independent of its fitting assignment vector. Omit unbiasedness under the weaker observed-outcome-vector premise and mixtures of the two premises across units.

- **P026-T6 (`SAP.P026a.T6`)**: `SAP.P026a.T6WholeStatement`,
  proved by `SAP.P026a.WH.W1.T6_whole`.
  Files: `SAP/P026a/Challenge/Part1.lean`, `SAP/P026a/Solution.lean`, `SAP/P026a/manifest.json`, `SAP/P026a/Defs/WholeW1.lean`, `SAP/P026a/WH/W1/Leaves.lean`, `SAP/P026a/WH/W1/P/T6_L1.lean`, `SAP/P026a/WH/W1/P/T6_L2.lean`, `SAP/P026a/WH/W1/P/T6_L3.lean`, `SAP/P026a/WH/W1/P/T6_L4.lean`, `SAP/P026a/WH/W1/Proofs/T6.lean`.
  Old restriction now removed: Retain the exact moments, residual vector, denominator positivity and rounding refutations for the specified opposite-block prediction and residualized FE formulas. Omit the separate assertions in A and B identifying those formulas as OLS fits or regression solutions; no least-squares optimality assertion is stated.

- **P026-T7 (`SAP.P026a.T7`)**: `SAP.P026a.T7WholeStatement`,
  proved by `SAP.P026a.WH.W2.T7_whole`.
  Files: `SAP/P026a/Challenge/Part1.lean`, `SAP/P026a/Solution.lean`, `SAP/P026a/manifest.json`, `SAP/P026a/Defs/WholeW2.lean`, `SAP/P026a/WH/W2/Leaves.lean`, `SAP/P026a/WH/W2/P/T7_L1.lean`, `SAP/P026a/WH/W2/P/T7_L2.lean`, `SAP/P026a/WH/W2/P/T7_L3.lean`, `SAP/P026a/WH/W2/P/T7_L4.lean`, `SAP/P026a/WH/W2/P/T7_L5.lean`, `SAP/P026a/WH/W2/P/T7_L6.lean`, `SAP/P026a/WH/W2/P/T7_L7.lean`, `SAP/P026a/WH/W2/P/T7_L8.lean`, `SAP/P026a/WH/W2/P/T7_L9.lean`, `SAP/P026a/WH/W2/P/T7_L10.lean`, `SAP/P026a/WH/W2/Glue.lean`, `SAP/P026a/WH/W2/Proofs/T7.lean`.
  Old restriction now removed: Retain (a)-(c) and the selected HT and G (Prior) moments and variance rounding in (d). Omit (d)'s blanket assertion that all columns without X remain unchanged: no IPW or FE column entries, or HT/G (Prior) variance-estimator SE/RMSE entries 0.037 and 0.020, are asserted. The numerical statements use the specified prediction and residualized coefficient formulas; their identification as OLS fits or regression solutions is not stated.

Proof dependency repairs: none were needed. Each other Solution theorem
uses its own `Bridge.targetN` proof term and does not use a switched theorem's
old statement. No other theorem declaration or proof was changed.

The manifest retains existing row credits and adds the whole theorem,
assembly, proved leaves, Bridge lemma and identifiable project dependencies
used by the new proofs. Existing definitions, leaves and generated Proofs
modules are unchanged.

Whole-version validation completed successfully. The required command
`python3 /home/ubuntu/sap/tools/rebuild_sap.py . P026a` rebuilt all 52
modules from scratch and reported a clean forbidden-token scan.
`scratch/P026aWholeAxioms.lean` imports `SAP.P026a.Solution` and runs
`#print axioms` on all six switched theorems; the results in
`scratch/P026aWholeAxioms.log` contain only `propext`, `Classical.choice`
and `Quot.sound`. The unchanged-target and import-closure checks passed.
No `lake` command was run; compilation used one Lean process at a time.
The six final switch records are in `switched.json`.
