# P027b package

Decisions: **9 whole, 2 restricted, 0 refuted, 0 omitted**. All **11** listed
theorems are proved; **0** open glue tasks remain. The only targets packaged are
P027-T14 through P027-T24.

## Restrictions

- **P027-T14:** Retains C1 in full: the two fixed five-unit-stratum populations,
  both true variances, all six design expectations, four biases and their reversed
  ranking. Drops C2's actual outcome-model-averaged bias identification and ranking
  reversal, and C3's actual averaged true variance, estimator expectations and
  relative biases at M=500. The narrower numeric row evaluates rational formulas
  without those probabilistic identifications. The separate model theorem
  credited to T15 is not used to enlarge T14. Quoted simulation rows are context.
- **P027-T16:** Retains the C1–C2 moment and correlation discrepancy at alpha=1/2
  for the explicit product law of three independent symmetric signs: correlation
  1/5 versus printed parameter 1/3, with difference 2/15. The errors in this
  witness replace the supplement's Gaussian errors. Drops a Gaussian-law witness
  and C3's divisor-1/divisor-2 interpretation of the two fixed stratum means.

There are no omitted targets. Counterexample targets T14 and T16 are themselves
counterexample claims, so their restricted witnesses are not classified as
refutations of positive canonical assertions.

## Whole targets and clause coverage

| Target | Content retained |
| --- | --- |
| T15 | Sample mean and all three estimator formulas, factor two, fixed-population variance, four actual model expectations, three nonnegative biases, all ranking cases and the heterogeneity threshold, exact ratios and differences, and all three large-size limits. |
| T17 | General common-stratum moments and correlation, actual divisor-1 stratum-mean variance, parameter comparison with equality condition, inverse conversion, strict monotonicity, left limit, and all six labels. |
| T18 | First-order inclusion, all joint cases including the diagonal, all covariance cases, actual indicator variance, and the M=2 diagonal discrepancy. The outcome-index correction is represented by stratumOutcomes. |
| T19 | Original mean-scale deterministic identities, actual model moments and conditional relative bias, calibration and four numerical predictions, orthogonal decomposition with dimensions and uniqueness, exact signal cancellation and lower bound, Gaussian representation and mean, general tail bound, four printed-row probability bounds, and exact rounding/floor/ceiling certificates. |
| T20 | Proposition 1's expectation identity, both same-sign cases, and positive- and negative-bias existence witnesses. |
| T21 | Both signs bounded by A-star, unbiased correction, exact corrected expectation, and conservativeness. |
| T22 | Both printed sufficient equality conditions imply unbiasedness; no necessity is asserted. |
| T23 | Equality with the exponent-two specialization and expected conservativeness. |
| T24 | Samplewise comparison with every constant conjugate pair and attainment at (2,2). |

## Definitions and bridges

The route is shared Mathlib-only definitions. Defs/Part1–Part2 define the finite
normalized designs, estimators, stratified model and moments. Part3–Part6 state
the nonperiodic targets; Part7–Part8 define and state the periodic claim. Both
Challenge and Solution import the same compiled Defs modules. No project module
is imported by Defs or Challenge.

- **Bridge/Part1:** toProject copies the Design weights, normalization and selected
  subsets. Its core correspondences and the concrete-design correspondences are
  proved by reduction. T14's extra bias values and rankings are arithmetic on the
  exported eight expectation/variance facts. T16 is direct transport. T18 adds
  indicator variance using the exported variance/second-moment and diagonal-joint
  identities. T20–T24 instantiate and combine the credited declarations; the two
  sign examples for T20 are projections of the credited cluster witnesses.
- **Bridge/Part2:** T15 combines the existing sample/model theorems, adds the
  definition of the collapsed estimator, and uses only scalar algebra for factor
  two, biases, nonnegativity and the heterogeneity threshold. T17 assembles the
  existing common-stratum, conversion, variance, monotonicity, limit and label facts.
- **Bridge/Part3:** phaseOriginal agrees by reduction. The two decomposition
  adapters copy every component and certificate; existence, uniqueness and the
  quadratic formula transport through those adapters. The proved Wave1 Gaussian,
  tail and printed-row declarations are used directly.
- **Bridge/Part4:** finite cardinal arithmetic and the existing constant-divisor
  expectation/variance identities convert the total-scale model moments to the
  original N-squared mean scale. The remaining work is scalar algebra on those
  moments, including the positive-expected-variance ratio and calibration.
- **Bridge/Part5:** the already proved floor/ceiling and rounding helpers give the
  explicit four-row certificates; all T19 components are conjoined.

No new probability argument, decomposition, inequality, asymptotic argument or
sampling-design result was added. The manifest names direct row applications,
explains unused rows individually, and lists additional exported glue helpers.

## Checks and points requiring care

Every Defs part and root, every Bridge part and root, the Challenge part and root,
and Solution compiled with the prescribed sap-lean wrapper in dependency order.
Every SAP file has both required implicit-argument options and is under 300 lines.
Both JSON files parse, cover exactly the eleven unit targets, and list identical
Challenge/Solution theorem names and statement definitions.

The scratch FinalDependencies.lean check ran for every Solution theorem. Each
reported exactly propext, Classical.choice and Quot.sound; the captured output is
scratch/final-dependencies.log. The Challenge contains only the required stubs.

Positive first-order probabilities are required for the general estimator
claims. Concrete stratified populations use M>0, and the periodic result uses
r>0 and m>=2. NoiseMoments and PairMoments explicitly require integrable errors
and products. Finite sums and quadratic expansions therefore have genuine finite
moments. Correlation denominators are positive from the displayed variance
formulas. T19 keeps the zero-noise case in its moment identities, qualifies its
relative-bias quotient by positive expected variance, and uses positive noise
variance for Gaussian law/tail claims. Probability measures keep all event masses
finite before conversion to real numbers.

The accepted canonical T19 text already includes these positive-variance clauses
and a probabilistic final conclusion. Older coverage notes concerning categorical
impossibility and missing positivity do not override that accepted text. No
realized replacement simulation values, faulty-column identification or
deterministic exclusion is asserted. The model predictions are explicitly linked
to actual outcome expectations under the stated calibration.

Palomar configuration is supplied in SAP/P027b/comparator.json. The orchestrator
subsequently supplied [a successful certification receipt](SAP/P027b/verification/comparator-result.json)
for the original snapshot: all eleven targets passed the Comparator and all three
kernels. That receipt predates the round 1 documentation correction described
below; it is retained as evidence for the original snapshot.

## Declaration review round 1

The sole open finding is the minor documentation issue for **SAP.P027b.T19** in
[the review findings](fw/round1/T19/r1g2/findings.json), corroborated by
[the review report](fw/round1/T19/r1g2/REPORT.md). The reviewer is right:
PeriodicRowCertificates was described as the complete six-clause finding with
positive-variance ratios, although its body contains only certificates for the
four printed rows. The full finding is T19Statement, and the expected-variance
ratio belongs to PeriodicModel.

Replaced that docstring in Defs/Part8.lean with: “Rowwise positivity, contrast,
rounding, and integer tail-exponent certificates for the four printed Table A3
means.” No mathematical definition body, theorem statement, hypothesis, proof,
restriction or decision changed. No finding is disputed.

The manifest records the finding and its documentation-only resolution on T19.
The Comparator configuration was rewritten and parsed; its settings and theorem
list are identical to those in the original certification receipt. The corrected
definition occurs in T19's statement closure. All other theorem statements retain
their existing definitions; the correction adds no new shared mathematical
definition and changes no shared mathematical body.

Recompiled every Defs part and root, every Bridge part and root, the Challenge
part and root, and Solution, in dependency order using sap-lean. The build passed;
the log is scratch/round1-compile.log. Reran the dependency print for all eleven
Solution theorems: each uses exactly propext, Classical.choice and Quot.sound.
The output is scratch/round1-dependencies.log.

Both JSON files parse, target and theorem lists agree, all eleven proofs remain
present under the same names, and all SAP source files retain both implicit-variable
options and the 300-line limit. The check in scratch/round1-validation.json also
confirms that replacing just the corrected docstring with its former text exactly
recovers the certified Defs/Part8.lean source hash, while every other Lean source
matches its certified hash. External kernels were not rerun for this documentation
revision. Counts remain **9 whole, 2 restricted, 0 refuted, 0 omitted; 11 proved,
0 open glue tasks**.

## Whole versions (new proofs)

P027-T14 and P027-T16 now have decision `whole`, no restriction, and proof status
`proved`. The current package has **11 whole, 0 restricted, 0 refuted, 0 omitted**
targets. The earlier restriction notes and counts above describe the prior version.
Both whole statements are defined in [Defs/WholeW1.lean](SAP/P027b/Defs/WholeW1.lean),
with their shared blueprint in [WH/W1/Leaves.lean](SAP/P027b/WH/W1/Leaves.lean).
The stubs in [Challenge/Part1.lean](SAP/P027b/Challenge/Part1.lean) and the proved
theorems in [Solution.lean](SAP/P027b/Solution.lean) now use these whole statements;
[manifest.json](SAP/P027b/manifest.json) records the new decisions and proof rows.

- **SAP.P027b.T14 (P027-T14):** `SAP.P027b.T14WholeStatement`, proved by
  `SAP.P027b.WH.W1.T14_whole` in [WH/W1/Proofs/T14.lean](SAP/P027b/WH/W1/Proofs/T14.lean),
  using the proved leaf [WH/W1/P/T14_L1.lean](SAP/P027b/WH/W1/P/T14_L1.lean).
  The whole version includes the actual Gaussian model-averaged biases at M=5,
  the averaged variance, estimates and relative biases at M=500, and integrability.
  **Old restriction now removed:** Retains C1, the two fixed M=5 populations, all design expectations, the true variances, and the reversed biases. Drops C2, identification and comparison of the actual outcome-model-averaged biases at M=5, and C3, the actual model-averaged true variance, estimator expectations and relative biases at M=500. The quoted simulation rows are context.
- **SAP.P027b.T16 (P027-T16):** `SAP.P027b.T16WholeStatement`, proved by
  `SAP.P027b.WH.W1.T16_whole` in [WH/W1/Proofs/T16.lean](SAP/P027b/WH/W1/Proofs/T16.lean),
  using the proved leaves [WH/W1/P/T16_L1.lean](SAP/P027b/WH/W1/P/T16_L1.lean) and
  [WH/W1/P/T16_L2.lean](SAP/P027b/WH/W1/P/T16_L2.lean).
  The whole version uses independent standard Gaussian errors, includes both
  fixed-mean variance conventions and the random-stratum variance, and proves
  the conditional variances, covariance and correlation with finite second moments.
  **Old restriction now removed:** Retains the C1-C2 numerical moment and correlation discrepancy at alpha=1/2 for the explicit product law of three independent symmetric signs. Replaces the printed Gaussian errors by these discrete errors; no Gaussian-law witness is asserted. Drops C3, the divisor-1 and divisor-2 variance interpretation of the two stratum means.
