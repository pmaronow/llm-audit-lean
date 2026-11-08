# P005a packaging report

Work: *Exact Bias Correction for Linear Adjustment of Randomized Controlled Trials*, Econometrica 92(5), 1503–1519 (2024), DOI 10.3982/ECTA20289.

Decisions: **2 whole, 11 restricted, 0 refuted, 1 omitted**. There are **13 proved theorems and 0 open glue tasks**. Only P005-T1 through P005-T14 are packaged. Counterexample targets already include their refutations in their canonical claims, so they are classified by clause completeness rather than as refuted positive assertions.

## Target restrictions and omission

- **P005-T1 (restricted):** Omits the separate product mean, the explicit expectation-factor identity, the individual coefficients and moments decomposing the bound, the exact positive gap, and all translation-invariance and centered-bound comparisons in canonical part (v).

- **P005-T2 (restricted):** Omits the separately asserted proof-step conclusions (a)–(d): assignmentwise location invariance, the sample-mean variance identity, the expectation and exact variance formula for the product of centered sums and its bound, and the generic variance-difference inequality. No literature proposition is assumed.

- **P005-T3 (restricted):** Omits the exact outcome second moment and allocation fraction, the explicit leverage-vector and mean-leverage identities, the zero centered-product moment, the three-category probabilities and covariance values, both exact gaps, and the third-expression and centered-bound comparisons in canonical part (vi).

- **P005-T4 (restricted):** Omits the intermediate chain mean(u²) ≤ mean(h²) ≤ nκd, the order of the numerical right-hand side, and both explicit allocation-coefficient bounds. The asymptotic part additionally requires positive covariate dimension at every n ≥ 3; its size, moment and allocation assumptions are imposed from n = 3.

- **P005-T5 (restricted):** Omits the exact outcome second moments, explicit allocation fraction, positive within-arm variance assertions, mean-leverage and outcome-mean identities, the separate leverage formula and third-moment coefficients, the two individual signed expectations, and the separate numerical value of the reversed-sign formula.

- **P005-T7 (restricted):** Omits the pointwise outcome bounds |y_i(1)| = |y_i(0)| ≤ 1 from canonical part (i), the exact grid sums, closed formulas for q, leverage and the population slope, the individual fitted-line and leading-term calculations and bounds, the separate rate and remainder-ratio bounds, the probability-one tail identities, and both finite-size numerical checks in canonical part (vi). The normalizing q is explicitly positive for n ≥ 6; initial total-function values are not asserted to describe normalized populations.

- **P005-T8 (omitted):** The only credited expansion theorem requires the unproved proposition Tropp2011RowSampling. The canonical claim has no such hypothesis, and no unconditional estimator expansion is available from this row. Do not turn the cited proposition into an assumption. The separately targeted logarithm equivalences are retained in T9.

- **P005-T9 (restricted):** Drops the interacted-estimator stochastic expansion and its remainder rate; retains only canonical equivalence clauses (a)–(c), for eventually positive dimensions and eventually nonnegative leverage sequences.

- **P005-T10 (restricted):** Omits the explicit assignment count and positive within-arm variance assertions, the leverage and mean-leverage identities, the exact population leverage covariance, the assignmentwise difference of the two expressions and its exact expectation gap, and the separate rational-coordinate scaling identities.

- **P005-T11 (restricted):** Omits the unsimplified alternative expression for the cancelling treated weight and the separate leverage-range assertion. The generic control expectation, weight uniqueness and unbiasedness are stated only for n_C ≥ 2. The asymptotic part requires positive dimension at every n ≥ 3 and imposes size, moment and allocation assumptions from n = 3.

- **P005-T12 (restricted):** Omits the explicit assignment count, mean-leverage identity, identification with the sum of the three nu components, and the separate rational-coordinate scaling identities. The three expectations and the strict wrong-inverse mismatch are stated directly in scalar OLS notation.

- **P005-T14 (restricted):** Omits the separate assertion that the incorrectly printed treated-set control sum can differ from the control mean. The actual-bias identity additionally requires standardized covariates and regularity under every assignment, and the observed-outcome factorization additionally requires standardized covariates.

The whole targets are P005-T6 (including the two individual signed expectations) and P005-T13 (including every component expectation and both coefficient equalities). Review coverage labels were not treated as permission to drop a canonical clause while calling a theorem whole. The narrower T4 rows are used only at their actual exported types.

## Definition and bridge route

All mathematical definitions live under `SAP.P005a` in seven Mathlib-only Defs parts. Both theorem modules import the same compiled Defs root. The definitions use the actual finite uniform assignment law, ordinary finite sums, matrix operations, real limits, and deterministic Big-O. No project module is imported by Defs or Challenge. Project declarations were not recreated in their original namespace.

`Bridge/Part1.lean` provides field-preserving adapters between the two population structures and an arm adapter. The population adapters are mutual inverses by `rfl`; the arm-set and arm-size correspondences are by cases followed by `rfl`. Covariance, standardization, leverage, maximum leverage, arm matrices, arm moments, the noninteracted matrix and sequence assumptions agree by `rfl`. The four explicit population witnesses also agree by `rfl`.

`Bridge/Part2.lean` proves the concrete T1, T3, T5, T7, T9, T10 and T12 statement correspondences by `Iff.rfl`. Their types reduce to the shared SAP definitions. Generic statements in the Solution instantiate the existing results at `toPopulation P`; the two arm cases align their branches. Complement transport and expectation negation instantiate existing finite-law results. The signed T6 components use the existing nu3 sign identity and expectation linearity, followed by ring normalization. The extra T14 displayed identities use unfolding, ring normalization and linear arithmetic on the two exported expansions. No new probability, variance, sampling, matrix or asymptotic argument is introduced.

P005-T2 deserves special attention: its credited conditional theorem is not instantiated. The already proved `GP005B4c_covariance_arm`, `control_arm_covariance_expectation` and complement transport supply the main repaired lemma without a literature premise. The existing location-invariance and variance-difference rows occur inside that unconditional proof. The exact product-of-sums variance formula is not added. P005-T8 and the expansion part of T9 remain unavailable without a missing literature proof; no such premise was added.

## Definedness and scope checks

All substantive finite randomization assertions have nonempty arms and a nonempty assignment support. Generic inverse uses retain determinant conditions, and the scalar inverse counterexample explicitly has positive variances in both arms. Maximum leverage is used with positive population sizes. The spike witness explicitly has positive normalizer q for n ≥ 6. Sequence conclusions use tails with n ≥ 3; initial values of total functions are not asserted to describe valid experiments. There are no nonintegrable means, infinite quantiles or infinite extended-real conversions in these statements.

The source sequence assumptions impose positive dimension from n = 3, in addition to the paper's moment, standardization and allocation conditions. This restriction is disclosed in T4 and T11. The stronger all-assignment population hypotheses used for T14's actual-bias identity and the standardization condition used for its observed-data factorization are also disclosed.

## Verification

All 14 SAP Lean files compiled successfully with the prescribed `sap-lean` wrapper in dependency order. The final rebuild also compiled `scratch/CheckAxioms.lean`, `scratch/CheckChallengeTypes.lean` and `scratch/CheckSolutionTypes.lean`. The only warnings were the intended Challenge placeholders.

`#print axioms` was run for every one of the 13 Solution theorems. Each reported exactly `propext`, `Classical.choice` and `Quot.sound`; the manifest records these results. The output and signature-check results are in `scratch/final_verification.log`.

The Challenge and Solution were separately loaded and all 13 theorem types were checked as raw Lean expressions, without reduction: each is precisely its shared `SAP.P005a.TkStatement` constant. The common definitions are imported from the same compiled Defs modules. Both JSON files parse. Target and row accounting, theorem-name agreement, import boundaries, option settings, source-token restrictions and the 300-line file limit pass (`scratch/structural_checks.json`). No existing project file was changed.

The initial local packaging did not run the Palomar Comparator. The subsequently supplied [baseline comparator result](SAP/P005a/verification/comparator-result.json) records acceptance of all 13 theorems by con-ron, nanoda and the Lean kernel for the pre-review snapshot. That historical result is retained without alteration; it is not a new certification run for this documentation revision.

Every listed theorem is proved. There are no open glue tasks and no proof-writer plans.

## Declaration review round 1

- **SAP.P005a.T7 / P005-T7 — restriction_inaccurate, minor:** Accepted the sole open finding in [the T7 review entry](fw/round1/T7/r1g2/findings.json), corroborated by [the reviewer report](fw/round1/T7/r1g2/REPORT.md). Canonical part (i) in `work.json` separately asserts the pointwise bounds `|y_i(1)| = |y_i(0)| ≤ 1`; `T7Statement` states only the population mean-square bounds. The previous omission list mentioned fitted-line and leading-term bounds from other clauses and did not disclose this omission. Added the exact pointwise clause to the T7 Challenge docstring, manifest restriction and target restriction above.

The correction changes only scope documentation. No theorem name, proposition, proof, bridge or shared definition was changed. T7 remains restricted; counts remain 2 whole, 11 restricted, 0 refuted, 1 omitted, with 13 proofs and no open glue tasks. `comparator.json` was regenerated and revalidated against the same 13 theorem names; its configuration content is unchanged. The review file also contains faithful findings for T6, T9, T10 and T11, which require no correction.

Round 1 validation: rebuilt all 14 SAP Lean modules with `sap-lean` in dependency order, then reran `#print axioms` for every Solution theorem and both independent statement-identity checks. All passed; each of the 13 proofs uses exactly `propext`, `Classical.choice` and `Quot.sound`. Both JSON files parse, all restriction descriptions match their docstrings, theorem names and row accounting agree, both implicit-variable options and the 300-line limit hold, and the source-token scan passes. Evidence: [validation log](scratch/round1_verification.log), [structural checks](scratch/round1_structural_checks.json), and [unchanged mathematical-source hashes](scratch/round1_unchanged_sources.json). No external comparator run was performed this round.

## Whole versions (new proofs)

The eleven targets below now use their supplied whole statements and compiled whole proofs. This section supersedes their earlier restriction descriptions. Current decisions are 13 whole, 0 restricted, 0 refuted and 1 omitted; P005-T6, P005-T8 and P005-T13 are unchanged.

Shared changed files: `SAP/P005a/Challenge/Part1.lean`, `SAP/P005a/Solution.lean` and `SAP/P005a/manifest.json`. Each Challenge stub keeps `:= by sorry`; each Solution proof is the corresponding `_whole` theorem.

- **P005-T14 / `SAP.P005a.T14`**: `SAP.P005a.T14WholeStatement` in `SAP/P005a/Defs/WholeW1.lean`; blueprint `SAP/P005a/WH/W1/Leaves.lean`; generated proof `SAP/P005a/WH/W1/Proofs/T14.lean` using `SAP.P005a.WH.W1.T14_whole`.
  Proved leaves: `SAP/P005a/WH/W1/P/T14_L1.lean`.
  Removed restriction: Omits the separate assertion that the incorrectly printed treated-set control sum can differ from the control mean. The actual-bias identity additionally requires standardized covariates and regularity under every assignment, and the observed-outcome factorization additionally requires standardized covariates.

- **P005-T1 / `SAP.P005a.T1`**: `SAP.P005a.T1WholeStatement` in `SAP/P005a/Defs/WholeW1.lean`; blueprint `SAP/P005a/WH/W1/Leaves.lean`; generated proof `SAP/P005a/WH/W1/Proofs/T1.lean` using `SAP.P005a.WH.W1.T1_whole`.
  Removed restriction: Omits the separate product mean, the explicit expectation-factor identity, the individual coefficients and moments decomposing the bound, the exact positive gap, and all translation-invariance and centered-bound comparisons in canonical part (v).

- **P005-T2 / `SAP.P005a.T2`**: `SAP.P005a.T2WholeStatement` in `SAP/P005a/Defs/WholeW1.lean`; blueprint `SAP/P005a/WH/W1/Leaves.lean`; generated proof `SAP/P005a/WH/W1/Proofs/T2.lean` using `SAP.P005a.WH.W1.T2_whole`.
  Proved leaves: `SAP/P005a/WH/W1/P/T2_L1.lean`.
  Removed restriction: Omits the separately asserted proof-step conclusions (a)–(d): assignmentwise location invariance, the sample-mean variance identity, the expectation and exact variance formula for the product of centered sums and its bound, and the generic variance-difference inequality. No literature proposition is assumed.

- **P005-T3 / `SAP.P005a.T3`**: `SAP.P005a.T3WholeStatement` in `SAP/P005a/Defs/WholeW1.lean`; blueprint `SAP/P005a/WH/W1/Leaves.lean`; generated proof `SAP/P005a/WH/W1/Proofs/T3.lean` using `SAP.P005a.WH.W1.T3_whole`.
  Proved leaves: `SAP/P005a/WH/W1/P/T3_L1.lean`.
  Removed restriction: Omits the exact outcome second moment and allocation fraction, the explicit leverage-vector and mean-leverage identities, the zero centered-product moment, the three-category probabilities and covariance values, both exact gaps, and the third-expression and centered-bound comparisons in canonical part (vi).

- **P005-T4 / `SAP.P005a.T4`**: `SAP.P005a.T4WholeStatement` in `SAP/P005a/Defs/WholeW1.lean`; blueprint `SAP/P005a/WH/W1/Leaves.lean`; generated proof `SAP/P005a/WH/W1/Proofs/T4.lean` using `SAP.P005a.WH.W1.T4_whole`.
  Proved leaves: `SAP/P005a/WH/W1/P/T4_L1.lean`.
  Removed restriction: Omits the intermediate chain mean(u²) ≤ mean(h²) ≤ nκd, the order of the numerical right-hand side, and both explicit allocation-coefficient bounds. The asymptotic part additionally requires positive covariate dimension at every n ≥ 3; its size, moment and allocation assumptions are imposed from n = 3.

- **P005-T5 / `SAP.P005a.T5`**: `SAP.P005a.T5WholeStatement` in `SAP/P005a/Defs/WholeW2.lean`; blueprint `SAP/P005a/WH/W2/Leaves.lean`; generated proof `SAP/P005a/WH/W2/Proofs/T5.lean` using `SAP.P005a.WH.W2.T5_whole`.
  Removed restriction: Omits the exact outcome second moments, explicit allocation fraction, positive within-arm variance assertions, mean-leverage and outcome-mean identities, the separate leverage formula and third-moment coefficients, the two individual signed expectations, and the separate numerical value of the reversed-sign formula.

- **P005-T7 / `SAP.P005a.T7`**: `SAP.P005a.T7WholeStatement` in `SAP/P005a/Defs/WholeW2.lean`; blueprint `SAP/P005a/WH/W2/Leaves.lean`; generated proof `SAP/P005a/WH/W2/Proofs/T7.lean` using `SAP.P005a.WH.W2.T7_whole`.
  Proved leaves: `SAP/P005a/WH/W2/P/T7_L1.lean`, `SAP/P005a/WH/W2/P/T7_L2.lean`, `SAP/P005a/WH/W2/P/T7_L3.lean`, `SAP/P005a/WH/W2/P/T7_L4.lean`, `SAP/P005a/WH/W2/P/T7_L5.lean`, `SAP/P005a/WH/W2/P/T7_L6.lean`.
  Removed restriction: Omits the pointwise outcome bounds |y_i(1)| = |y_i(0)| ≤ 1 from canonical part (i), the exact grid sums, closed formulas for q, leverage and the population slope, the individual fitted-line and leading-term calculations and bounds, the separate rate and remainder-ratio bounds, the probability-one tail identities, and both finite-size numerical checks in canonical part (vi). The normalizing q is explicitly positive for n ≥ 6; initial total-function values are not asserted to describe normalized populations.

- **P005-T9 / `SAP.P005a.T9`**: `SAP.P005a.T9WholeStatement` in `SAP/P005a/Defs/WholeW2.lean`; blueprint `SAP/P005a/WH/W2/Leaves.lean`; generated proof `SAP/P005a/WH/W2/Proofs/T9.lean` using `SAP.P005a.WH.W2.T9_whole`.
  Proved leaves: `SAP/P005a/WH/W2/P/T9_L1.lean`, `SAP/P005a/WH/W2/P/T9_L2.lean`, `SAP/P005a/WH/W2/P/T9_L3.lean`, `SAP/P005a/WH/W2/P/T9_L4.lean`, `SAP/P005a/WH/W2/P/T9_L5.lean`, `SAP/P005a/WH/W2/P/T9_L6.lean`, `SAP/P005a/WH/W2/P/T9_L7.lean`, `SAP/P005a/WH/W2/P/T9_L8.lean`, `SAP/P005a/WH/W2/P/T9_L9.lean`, `SAP/P005a/WH/W2/P/T9_L10.lean`, `SAP/P005a/WH/W2/P/T9_L11.lean`, `SAP/P005a/WH/W2/P/T9_L12.lean`, `SAP/P005a/WH/W2/P/T9_L13.lean`, `SAP/P005a/WH/W2/P/T9_L14.lean`, `SAP/P005a/WH/W2/P/T9_L15.lean`.
  Removed restriction: Drops the interacted-estimator stochastic expansion and its remainder rate; retains only canonical equivalence clauses (a)–(c), for eventually positive dimensions and eventually nonnegative leverage sequences.

- **P005-T10 / `SAP.P005a.T10`**: `SAP.P005a.T10WholeStatement` in `SAP/P005a/Defs/WholeW2.lean`; blueprint `SAP/P005a/WH/W2/Leaves.lean`; generated proof `SAP/P005a/WH/W2/Proofs/T10.lean` using `SAP.P005a.WH.W2.T10_whole`.
  Removed restriction: Omits the explicit assignment count and positive within-arm variance assertions, the leverage and mean-leverage identities, the exact population leverage covariance, the assignmentwise difference of the two expressions and its exact expectation gap, and the separate rational-coordinate scaling identities.

- **P005-T11 / `SAP.P005a.T11`**: `SAP.P005a.T11WholeStatement` in `SAP/P005a/Defs/WholeW2.lean`; blueprint `SAP/P005a/WH/W2/Leaves.lean`; generated proof `SAP/P005a/WH/W2/Proofs/T11.lean` using `SAP.P005a.WH.W2.T11_whole`.
  Removed restriction: Omits the unsimplified alternative expression for the cancelling treated weight and the separate leverage-range assertion. The generic control expectation, weight uniqueness and unbiasedness are stated only for n_C ≥ 2. The asymptotic part requires positive dimension at every n ≥ 3 and imposes size, moment and allocation assumptions from n = 3.

- **P005-T12 / `SAP.P005a.T12`**: `SAP.P005a.T12WholeStatement` in `SAP/P005a/Defs/WholeW3.lean`; blueprint `SAP/P005a/WH/W3/Leaves.lean`; generated proof `SAP/P005a/WH/W3/Proofs/T12.lean` using `SAP.P005a.WH.W3.T12_whole`.
  Removed restriction: Omits the explicit assignment count, mean-leverage identity, identification with the sum of the three nu components, and the separate rational-coordinate scaling identities. The three expectations and the strict wrong-inverse mismatch are stated directly in scalar OLS notation.

Dependent Solution proof repairs: none. No other Solution proof refers to a switched target; the P005-T6 and P005-T13 declarations and proofs remain byte-for-byte unchanged.

The existing Defs, blueprints, leaves and generated whole proofs are reused without modification. The manifest retains previous rows and adds the whole proof, its assembly and leaf proofs, and identifiable supporting project declarations. Existing `rows_not_used` entries are preserved as requested.

Validation of the whole switches: `python3 /home/ubuntu/sap/tools/rebuild_sap.py . P005a` rebuilt all 61 unit modules from scratch and reported a clean token scan. `scratch/CheckWholeSwitchAxioms.lean` imports only `SAP.P005a.Solution` and runs `#print axioms` for all eleven switched theorems; each reports exactly `propext`, `Classical.choice` and `Quot.sound`. Lean processes ran sequentially, and no `lake` command was run. Scope checks confirm that only the requested Challenge/Solution declarations and permitted manifest fields changed; all existing Defs, bridges, whole proofs, leaves and other target entries are unchanged. Per-target results are in `switched.json`.
