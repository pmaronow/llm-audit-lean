P033 packages **11 whole, 4 restricted, 0 refuted and 3 omitted targets**. All 15 listed theorems are proved; there are no open glue tasks.

Earlier certification repair: the strict runner rejected P033-T16 because the manifest used `omission_reason`, which its completeness check does not recognize. The existing explanations for T16, T17 and T18 were moved verbatim to the accepted `reason` field. The manifest was also formatted to 285 lines to meet the file-length limit. That repair changed no Lean sources or decisions and was subsequently accepted by the orchestrator's three-kernel run. Declaration review round 1 below changes T4's scope label and docstring; every theorem statement, definition and proof remains unchanged.

The canonical claims govern the statements. The counterexample targets already ask for counterexamples, so their decisions are whole or restricted, rather than refuted. No empirical diagnosis or table entry is inferred from a mathematical witness.

The restrictions are recorded identically in the Challenge docstrings and manifest:

- **P033-T1:** Omits the one-side probabilistic identities Var(sum a_i Y_i) = 83/50, Var(sum d_i Y_i) = 243/50, Cov(sum a_i Y_i, sum d_i Y_i) = -21/25, and Var(sum b_i Y_i) = 41/5. Retains the corresponding deterministic coefficient certificates and numerical variance decomposition, both full-estimator probability witnesses, WLS normal-equation certificates, and the realized comparison.
- **P033-T2:** Omits higher differentiability of the conditional mean functions. Retains their continuity, the quartic expansion and its zeros and cutoff value, the conditional-law identities, all coverage and study-count conclusions, and the general bias-adjustment variance identity.
- **P033-T4:** Omits the physical n(n+1)-cluster-per-side grid at distances j/[n(n+1)], the bandwidths h=b=1/n, and the identification of its exactly n positive-kernel-weight clusters per side and its estimators with the normalized n-point design. Retains all normalized-grid identities, the variance limit n V_n -> 48/5, the residual cancellation, the independent-cluster plug-in results and the stipulated table arithmetic.
- **P033-T5:** Adds dE != dI and 0 < sd to the general count-scaling clause so that its Wald effect and standardization have nonzero denominators. Omits no clauses of the concrete binary-outcome witness.

The omissions are:

- **P033-T16:** No Lean rows. This is the printed empirical diagnosis of the original studies, including the majority assertion. The conditional witnesses in T1–T2 do not establish that diagnosis.
- **P033-T17:** No Lean rows. The printed methodological description and empirical power-table entries are not certified by the clustered counterexample or its mathematical correction in T3–T4.
- **P033-T18:** No Lean rows. The printed standardization description and empirical table cells are not certified by the individual-outcome example or correction in T5–T6.

[Defs.lean](SAP/P033/Defs.lean) imports four parts containing shared SAP definitions built from Mathlib notions. These include actual Gaussian measures and their CDF, explicit product outcome laws, uniform finite means and variances, finite coefficient vectors, interval integrals, binomial sums and the stated limits. Challenge imports only these definitions. Solution imports the same compiled definitions and the project through [Bridge.lean](SAP/P033/Bridge.lean).

The bridges compare the project types with the SAP formulations by `Iff.rfl`, with explicit matching universe parameters where necessary. There are no structure adapters. T5 instead uses an implication that projects the original conjunction and inserts the two denominator guards into its scaling clause. The additional T7 conditioning certificate instantiates the existing density-integral and product-measure formulas: the 20% window has mass 2401/12500, and the event that all 19 observations fall in that window has positive product mass and implies that the caliper count is 19.

The additional existing declarations and glue are:

| Targets | Existing facts and transport |
| --- | --- |
| T1 | `m1_exact_certificate` and `m1_wls_rows` retain the Gram, determinant, reproduction, inverse-row and realization certificates. The displayed bias/corrected vectors and variance ratio use finite arithmetic. |
| T2 | `m2_polynomial_certificate` supplies the explicit polynomial properties and continuity. The existing M1 moments, pivot and Gaussian tail bound are transported along `m2_conditional_law_eq`. Equality of study laws is transported to measurable statistics. |
| T3 | `cluster_exact_certificate` and `cluster_wls_rows` supply the missing Gram, kernel and WLS certificates. `nn_residual_sum` supplies the noisy zero scores. The existing zero-estimate counts are transported to membership in the actual zero-width intervals by finite-set extensionality. |
| T4 | Direct definitional transport of the credited normalized-grid statement; the physical-grid and bandwidth clauses are omitted and disclosed. |
| T6, T12–T15 | Direct definitional transport of the credited complete statements. |
| T5 | Logical weakening of the credited scaling clause, preserving the full concrete witness. |
| T7 | The credited statement is supplemented by `caliper_exact_tails` and the positive conditioning event described above. |
| T8 | The credited density theorem is supplemented by the structural finite-set inclusion proving that successes do not exceed the window count. |
| T9 | The credited theorem is supplemented by arithmetic for the four overlaps and positivity/strict upper bounds for the four ratios. |
| T10 | The credited witness is supplemented by the reciprocal-line height calculation. |
| T11 | Existing Gaussian quantile bounds and critical-value positivity give the reciprocal-slope enclosure 0.51021 < 1/z < 0.51022 by arithmetic. |

The [manifest](SAP/P033/manifest.json) records every credited row used and the additional supporting declarations. All credited rows in this unit are usable and are used; none are discarded. No hypothesis was imported from review suggestions. No new statistical or asymptotic argument was written.

The probability witnesses in T1–T2 use the explicit law conditional on the eight fixed scores. Equality of these kernels is not asserted to be equality of the unconditional random-score population laws, and exact coverage at the displayed mean functions is not a uniform smoothness-class guarantee. The clustered sign models use the uniform finite Boolean cube, with its ordinary finite expectation and variance. T4 states only the normalized n-point-per-side design; no physical bandwidth or reduction from a larger grid is asserted. Its finite assertions require n >= 3, and its limit is unaffected by the total functions' initial values. The actual limits in T4, T7 and T8 are included despite stale asymptotic metadata in the history.

The saved standard error, counts, weights and threshold-crossing facts have the stipulated status given in the canonical claims. Theorems about their fractions are arithmetic, not a verification of replication files or regenerated tables. Positive standard deviations, nonzero denominators, positive conditioning masses, integrable normalized densities and positive interval lengths guard the quantities where needed. The new study-statistic pushforward clause explicitly requires measurability. The honest-length statements include existence, uniqueness, positivity and the defining coverage equality, and the normal critical value is tied to the actual Gaussian quantile.

All nine SAP Lean files, in dependency order, and [CheckAxioms.lean](scratch/CheckAxioms.lean) were recompiled successfully after declaration review round 1 using the specified `sap-lean` wrapper. Every SAP Lean file has both required implicit-variable options and at most 247 lines. Each of the 15 proved theorems again reports exactly `propext`, `Classical.choice` and `Quot.sound`; the output is saved in [proof-dependencies.log](scratch/proof-dependencies.log). Both JSON files parse, cover exactly the 18 unit targets, and list exactly the 15 non-omitted theorem names. The accepted reason fields for T16–T18 are preserved. The round-1 validation evidence is recorded in [round1-validation.json](scratch/round1-validation.json).

[comparator.json](SAP/P033/comparator.json) was resynchronized with the manifest and retains the same modules, 15 theorem names, permitted dependencies and external-kernel settings. The orchestrator's [strict result](SAP/P033/verification/comparator-result.json), dated 2026-11-03 23:37:41 UTC, records acceptance by Lean, con-ron and nanoda of the snapshot before declaration review round 1. That record is retained without alteration; it predates the corrected T4 label and docstring. The strict runner creates certification directories and worktrees outside this task's permitted write locations, so a new frozen-snapshot certification run remains with the orchestrator.

## Declaration review round 1

The open finding is **SAP.P033.T4 / P033-T4, `label_wrong`, major**, fingerprint `f5c1a01a13ef4ad0`; both issues in its [findings entry](fw/round1/T4/r1g1/findings.json) are accepted after checking the canonical claim, definitions and credited theorem.

1. **Whole label omits the physical-design clause.** [Canonical T4(iii)](/home/ubuntu/sap/wt/ARCH-P033/work.json:211) specifies n(n+1) physical clusters per side, scores j/[n(n+1)], bandwidths h=b=1/n, and exactly n positive-weight clusters per side. [The SAP distance](/home/ubuntu/sap/wt/ARCH-P033/SAP/P033/Defs/Part1.lean:146) is only (j+1)/(n+1) on `Fin n`; [T4Statement](/home/ubuntu/sap/wt/ARCH-P033/SAP/P033/Defs/Part2.lean:186) does not state the physical grid or its reduction to those normalized estimators. The credited [project theorem](/home/ubuntu/sap/wt/ARCH-P033/AronowAudit/P033/P033_Audit.lean:2396) has the same limitation, notwithstanding its explanatory comments and historical full-coverage judgment. Changed T4 from `whole` to `restricted`, with the exact omitted physical-grid, bandwidth and identification clauses disclosed in the manifest and docstring. No physical-design argument was added.
2. **Docstring overstates shrinking-bandwidth scope.** Replaced the assertion that cancellation persists in a shrinking-bandwidth sequence with a description of the normalized n-point-per-side triangular-kernel design. The restriction explicitly preserves all existing normalized-grid identities, the variance limit, cancellation, independent-cluster plug-in results and stipulated table arithmetic. It no longer suggests that a physical bandwidth is part of the statement.

No shared definition changed, so no other declaration acquires a changed definition dependency. The T4 statement and proof remain identical under `SAP.P033.T4`, and all other theorem names and statements are preserved. Counts change only from 12 whole / 3 restricted to 11 whole / 4 restricted; all 15 theorems remain proved and there are no open glue tasks. There are no disagreements with the open finding.

## Whole versions (new proofs)

P033-T1, P033-T2, P033-T4 and P033-T5 now use the proved whole statements and decisions in `switch.json`. This section supersedes the earlier restriction descriptions: P033 now has 15 whole, 0 restricted, 0 refuted and 3 omitted targets.

Each switched declaration in [Challenge/Part1.lean](SAP/P033/Challenge/Part1.lean) retains `:= by sorry` and uses the exact new docstring. [Solution.lean](SAP/P033/Solution.lean) imports the generated Proofs modules and uses their `_whole` theorem terms. The whole definitions in [Defs/WholeW1.lean](SAP/P033/Defs/WholeW1.lean), the blueprint [Leaves.lean](SAP/P033/WH/W1/Leaves.lean), and the existing proved leaves are unchanged.

- **P033-T1 / SAP.P033.T1:** `SAP.P033.T1WholeStatement`, proved by `SAP.P033.WH.W1.T1_whole` in [SAP/P033/WH/W1/Proofs/T1.lean](SAP/P033/WH/W1/Proofs/T1.lean); supporting files: `WH/W1/Existing.lean` and `WH/W1/Moments.lean`.
  Old restriction now removed: Omits the one-side probabilistic identities Var(sum a_i Y_i) = 83/50, Var(sum d_i Y_i) = 243/50, Cov(sum a_i Y_i, sum d_i Y_i) = -21/25, and Var(sum b_i Y_i) = 41/5. Retains the corresponding deterministic coefficient certificates and numerical variance decomposition, both full-estimator probability witnesses, WLS normal-equation certificates, and the realized comparison.
- **P033-T2 / SAP.P033.T2:** `SAP.P033.T2WholeStatement`, proved by `SAP.P033.WH.W1.T2_whole` in [SAP/P033/WH/W1/Proofs/T2.lean](SAP/P033/WH/W1/Proofs/T2.lean); supporting files: `WH/W1/Existing.lean` and `WH/W1/Moments.lean`.
  Old restriction now removed: Omits higher differentiability of the conditional mean functions. Retains their continuity, the quartic expansion and its zeros and cutoff value, the conditional-law identities, all coverage and study-count conclusions, and the general bias-adjustment variance identity.
- **P033-T4 / SAP.P033.T4:** `SAP.P033.T4WholeStatement`, proved by `SAP.P033.WH.W1.T4_whole` in [SAP/P033/WH/W1/Proofs/T4.lean](SAP/P033/WH/W1/Proofs/T4.lean); supporting files: `WH/W1/P/T4_L1.lean` through `WH/W1/P/T4_L6.lean`.
  Old restriction now removed: Omits the physical n(n+1)-cluster-per-side grid at distances j/[n(n+1)], the bandwidths h=b=1/n, and the identification of its exactly n positive-kernel-weight clusters per side and its estimators with the normalized n-point design. Retains all normalized-grid identities, the variance limit n V_n -> 48/5, the residual cancellation, the independent-cluster plug-in results and the stipulated table arithmetic.
- **P033-T5 / SAP.P033.T5:** `SAP.P033.T5WholeStatement`, proved by `SAP.P033.WH.W1.T5_whole` in [SAP/P033/WH/W1/Proofs/T5.lean](SAP/P033/WH/W1/Proofs/T5.lean); supporting files: the existing `Bridge.T5_of_project` proof in `WH/W1/Leaves.lean`.
  Old restriction now removed: Adds dE != dI and 0 < sd to the general count-scaling clause so that its Wald effect and standardization have nonzero denominators. Omits no clauses of the concrete binary-outcome witness.

For T5, removing the restricted decision does not remove denominator guards: the supplied whole statement preserves the nonzero-denominator presuppositions of the claim.

The switched manifest entries now have null restrictions, whole statement definitions, proved status, and the identifiable project declarations used by the new proofs in `rows_used`. All other manifest entries are unchanged.

Dependent-proof repairs: none. No other Solution proof refers to the switched theorem names; every other theorem statement, docstring and proof is unchanged.

Validation: `python3 /home/ubuntu/sap/tools/rebuild_sap.py . P033` rebuilt all 23 modules from scratch and passed the forbidden-token scan. [P033WholeAxioms.lean](scratch/P033WholeAxioms.lean), importing `SAP.P033.Solution`, ran `#print axioms` on all four switched theorems. Each reports exactly `propext`, `Classical.choice` and `Quot.sound`; see [P033WholeAxioms.log](scratch/P033WholeAxioms.log). Lean compilations ran sequentially through `sap-lean`; no `lake` command was run.
