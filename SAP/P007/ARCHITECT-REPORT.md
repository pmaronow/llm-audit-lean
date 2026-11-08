P007: Listwise Deletion in High Dimensions (Political Analysis 31, 2023).

| Decision | Targets |
| --- | ---: |
| whole | 14 |
| restricted | 2 |
| refuted | 0 |
| omitted | 1 |

There are 16 Challenge theorems and 16 proved Solution theorems. Open glue tasks: none.

The restricted targets are:

- **P007-T2:** The simulation comparison covers exactly the supplied estimates at four, five and six variables. It drops the corrected sentence's assertion about every larger variable count above six. The integer uniqueness result, preprocessing counts, corrected average, universal four-variable bound and all three displayed estimate comparisons are retained. The before-removal average is explicitly linked to the same mask as the retained average.
- **P007-T10:** The closing assertion that the fraction bound and all-deletion bound coincide only when there is one row is restricted to `0 < q < 1`. At `q = 0`, both bounds equal one for every positive row and column count. The theorem states this endpoint explicitly, retains both algebraic identities at zero, and retains the expectation bounds without row independence. The narrower row `fraction_bound_vs_all_bound` is used within its exact positive-domain hypotheses; the identities including zero are definitional algebra.

**P007-T13 is omitted.** Its record has `no_lean = true` and no rows. Its positive printed statements concern the named empirical array; this target supplies no formal empirical array declaration or credited proof. The conditional refutations and corrections already have their own targets T1, T2 and T12. They do not license an unconditional assertion about reconstructed data here.

Certification metadata correction: the strict orchestrator run rejected T13 because its explanation was stored only in the custom `omission_reason` field while `restriction` was null. The existing explanation is now supplied in both `reason` and `restriction`, and the custom field has been removed. The comparator theorem list was regenerated from the manifest with the same 16 non-omitted targets. That metadata correction changed no target decision, Lean statement, definition or proof; at that stage all nine Lean source hashes matched the failed run's frozen snapshot.

T1, T3, T4, T7 and T9 are classified `whole` because their canonical claims are themselves refutations or explicit counterexamples. The refutations concern the exact sentences specified in those records. T1 remains conditional on the specified observed-cell total. The `wrong_credit` synthetic-array row is excluded.

The shared-definitions route is used. `SAP/P007/Defs/Part1.lean` contains SAP names for finite probability distributions, event probabilities and expectations, prefix events, observation bounds, subsampling averages and explicit witness weights. Parts 2–4 contain the target statements. Both Challenge and Solution import the same compiled definitions. Defs imports only Mathlib and earlier Defs parts; Challenge parts import only the Defs root. No project declaration is copied under its original name.

The finite joint distribution of Boolean indicators represents arbitrary dependence within rows. Mutual independence is the full eventwise row condition, with no identical-distribution condition. The grouped statements use one coordinate per nonempty group. Sequence laws may change freely with the sample size, while their observation bound is one fixed number.

`SAP/P007/Bridge.lean` provides these correspondences:

- `toAudit` and `fromAudit` copy weights and reuse the existing nonnegativity and normalization proofs. Both round trips are proved by reflexivity.
- Probabilities, expectations, row independence, observed prefixes, survival probabilities, all-deletion probability, observation bounds, repaired coefficients and identical-distribution predicates agree by reflexivity after those adapters.
- The fixed-array sampling, counting, missing-average and observed-column definitions agree by reflexivity.
- Bound functions, threshold functions, growth conditions, deletion indicators and deletion fractions agree by reflexivity.
- Independent-cell weights, equal-observation weights and the unequal-observation weights agree by reflexivity. The three point-mass or mixture witness weights agree by function extensionality and simplification of their constructors and decisions.
- `equalModel_of_audit` and `unequalModel_of_audit` package the existing normalized models and reuse their exported independence and observation-bound facts. They introduce no normalization argument.

The Solution assembles exported components by instantiation, conjunction, structural conversion, rewriting and elementary arithmetic. In particular, T7 retains all specified witnesses, both worked crossings, the null upper-guarantee examples and the large-row probability estimate. T8 retains monotonicity, the unique real inverse, all integer equivalences, both rounding alternatives, general probability guarantees, explicit attainment, both numerical intervals and a failure of an actual-probability upper guarantee. T5 and T6 retain every enumerated finite step of the repaired proofs. The asymptotic probability conclusions are T16 and T17.

Shared rows and existing support lemmas are identified separately in the manifest's `supporting_declarations`. For example, T8 reuses the already proved Lemma 3 for its general lower bound, and T10 reuses the already proved equality model for attainment. `rows_not_used` records every unused credited row and its reason; the lists partition each target's credited rows. Internal dependencies of the original proofs are not separately enumerated.

The domains avoid unintended total-function values. Conditional probabilities are tested only at positive-probability prefixes; the repaired product coefficients explicitly specify zero at a null prefix. Subsampling means have positive row counts and nonempty column sample sets. Deletion fractions have positive row counts. Real inverse thresholds require positive row counts and interior observation and target probabilities. The limit statements use the original full natural-number sequences, with probability assumptions starting at one; the logarithmic growth condition concerns their tail, so the initial total-log values at zero and one do not impose an extra probabilistic condition.

The archived-average tolerance and the supplied simulation decimals remain the canonical inputs. Their arithmetic is checked exactly; the package does not independently read the replication log or recount the original dataset. The finite Bernoulli steps in T6 are the enumerated finite content of that target; the surrounding quoted convergence discussion is represented by the headline proposition targets.

For declaration review round 1, all nine Lean modules rebuilt successfully with the requested wrapper, in this order:

```text
/home/ubuntu/sap/tools/sap-lean \
  SAP/P007/Defs/Part1.lean SAP/P007/Defs/Part2.lean \
  SAP/P007/Defs/Part3.lean SAP/P007/Defs/Part4.lean \
  SAP/P007/Defs.lean SAP/P007/Bridge.lean \
  SAP/P007/Challenge/Part1.lean SAP/P007/Challenge.lean \
  SAP/P007/Solution.lean
```

The required dependency audit was rerun after this rebuild using `scratch/P007_Axioms.lean`, with results in `scratch/P007_Axioms.txt`. Each of the 16 proved theorems uses exactly `propext`, `Classical.choice` and `Quot.sound`. The recorded dependencies match the manifest and the comparator's permitted list.

Both JSON files parse. Target coverage, credited-row accounting, identical Challenge/Solution statement names, the Mathlib-only Challenge import boundary, source-token restrictions and the 300-line file limits were checked. No tracked source files were modified.

The Palomar Comparator configuration is complete. The strict orchestrator result in `SAP/P007/verification/comparator-result.json`, stamped `20261103T205135Z`, records acceptance of the metadata-corrected package by the default Lean, con-ron and nanoda kernels. That certificate predates the T7 statement revision below; certification of the revised statement is pending.

## Declaration review round 1

- **SAP.P007.T7 / P007-T7 — `label_wrong`, minor:** The reviewer is right that canonical part (c3) explicitly includes `99/100 < 1 - 30000/4^33`, while the earlier statement included only the estimate's comparison with the actual probability and the actual probability's comparison with `99/100`. See the T7 entry in [the findings](fw/round1/T7/r3g2/findings.json), [the review report](fw/round1/T7/r3g2/REPORT.md), and `P007-T7.canonical_claim.statement`, part (c3), in [work.json](work.json). Added the missing strict comparison as a conjunct in [T7Statement](SAP/P007/Defs/Part3.lean), and proved it with one `norm_num` in [the Solution](SAP/P007/Solution.lean). The same closed numerical comparison is already checked in the existing proof [P007_Probability.lean:1067](AronowAudit/P007/P007_Probability.lean#L1067). This is numerical glue. The `whole` decision now states that clause explicitly; no hypothesis was added and no conclusion dropped.

Only the target-specific definition `SAP.P007.T7Statement` and its proof changed. The shared model, probability, bound and threshold definitions are unchanged, as are every other target statement and every theorem's fully qualified name. Pre-revision hashes in `scratch/P007_Round1_Baseline.json` support the scope check. The manifest records the resolution; the comparator configuration is regenerated with the same 16 names and permitted dependencies. Counts remain 14 whole, 2 restricted, 0 refuted and 1 omitted, with 16 proved theorems and no open glue tasks.

Validation after this revision: all nine Lean modules compiled in dependency order; `#print axioms` was rerun for all 16 proved theorems and matched each manifest entry using only the three permitted dependencies. Both JSON files parse, and target accounting, theorem-name agreement, import boundaries, file line limits and source-token restrictions pass. The content comparison confirms that no definition shared with another target changed. The earlier three-kernel certificate remains historical; the revised T7 statement awaits orchestrator recertification.

## Whole versions (new proofs)

- **P007-T10 / `SAP.P007.T10`:** Switched to `SAP.P007.T10WholeStatement`, with decision `refuted`, using `SAP.P007.WH.W1.T10_whole`. The whole statement gives the normalized independent-cell counterexample at `n = 2`, `k = 1`, `q = 0`, where both bounds equal one although `n ≠ 1`.
- **Files:** `SAP/P007/Challenge/Part1.lean` contains the updated stub and docstring; `SAP/P007/Solution.lean` uses the whole proof; `SAP/P007/manifest.json` records the switch. The supplied whole statement, blueprint and compiled proof sources are `SAP/P007/Defs/WholeW1.lean`, `SAP/P007/WH/W1/Leaves.lean` and `SAP/P007/WH/W1/Proofs/T10.lean`.
- **Removed restriction:** “The final assertion that the bounds coincide only for n=1 is qualified by 0<q<1. At q=0 the theorem instead records equality to one for every positive n,k. All expectation bounds and algebraic identities retain q=0.” This switch supersedes the earlier restricted classification of T10; the other target entries are unchanged.

Validation: `python3 /home/ubuntu/sap/tools/rebuild_sap.py . P007` rebuilt all 12 modules from scratch and passed the forbidden-token scan. A scratch file importing `SAP.P007.Solution` ran `#print axioms SAP.P007.T10`, yielding exactly `propext`, `Classical.choice` and `Quot.sound`. Challenge import boundaries, the absence of Challenge imports from Solution, and preservation of all other target entries, statements, definitions and proofs were checked. Lean processes ran serially; no `lake` command was run.

## Whole versions (new proofs)

- **P007-T10 / `SAP.P007.T10` (W2):** Switched to `SAP.P007.T10WholeStatement_W2`, with decision `whole`, using `SAP.P007.WH.W2.T10_whole`. This supersedes the W1 refutation recorded above. The whole corrected statement covers arbitrary measurable arrays on probability spaces, the expectation bounds without row independence, independent-cell attainment and existence, and the full-domain equality criterion `n = 1 ∨ q = 0`.
- **Files:** Updated the stub and docstring in `SAP/P007/Challenge/Part1.lean`, the proof in `SAP/P007/Solution.lean`, and the T10 entry in `SAP/P007/manifest.json`. The supplied statement, blueprint with proved leaves, and generated theorem are `SAP/P007/Defs/WholeW2.lean`, `SAP/P007/WH/W2/Leaves.lean`, and `SAP/P007/WH/W2/Proofs/T10.lean`; these proof sources are unchanged.
- **Removed restriction:** The original T10 restriction limited the claim that the bounds coincide only for one row to `0 < q < 1`, treating `q = 0` separately. W2 states and proves coincidence on the entire domain `q ∈ [0,1)` exactly when `n = 1` or `q = 0`, with both bounds equal to one at zero. The immediately preceding W1 manifest entry already had `restriction: null`; this switch replaces its refutation with the whole corrected claim.
- **Dependent proof repairs:** None. No other Solution proof uses `SAP.P007.T10`; all other target statements, docstrings, proofs, and manifest entries are unchanged.

Validation (W2): `python3 /home/ubuntu/sap/tools/rebuild_sap.py . P007` rebuilt all 15 modules from scratch and passed the forbidden-token scan. `scratch/P007_W2_Axioms.lean` imports `SAP.P007.Solution` and runs `#print axioms SAP.P007.T10`; the result in `scratch/P007_W2_Axioms.txt` is exactly `propext`, `Classical.choice`, and `Quot.sound`. Scope checks confirm preservation of every other target and all supplied statement/proof sources, exact agreement with the switch docstring and type, and the Challenge/Solution import boundaries. Lean compilation ran serially; no `lake` command was run. The switch result is recorded in `switched.json`.
