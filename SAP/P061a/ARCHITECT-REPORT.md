P061a packages only P061-T1 through P061-T11. Decisions: **6 whole, 5 restricted, 0 refuted, 0 omitted**. There are eleven Challenge theorems and eleven proved Solution theorems. There are no open glue tasks.

The whole targets are T1, T2, T3, T6, T8 and T9. T11 now states the positive finite-support case of Equations (4)–(8), with explicit ordinary-mean certificates. No Challenge theorem is labelled refuted.

The restricted targets are:

- **T4:** Includes the independent correlated-pair law, full support, exposure margins, bounded partner-only responses, independence outside each pair, pair covariance, unit exposure means, the exact target and estimator moments, positive standard errors, squared standardized-gap bounds and divergence, and interval coverage bounds and limits. It does not state explicit graph predicates asserting maximum degree exactly one or exactly one outcome neighbor, the alternate variance-polynomial expression in a and rho, the unsquared standardized-gap limit, or the order classifications in N for the gap and standard error. Limit sequences use m+2, so every evaluated standard error belongs to a population covered by its positivity certificate.
- **T5:** Requires absolute integrability of each hybrid response separately, beyond integrability of their difference, and strictly positive estimated scales at every assignment. The interval conclusion gives the ADE coverage limit only for q>0 with no limiting atom at either endpoint; it does not separately state the AEED interval limit. The neighborhood total variation inequality applies to a finite common assignment alphabet and the full assignment space. The explicit T4 sequence with vanishing unstandardized gap and diverging standardized gap is not included in this target. The zero-drift transfer, nonzero-drift shifted limit, finite neighborhood inequality and sufficient-rate implication are all retained. Neither of the two reviewed narrower rows is used outside these limits.
- **T7:** Includes the normalized geometric law on the full real feasible domain, its exact support and exposure probabilities, the ordinary zero-cell mean with its moment certificate, failure of the targeted signed sum and HT integrability, the exact alternating weighted terms and partial sums, the estimator formula, and nonsummability of both nonnegative sign parts for response and estimator. It does not separately state ordered partial-sum nonconvergence, nonexistence of the derived AEPO/EED/AEED, or extended-real positive-infinity identities for the sign parts. Exact oscillating partial sums and sign-part nonsummability are the exported certificates.
- **T10:** Retains all three corrected rate characterizations together using ordinary Mathlib little-o and big-O for nonnegative real sequences indexed by population size. It identifies no dependency graph and does not assert that a sequence satisfies a growth condition, prove a CLT or Chebyshev sharpness, or verify a literature attribution. The uniform quotient bound quantifies only positive population sizes; the asymptotic assertions ignore the initial zero index. The proof transports the credited degree-rate encodings through existing Mathlib asymptotic equivalences and simplifies nonnegative norms. 
- **T11:** Adds finite positive-probability support, while retaining an arbitrary feasible assignment type and all zero-mass feasible assignments. It includes the supported-atom probability expression, both targeted absolute-moment certificates, EPO/conditional-mean equalities, AEPO averaging, unit conditional-mean contrasts and both AEED identities. It excludes every infinite-positive-support design, including those with finite targeted moments, and adds no stability, independence or global outcome bound. This is a restriction of the canonical claim, not a proposed correction of its text. There are no omitted targets.

Statements use ordinary Mathlib notions and shared SAP definitions. T10 uses Mathlib notions directly and adds no definition. `Defs/Part1.lean` defines normalized nonnegative atomic masses, ordinary absolute-moment existence, exposure targets, estimators, stability, independence, hybrid coordinates and convergence. `Part2.lean` defines the concrete schedules and finite neighborhood quantities. The remaining parts contain the target propositions. Every definition imports only Mathlib and earlier SAP definition parts. The Challenge imports only these definitions. Solution imports the Bridge and project modules, and never imports Challenge.

The structural adapters `Bridge.toProject` and `Bridge.fromProject` copy only the atom masses and their existing normalization certificates. Their round trips and the basic probability, expectation, moment, target and estimator correspondences are reflexive. SAP declarations have SAP names; no project declaration has been redeclared under its original fully qualified name. Challenge and Solution share the same compiled definition modules.

The bridges are:

| Target | Bridge result | Existing mathematics and glue |
| --- | --- | --- |
| T1 | `version_correspondence` | Conjoins the version counterexample, unit marginals, both direct averages, persistent-gap limits, schedule obstruction and HT moments. Unit EEDs use subtraction of exported EPOs; uniform masses and the two explicit vectors use arithmetic simplification. |
| T2 | `edge_correspondence` | Conjoins the network image and domain counterexample with the all-even-population result. Positivity uses the exported quarter-probabilities, support stability restricts global stability, and the four explicit vectors and raw-domain equivalences use finite arithmetic evaluation. |
| T3 | `comparison_correspondence` | Instantiates the two existing independence comparisons through the structural adapter. No hybrid feasibility or integrability is assumed beyond the canonical hypotheses: the coordinate comparison exports them. |
| T4 | `pair_inference_correspondence` | Transports the finite counterexample and four existing limits. Positive standard errors follow by square-root positivity from the exported variance formula and lower bound. The limit index shift is composition with the natural-number addition filter map. Named specialized correspondences are reflexive. |
| T5 | `transfer_correspondence` | Instantiates the reviewed inference-transfer, finite-alphabet neighborhood, sufficient-rate and nonzero-drift declarations. The added positivity of estimated scales only restricts their domain. |
| T6 | `attribution_correspondence` | Conjoins the finite-domain attribution, averaged EED identity and binary specialization. Finite-domain moments come from the existing finite-type result. Historical priority is not a mathematical conclusion. |
| T7 | `divergent_correspondence` | Conjoins the existing real-support, missing-moment, alternating-term, partial-sum and sign-divergence results. The actual HT weighted terms are twice the response terms. Nonsummability is transported through multiplication by the nonzero scalar two using existing sum-scaling equivalence and nonnegative max scaling. The zero-cell moment comes from the existing constant-cell result after unfolding its zero response. |
| T8 | `first_moment_correspondence` | Instantiates corrected first moments, finite-support moments and targeted-cell stability. The conditional absolute-mean formula applies the existing EPO/conditional-mean equality to absolute responses; the remaining work is absolute-value/indicator algebra and finite summation of exported identities. |
| T9 | `sampling_correspondence` | Transports the two existing sampling designs, support/margin/EPO certificates and unequal targets. Equality of records with equal mass functions is structural, with proof fields identified by proof irrelevance. |
| T10 | Direct glue in `SAP.P061a.T10` | Combines the credited three encodings with Mathlib little-o/quotient, big-O/boundedness and natural-sequence uniform-bound equivalences. Powers are eventually nonzero by positivity at positive population sizes. Nonnegativity removes norms; extending a positive-index bound to the source encoding uses only the zero index and the bound `max C 0`. |
| T11 | `finite_targets_correspondence` | Projects the positive finite-support component of the credited resolved declaration. Positivity is unpacked into per-unit inequalities. Zero-mass terms supply the supported-atom probability expression by pointwise algebra; finite sums and subtraction transport the exported conditional-mean equalities to the remaining population and unit identities. |

Ordinary means are represented by absolute summability of weighted real responses. Total real sums alone are never used to claim existence. General mean identities have targeted moment and positive probability premises; the finite counterexamples have finite assignment domains and certified positive target probabilities. The divergent example certifies the zero-cell moment separately and makes no ordinary-mean assertion for its divergent cell. The transfer theorem requires positive scales and feasible hybrids on positive support. Its population index zero is only the conventional initial value of a limit sequence; finite-population comparisons require positive population size. Finite response ranges in the neighborhood theorem have nonempty finite domains. Limiting laws are probability measures, so interval probabilities converted to real numbers are finite.

All Defs parts and root, Bridge parts and root, Challenge part and root, and Solution were compiled using `sap-lean` in dependency order. The scratch file `scratch/PrintAxioms.lean` prints all eleven proved theorems; each reports exactly `propext`, `Classical.choice` and `Quot.sound`. `scratch/axioms.log` records that output. The manifest records the actual printed dependencies, all credited rows either used or explained as unused, and the restrictions above. Both JSON files parse, all SAP files are within the 300-line limit, and the two theorem lists and statement types agree.

The requested Comparator configuration is present. The configured external kernel commands are not on PATH in this workspace, so no Comparator run or three-kernel certification is claimed here. The package has no unproved Solution theorem or open glue task; external certification remains a downstream check. The source project and pilot units were not edited.


## Declaration review round 1

- **OMIT.P061-T10 — omission_questionable/minor: accepted.** The [review finding](/home/ubuntu/sap/wt/ARCH-P061a/fw/round1/P061-T10/r1g3/findings.json:1) correctly identifies recoverable content in the canonical statement's three population-indexed formulas. The [credited declaration](/home/ubuntu/sap/wt/ARCH-P061a/AronowAudit/P061/P061_Foundations.lean:1248) supplies their encodings, and the existing Mathlib equivalences in `Mathlib/Analysis/Asymptotics/Lemmas.lean` supply the standard asymptotic formulations. Replaced the omission with restricted theorem `SAP.P061a.T10`, stating all three equivalences in one conjunction. Its docstring discloses nonnegative sequence inputs, the positive-population domain for the finite quotient bound, and the absent graph, actual-rate, CLT, sharpness and attribution conclusions. The proof contains only the credited row, existing asymptotic equivalences, positivity and nonnegative-norm rewrites, and arithmetic at the excluded initial index. No growth, CLT or sharpness proof was added.

At completion of round 1, existing shared definitions, Bridge files and `Challenge/Part1.lean` were byte-for-byte unchanged; their hashes are recorded in `scratch/round1-preserved.json`. The new statement is inline in `Challenge/Part2.lean` and Solution, so it introduces no new shared definition and changes no previous statement or fully qualified theorem name. The Challenge root and Comparator list now include T10. Every target is now represented, and all eleven theorems are proved. The complete dependency-ordered rebuild and all eleven printed dependency checks were rerun; both JSON files and the manifest's row accounting were validated again.


## Declaration review round 2

The round-2 dispositions are historical and are superseded for T11 by round 3 below. The [faithful/none finding](/home/ubuntu/sap/wt/ARCH-P061a/fw/round2/T11/r3g2/findings.json:47) was accepted, and the [weaker_reading/major recheck](/home/ubuntu/sap/wt/ARCH-P061a/fw/round2/T11/refcheck-base-b4/refcheck.json:165) was initially disputed on the positivity-only reading of the [canonical existence assertion](/home/ubuntu/sap/wt/ARCH-P061a/work.json:2383). That round clarified the docstring but retained the negation. Its full rebuild and eleven dependency checks passed. The current package no longer uses that refutation as its T11 Challenge.

## Declaration review round 3

- **SAP.P061a.T11 — not_faithful/major: resolved by a positive restriction.** The [finding](/home/ubuntu/sap/wt/ARCH-P061a/fw/round3/T11/r5g3/findings.json:1) identifies that the previous theorem negated a positivity-only contract and could be witnessed by data lacking ordinary conditional means. Replaced it with the positive finite-support component already proved by the [credited declaration](/home/ubuntu/sap/wt/ARCH-P061a/AronowAudit/P061/P061_PaperDomains.lean:235). The Challenge no longer asserts that the printed claim is false. This replaces the round-2 packaging decision and avoids relying on the disputed refutation reading.

The new theorem keeps the fully qualified name `SAP.P061a.T11`. It assumes positive population size, positive target exposures, and finite positive-probability support; the feasible assignment type may still be infinite. It concludes the support-restricted atom expression for exposure probabilities, finite targeted moments for both exposures, the ordinary conditional-mean equalities, the conditional-mean form of the population means and unit contrast, and both forms of the population contrast. The source's positive finite-support result supplies the substantive existence and conditional-mean facts. The rest is pointwise zero-mass algebra, conjunction, finite-sum congruence and subtraction of exported equalities. No new moment or probability theorem was proved.

The decision is **restricted** because the [canonical setup](/home/ubuntu/sap/wt/ARCH-P061a/work.json:33), S10(b), allows infinite positive-probability support. The finite-support hypothesis is an explicit weakening of the [canonical T11 claim](/home/ubuntu/sap/wt/ARCH-P061a/work.json:2383); it was taken from the existing positive row, not added to the canonical text. All infinite-support cases are dropped, even if their ordinary conditional means exist. Accordingly the review's suggested whole label is not used for this narrower result. No boundedness, independence, SUTVA or NURVA assumption is added.

Only the body of `T11Statement` changed among shared definitions, and only Challenge T11 depends on that definition. Its closure therefore requires renewed review; the other ten Challenge statements and their definitions are unchanged. `scratch/round3-preserved.json` records the pre-round sources and statement headers. The old auxiliary `positivityWellDefined` proposition and its Bridge refutation remain explicitly scoped to the reading with no existence hypotheses and are absent from the revised T11 statement and proof use. The manifest no longer labels T11 refuted or claims a canonical positivity-only refutation. Its row accounting selects only the positive component of the credited resolved declaration.

All Defs parts and root, Bridge parts and root, both Challenge parts and root, and Solution were rebuilt in dependency order. All eleven dependency prints were rerun and use only the permitted foundations. The Comparator retains the same eleven theorem names. Both JSON files parse; statement matching, row accounting and the 300-line file limit were checked. Counts are now 6 whole, 5 restricted, 0 refuted and 0 omitted, with eleven proved theorems and no open glue tasks. External kernel certification remains pending as described above.


## Whole versions (new proofs)

This section supersedes the earlier restricted packaging of T4, T7 and T5. The supplied whole statements and proofs are now exported by Challenge and Solution. The resulting decisions are 9 whole and 2 restricted (T10 and T11), with all 11 Solution theorems proved.

### P061-T4 — `SAP.P061a.T4`

Challenge type: `SAP.P061a.T4WholeStatement`; Solution proof: `SAP.P061a.WH.W1.T4_whole`.

Files: `SAP/P061a/Challenge/Part1.lean`, `SAP/P061a/Solution.lean`, `SAP/P061a/manifest.json`, `SAP/P061a/Defs/WholeW1.lean`, `SAP/P061a/WH/W1/Leaves.lean`, and `SAP/P061a/WH/W1/Proofs/T4.lean`. Proved leaves: `SAP/P061a/WH/W1/P/T4_L1.lean`, `SAP/P061a/WH/W1/P/T4_L2.lean`, `SAP/P061a/WH/W1/P/T4_L3.lean`. `SAP/P061a/WH/W1/Support.lean` supplies shared support. The supplied definitions, blueprint, support and proof files are unchanged.

Old restriction now removed: Retains independence outside each pair, the partner-only response formula, covariance, exact moments, positive standard errors, squared standardized-gap divergence and coverage limits. Omits explicit graph predicates asserting maximum degree exactly one and exactly one outcome neighbor, the alternate V expression in a and rho, the unsquared standardized-gap limit, and the order classifications in N for the gap and standard error. Limits are reindexed by m+2 to keep all evaluated standard errors positive.

### P061-T7 — `SAP.P061a.T7`

Challenge type: `SAP.P061a.T7WholeStatement`; Solution proof: `SAP.P061a.WH.W1.T7_whole`.

Files: `SAP/P061a/Challenge/Part1.lean`, `SAP/P061a/Solution.lean`, `SAP/P061a/manifest.json`, `SAP/P061a/Defs/WholeW1.lean`, `SAP/P061a/WH/W1/Leaves.lean`, and `SAP/P061a/WH/W1/Proofs/T7.lean`. Proved leaves: `SAP/P061a/WH/W1/P/T7_L1.lean`. `SAP/P061a/WH/W1/Support.lean` supplies shared support. The supplied definitions, blueprint, support and proof files are unchanged.

Old restriction now removed: Retains the normalized full real-assignment witness, support, positivity, ordinary zero-cell mean, exact weighted response and HT terms, oscillating partial sums, nonsummability of both sign parts, and failure of the targeted signed sum and HT integrability. Does not separately state nonconvergence of the ordered partial sums, the derived AEPO/EED/AEED nonexistence assertions, or extended-real positive-infinity identities for the sign parts.

### P061-T5 — `SAP.P061a.T5`

Challenge type: `SAP.P061a.T5WholeStatement_W2`; Solution proof: `SAP.P061a.WH.W2.T5_whole`.

Files: `SAP/P061a/Challenge/Part1.lean`, `SAP/P061a/Solution.lean`, `SAP/P061a/manifest.json`, `SAP/P061a/Defs/WholeW2.lean`, `SAP/P061a/WH/W2/Leaves.lean`, and `SAP/P061a/WH/W2/Proofs/T5.lean`. The W2 blueprint already contains all proved components and has no separate leaf files. The supplied definitions, blueprint, support and proof files are unchanged.

Old restriction now removed: Requires separate absolute integrability of each of the two hybrid responses and strict positivity of every estimated scale. Gives the ADE interval limit only for q>0 and limiting masses L({q})=L({-q})=0, without a separate AEED interval-limit assertion. The local total variation inequality is restricted to a finite common assignment alphabet and its full assignment space. Omits the explicit T4 sequence with vanishing unstandardized gap and diverging standardized gap.

### Other Solution proofs

No other Solution proof uses a switched theorem; no dependent proof repairs were needed. All other theorem statements, docstrings, proofs and manifest entries are unchanged.

### Verification

`python3 /home/ubuntu/sap/tools/rebuild_sap.py . P061a` completed successfully: 37 modules rebuilt from source; token scan clean. The rebuild and the subsequent axiom check ran sequentially, with one Lean process at a time and no Lake invocation.

The scratch file `/tmp/p061a-switch-3bm58guf/PrintWholeAxioms.lean` imports `SAP.P061a.Solution` and prints all three switched declarations. Its output is recorded in `/tmp/p061a-switch-3bm58guf/whole-axioms.log`:

```text
'SAP.P061a.T4' depends on axioms: [propext, Classical.choice, Quot.sound]
'SAP.P061a.T7' depends on axioms: [propext, Classical.choice, Quot.sound]
'SAP.P061a.T5' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Only the three requested Challenge declarations and Solution declarations, their imports, and their manifest entries changed. All other SAP files are byte-for-byte unchanged, and no source files were deleted.
