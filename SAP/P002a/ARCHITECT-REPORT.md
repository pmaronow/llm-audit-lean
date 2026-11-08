# P002a packaging report

Counts: **14 whole, 0 restricted, 1 refuted, 0 omitted**. All fifteen Solution theorems are proved; there are no open glue tasks. The restriction and omission discussions below record earlier revisions and are superseded by the supplied whole statements and the current round-3 resolution.

Only P002-T1 through P002-T15 are included. P002b is outside this unit. Decisions follow the canonical claims and final row statuses, including explicit omissions of clauses that a coverage summary called complete.

## Earlier restrictions (historical)

- **P002-T1 (restricted):** Retains admissibility, both twelve-unit variance-bound failures, the repeated-block family, zero population OLS coefficients and the failed arithmetic step. Omits the additional explicit covariance and fourth-moment evaluations, zero contrast-variance evaluations, exact printed-right-hand-side values and expanded oracle-statistic formula.

- **P002-T2 (restricted):** States the two corrected final lower bounds, with positive covariate dimension for the adjusted bound. Omits the intermediate corrected chains (C.3)-(C.8), the residual-square inequality in the proof of (E.10), the negative-delta parameter-space inclusions and the explicit identification with the printed bounds for nonnegative delta.

- **P002-T4 (restricted):** Retains moment collapse, common adjusted outcomes and both parameter-class coverage counterexamples, including nonemptiness and their limiting infima. Omits the detailed zero-statistic and quantile identities, fitted-coefficient and rank-event calculations, the separate 258 and 774 rank-loss bounds, the explicit grid-moment identities, and all of the six-unit illustration (d): its admissibility, heterogeneous effects, 20-assignment exact coverage and 312 nonzero values among 400 reassignment pairs.

- **P002-T5 (restricted):** Requires a nontrivial filter of arbitrarily large nonempty parameter classes for each uniform lower bound, and positive covariate dimension for the adjusted bound. Retains nominal convergence and sufficient unadjusted sharpness under a supplied admissible nondegenerate constant-effect sequence. Does not assert necessity of that sequence condition or a sharpness characterization for adjusted classes, and omits the separate assertion that degenerate classes may have coverage one.

- **P002-T6 (restricted):** Retains the admissible even family, odd extension, full-rank even-sample fits, exploding feasible-variance lower bound, estimator bound below 5/n, and probability-one failure of printed (E.61). Omits the intermediate moment and residual evaluations, the exact rare-block slopes and statistic values, the zero-expectation identity, the binomial-coefficient variance bound, the sharper 121/(25n) estimator bound and the pointwise ratio bound. No separate conclusion about (E.58)-(E.60) is asserted.

- **P002-T7 (restricted):** States all four Lemma 20 limits (E.58)-(E.61), with the corrected (E.61) denominator, for every positive threshold, almost surely along every fixed strictly increasing subsequence. Adds strict positivity of both population OLS residual variances at every size; Xi models with a vanishing population residual variance in either arm at some size are dropped. Uses the `wrong_credit` row `corrected_lemma20_proof` only for exactly what its Lean statement says (see the third-rung revision).

- **P002-T8 (restricted):** Uses only the two-unit counterexample to the covariate-to-augmented-Gram implication. Omits the general even-size family and separate exact assertions that the covariate Gram is 4, the augmented Gram is diag(1,4) and its smallest eigenvalue is 1.

- **P002-T9 (restricted):** For the asymptotic coefficient-error bound, requires the assignment vectors at different sample sizes to be jointly independent, in addition to their complete-randomization marginal laws. This independence requirement does not apply to the finite Gram and spectral clauses.

- **P002-T11 (restricted):** Requires strictly positive S1 squared for the normalized equality and at every size for the normalized rate; the finite unnormalized identities hold for all valid designs. Omits the separately simplified coefficient n0/(n1 n pi squared (1-pi) squared) and the separate identity for the sum of centered squares divided by S1 squared.

- **P002-T14 (restricted):** Retains the balanced-sign family, exact positive reassignment variance, probability-one failure of the printed ratio, its limit one and the finite corrected-ratio probability bound. Omits the hypergeometric law and second-moment identity, exact estimator and ratio formulas, the zero-or-at-least-three support claim, square-root-order divergence, the range and mean deficit of the corrected variance ratio, and a separately stated zero limit for its tail probabilities.

- **P002-T15 (restricted):** Adds strict positivity of both adjusted potential-outcome population variances at every size and strict positivity of the conditional reassignment variance for every size and realized assignment vector. Covers every fixed strict subsequence and all positive tolerances almost surely, with arbitrary complete-randomization marginal couplings. Does not cover models or realized vectors with a zero denominator.

## Whole claims and refutation

- **T10:** both failed printed centering evaluations and the corrected values, including positive scaling variance and the corrected mean-square expectation.
- **T12:** admissible eight-unit witness, the 70-assignment design, exact variance and incorrect printed lower bound, arm-mean contrast, and equality in the corrected bound.
- **T13:** the two corrected finite variance lower bounds, including the explicit balance constant, for every frozen real response vector and valid observed assignment.
- **T3 (refuted):** negates both printed universal lower bounds. The other counterexample targets are already canonical refutations and are classified by their clause coverage instead.

## Shared definitions and bridges

The statement route is Mathlib plus shared definitions under `SAP.P002a`. Defs contain independent population and covariate-population structures, finite design averages, the paper statistics, parameter classes, fixed witness families and the target propositions. Challenge imports only these shared modules. Solution imports the same definitions and never imports Challenge.

`Bridge/Part1.lean` copies population data fields in both directions. The round trips, scalar and matrix quantities, OLS selection, statistics, parameter predicates and randomization marginals agree by `rfl`. Using the same local classical decision instance makes the finite quantile definitions agree definitionally, including the minimum-selection branch.

`Bridge/Part2.lean` transports the two nested coverage infima by mapping their subtype indices in each direction and applying the elementary infimum bounds. Nonempty-class size sets agree by mapping existential witnesses. The printed universal contracts agree by mapping universally quantified populations in both directions. These are structural changes of data representation.

Solution uses the existing exported results by instantiation and conjunction. Its additional steps are the structural infimum rewrites, finite four-unit and eight-unit arithmetic, selection of a valid finite assignment, and moving a constant divisor through finite expectation. No new asymptotic, statistical, spectral or sampling argument is introduced.

## Domain checks and review concerns

- Valid designs have two nonempty arms and at least two units; the parameter predicates require a complier. The group covariance retains the paper singleton convention.
- Absolute studentized statistics retain the supplied extended nonnegative convention, including infinite values. Valid designs and interior significance levels make the finite attainable-quantile construction meaningful. These quantiles are never converted to real numbers.
- T5 requires arbitrarily large nonempty size classes instead of interpreting a limit through a trivial filter. Empty inner LATE fibers remain harmless in the extended nonnegative nested infimum.
- T11 guards the variance divisor in the normalized equality and rate. T15 guards both population arm variances and every conditional reassignment variance used as a divisor. The explicit T6 and T14 counterexamples have strictly positive denominators by their exported bound or exact variance formula.
- T7 adds no positivity hypothesis on the reassignment variance used as a denominator: at a zero variance, `Real.sqrt 0 = 0` makes the (E.58) event certain, so the stated (E.58) limit already forces that variance to be positive for all large indices.
- T9 uses a positive number of covariates for the spectral infimum, and a positive population size. Thus its unit-vector sets are nonempty; their squared-form values are bounded below.
- The `wrong_credit` corrected-Lemma-20 row is used for T7 only for exactly what its own Lean statement says, and T7 is restricted accordingly; its residual-positivity premise comes from that Lean statement, not from the defensible-statement note. The zero-response diagnostic row (`wrong_credit`, T15) is not needed: T15 is stated from `corrected_lemma12_proof` alone.
- Canonical counterexample details beyond the exported components are explicitly omitted. In particular, the six-unit illustration and square-root-order divergence have not been reconstructed.

## Verification

All eight Defs parts and their root, all three Bridge parts and their root, the Challenge part and root, and Solution were compiled in dependency order with the supplied `sap-lean` wrapper (third-rung run: `scratch/round3-compile.log`). Every proved theorem was checked with `#print axioms` in `scratch/Axioms.lean` (third-rung run: `scratch/round3-axioms.log`; earlier runs in `scratch/proof-check.log`). Each theorem depends only on `propext`, `Classical.choice` and `Quot.sound`.

`manifest.json` and `comparator.json` parse, agree on all fifteen theorem names, and account for every unit target and every credited row. Each restricted docstring contains the corresponding manifest restriction. The current file-length audit is recorded in the round-3 section below.

The requested Palomar configuration is provided; after the third-rung revision it lists fifteen theorem names (the fourteen earlier names unchanged, plus `SAP.P002a.T7`). The supplied [comparator result](SAP/P002a/verification/comparator-result.json) and [kernel log](SAP/P002a/verification/comparator.log) record acceptance by all three kernels for the pre-review snapshot dated 2026-11-03. They are preserved as historical evidence. This review round reruns Lean compilation and the dependency check; it does not rerun the external kernels.

Open glue tasks: **none**.


## Declaration review round 1

- **SAP.P002a.T9 / P002-T9 — accepted (`not_faithful`, major).** The cross-size independence premise in [T9Sequence](SAP/P002a/Defs/Part6.lean:47) is stronger than the complete-randomization marginals in the canonical claim, and was not disclosed. The [finding](fw/round1/T9/r1g2/findings.json) is correct: neither [the canonical display and definitions](work.json:881) nor the unit standing assumptions make that extra premise part of this target. The [credited theorem](AronowAudit/P002/Wave1/E61Eigenvalue.lean:33) explicitly requires it. Changed the decision from `whole` to `restricted` and copied the exact independence restriction into both manifest and Challenge docstring. The finite Gram and spectral clauses retain their scope. The previous report's description of this premise as part of the paper coupling was not sufficient to justify a `whole` label under the canonical-text precedence rule.

- **OMIT.P002-T7 — disagreed (`omission_questionable`, major).** The [finding](fw/round1/P002-T7/r1g4/findings.json) correctly describes the mathematical content of the proved nondegenerate theorem, but its proposed use conflicts with the final-status eligibility rule. [The brief](brief.md:6) expressly defines `wrong_credit` as “not usable for this target”; the restriction rule applies to usable rows. The row has [final_status `wrong_credit`](work.json:736), while `narrower_than_claim` is only its [first-pass label](work.json:742). Neither that historical label, `no_lean=false`, nor the existence of four proved declarations supersedes the final status. The [precedence rule](brief.md:30) also makes suggested fixes diagnostic history, so the [defensible-statement note](work.json:769) does not restore eligibility. I checked [the theorem and its extra residual-positivity premise](AronowAudit/P002/Wave1/Gap/DecisionLemma20.lean:1654): it does prove all four limits in the restricted mathematical scope described by the reviewer. That observation does not permit this row's use for T7 under the unchanged brief. The remaining eligible rows state only [finite oracle-variance identities](AronowAudit/P002/Wave1/Gap/GP0022B3.lean:206) and [least-squares existence](AronowAudit/P002/P002_Audit.lean:243) and [full-rank minimization](AronowAudit/P002/P002_Audit.lean:548), not one of the four target limits. Retained omission and clarified its manifest reason; no helper-only Challenge or new target was introduced.

No shared definition, theorem statement, bridge, or Solution proof changed. Only the T9 docstring and target metadata changed; all fourteen fully qualified theorem names remain identical. The source-hash check in `scratch/round1-validation.json` records this scope, so no additional declaration acquires a changed definition. `comparator.json` was regenerated from the updated manifest and retains the same fourteen names and kernel settings.

Recompiled every Defs, Bridge, Challenge and Solution module in dependency order and reran `scratch/Axioms.lean`. Round-1 logs are `scratch/round1-compile.log` and `scratch/round1-axioms.log`; all fourteen theorems use only the permitted dependencies. JSON, target/row accounting, signature equality, implicit options, import restrictions and line limits were rechecked. There are no open glue tasks.


## Declaration review round 2

**OMIT.P002-T7 — disagreement retained (`omission_questionable`, major).** I reread the current [finding](fw/round2/P002-T7/r2g2/findings.json), the [four-clause theorem](AronowAudit/P002/Wave1/Gap/DecisionLemma20.lean:1654), its [residual-positivity premise](AronowAudit/P002/Wave1/Gap/DecisionLemma20.lean:1660), and the final row status. The mathematical observation is correct: the existing declaration proves all four corrected limits for its nondegenerate scope, distinct from T9 and T15. The omission is solely about eligibility for this target. Updated the manifest and the omission entry above to say this explicitly.

The reviewer identifies the source of the disagreement in its [report](fw/round2/P002-T7/r2g2/REPORT.md:16): its review instructions “provide no categorical final-status exclusion.” This unit has that exclusion: [brief.md](brief.md:6) defines `wrong_credit` as “not usable for this target,” and [the row](work.json:736) retains final_status `wrong_credit`. The [round-2 update](revise-fw2.md:10) says the brief's rules still apply. A review instruction that omits this rule does not repeal the rule governing this package. The proposal to add restricted T7 would use precisely the row that the binding rule excludes; mathematical provability and eligibility are separate checks, and the package must satisfy both.

Addressing each numbered issue in the finding:

1. `no_lean=false` and four proved rows establish that declarations exist; they do not make an excluded row eligible. The updated reason no longer leaves the mathematical availability of the restricted theorem implicit.
2. The entire four-clause nondegenerate result is present in the cited theorem and needs only structural transport. This is acknowledged. No claim of missing mathematics is used to justify omission; final-status exclusion is the reason.
3. Population residual positivity is substantive, and neither Xi nor positive unprojected variances supplies it. The three remaining eligible rows prove only [finite oracle-variance identities](AronowAudit/P002/Wave1/Gap/GP0022B3.lean:206), [OLS existence](AronowAudit/P002/P002_Audit.lean:243), and [full-rank minimization](AronowAudit/P002/P002_Audit.lean:548). No helper-only theorem replaces T7.
4. The adjusted feasible/oracle limits differ from T9 and T15, and those theorems are not offered as coverage for T7. The omitted target remains explicitly recorded, with no renamed or substitute Challenge.

No Lean source file changed in round 2, including every shared definition, theorem statement, and proof. The manifest reason was clarified; `comparator.json` was regenerated and checked against the unchanged fourteen proved theorem names. Full dependency-order compilation and all fourteen `#print axioms` checks were repeated; results are in `scratch/round2-compile.log`, `scratch/round2-axioms.log`, and `scratch/round2-validation.json`. Counts remain **3 whole, 10 restricted, 1 refuted, 1 omitted**, with **14 proved** and **0 open glue tasks**.


## Third-rung revision (Opus)

Open item: **OMIT.P002-T7 (`omission_questionable`, major)**, [finding](fw/round3/P002-T7/r3g1/findings.json). It covers earlier issues 1-4 from rounds 1-3.

**Verdict: the referee is right. T7 changed from `omitted` to `restricted`.**

- **Why the omission no longer holds.** The earlier omission rested only on reading the brief's "`wrong_credit` … not usable for this target" as a categorical exclusion (round-1 and round-2 sections above). The third-rung instructions clarify that rule. A `wrong_credit` row does not establish the component it was credited for, but it may be used for exactly what its own Lean statement says, like a `narrower` row. The target is then `restricted`, and the docstring discloses what is dropped. Under that rule, nothing justifies omitting T7: [corrected_lemma20_proof](AronowAudit/P002/Wave1/Gap/DecisionLemma20.lean:1654) (final status `wrong_credit`, [work.json](work.json:740)) is a statement of this claim, not a helper fact.
- **Canonical claim** ([work.json](work.json:710)). Let $(\theta_n)$ have $\theta_n \in \Xi_n$ for all $n$, with $\beta_n = \bar\beta(\theta_n)$, and let $(\theta_{n_k})$ be any subsequence. Then, almost surely in $Z$:
  - (E.58): for every $\kappa>0$, $\mathbb P^*(|\hat\tau^*_{adj}-\tilde\tau^*_{adj}| \ge \kappa\sqrt{var^*(\tilde\tau^*_{adj})}) \to 0$.
  - (E.59) and (E.60): for every $x>0$, $|\mathbb P^*(|\tilde\tau^*_{adj}| \ge x\sqrt{var^*(\tilde\tau^*_{adj})}) - \mathbb P(|\mathcal Z|\ge x)| \to 0$, and the same with $\hat\tau^*_{adj}$ in the event.
  - (E.61, corrected): for every $\kappa>0$, $\mathbb P^*(|\hat\sigma^2_{adj,*}/var^*(\tilde\tau^*_{adj}) - 1| \ge \kappa) \to 0$.
- **Lean statement used.** `corrected_lemma20_proof` ([lines 1654-1685](AronowAudit/P002/Wave1/Gap/DecisionLemma20.lean:1654)) proves exactly these four conjuncts under `∀ᵐ ω ∂μ`. Its parameters are:
  - a strictly increasing `sizes`;
  - `P n : CovPopulation (sizes n) k` with `Xi (P n) δ e A B r`, `0 < k`, `δ < 1`, `e, A, B > 0` and `0 < r ≤ 1/2`;
  - the extra premise [`hpositive`](AronowAudit/P002/Wave1/Gap/DecisionLemma20.lean:1660): `∀ n a, 0 < popVar (residual (P n) a (late (P n).pop))`;
  - `RandomizationSequence` marginals;
  - a fixed strictly increasing `sub`.

  The new [T7Statement](SAP/P002a/Defs/Part8.lean:17) is this statement verbatim over the SAP definitions, and the [Solution](SAP/P002a/Solution.lean:87) applies the row to `toCovPopulation (P n)` (pure instantiation).
- **Component check against the canonical definitions.**
  - $\mathbb P^*$ / $var^*$ are the uniform law over `n1`-subsets (`probability`, `designVariance`), with the observed $Y_i-\beta D_i$ (`observedW` at the realized `Z N ω`) held fixed.
  - $\hat\tau^*_{adj}$ (`adjustedTau`) is (9) with the arm regressions refit on the reassigned arms.
  - $\tilde\tau^*_{adj}$ (`oracleStar`) uses the pooled full-population coefficients of $Y_i-\beta D_i$ on $(1,x_i)$ for both arms, as in (D.3)-(D.4).
  - $\hat\sigma^2_{adj,*}$ (`adjustedSigma2`) is the reassigned-arm residual sums of squares over $n_1^2$ and $n_0^2$.
  - $\mathbb P(|\mathcal Z|\ge x)$ is the new SAP `normalTail`. Its body is identical to `AronowAudit.P002.normalTail`, bridged by `rfl` in [Bridge/Part3](SAP/P002a/Bridge/Part3.lean:12).
  - "Almost surely … for every κ" is stated with the almost-sure quantifier outside the threshold quantifiers, for each fixed subsequence, as printed.
  - The constants match Assumption 5 ($\delta<1$; $\tilde\varepsilon,A,B>0$) and Assumption 4 ($0<r\le 1/2$). The covariate dimension $k$ is in the paper's $\mathbb N$, which Supplement A defines as the positive integers (standing assumptions), so `0 < k` is not a restriction.
  - Indexing by a strictly increasing `sizes` and requiring only the marginal assignment laws generalize the paper's sequence and its independent coupling (Supplement p. 27).
- **What is dropped (the restriction).** Every Xi model with a vanishing population OLS residual variance in either arm at some size. Xi's moment condition (ii) is satisfied by identically zero residuals, and positive unprojected adjusted-outcome variances do not exclude such models. The audit record ([work.json](work.json:736) row evidence) describes a degenerate Xi family on which (E.59) would fail, but no declaration formalizes it. This package therefore neither asserts that refutation nor labels T7 `refuted`, since stating it would need a new proof. No clause among (E.58)-(E.61) is dropped.
- **Junk values.**
  - `Real.sqrt` is applied to a variance, which is nonnegative.
  - `normalTail` is `toReal` of a probability measure, so it is finite.
  - No positivity hypothesis is added for the reassignment-variance denominator: if it were zero, `Real.sqrt 0 = 0` would make the (E.58) event certain. Valid designs have nonempty assignment sets, so the stated (E.58) limit forces the variance to be positive at all large indices, and the division convention cannot make any stated limit easier.
  - Where a reassigned arm's augmented Gram matrix is singular, `ols` takes its fixed least-squares minimizer (the shared convention already used by T4-T6). The paper leaves that fit undefined.
- **Other rows.** The three `ok` rows (`oracle_variances_proof`, `ols_minimizer_exists`, `ols_minimizer_fullrank`) are finite helpers internal to the four-limit row and are not invoked separately; none is offered as T7 content.

**Consequential check (not an open item).** T15's `wrong_credit` row `zero_response_ratio_failure` was listed as "cannot support this target". Under the clarified rule I reread its [own Lean statement](AronowAudit/P002/P002_Audit.lean:1765). It is a finite zero-response diagnostic whose probability-one conclusion comes from the 0/0 = 0 convention, and it states no clause of T15's limit claim, so it remains unused. Only its manifest reason was reworded. T15 is unchanged.

**What changed.**
- New `SAP/P002a/Defs/Part8.lean`: `normalTail` and `T7Statement`.
- New `SAP/P002a/Bridge/Part3.lean`: `normalTail_eq`, by `rfl`.
- `Defs.lean` and `Bridge.lean` each import their new part.
- The `SAP.P002a.T7` stub and docstring were added to `Challenge/Part1.lean`.
- The `SAP.P002a.T7` proof and the `DecisionLemma20` import were added to `Solution.lean`.
- In `manifest.json`, T7 is now `restricted`, `proved`, with `rows_used` set to the Lemma 20 row. The T15 unused-row reason was reworded.
- `comparator.json` now lists fifteen theorem names.

No existing shared definition, statement, bridge or proof changed, and the fourteen earlier theorems keep their fully qualified names and statements.

**Verification.**
- Every module was recompiled with `sap-lean` in dependency order: Defs Parts 1-8 and root, Bridge Parts 1-3 and root, Challenge part and root, Solution. The log is `scratch/round3-compile.log`; the only diagnostics are the Challenge `placeholder` warnings.
- `#print axioms` for all fifteen theorems, and for `corrected_lemma20_proof` itself, shows only `propext`, `Classical.choice` and `Quot.sound` (`scratch/round3-axioms.log`).
- That earlier run reported a clean token scan and both implicit options. The current file-length audit is recorded in the round-3 section below.
- Both JSON files parse, every restricted docstring contains its manifest restriction, and every credited row is accounted for.

Counts: **3 whole, 11 restricted, 1 refuted, 0 omitted**; **15 proved**, **0 open glue tasks**.

## Whole versions (new proofs)

The eleven targets below now use the supplied whole statements and generated whole proofs, with the decisions from `switch.json`. Current counts are **14 whole, 0 restricted, 1 refuted**; all fifteen Solution theorems remain proved. Earlier restriction and count sections above are historical.

For every listed target, the Challenge stub and replacement docstring are in `SAP/P002a/Challenge/Part1.lean`, the whole proof is used in `SAP/P002a/Solution.lean`, and metadata is updated in `SAP/P002a/manifest.json`. The statement, blueprint, proved leaves (where present), and generated proof files are listed below.

- **P002-T15 (`SAP.P002a.T15`):** `SAP.P002a.T15WholeStatement`, proved by `SAP.P002a.WH.W1.T15_whole`. Files: `SAP/P002a/Defs/WholeW1.lean`, `SAP/P002a/WH/W1/Leaves.lean`, `SAP/P002a/WH/W1/Proofs/T15.lean`. Removed former restriction entry: Adds strict positivity of both adjusted potential-outcome population variances at every size and strict positivity of the conditional reassignment variance for every size and realized assignment vector. Covers every fixed strict subsequence and all positive tolerances almost surely, with arbitrary complete-randomization marginal couplings. Does not cover models or realized vectors with a zero denominator.

- **P002-T8 (`SAP.P002a.T8`):** `SAP.P002a.T8WholeStatement`, proved by `SAP.P002a.WH.W1.T8_whole`. Files: `SAP/P002a/Defs/WholeW1.lean`, `SAP/P002a/WH/W1/Leaves.lean`, `SAP/P002a/WH/W1/Proofs/T8.lean`. Removed former restriction entry: Uses only the two-unit counterexample to the covariate-to-augmented-Gram implication. Omits the general even-size family and separate exact assertions that the covariate Gram is 4, the augmented Gram is diag(1,4) and its smallest eigenvalue is 1.

- **P002-T9 (`SAP.P002a.T9`):** `SAP.P002a.T9WholeStatement`, proved by `SAP.P002a.WH.W1.T9_whole`. Files: `SAP/P002a/Defs/WholeW1.lean`, `SAP/P002a/WH/W1/Leaves.lean`, `SAP/P002a/WH/W1/Proofs/T9.lean`. Removed former restriction entry: For the asymptotic coefficient-error bound, requires the assignment vectors at different sample sizes to be jointly independent, in addition to their complete-randomization marginal laws. This independence requirement does not apply to the finite Gram and spectral clauses.

- **P002-T11 (`SAP.P002a.T11`):** `SAP.P002a.T11WholeStatement`, proved by `SAP.P002a.WH.W1.T11_whole`. Files: `SAP/P002a/Defs/WholeW1.lean`, `SAP/P002a/WH/W1/Leaves.lean`, `SAP/P002a/WH/W1/Proofs/T11.lean`. Removed former restriction entry: Requires strictly positive S1 squared for the normalized equality and at every size for the normalized rate; the finite unnormalized identities hold for all valid designs. Omits the separately simplified coefficient n0/(n1 n pi squared (1-pi) squared) and the separate identity for the sum of centered squares divided by S1 squared.

- **P002-T14 (`SAP.P002a.T14`):** `SAP.P002a.T14WholeStatement`, proved by `SAP.P002a.WH.W2.T14_whole`. Files: `SAP/P002a/Defs/WholeW2.lean`, `SAP/P002a/WH/W2/Leaves.lean`, `SAP/P002a/WH/W2/P/T14_L1.lean`, `SAP/P002a/WH/W2/P/T14_L2.lean`, `SAP/P002a/WH/W2/P/T14_L3.lean`, `SAP/P002a/WH/W2/P/T14_L4.lean`, `SAP/P002a/WH/W2/Proofs/T14.lean`. Removed former restriction entry: Retains the balanced-sign family, exact positive reassignment variance, probability-one failure of the printed ratio, its limit one and the finite corrected-ratio probability bound. Omits the hypergeometric law and second-moment identity, exact estimator and ratio formulas, the zero-or-at-least-three support claim, square-root-order divergence, the range and mean deficit of the corrected variance ratio, and a separately stated zero limit for its tail probabilities.

- **P002-T1 (`SAP.P002a.T1`):** `SAP.P002a.T1WholeStatement`, proved by `SAP.P002a.WH.W2.T1_whole`. Files: `SAP/P002a/Defs/WholeW2.lean`, `SAP/P002a/WH/W2/Leaves.lean`, `SAP/P002a/WH/W2/Proofs/T1.lean`. Removed former restriction entry: Retains admissibility, both twelve-unit variance-bound failures, the repeated-block family, zero population OLS coefficients and the failed arithmetic step. Omits the additional explicit covariance and fourth-moment evaluations, zero contrast-variance evaluations, exact printed-right-hand-side values and expanded oracle-statistic formula.

- **P002-T2 (`SAP.P002a.T2`):** `SAP.P002a.T2WholeStatement`, proved by `SAP.P002a.WH.W2.T2_whole`. Files: `SAP/P002a/Defs/WholeW2.lean`, `SAP/P002a/WH/W2/Leaves.lean`, `SAP/P002a/WH/W2/P/T2_L1.lean`, `SAP/P002a/WH/W2/P/T2_L2.lean`, `SAP/P002a/WH/W2/P/T2_L3.lean`, `SAP/P002a/WH/W2/Proofs/T2.lean`. Removed former restriction entry: States the two corrected final lower bounds, with positive covariate dimension for the adjusted bound. Omits the intermediate corrected chains (C.3)-(C.8), the residual-square inequality in the proof of (E.10), the negative-delta parameter-space inclusions and the explicit identification with the printed bounds for nonnegative delta.

- **P002-T4 (`SAP.P002a.T4`):** `SAP.P002a.T4WholeStatement`, proved by `SAP.P002a.WH.W2.T4_whole`. Files: `SAP/P002a/Defs/WholeW2.lean`, `SAP/P002a/WH/W2/Leaves.lean`, `SAP/P002a/WH/W2/P/T4_L1.lean`, `SAP/P002a/WH/W2/P/T4_L2.lean`, `SAP/P002a/WH/W2/P/T4_L3.lean`, `SAP/P002a/WH/W2/P/T4_L4.lean`, `SAP/P002a/WH/W2/Proofs/T4.lean`. Removed former restriction entry: Retains moment collapse, common adjusted outcomes and both parameter-class coverage counterexamples, including nonemptiness and their limiting infima. Omits the detailed zero-statistic and quantile identities, fitted-coefficient and rank-event calculations, the separate 258 and 774 rank-loss bounds, the explicit grid-moment identities, and all of the six-unit illustration (d): its admissibility, heterogeneous effects, 20-assignment exact coverage and 312 nonzero values among 400 reassignment pairs.

- **P002-T5 (`SAP.P002a.T5`):** `SAP.P002a.T5WholeStatement`, proved by `SAP.P002a.WH.W2.T5_whole`. Files: `SAP/P002a/Defs/WholeW2.lean`, `SAP/P002a/WH/W2/Leaves.lean`, `SAP/P002a/WH/W2/P/T5_L1.lean`, `SAP/P002a/WH/W2/P/T5_L10.lean`, `SAP/P002a/WH/W2/P/T5_L11.lean`, `SAP/P002a/WH/W2/P/T5_L2.lean`, `SAP/P002a/WH/W2/P/T5_L3.lean`, `SAP/P002a/WH/W2/P/T5_L4.lean`, `SAP/P002a/WH/W2/P/T5_L5.lean`, `SAP/P002a/WH/W2/P/T5_L6.lean`, `SAP/P002a/WH/W2/P/T5_L7.lean`, `SAP/P002a/WH/W2/P/T5_L8.lean`, `SAP/P002a/WH/W2/P/T5_L9.lean`, `SAP/P002a/WH/W2/Proofs/T5.lean`. Removed former restriction entry: Requires a nontrivial filter of arbitrarily large nonempty parameter classes for each uniform lower bound, and positive covariate dimension for the adjusted bound. Retains nominal convergence and sufficient unadjusted sharpness under a supplied admissible nondegenerate constant-effect sequence. Does not assert necessity of that sequence condition or a sharpness characterization for adjusted classes, and omits the separate assertion that degenerate classes may have coverage one.

- **P002-T6 (`SAP.P002a.T6`):** `SAP.P002a.T6WholeStatement`, proved by `SAP.P002a.WH.W3.T6_whole`. Files: `SAP/P002a/Defs/WholeW3.lean`, `SAP/P002a/WH/W3/Leaves.lean`, `SAP/P002a/WH/W3/P/T6_L1.lean`, `SAP/P002a/WH/W3/P/T6_L2.lean`, `SAP/P002a/WH/W3/P/T6_L3.lean`, `SAP/P002a/WH/W3/P/T6_L4.lean`, `SAP/P002a/WH/W3/P/T6_L5.lean`, `SAP/P002a/WH/W3/Proofs/T6.lean`. Removed former restriction entry: Retains the admissible even family, odd extension, full-rank even-sample fits, exploding feasible-variance lower bound, estimator bound below 5/n, and probability-one failure of printed (E.61). Omits the intermediate moment and residual evaluations, the exact rare-block slopes and statistic values, the zero-expectation identity, the binomial-coefficient variance bound, the sharper 121/(25n) estimator bound and the pointwise ratio bound. No separate conclusion about (E.58)-(E.60) is asserted.

- **P002-T7 (`SAP.P002a.T7`):** `SAP.P002a.T7WholeStatement_W4`, proved by `SAP.P002a.WH.W4.T7_whole`. Files: `SAP/P002a/Defs/WholeW4.lean`, `SAP/P002a/WH/W4/Leaves.lean`, `SAP/P002a/WH/W4/Proofs/T7.lean`. Removed former restriction entry: Adds strict positivity of both population OLS residual variances, popVar (residual (P n) a (late (P n).pop)) > 0 for a in {0,1}, at every size. Xi models in which either arm's population residual variance vanishes at some size are dropped; Xi admits them and positive unprojected adjusted-outcome variances do not exclude them. None of the four limits (E.58)-(E.61) is dropped: each is stated for every positive threshold, almost surely along every fixed strictly increasing subsequence.

For T7, the canonical correction of 2026-11-04 includes pointwise residual positivity, so that premise remains in the new whole statement; its former classification as an extra restriction is removed. T11 retains the stated positivity guards for normalized divisions. T15 retains standing adjusted-outcome variance positivity while removing the finite-size conditional-variance positivity premise.

Dependent-proof repairs: none. No unchanged Solution theorem uses a switched theorem, and the statements, docstrings, proofs and manifest entries of T3, T10, T12 and T13 are unchanged.

Verification: `rebuilt 66 modules of SAP/P002a; token scan clean` using `python3 /home/ubuntu/sap/tools/rebuild_sap.py . P002a` from the working directory (one Lean process at a time; no `lake`). The scratch file `scratch/P002aWholeAxioms.lean` imports only `SAP.P002a.Solution` and prints axioms for all eleven switched theorems; each uses only `propext`, `Classical.choice` and `Quot.sound`. Logs: `scratch/P002aWholeRebuild.log`, `scratch/P002aWholeAxioms.log`. The exact declarations and proof terms are recorded in `switched.json`.


## Declaration review round 3

**SAP.P002a.T7 / P002-T7 — accepted (`restriction_inaccurate`, minor).** The current [finding](fw/round3/T7/r7g2/findings.json) identifies an obsolete `row_use_note`, not a defect in the declaration. I checked the explicit population OLS residual-variance premise in [T7WholeStatement_W4](SAP/P002a/Defs/WholeW4.lean:42), all four conclusions (E.58)-(E.61), and the [direct application of the existing theorem](SAP/P002a/WH/W4/Leaves.lean:15). The [Challenge docstring](SAP/P002a/Challenge/Part1.lean:69) already states this nondegenerate scope, and the manifest already has `decision: whole` and `restriction: null`.

Replaced the contradictory row-use note with the reviewer's proposed text: residual positivity belongs to the corrected canonical P002-T7 claim dated 2026-11-04, so the current theorem states that claim wholly and adds no restriction. The older wrong-credit assessment concerned the superseded unqualified claim. The clarification in the current instructions permits use of that row for exactly its Lean statement; all four limits are retained. No theorem, definition, docstring, decision, or proof changed. The earlier omission finding under `fw/round3/P002-T7/r3g1/` concerns the superseded state before T7 was added; the current theorem and whole decision address it.

Scope provenance: the [current review](fw/round3/T7/r7g2/REPORT.md) and this round's orchestrator update identify the corrected nondegenerate target. The supplied `work.json` still records the older unqualified T7 text at [line 710](work.json:710); I preserved that source packet and used the current corrected target identified by the update. This distinction explains the historical scope discussions above. The report's opening counts now match the existing manifest: **14 whole, 0 restricted, 1 refuted, 0 omitted**.

`comparator.json` was regenerated from the manifest and retains the same fifteen theorem names and kernel settings. The metadata check also removed two contradictory unused-row entries: T2 already lists `corrected_variance_algebra` as used, and T9 already lists `leastRayleigh_lower` as used. Every existing SAP Lean module was compiled with `sap-lean` in dependency order, including the supplied whole-statement and whole-proof modules, and `#print axioms` was rerun for every Solution theorem. Logs and source hashes are recorded in `scratch/round3-fix-compile.log`, `scratch/round3-fix-axioms.log`, and `scratch/round3-fix-validation.json`. The source-hash check confirms that no Lean source changed, so no additional declaration acquires a changed definition in this revision. No new mathematical proof was written.

Current file-length audit: the inherited whole-proof expansion contains files above the original 300-line limit; they are listed with line counts in `scratch/round3-fix-validation.json`. This metadata correction preserves those existing files and records the discrepancy rather than changing reviewed declarations or proof modules. The updated manifest, comparator configuration and report are within the limit. All fifteen theorem proofs use only the permitted dependencies, and there are **0 open glue tasks**.

Round-3 result: **66 modules rebuilt successfully**, with the 15 permitted Challenge-placeholder warnings and 87 inherited linter/deprecation warnings, and **15 theorem dependency checks passed**. All Lean source hashes are unchanged.
