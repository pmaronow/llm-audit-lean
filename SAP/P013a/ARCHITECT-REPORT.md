P013a packages exactly the 14 targets assigned to this unit in `work.json`.
There are **8 whole, 5 restricted, 1 refuted, and 0 omitted** targets.
All 14 Solution theorems are proved; there are **0 open glue tasks**.

The restricted targets are:

- **P013-T1:** Retains the paired experiment, exact finite identities, limiting
  scaled variances, variance-ratio limit, normal limit, exact limiting coverage
  formula and strict undercoverage. Omits the displayed decimal approximation
  at the 5% level. The graph row sum is bounded by 2; its equality to 2 is not
  asserted. The exact joint probabilities and product design remain explicit.
- **P013-T2:** Coverage and both joint-probability rate implications additionally
  require `NestedPopulationSetup`: a common outcome table under injective
  exposure labels, with fixed comparison labels across population sizes. This
  forces existing units' comparison outcomes to remain fixed. This restriction
  is present in the actual uniform-joint rate statement as well as in the rows
  marked narrower. The statement retains both concentration-to-lower-tail
  implications, both rates and their lower-tail consequences. It omits the
  further centered-concentration conclusions following those rates and the final
  negative assertion about C3, genuine C5 and C6 without the lower-tail condition.
- **P013-T8:** Retains centered concentration, the finite relative-tail bound,
  its zero limit, and both coverage lower bounds. Only the expectation-limit
  implication in part (d) additionally assumes every realized variance estimate
  is strictly positive at every size. Thus its ratios and studentized statistics
  have nonzero denominators. The coverage events count negative estimates as
  noncoverage. No finite-sample positivity premise is added to parts (a)--(c).
- **P013-T9:** Retains the mean-consistency implication from part (i) and the
  algebraic identity from part (iii). The consistency implication carries the
  existing row's common-outcome-table premise `NestedPopulationSetup`. It omits
  contrast consistency from part (i), coverage from part (ii), and relative-bias
  guidance from part (iv).
- **P013-T14:** Retains the exposure-total statements of Lemma 5.1 and
  Propositions 5.1 and 5.2 with the quadratic A2 correction. Covers the Appendix
  sampling results only through this specialization with `0 < pi_i < 1` and
  exponents `a_ij = b_ij = 2`; omits the general conjugate-exponent estimator and
  the generic sampling cases allowing `pi_i = 1`.

No targets are omitted. P013-T12 is the one `refuted` target: its canonical claim
is affirmative, and the theorem negates both the unrestricted bias bound and the
logarithmic-rule guarantee on the meaningful nonzero-total domain. The correct
numerical replicate example is retained under T4. T1, T3, T5 and T7 already have
refutations as their canonical claims, so their decisions follow coverage of
those refutations rather than using the `refuted` label.

The definition route uses six Mathlib-only Defs parts, shared by Challenge and
Solution. The SAP structures describe positive finite design weights, exposure
maps and fixed outcome tables. Expectations, probabilities and covariances are
ordinary finite weighted sums. The variance estimates retain the ordered-pair
terms and the paper's specified division convention at zero joint probabilities.
The simulations retain the independent product law and smoothed probabilities.
The two fixed counterexample families retain their assignment weights and
outcomes explicitly. Only the assigned targets T1--T14 are packaged.

`Bridge.lean` supplies field-preserving adapters in both directions for designs,
populations, experiments and experiment sequences. It checks probabilities,
expectations, variances, marginals, joints, estimators, dependency conditions,
sequence premises, coverage and the concrete family definitions by `rfl` or
`Iff.rfl`. The design round trip uses constructor elimination followed by `rfl`.
No correspondence requires a statistical or analytic argument. The Solution
instantiates the existing declarations with these adapters; concrete models agree
definitionally. Its other steps are conjunction, logical rearrangement and finite
sum/algebraic transport of exported facts.

T5 assembles the identity and triangle witnesses and the shared-exposure family,
including exact identity row sums equal to 1 in both presentations;
T6 includes the explicit linear finite pair-count bounds and the normalized
pair-count limit defining Condition 4. T7 also reuses the existing
`block_asymptotic_positive_estimator` declaration to certify the denominator in
the fixed block family's studentization. T13 states the single-exposure total
claims separately from the contrast claims within its one theorem, so total
unbiasedness does not require a second exposure as an incidental premise.

The nonempty-population and positivity premises exclude undefined population
means and inverse marginal probabilities. Minimum probabilities are represented
by attained-minimum specifications. Normal critical values occur only for
levels strictly between zero and one. The block outcomes use positive unit
indices, and the existing endpoint results control their least-block definition.
T9's scalar studentization identity requires both variances to be positive.

Validation completed:

- Compiled all six Defs parts, the Defs root, Bridge, both Challenge parts, the
  Challenge root, Solution and the scratch dependency check using `sap-lean` in
  dependency order. The compilation command finished with exit status 0.
- Ran `#print axioms` for all 14 Solution theorems in `scratch/Axioms.lean`.
  Every result lists exactly `propext`, `Classical.choice` and `Quot.sound`;
  the results are recorded in `scratch/round1-axioms.log` and the manifest.
- Independently imported Challenge and Solution into separate Lean environments
  in `scratch/Identity.lean`. All 14 theorem types and the declarations in
  their recursively referenced type/definition closure were structurally
  identical. The latest result is recorded in `scratch/round1-identity.log`.
- Parsed both JSON files; checked exact unit-target coverage, complete accounting
  of credited rows, matching theorem lists, proved status, permitted dependencies,
  required option settings, import boundaries and the 300-line file limit.
  Forbidden source tokens occur only in the permitted Challenge stubs.

The orchestrator's preserved
[Comparator result](SAP/P013a/verification/comparator-result.json) and
[kernel log](SAP/P013a/verification/comparator.log) record acceptance of the
preceding snapshot by all three kernels on 2026-11-03. They are historical
evidence; the changed T5 statement requires renewed certification. This revision
reruns Lean compilation and the local structural check, without claiming a new
external-kernel run. `comparator.json` retains the 14 theorem names and requested
kernel configuration. Some imported project modules contain unfinished
statements; none appears in the dependency checks for the 14 packaged proofs.
Existing project sources were not edited.

## Declaration review round 1

- **T5 — exact identity row sum, minor label finding: accepted and fixed.**
  The equality to 1 is explicit in the
  [canonical P013-T5 statement](work.json), part (a), whereas
  [the credited identity row](AronowAudit/P013/P013_Audit.lean) at line 726 exports
  only an upper bound. Added `sum_j 1_(i=j) = 1` in both identity-graph
  presentations of `T5Statement`, at
  [Defs/Part5.lean](SAP/P013a/Defs/Part5.lean) lines 146 and 157. The two new
  proof obligations in [Solution.lean](SAP/P013a/Solution.lean) are discharged by
  `intro i; simp`, simplification of a finite singleton sum. All existing
  counterexample components remain proved, so T5 retains `whole`. Its docstring
  now states both exact row sums. This changes only the definition
  `SAP.P013a.T5Statement`; the affected Challenge declaration is `SAP.P013a.T5`.
- **T14 — omitted general Appendix scope, minor label finding: accepted and
  fixed.** The [canonical P013-T14 entry](work.json), `definitions_needed` at
  line 2764, includes Appendix Propositions A.1 and A.2 and Corollary A.2,
  including arbitrary positive conjugate exponents and marginal probabilities
  equal to 1. The existing exports `varianceHT_bias` and
  `varianceHT_conservative` in
  [P013_Audit.lean](AronowAudit/P013/P013_Audit.lean), lines 435 and 494, supply
  the exposure specialization with strict marginal positivity below 1 and the
  quadratic correction. Changed T14's manifest decision to `restricted` and
  added the same precise disclosure to its restriction and Challenge docstring.
  Its theorem statement, proof and definitions are unchanged. No general
  exponent proof or additional mathematical assumption was introduced.

All 14 fully qualified theorem names remain listed and proved. The manifest and
Comparator configuration were parsed and checked against the rebuilt modules;
the configuration needs no semantic change. The round's full compilation and
dependency audit are in `scratch/round1-build.log`; all 14 dependency results are
also saved separately in `scratch/round1-axioms.log`. There are no open glue tasks
and no disputed findings.

## Whole versions (new proofs)

The five targets below now use the proved whole statements. The current totals
are **13 whole, 0 restricted, 1 refuted, and 0 omitted** targets; the restriction
discussion above describes the preceding snapshot. No other Solution proof uses
a switched theorem, so no dependent-proof repairs were needed.

### P013-T1 (`SAP.P013a.T1`)

- Challenge: `SAP/P013a/Challenge/Part1.lean`; Solution: `SAP/P013a/Solution.lean`.
- Whole statement: `SAP.P013a.T1WholeStatement` in `SAP/P013a/Defs/WholeW1.lean`.
- Blueprint: `SAP/P013a/WH/W1/Leaves.lean`; proof: `SAP/P013a/WH/W1/Proofs/T1.lean` (`SAP.P013a.WH.W1.T1_whole`).

- Removed restriction: Retains the explicit paired family, its finite identities, all exact asymptotic limits and the strict undercoverage formula. Omits the decimal approximation 0.9103748944... at alpha=0.05. States the pair-graph row-sum bound at most 2, rather than the canonical equality to 2.

- Proved numerical leaf: `SAP/P013a/WH/W1/P/T1_L1.lean`; shared support:
  `SAP/P013a/WH/W1/Support.lean` and `SAP/P013a/WH/W1/Numerics.lean`.

### P013-T2 (`SAP.P013a.T2`)

- Challenge: `SAP/P013a/Challenge/Part1.lean`; Solution: `SAP/P013a/Solution.lean`.
- Whole statement: `SAP.P013a.T2WholeStatement` in `SAP/P013a/Defs/WholeW1.lean`.
- Blueprint: `SAP/P013a/WH/W1/Leaves.lean`; proof: `SAP/P013a/WH/W1/Proofs/T2.lean` (`SAP.P013a.WH.W1.T2_whole`).

- Removed restriction: Adds NestedPopulationSetup to the coverage implication and both joint-probability rate implications: injective exposure labels, fixed comparison labels and one common potential-outcome table across population sizes. Thus existing units have stable comparison outcomes. Retains the two rates, their lower-tail consequences and both concentration-to-lower-tail implications. Omits the separate assertion of centered concentration following each rate and the final counterexample assertion that C3, genuine C5 and C6 alone do not imply coverage.

- Shared support: `SAP/P013a/WH/W1/Support.lean`; this target has no
  separate open leaf.

### P013-T8 (`SAP.P013a.T8`)

- Challenge: `SAP/P013a/Challenge/Part2.lean`; Solution: `SAP/P013a/Solution.lean`.
- Whole statement: `SAP.P013a.T8WholeStatement` in `SAP/P013a/Defs/WholeW1.lean`.
- Blueprint: `SAP/P013a/WH/W1/Leaves.lean`; proof: `SAP/P013a/WH/W1/Proofs/T8.lean` (`SAP.P013a.WH.W1.T8_whole`).

- Removed restriction: Retains centered concentration, the finite relative lower-tail bound and its zero limit, both coverage lower limits and the expectation-limit/studentization implication. For that last implication only, adds strict positivity of every realized variance estimate at every size, so both the variance ratio and studentized statistic have nonzero denominators. Negative variance estimates count as noncoverage in the coverage clauses.

- Shared support: `SAP/P013a/WH/W1/Support.lean`; this target has no
  separate open leaf.

### P013-T9 (`SAP.P013a.T9`)

- Challenge: `SAP/P013a/Challenge/Part2.lean`; Solution: `SAP/P013a/Solution.lean`.
- Whole statement: `SAP.P013a.T9WholeStatement` in `SAP/P013a/Defs/WholeW1.lean`.
- Blueprint: `SAP/P013a/WH/W1/Leaves.lean`; proof: `SAP/P013a/WH/W1/Proofs/T9.lean` (`SAP.P013a.WH.W1.T9_whole`).

- Removed restriction: Retains only the mean-consistency assertion of part (i) and the studentization identity of part (iii). Adds NestedPopulationSetup, requiring one outcome table across sizes under injective exposure labels with fixed comparison labels, to the mean-consistency implication. Omits contrast consistency in part (i), the coverage assertion of part (ii), and relative-bias guidance in part (iv).

- Shared support: `SAP/P013a/WH/W1/Support.lean`; this target has no
  separate open leaf.

### P013-T14 (`SAP.P013a.T14`)

- Challenge: `SAP/P013a/Challenge/Part2.lean`; Solution: `SAP/P013a/Solution.lean`.
- Whole statement: `SAP.P013a.T14WholeStatement` in `SAP/P013a/Defs/WholeW1.lean`.
- Blueprint: `SAP/P013a/WH/W1/Leaves.lean`; proof: `SAP/P013a/WH/W1/Proofs/T14.lean` (`SAP.P013a.WH.W1.T14_whole`).

- Removed restriction: Retains the exposure-total statements of Lemma 5.1 and Propositions 5.1 and 5.2 with the quadratic A2 correction. Covers the Appendix sampling results only through this specialization with 0 < pi_i < 1 and exponents a_ij = b_ij = 2; omits the general conjugate-exponent estimator and the generic sampling cases allowing pi_i = 1.

- Shared support: `SAP/P013a/WH/W1/Support.lean`; this target has no
  separate open leaf.

Validation for all five switches:

- `python3 /home/ubuntu/sap/tools/rebuild_sap.py . P013a` completed with exit
  status 0: all 22 modules rebuilt from scratch; forbidden-token scan clean.
  Recorded in `scratch/SwitchP013aRebuild.log`.
- `scratch/SwitchP013aAxioms.lean` imports only `SAP.P013a.Solution` and runs
  `#print axioms` on each switched theorem. All five list exactly `propext`,
  `Classical.choice` and `Quot.sound`; see `scratch/SwitchP013aAxioms.log`.
- The scope audit confirms every other target, statement, definition and proof
  is unchanged, and both import boundaries hold. `lake` was never run; Lean
  compilation was sequential. Per-target results are in `switched.json`.
