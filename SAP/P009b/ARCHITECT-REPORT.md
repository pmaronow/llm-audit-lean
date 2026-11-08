P009b after declaration review round 2: 17 targets; 6 whole, 8 restricted, 3 refuted, 0 omitted.
All 17 Solution theorems retain their fully qualified names and are proved; there are
no open glue tasks. Only P009-T18 through P009-T34 are packaged.

## Referee findings and revision 2 actions

I checked all 17 entries in each [referee A report](referees/round1/a/findings.json)
and [referee B report](referees/round1/b/findings.json) against the canonical content in
[work.json](work.json), the SAP definitions, and the credited project statements.
The only substantive error identified by a referee is A's T25 finding. It is correct.

The old empiricalBias definition parsed as ((sum of estimates) − 1)/R. It therefore
subtracted the target value only once. With all estimates equal to one, it returned
1/2 at R=2 and 49999/50000 at R=50000, instead of zero. I changed the SAP definition
to (∑ r, (estimates r − 1))/R, with explicit summand parentheses. reportedBias remains
its absolute value. The corrected definition captures the entire canonical caption
claim, so T25 remains whole after the repair.

The corresponding Bridge no longer claims definitional equality with the project's
misparsed statistic. T25Caption_transport uses existing absolute-value nonnegativity,
the definitional absolute-value identity, and only the statistic-independent constants
from the credited caption row. The population-bias transport and the R=1 sign-loss
proof are retained. This is logic and instantiation of existing declarations; the
read-only project files are unchanged. The T25 docstring now displays the corrected
summand explicitly.

I disagree with B's original T25 correct_whole verdict for the original source. B's
[blind reading, line 33](referees/round1/b/reading.md) silently put subtraction inside
the sum. The original syntax does not do that. The compiled definitional equality in
[scratch/Revision2Bias.lean](scratch/Revision2Bias.lean) independently reproduces the
old parse and A's two numerical discrepancies. The same file checks the corrected
statistic is zero at R=2 and R=50000 with all estimates one, checks its defining
summand by definitional equality, and verifies that constant estimates two give signed
error one for every positive R. The intended expression is the formal-content clause
(i) of P009-T25 in [work.json](work.json). Thus A's correction takes precedence over
B's mistaken expansion; B's assessment becomes valid for the repaired statement.

The table lists every target finding from both referees and the action taken. A and B
refer to their mathematical scope verdicts before revision 2's classification update.

| Target | A | B | Action |
| --- | --- | --- | --- |
| T18 | correct_whole | correct_whole | Retained existing statement; the further omission is addressed in declaration review round 2 below. |
| T19 | correct_whole | correct_whole | Kept all counterexample facts; relabelled refuted under revision 2. |
| T20 | correct_restricted | correct_restricted | Retained the disclosed restrictions and proof. |
| T21 | correct_restricted | correct_restricted | Kept the aggregate counterexample and its exclusions; relabelled refuted. |
| T22 | correct_restricted | correct_restricted | Retained all finite/asymptotic scope disclosures and the proof. |
| T23 | correct_restricted | correct_restricted | Kept sampling-integral refutation, integrability and exclusions; relabelled refuted. |
| T24 | correct_restricted | correct_restricted | Retained the finite exception and disclosed empirical exclusions. |
| T25 | not_faithful | correct_whole | Accepted A's three linked issues; fixed definition and bridge, checked R>1, retained whole. |
| T26 | correct_restricted | correct_restricted | Retained supplied-exponent scope and disclosed omissions. |
| T27 | correct_restricted | correct_restricted | Retained supplied-minimizer scope and disclosed omissions. |
| T28 | correct_whole | correct_whole | Retained the mean, centering, distance and eventual clauses. |
| T29 | correct_restricted | correct_restricted | Retained natural powers and the full chain on that domain. |
| T30 | correct_whole | correct_whole | Retained both estimator identities and equality characterizations. |
| T31 | correct_whole | correct_whole | Retained finite CDF and all-threshold convergence. |
| T32 | correct_whole | correct_whole | Retained updates, crossings and simultaneous flips. |
| T33 | correct_whole | correct_whole | Retained all corrected spillover and B1 clauses. |
| T34 | correct_restricted | correct_restricted | Retained endpoint/final bounds and all first-moment exclusions. |

Revision 2 explicitly forbids labelling a refutation whole. Accordingly T19, T21 and
T23 are now refuted, and each docstring begins "The printed claim is false:".
The two partial refutations retain their exact non-null restriction texts. These are
classification changes under the latest instruction, not mathematical disagreements
with the referees' assessment of the counterexample facts. No theorem was broadened.

## Declaration review round 1

- **SAP.P009b.T23 / P009-T23 — restriction_inaccurate, minor**
  ([finding](fw/round1/T23/r1g2/findings.json), entry for T23): accepted.
  The canonical claim specifies squared bias divided by variance. The retained
  signed-bias integrals equal −1 and the complete-design variance integrals equal
  58/(3n), while the last conjunct of
  [T23CoreStatement](SAP/P009b/Defs/Part3.lean:131) is
  1/(58/(3n)) = 3n/58. This is the squared-bias ratio; the signed-bias ratio
  would have the opposite sign. Changed the retained description to
  "complete-design squared-bias/variance ratio" and the omitted assertion to
  "divergence of the squared-bias/variance ratios" in the Challenge docstring,
  manifest restriction and target-scope text below. The manifest is the
  package source record. There is no disagreement with this finding.

The findings file also covers T24–T27; those entries have no issues or requested
fixes. T23's refuted decision, its integrability hypotheses, the existing omitted
clauses and all 17 fully qualified theorem names are retained. No shared definition,
statement, bridge or Solution proof was edited. Comparator configuration was parsed
and rewritten with the same theorem list, modules and checker arguments.

After this correction the entire package was recompiled with sap-lean in dependency
order and the trusted dependencies of all 17 Solution theorems were printed again.
Every theorem remains proved using only propext, Classical.choice and Quot.sound.
Both JSON files parse and the package consistency checks passed. At the close of
declaration review round 1, the counts were 7 whole, 7 restricted, 3 refuted,
0 omitted; 17 proved and 0 open glue tasks. Round 2 updates the T18 decision below.

## Declaration review round 2

- **SAP.P009b.T18 / P009-T18 — not_faithful, minor**
  ([findings](fw/round2/T18/r3g1/findings.json), entry for T18): accepted both
  linked issues. The final display of the canonical definitions_needed field in
  [work.json](work.json:50) asserts that each supported masked-vector likelihood
  ratio equals the likelihood ratio for its treated-incoming count. In contrast,
  [T18CoreStatement](SAP/P009b/Defs/Part3.lean:45) states only the final bound on
  a supported-vector ratio. Its other clauses are scalar laws, ratios and bounds;
  [T18ZeroStatement](SAP/P009b/Defs/Part5.lean:16) adds only probability one for
  the zero-count event. Thus the separate equality is missing from the packaged
  theorem, and the previous whole decision overstated its scope.

I selected the reviewer's explicit restriction alternative. T18 is now restricted,
and its Challenge docstring and manifest use the exact disclosure below. This
retains all existing scalar conclusions, both zero-count assertions and the full
supported-vector bound of Lemma A12. The credited
[corrected_hypergeometric_proof](AronowAudit/P009/Wave1/Gap/GLP0091B4.lean:510)
exports those conclusions but not the vector-to-count ratio equality as a conclusion.
No additional proof of that equality is attempted. There is no disagreement with
this finding and no new hypothesis, shared definition or proof is introduced.
The same report's entries for T19–T22 have no open issues.

All 17 theorem names and types, SAP definitions, bridge adapters and Solution proofs
are unchanged. The manifest's T18 decision/restriction and the Challenge documentation
now describe the narrower scope. Comparator configuration was parsed and rewritten
with the same theorem list and checker arguments. The package was recompiled in
full dependency order with sap-lean and all 17 trusted-dependency lists were refreshed;
only propext, Classical.choice and Quot.sound occur. Both JSON files and the package
consistency checks pass. Current counts are 6 whole, 8 restricted, 3 refuted, 0 omitted;
17 proved and 0 open glue tasks.

## Target scope

The whole targets are T25, T28, T30, T31, T32 and T33. The refuted targets are
T19, T21 and T23. There are no omitted targets and no open glue tasks.
Every remaining restricted target is listed below with its full restriction. The
same text is in its Challenge docstring and manifest entry.

- **P009-T18**: Retains the two hypergeometric laws, zero-count assertions, scalar likelihood-ratio identity and bounds, and supported-vector bound. Drops the identity equating each supported-vector likelihood ratio to its treated-incoming-count likelihood ratio.

- **P009-T20**: Retains the two pointwise witness-count inequalities and the final e_AVG ≤ C₂² bound for indicators induced by finite full-cube outcome schedules, positive sample sizes, and symmetric pairings without fixed points. Drops the displayed aggregate proof chain: the summed bound by triple products, its equality to the sum of outgoing-count products, the bound by paired squares, the splitting into two sums, and the permutation reindexing equality. Does not assert the arbitrary supplied-indicator-array version.

- **P009-T22**: Drops all individual pair/arm conditional covariance identities in clause (ii), convergence about the printed centre, and all three limiting-regime assertions (limit one, limit minus one, and comparable-order sign alternatives). Retains the aggregate finite formulas, exact difference of the two centres and its bound, and corrected-centre convergence. The convergence clause requires a common RegularSequence bound with observed moment order q ≥ 4, in addition to the fair one-source model and source baseline −1/4.

- **P009-T24**: Retains the finite complete-interference exception for every positive even sample size, arbitrary fixed baselines, and both balanced complete and paired designs, including supportwise identities, both signed and absolute biases, and both mean squared errors. Drops the blanket empirical assertion that bias is negligible in all other settings and sample sizes, and does not certify the printed Monte Carlo table entries.

- **P009-T26**: Retains the pairwise mixing coefficient, external coefficient for each specified exponent, the exponent-one formula, its positive normalized limit, and failure of the little-o condition. Drops the potential-outcome bound |y_i(z)| ≤ k^(3/2), the claim of unbounded maximal moment order and its selection of exponent one, the separately stated normalization by n/4 at p=1/2, and the p=1/3 non-equivalence example.

- **P009-T27**: Retains the finite Bernoulli atom bounds under the standing regularity conditions, the finite-law three-point approximation, and the error bound and two limits for any supplied minimizing sequence. Does not assert existence of a minimizing sequence. Drops the separate assertion that the exponential upper bound tends to zero and the explicit heavy-atom example showing that lower bounds alone do not imply the limits.

- **P009-T29**: Restricts the power a to natural numbers; fractional and all other non-natural orders are omitted. Retains every numerical link of the moment chain and the endpoint bound, with absolute covariance strengthening the printed signed covariance bound.

- **P009-T34**: Retains the half-difference identity, the per-arm endpoint bound by k, k ≥ 2, the two-arm bound by 2k ≤ 2k², and Lemma A17. Drops both intermediate first-moment links: the conditional/unconditional potential-mean difference is at most the unconditional absolute first moment, and that first moment is at most k. Does not separately assert the displayed weighted proof-chain equalities.

The partial refutations retain these exclusions:

- **P009-T21**: Retains the specified six-unit experiment and all aggregate numerical quantities and discrepancies, including n*d_AVG, the MSQ/B1/B2 decomposition and the expected normalized variance gap. Drops the enumeration of the six contributing ordered pairs and their individual conditional covariance values. Refutes only the exact printed evaluations; makes no assertion refuting convergence.

- **P009-T23**: Retains the uniform-baseline sampling integrals of both signed biases, both design variances, both mean squared errors, and the complete-design squared-bias/variance ratio. Adds integrability of each of the twelve sampling integrands. Drops the universal fixed-baseline clauses (a)–(d), the supportwise balance/outcome/effect/estimator/marginal identities, the claimed divergence of the squared-bias/variance ratios, and any identification of the integrals of design variances with a variance on a joint sampling-and-assignment space. The auxiliary 100-unit zero-baseline row is not used.

T19 retains its complete six-unit counterexample, including the interference
certificates, pairing involution and individual witness terms. T21 refutes only the
exact printed aggregate evaluations; it does not refute the convergence display.
T23 states sampling integrals of design quantities and does not assert a separate
joint-space variance identity or an asymptotic divergence conclusion.

## Shared definitions and bridges

The package uses SAP-named definitions compiled once and imported by both sides.
Defs/Part1 and Part2 contain the finite randomization setting and relevant paper
quantities; Part3 and Part4 contain exported claim components; Part5 assembles targets.
Each Defs part imports Mathlib and only earlier Defs parts. The Challenge imports
only these definitions. The Solution never imports the Challenge. Both theorem types
refer to the same T18Statement through T34Statement constants, with shared explicit
universe parameters for T27, T28 and T31.

Bridge/Part1 defines toLaw, toExperiment, toPairing and toStudy by copying fields,
retaining all probability, pairing and growth certificates. mean_correspondence and
potential_correspondence use definitional equality. to_design splits the design
disjunction and maps an existential pairing witness. Individual transports work as follows:

- T18Core, T20Core, T27Atoms, T29Core and T30Core convert experiment/pairing data
  and instantiate the supplied project theorem; all relevant definitions reduce.
- T19Core, T21Core, T22Finite, T28Eventual, T31Finite, T32Update, T32Crossings,
  T32Paired and T33Core use direct definitional correspondence.
- T25Caption uses existing absolute-value nonnegativity and a definitional identity
  for the corrected statistic, retaining the supplied row's two numeric constants.
- T22Limit converts the study and transports its fair-law equality with congrArg toLaw.
- T23Core maps law/pairing families pointwise and retains explicit integrability.
- T24Core and T25Population convert experiments and use to_design.
- T26Core and T27Minimizer convert the study and retain all original hypotheses.
- T27Approximation and T28Finite convert laws; T31Limit converts the law sequence.
- T34Core converts the experiment/pairing and instantiates the supplied theorem.

Remaining Solution steps are conjunction, instantiation, definitional reduction,
finite-sum transport and arithmetic on existing results. In particular, the T25 repair
uses only already established absolute-value facts; it proves no new statistical result.
The other glue includes T18's zero-count binomial simplification, T19's credited
sum-of-bits indicator instances and witness arithmetic, T21's numerical substitutions,
T22's common-denominator centre subtraction, T24's absolute biases, T25's one-element
sign-loss example, T28's three-value pointwise mean identity and combination of its
centering declarations, and T34's addition of the two exported arm bounds.

## Ordinary-value domains and validation

Positive sizes exclude empty averages and empty extrema where those quantities occur.
T25 requires positive replicate count. T30 requires positive arm marginals. The
balanced complete and paired designs have nonempty arms on supported assignments;
the fair finite designs used for one-source quantities have positive marginal and
relevant distinct-pair event probabilities. T18's count and complete-design bounds
keep its binomial and probability ratios in their intended domains; its vector ratio
is used only at positive-probability patterns. T28 excludes thresholds at the atoms.
Finite sums give ordinary finite means. T23 explicitly assumes integrability of all
twelve sampling integrands. The Rayleigh supremum in positive finite dimension has a
nonempty bounded value set. I found no additional junk-value defect in either report.

All SAP files begin after their imports with both required implicit-variable options.
The full package is recompiled in dependency order using sap-lean, including every
Defs, Bridge and Challenge part/root, the Solution, the T25 regression checks, and
scratch/AxiomsP009b.lean. All 17 theorem names are unchanged. The fresh trusted-dependency
lists contain only propext, Classical.choice and Quot.sound and are recorded in the
manifest. Both JSON files parse. comparator.json retains the same 17 theorem names,
shared modules, permitted constants and external-checker arguments; declaration review
round 2 changes only T18 documentation and classification, not the theorem list.

scratch/validate_p009b.sh records the reproducible checks. scratch/check_package.py
checks target and row accounting, restrictions in docstrings, refutation prefixes,
shared statement references/universes, import boundaries, the two required options,
file lengths and trusted dependencies. No unusable credited row is invoked. The
orchestrator-supplied verification directory is retained as historical evidence.

The existing [Comparator result](SAP/P009b/verification/comparator-result.json) records
a successful check of the previous source snapshot, stamped 20261103T210237Z. That
certificate does not cover this revision: Defs/Part2, Bridge/Part1, Challenge/Part1 and
the manifest have changed. The revision requires a fresh external Comparator run;
no current external certificate is claimed. Its configuration is ready for that run.

The fidelity limitations remain exactly those listed above. The T25 summation mistake
is corrected in the shared definition, so both Challenge and Solution now use the
canonical statistic. Read-only project and referee files are unchanged.

## Whole versions (new proofs)

The following five targets now use their proved whole statements and generated whole proofs. This section supersedes the earlier scope and count descriptions for these targets; the current totals are 11 whole, 3 restricted and 3 refuted, with all 17 targets proved. Each target is updated in [Challenge/Part1.lean](SAP/P009b/Challenge/Part1.lean), [Solution.lean](SAP/P009b/Solution.lean) and [manifest.json](SAP/P009b/manifest.json).

- **SAP.P009b.T27 / P009-T27**: `SAP.P009b.T27WholeStatement` is proved by `SAP.P009b.WH.W1.T27_whole`.

  Files: [SAP/P009b/Defs/WholeW1.lean](SAP/P009b/Defs/WholeW1.lean), [SAP/P009b/WH/W1/Leaves.lean](SAP/P009b/WH/W1/Leaves.lean), [SAP/P009b/WH/W1/P/T27_L1.lean](SAP/P009b/WH/W1/P/T27_L1.lean), [SAP/P009b/WH/W1/P/T27_L2.lean](SAP/P009b/WH/W1/P/T27_L2.lean), [SAP/P009b/WH/W1/P/T27_L3.lean](SAP/P009b/WH/W1/P/T27_L3.lean), [SAP/P009b/WH/W1/Proofs/T27.lean](SAP/P009b/WH/W1/Proofs/T27.lean).

  Removed restriction: Retains the finite Bernoulli atom bounds under the standing regularity conditions, the finite-law three-point approximation, and the error bound and two limits for any supplied minimizing sequence. Does not assert existence of a minimizing sequence. Drops the separate assertion that the exponential upper bound tends to zero and the explicit heavy-atom example showing that lower bounds alone do not imply the limits.

- **SAP.P009b.T18 / P009-T18**: `SAP.P009b.T18WholeStatement` is proved by `SAP.P009b.WH.W1.T18_whole`.

  Files: [SAP/P009b/Defs/WholeW1.lean](SAP/P009b/Defs/WholeW1.lean), [SAP/P009b/WH/W1/Leaves.lean](SAP/P009b/WH/W1/Leaves.lean), [SAP/P009b/WH/W1/P/T18_L1.lean](SAP/P009b/WH/W1/P/T18_L1.lean), [SAP/P009b/WH/W1/Proofs/T18.lean](SAP/P009b/WH/W1/Proofs/T18.lean).

  Removed restriction: Retains the two hypergeometric laws, zero-count assertions, scalar likelihood-ratio identity and bounds, and supported-vector bound. Drops the identity equating each supported-vector likelihood ratio to its treated-incoming-count likelihood ratio.

- **SAP.P009b.T20 / P009-T20**: `SAP.P009b.T20WholeStatement` is proved by `SAP.P009b.WH.W1.T20_whole`.

  Files: [SAP/P009b/Defs/WholeW1.lean](SAP/P009b/Defs/WholeW1.lean), [SAP/P009b/WH/W1/Leaves.lean](SAP/P009b/WH/W1/Leaves.lean), [SAP/P009b/WH/W1/P/T20_L1.lean](SAP/P009b/WH/W1/P/T20_L1.lean), [SAP/P009b/WH/W1/Proofs/T20.lean](SAP/P009b/WH/W1/Proofs/T20.lean).

  Removed restriction: Retains the two pointwise witness-count inequalities and the final e_AVG ≤ C₂² bound for indicators induced by finite full-cube outcome schedules, positive sample sizes, and symmetric pairings without fixed points. Drops the displayed aggregate proof chain: the summed bound by triple products, its equality to the sum of outgoing-count products, the bound by paired squares, the splitting into two sums, and the permutation reindexing equality. Does not assert the arbitrary supplied-indicator-array version.

- **SAP.P009b.T22 / P009-T22**: `SAP.P009b.T22WholeStatement` is proved by `SAP.P009b.WH.W2.T22_whole`.

  Files: [SAP/P009b/Defs/WholeW2.lean](SAP/P009b/Defs/WholeW2.lean), [SAP/P009b/WH/W2/Leaves.lean](SAP/P009b/WH/W2/Leaves.lean), [SAP/P009b/WH/W2/P/T22_L1.lean](SAP/P009b/WH/W2/P/T22_L1.lean), [SAP/P009b/WH/W2/P/T22_L2.lean](SAP/P009b/WH/W2/P/T22_L2.lean), [SAP/P009b/WH/W2/P/T22_L3.lean](SAP/P009b/WH/W2/P/T22_L3.lean), [SAP/P009b/WH/W2/Proofs/T22.lean](SAP/P009b/WH/W2/Proofs/T22.lean).

  Removed restriction: Drops all individual pair/arm conditional covariance identities in clause (ii), convergence about the printed centre, and all three limiting-regime assertions (limit one, limit minus one, and comparable-order sign alternatives). Retains the aggregate finite formulas, exact difference of the two centres and its bound, and corrected-centre convergence. The convergence clause requires a common RegularSequence bound with observed moment order q ≥ 4, in addition to the fair one-source model and source baseline −1/4.

- **SAP.P009b.T26 / P009-T26**: `SAP.P009b.T26WholeStatement` is proved by `SAP.P009b.WH.W2.T26_whole`.

  Files: [SAP/P009b/Defs/WholeW2.lean](SAP/P009b/Defs/WholeW2.lean), [SAP/P009b/WH/W2/Leaves.lean](SAP/P009b/WH/W2/Leaves.lean), [SAP/P009b/WH/W2/P/T26_L1.lean](SAP/P009b/WH/W2/P/T26_L1.lean), [SAP/P009b/WH/W2/Proofs/T26.lean](SAP/P009b/WH/W2/Proofs/T26.lean).

  Removed restriction: Retains the pairwise mixing coefficient, external coefficient for each specified exponent, the exponent-one formula, its positive normalized limit, and failure of the little-o condition. Drops the potential-outcome bound |y_i(z)| ≤ k^(3/2), the claim of unbounded maximal moment order and its selection of exponent one, the separately stated normalization by n/4 at p=1/2, and the p=1/3 non-equivalence example.

Dependent-proof repairs: none were required. No other Solution proof references any of the five switched theorems, so every other theorem statement, docstring and proof is unchanged.

Validation: `python3 /home/ubuntu/sap/tools/rebuild_sap.py . P009b` rebuilt all 32 modules from scratch and passed the forbidden-token scan. `/home/ubuntu/sap/tools/sap-lean scratch/WholeAxiomsP009b.lean` imported `SAP.P009b.Solution` and ran `#print axioms` on all five switched theorems; each reported exactly `propext`, `Classical.choice` and `Quot.sound`. Lean compilation was sequential, with at most one Lean process running.

## Whole versions (new proofs)

P009-T29 and P009-T34 now use their proved whole statements and generated whole proofs. This section supersedes the earlier restrictions for these two targets; the current totals are 13 whole, 1 restricted and 3 refuted, with all 17 targets proved. Both are updated in [Challenge/Part1.lean](SAP/P009b/Challenge/Part1.lean), [Solution.lean](SAP/P009b/Solution.lean) and [manifest.json](SAP/P009b/manifest.json).

- **SAP.P009b.T29 / P009-T29**: `SAP.P009b.T29WholeStatement_W3` is proved by `SAP.P009b.WH.W3.T29_whole`.

  Files: [SAP/P009b/Defs/WholeW3.lean](SAP/P009b/Defs/WholeW3.lean), [SAP/P009b/WH/W3/Leaves.lean](SAP/P009b/WH/W3/Leaves.lean), [SAP/P009b/WH/W3/P/T29_L1.lean](SAP/P009b/WH/W3/P/T29_L1.lean), [SAP/P009b/WH/W3/Proofs/T29.lean](SAP/P009b/WH/W3/Proofs/T29.lean).

  Removed restriction: Restricts the power a to natural numbers; fractional and all other non-natural orders are omitted. Retains every numerical link of the moment chain and the endpoint bound, with absolute covariance strengthening the printed signed covariance bound.

- **SAP.P009b.T34 / P009-T34**: `SAP.P009b.T34WholeStatement_W4` is proved by `SAP.P009b.WH.W4.T34_whole`.

  Files: [SAP/P009b/Defs/WholeW4.lean](SAP/P009b/Defs/WholeW4.lean), [SAP/P009b/WH/W4/Leaves.lean](SAP/P009b/WH/W4/Leaves.lean), [SAP/P009b/WH/W4/Proofs/T34.lean](SAP/P009b/WH/W4/Proofs/T34.lean).

  Removed restriction: Retains the half-difference identity, the per-arm endpoint bound by k, k ≥ 2, the two-arm bound by 2k ≤ 2k², and Lemma A17. Drops both intermediate first-moment links: the conditional/unconditional potential-mean difference is at most the unconditional absolute first moment, and that first moment is at most k. Does not separately assert the displayed weighted proof-chain equalities.

Dependent-proof repairs: none were required. No other Solution proof references T29 or T34; all other theorem statements, docstrings, proofs and manifest entries are unchanged.

Validation: `python3 /home/ubuntu/sap/tools/rebuild_sap.py . P009b` rebuilt all 39 modules from scratch and passed the forbidden-token scan. `/home/ubuntu/sap/tools/sap-lean scratch/WholeSwitchAxiomsP009b.lean` imported `SAP.P009b.Solution` and ran `#print axioms` on T29 and T34; each reported exactly `propext`, `Classical.choice` and `Quot.sound`. Compilation was sequential, with at most one Lean process running at a time. No `lake` command was run.


## 2026-11-05 independently reviewed repair proposal

P009b now carries the independently certified on-support T21 refutation for every realized covariate/error vector in the specified uniform baseline support; the old off-support numerical witness remains auxiliary. T25 is accurately restricted for the deposited-code and empirical-table clauses. The original Opus T26 exponent-range docstring correction and other docfix resolution remain incorporated. All seventeen declaration targets are proved. No canonical work claim was changed.

The source, accepted certificate, current canonical work packet, exact Defs/Challenge closure, and fresh normal full-unit declaration and omission reviews are bound in assure/repair-integration-2026-11-05/P009b/plan.json. Original Opus docfix findings and earlier review rows remain historical evidence. This entry does not accept a claim event, rewrite WH adjudication, enable whole promotion, perform A3 replay, collect, release, or push.
