# P027a package report

11 assigned targets: **8 whole, 2 restricted, 0 refuted, 1 omitted**.
All **10 listed theorems are proved**; **0 open glue tasks** remain.
Whole targets: T1, T2, T3, T4, T10, T11, T12 and T13. T5 and T6 remain
restricted; T9 is omitted. Only the assigned targets are packaged.

## Historical restrictions before the whole-statement switch

The later whole-version section records which seven restrictions were removed.
Only the T5 and T6 restrictions and T9 omission below remain current.

- **P027-T1 (restricted):** the continuous uniform-start measure is not identified explicitly; the size sum and printed-PPS size formula, demeaning of x/4, the four group totals and A as their negative squared sum, total-scale numerical moments, relative bias -5/36, the comparison of the C2 expectation with the variance, and the samplewise identity z_k/p_k = estimated total are not separately stated. For the family, the alternative expression A = -N^2/q and the assertions that A and A/N^2 do not tend to zero are omitted.

- **P027-T2 (restricted):** adds integrability of the outcome-model variance, expected HT estimator and A, and integrability of the calibrated mean-scale A integrand. Calibration is imposed as the displayed equality for beta squared; the empirical size-variance calculation and its derivation from the supplement's beta formula are omitted. The intermediate off-diagonal and squared-total-sum rewritings of A, the explicit expected-estimator weighted-sum expansion, the explicit equality of the mean-scale design bias to A/N^2, the expectation of the difference inside the outcome integral, the finite uniform bound away from zero, and the numerical value at q=4, rho=0.99 are omitted. The scalar limit is reindexed to positive sample sizes.

- **P027-T3 (restricted):** omits the explicit marginal/joint probability and zero-pair lists and counts, the C1–C2 samplewise total and HT/C2 estimator and correction values, the original total expectation 3, the uncorrected-estimator expectations, and the positive witness's totalled A value. The finite sample laws, preservation of the positive witness's estimated total, both witnesses' variances, quadratic bounds and C2 expectations and biases are retained.

- **P027-T4 (restricted):** the bias-change conclusions use an exactly common-indicator fiber representation; the general probability-zero-disagreement input is used only for preservation on positive-weight atoms, variance and A. The within-group pairwise squared-difference identity and the explicit four-unit example reducing bias from 20 to zero are omitted. The comparison with the separately packaged three-unit witness is not restated.

- **P027-T5 (restricted):** omits the universal population and finite-collection bounds, the four stronger numerical lower bounds for relative bias, the individual phase totals, and the displayed table columns other than true variance, C2 and q. Retains the scalar 120-unit witness and its mean-scale values using 120^2. No identification of the reported column with a particular implementation or with averages of grouped design expectations is asserted.

- **P027-T6 (restricted):** states the finite phase law, without a continuous uniform-start identification. Adds integrability of the model variance, grouped expected estimator and every squared group total. Omits separate assertions for the expectation of the unit-level correction and A-star, the expectation of the grouped correction, E_y(S)=qL and V's expression in terms of E_y(S), explicit mean-scale identities, separate grouped HT total/uncorrected-estimator and variance-preservation identities, and the original eight-unit representation of the realized-ratio example (its grouped totals are retained). No assertion about which implementation produced the table or figure is made.

- **P027-T9 (omitted):** No credited Lean rows and no Lean statement for this target. The conditional interpretation of the reported table column is not inferred from the numerical statements assigned to T5 or from the formulas assigned to T6.

- **P027-T10 (restricted):** the continuous uniform-start measure on [0,8) and its induced four-atom sampling law are not identified explicitly. Omits the connection to the normalized random-size generator and any Gaussian event-probability assertion, the explicit joint probabilities and zero-pair count, the size-vector feasibility inequality and residual representation, and the explicit C2-versus-variance inequality. Retains the finite design, intervalwise systematic selection, printed first-order probabilities, samplewise HT values, total/mean moments, C2 expectation and the open-box bound.

- **P027-T11 (restricted):** adds integrability of A and the mean-scale design-bias integrand. Omits the realized-outcome assertion A(y0)=-16 and the resulting explicit average-versus-realization comparison and populationwise-guarantee discussion.

- **P027-T13 (restricted):** adds integrability of every systematic inclusion indicator on [0,1). Omits the scalar cap-map continuity, monotonicity and saturation facts, the explicit specialization of the general construction to the feasible printed formula, and identification of the explicit certainty-unit sample law with the continuous systematic construction. The explicit repaired finite law, its joint probabilities and the naive-capping sum are retained. The conditional redraw law and the provenance of the simulation code are not asserted.

## Definitions and bridges

The shared-definitions route is used throughout. Eight Mathlib-only Defs parts
contain finite sample data, weighted expectations and variances, the HT and C2
estimators, ordered distinct zero-inclusion pair sums, concrete witnesses,
periodic phases, outcome moments, systematic selection and negative-binomial
measures. The remaining definitions state components of the claims. All names
are in `SAP.P027a`. Challenge imports only these shared definitions; Solution
imports the shared definitions, Bridge and the existing audit modules.

`Design` stores the weight and selected subset at each finite atom. `Valid`
says that these weights are nonnegative and sum to one. This is the plain-data
version of the audit's design structure. General design claims require `Valid`
and positive marginal inclusion probabilities. No arbitrary unnormalized
weight array is treated as a sampling law.

`Bridge.toAudit` inserts exactly the two normalization proofs supplied by
`Valid`; `fromAudit` forgets only proof fields. `valid_fromAudit` takes the
existing structure's nonnegativity and total fields. The correspondences for
expectation, marginal and joint inclusion probabilities, totals, variances,
HT estimators, A, quadratic corrections and C2 are all `rfl`. The concrete
eight-unit laws and the general grouped/original phase data also agree by
`rfl`, as does the calibrated scalar bias function. `periodic_inclusions`
combines existing normalization, positivity and inclusion results.

The finite sample representation uses exactly the sampled subsets and weights
of the existing declarations. It allows duplicate atoms and zero weights.
The general almost-sure aggregation result is stated only on positive-weight
atoms for samplewise preservation, matching its probability-zero premise.
The stronger bias formulas separately use the exact common-indicator lift;
this limitation is explicit in T4.

The only additional proof steps are instantiation, conjunction/projection,
record adaptation, transport of the positive cluster witness's variance
along equal total functions and equal weights, and rational arithmetic on
exported numerical facts. The calibrated limit is composed with `m ↦ m+1`
so its displayed sizes are positive. The NB finite-moment integrability in
T12 uses the already exported coordinate-integral and series results; it
introduces no probability or analytic argument. Supporting declarations that
are not separate credited rows are named in the manifest for T6 and T12.

## Meaning and scope checks

Canonical claims govern the decisions. The review's aggregate coverage labels
were not treated as proofs of clauses absent from the selected statements.
No printed heuristic is replaced by an invented universal assertion. The
counterexample targets remain restricted counterexample statements, not
refutations of different positive assertions. T9 receives no theorem because
it has no credited rows, even though its subject overlaps T5 and T6.

The original population-size divisor is retained: 64 for the eight-unit mean
estimators, 14400 for the 120-unit witness, and `(m*q)^2` for general periodic
mean-scale quantities. The grouped estimator is never normalized by the
number of groups when a mean-scale comparison is stated. Pair sums remain
ordered and exclude the diagonal for A and its correction; the HT estimator
includes the diagonal where the joint probability is positive.

Positive sampling probabilities, positive population/sample parameters and
positive variance or model second moment guard the relevant divisions.
Explicit integrability guards are added to the restricted outcome-model and
systematic-indicator statements. T12 proves that its NB laws are probability
measures and that the first and centered second moments are integrable;
therefore its real-valued masses do not come from infinite measure values.
The fixed-fraction limit concerns the displayed scalar bias formula, with
all terms reindexed to positive sizes. No claim about unavailable code or
positive-probability Gaussian failures is inferred from deterministic facts.

## Revision 2: both round-one referee reports

I checked all 22 entries in [referee A's findings](referees/round1/a/findings.json)
and [referee B's findings](referees/round1/b/findings.json) against the theorem
types, shared definitions, and each target's canonical `statement` and
`definitions_needed` in [work.json](work.json), together with the standing
assumptions. Audit-history notes and suggested finite lemmas were not treated
as additional clauses or as permission to remove canonical clauses.

| Target | Referee A | Referee B | Check and action |
| --- | --- | --- | --- |
| P027-T1 | Correctly restricted | Correctly restricted | Retained both the eight-unit witness and alternating-family identities. The missing start-measure identification, numerical expansions and explicit nonvanishing assertions remain disclosed; no relabelling. See [Periodic8Witness and AlternatingFamily](SAP/P027a/Defs/Part4.lean). |
| P027-T2 | Correctly restricted | Correctly restricted | Checked the uniform-start law, negative-square criterion, bounds, model moment and calibrated limit blocks. The integrability guards, square-level calibration and omitted intermediate/calibration clauses remain disclosed. See [finite clauses](SAP/P027a/Defs/Part4.lean) and [model clauses](SAP/P027a/Defs/Part5.lean). |
| P027-T3 | Correctly restricted | Correctly restricted | Both witnesses and both bias increases are retained; samplewise enumerations and probability lists are absent and disclosed. See [T3Statement and ClusterBiasIncrease](SAP/P027a/Defs/Part5.lean). |
| P027-T4 | Correctly restricted | Correctly restricted | Checked the support-only preservation result separately from the exact common-indicator bias formulas; the missing squared-difference identity and four-unit reduction example remain disclosed. See [aggregation clauses](SAP/P027a/Defs/Part6.lean). |
| P027-T5 | Correctly restricted | Correctly restricted | Retained four rounded numerical violations and the exact 120-unit total/mean calculations. The universal finite-collection interpretation and implementation provenance remain excluded. See [table and witness clauses](SAP/P027a/Defs/Part6.lean). |
| P027-T6 | Correctly restricted | Correctly restricted | Retained the finite phase identities, original/grouped corrections, comparison and guarded outcome ratio; continuous-start and explicit mean-scale/provenance omissions remain disclosed. See [T6 clauses](SAP/P027a/Defs/Part7.lean). |
| P027-T9 | Omission justified | Omission justified | Confirmed that this target has no credited rows. The T5 numerical facts and T6 estimator formulas do not identify the reported table's implementation. Omission retained; no invented refutation of printed guidance. See [canonical T9](work.json) and the manifest. |
| P027-T10 | Minor missing disclosure | Correctly restricted | Accepted A's finding. Added the continuous uniform-start measure and its induced four-atom law to the docstring, manifest restriction and report. B's restricted classification is retained with this more complete disclosure. Details below. |
| P027-T11 | Correctly restricted | Correctly restricted | Checked that the inner variance is the conditional sampling variance and that the outer integral averages outcomes; integrability guards and the omitted realized-outcome comparison remain disclosed. See [OutcomeAverageConservativity](SAP/P027a/Defs/Part7.lean). |
| P027-T12 | Correctly whole | Correctly whole | Checked all four canonical clauses: printed probabilities and infeasibility; the normalized product law, finite moments and positive witness mass; and all six configurations. This proves the canonical counterexample rather than contradicting it, so whole remains correct. See [T12 clauses](SAP/P027a/Defs/Part8.lean). |
| P027-T13 | Correctly restricted | Correctly restricted | Checked necessity, cap existence, guarded systematic construction and the repaired finite law; cap-map properties, construction identifications and redraw/provenance clauses remain disclosed as omissions. See [T13 clauses](SAP/P027a/Defs/Part8.lean). |

**A's T10 finding is correct.** The canonical population/design explicitly
makes the sampling start uniform on `[0,8)`; this is part of its statement,
not an audit-history addition ([canonical T10](work.json)).
[Random8Witness](SAP/P027a/Defs/Part7.lean) gives a finite valid law and
pointwise selection equivalences on four intervals. It does not state a
normalized restricted-Lebesgue start measure or equality of the resulting
sampling law with that finite law. The existing restrictions on the size
generator and outcome event probabilities concern different randomness and
do not disclose this omission. The new sentence is:

> The continuous uniform-start measure on [0,8) and its induced four-atom sampling law are not identified explicitly.

That sentence is now in the [T10 docstring](SAP/P027a/Challenge/Part1.lean),
[manifest](SAP/P027a/manifest.json), and the T10 restriction above. No theorem
or shared definition changed. No extra mathematical argument was introduced.
The ten fully qualified theorem names, decision counts and proof statuses
are preserved. The Comparator configuration was regenerated for this same
complete theorem list and the same permitted dependencies and kernel commands.

The other 21 entries report no adverse finding. Their classifications remain
supported by the checks listed above; no adverse finding was rejected. The
refutation rule was checked against the canonical assertion itself: T1, T3,
T5, T10 and T12 assert their canonical counterexamples (or restricted parts),
while T5 concerns the after-totalling reading of the table. No packaged theorem
contradicts its own canonical assertion, and no printed guidance is declared
false. Positive sampling probabilities, nonempty sizes, positive variance or
model second moments, normalization and the explicit integrability guards
continue to prevent the relevant total-function conventions from supplying
spurious moments or ratios.

## Verification before the whole-statement switch

Revision 2 reran the full dependency-ordered compilation of all eight Defs
parts, the Defs root, Bridge, Challenge part and root, and Solution, followed
by `scratch/Axioms.lean`. Both commands returned exit code 0. The fresh
dependency output is in `scratch/axioms.log`; the compiled-file list, exit
codes and all ten dependency lists are in
[scratch/revision2-validation.json](scratch/revision2-validation.json).
The manifest and Comparator JSON parse, all restricted docstrings match their
manifest/report disclosures, all row entries are accounted for, and every
SAP source retains both required implicit-variable options and is at most
300 lines. Hash checks confirm that shared definitions and Solution proofs
are unchanged from before this revision.

Every Defs part and its root, Bridge, the Challenge part and its root, and
Solution compiled with `/home/ubuntu/sap/tools/sap-lean` in dependency order.
The expected Challenge placeholder warnings are confined to the stub module.
The resulting Solution passed a separate `#print axioms` run for all ten
listed theorems in `scratch/Axioms.lean`; the output is in `scratch/axioms.log`.
Each result uses exactly `propext`, `Classical.choice`, and `Quot.sound`.
The manifest's dependency lists were checked against this output.

Both JSON files parse. The target list, theorem list, row accounting, import
boundaries and the 300-line limit for every authored SAP file were checked.
No existing project or example source was edited, and no new mathematics was
proved. Revision 2 changes only the T10 disclosure and metadata/reporting. There are no open glue plans.

`comparator.json` supplies the requested modules, ten theorem names, empty
explicit definition list, permitted dependencies and external-kernel commands.
The external Comparator and three-kernel certification were not run: the
Comparator and the configured external-kernel executables were not available
on PATH. This report records successful Lean compilation and dependency
checks, and does not claim an external-kernel certificate.

## Whole versions (new proofs)

The seven targets below now use their proved whole statements. Each Challenge declaration retains its permitted placeholder proof; each Solution theorem uses the corresponding generated `_whole` theorem. The prior restriction text is retained below as a record of what this switch removes.


- **P027-T1**: `SAP.P027a.T1 : SAP.P027a.T1WholeStatement`, proved by `SAP.P027a.WH.W1.T1_whole`. Files: [SAP/P027a/Challenge/Part1.lean](SAP/P027a/Challenge/Part1.lean), [SAP/P027a/Solution.lean](SAP/P027a/Solution.lean), [SAP/P027a/manifest.json](SAP/P027a/manifest.json), [SAP/P027a/Defs/WholeW1.lean](SAP/P027a/Defs/WholeW1.lean), [SAP/P027a/WH/W1/Leaves.lean](SAP/P027a/WH/W1/Leaves.lean), [SAP/P027a/WH/W1/Helpers.lean](SAP/P027a/WH/W1/Helpers.lean), [SAP/P027a/WH/W1/Proofs/T1.lean](SAP/P027a/WH/W1/Proofs/T1.lean), [SAP/P027a/WH/W1/P/T1_L1.lean](SAP/P027a/WH/W1/P/T1_L1.lean). Removed restriction: the continuous uniform-start measure is not identified explicitly; the size sum and printed-PPS size formula, demeaning of x/4, the four group totals and A as their negative squared sum, total-scale numerical moments, relative bias -5/36, the comparison of the C2 expectation with the variance, and the samplewise identity z_k/p_k = estimated total are not separately stated. For the family, the alternative expression A = -N^2/q and the assertions that A and A/N^2 do not tend to zero are omitted.


- **P027-T2**: `SAP.P027a.T2 : SAP.P027a.T2WholeStatement`, proved by `SAP.P027a.WH.W1.T2_whole`. Files: [SAP/P027a/Challenge/Part1.lean](SAP/P027a/Challenge/Part1.lean), [SAP/P027a/Solution.lean](SAP/P027a/Solution.lean), [SAP/P027a/manifest.json](SAP/P027a/manifest.json), [SAP/P027a/Defs/WholeW1.lean](SAP/P027a/Defs/WholeW1.lean), [SAP/P027a/WH/W1/Leaves.lean](SAP/P027a/WH/W1/Leaves.lean), [SAP/P027a/WH/W1/Helpers.lean](SAP/P027a/WH/W1/Helpers.lean), [SAP/P027a/WH/W1/Proofs/T2.lean](SAP/P027a/WH/W1/Proofs/T2.lean), [SAP/P027a/WH/W1/P/T2_L1.lean](SAP/P027a/WH/W1/P/T2_L1.lean), [SAP/P027a/WH/W1/P/T2_L2.lean](SAP/P027a/WH/W1/P/T2_L2.lean). Removed restriction: adds integrability of the outcome-model variance, expected HT estimator and A, and integrability of the calibrated mean-scale A integrand. Calibration is imposed as the displayed equality for beta squared; the empirical size-variance calculation and its derivation from the supplement's beta formula are omitted. The intermediate off-diagonal and squared-total-sum rewritings of A, the explicit expected-estimator weighted-sum expansion, the explicit equality of the mean-scale design bias to A/N^2, the expectation of the difference inside the outcome integral, the finite uniform bound away from zero, and the numerical value at q=4, rho=0.99 are omitted. The scalar limit is reindexed to positive sample sizes.


- **P027-T3**: `SAP.P027a.T3 : SAP.P027a.T3WholeStatement`, proved by `SAP.P027a.WH.W1.T3_whole`. Files: [SAP/P027a/Challenge/Part1.lean](SAP/P027a/Challenge/Part1.lean), [SAP/P027a/Solution.lean](SAP/P027a/Solution.lean), [SAP/P027a/manifest.json](SAP/P027a/manifest.json), [SAP/P027a/Defs/WholeW1.lean](SAP/P027a/Defs/WholeW1.lean), [SAP/P027a/WH/W1/Leaves.lean](SAP/P027a/WH/W1/Leaves.lean), [SAP/P027a/WH/W1/Helpers.lean](SAP/P027a/WH/W1/Helpers.lean), [SAP/P027a/WH/W1/Proofs/T3.lean](SAP/P027a/WH/W1/Proofs/T3.lean). Removed restriction: omits the explicit marginal/joint probability and zero-pair lists and counts, the C1–C2 samplewise total and HT/C2 estimator and correction values, the original total expectation 3, the uncorrected-estimator expectations, and the positive witness's totalled A value. The finite sample laws, preservation of the positive witness's estimated total, both witnesses' variances, quadratic bounds and C2 expectations and biases are retained.


- **P027-T4**: `SAP.P027a.T4 : SAP.P027a.T4WholeStatement`, proved by `SAP.P027a.WH.W1.T4_whole`. Files: [SAP/P027a/Challenge/Part1.lean](SAP/P027a/Challenge/Part1.lean), [SAP/P027a/Solution.lean](SAP/P027a/Solution.lean), [SAP/P027a/manifest.json](SAP/P027a/manifest.json), [SAP/P027a/Defs/WholeW1.lean](SAP/P027a/Defs/WholeW1.lean), [SAP/P027a/WH/W1/Leaves.lean](SAP/P027a/WH/W1/Leaves.lean), [SAP/P027a/WH/W1/Helpers.lean](SAP/P027a/WH/W1/Helpers.lean), [SAP/P027a/WH/W1/Proofs/T4.lean](SAP/P027a/WH/W1/Proofs/T4.lean), [SAP/P027a/WH/W1/P/T4_L1.lean](SAP/P027a/WH/W1/P/T4_L1.lean), [SAP/P027a/WH/W1/P/T4_L2.lean](SAP/P027a/WH/W1/P/T4_L2.lean). Removed restriction: the bias-change conclusions use an exactly common-indicator fiber representation; the general probability-zero-disagreement input is used only for preservation on positive-weight atoms, variance and A. The within-group pairwise squared-difference identity and the explicit four-unit example reducing bias from 20 to zero are omitted. The comparison with the separately packaged three-unit witness is not restated.


- **P027-T10**: `SAP.P027a.T10 : SAP.P027a.T10WholeStatement`, proved by `SAP.P027a.WH.W1.T10_whole`. Files: [SAP/P027a/Challenge/Part1.lean](SAP/P027a/Challenge/Part1.lean), [SAP/P027a/Solution.lean](SAP/P027a/Solution.lean), [SAP/P027a/manifest.json](SAP/P027a/manifest.json), [SAP/P027a/Defs/WholeW1.lean](SAP/P027a/Defs/WholeW1.lean), [SAP/P027a/WH/W1/Leaves.lean](SAP/P027a/WH/W1/Leaves.lean), [SAP/P027a/WH/W1/Helpers.lean](SAP/P027a/WH/W1/Helpers.lean), [SAP/P027a/WH/W1/Proofs/T10.lean](SAP/P027a/WH/W1/Proofs/T10.lean), [SAP/P027a/WH/W1/P/T10_L1.lean](SAP/P027a/WH/W1/P/T10_L1.lean). Removed restriction: the continuous uniform-start measure on [0,8) and its induced four-atom sampling law are not identified explicitly. Omits the connection to the normalized random-size generator and any Gaussian event-probability assertion, the explicit joint probabilities and zero-pair count, the size-vector feasibility inequality and residual representation, and the explicit C2-versus-variance inequality. Retains the finite design, intervalwise systematic selection, printed first-order probabilities, samplewise HT values, total/mean moments, C2 expectation and the open-box bound.


- **P027-T11**: `SAP.P027a.T11 : SAP.P027a.T11WholeStatement`, proved by `SAP.P027a.WH.W2.T11_whole`. Files: [SAP/P027a/Challenge/Part1.lean](SAP/P027a/Challenge/Part1.lean), [SAP/P027a/Solution.lean](SAP/P027a/Solution.lean), [SAP/P027a/manifest.json](SAP/P027a/manifest.json), [SAP/P027a/Defs/WholeW2.lean](SAP/P027a/Defs/WholeW2.lean), [SAP/P027a/WH/W2/Leaves.lean](SAP/P027a/WH/W2/Leaves.lean), [SAP/P027a/WH/W2/Proofs/T11.lean](SAP/P027a/WH/W2/Proofs/T11.lean). Removed restriction: adds integrability of A and the mean-scale design-bias integrand. Omits the realized-outcome assertion A(y0)=-16 and the resulting explicit average-versus-realization comparison and populationwise-guarantee discussion.


- **P027-T13**: `SAP.P027a.T13 : SAP.P027a.T13WholeStatement`, proved by `SAP.P027a.WH.W2.T13_whole`. Files: [SAP/P027a/Challenge/Part1.lean](SAP/P027a/Challenge/Part1.lean), [SAP/P027a/Solution.lean](SAP/P027a/Solution.lean), [SAP/P027a/manifest.json](SAP/P027a/manifest.json), [SAP/P027a/Defs/WholeW2.lean](SAP/P027a/Defs/WholeW2.lean), [SAP/P027a/WH/W2/Leaves.lean](SAP/P027a/WH/W2/Leaves.lean), [SAP/P027a/WH/W2/Proofs/T13.lean](SAP/P027a/WH/W2/Proofs/T13.lean), [SAP/P027a/WH/W2/P/T13_L1.lean](SAP/P027a/WH/W2/P/T13_L1.lean), [SAP/P027a/WH/W2/P/T13_L2.lean](SAP/P027a/WH/W2/P/T13_L2.lean). Removed restriction: adds integrability of every systematic inclusion indicator on [0,1). Omits the scalar cap-map continuity, monotonicity and saturation facts, the explicit specialization of the general construction to the feasible printed formula, and identification of the explicit certainty-unit sample law with the continuous systematic construction. The explicit repaired finite law, its joint probabilities and the naive-capping sum are retained. The conditional redraw law and the provenance of the simulation code are not asserted.


Other Solution proof repairs: none required. The unchanged T5, T6 and T12 proofs do not reference a switched theorem; their statements, proofs, docstrings and manifest entries remain unchanged.

Verification: `python3 /home/ubuntu/sap/tools/rebuild_sap.py . P027a` completed from scratch with exit code 0: rebuilt 33 modules of SAP/P027a; token scan clean. The [rebuild log](scratch/p027a-whole-rebuild.log) records the result. [P027aWholeAxioms.lean](scratch/P027aWholeAxioms.lean) imports only `SAP.P027a.Solution` and runs `#print axioms` for all seven switched theorems; its [audit log](scratch/p027a-whole-axioms.log) lists only `propext`, `Classical.choice` and `Quot.sound` for each. Both that audit and the [new manifest declaration checks](scratch/P027aWholeRows.lean) compiled with exit code 0 using `sap-lean`. Source hashes and target-level comparisons confirm the edit scope and preservation of all other targets. Challenge imports and the Solution import graph satisfy the required boundaries. All Lean compilation ran serially; no `lake` command was used. The per-target results are in [switched.json](switched.json).

## Declaration review round 1

**Finding: SAP.P027a.T10 — not_faithful/minor, docstring scope omission.**
I accept the [T10 entry in the review findings](fw/round1/T10/r4g2/findings.json)
and its explanation in the [review report](fw/round1/T10/r4g2/REPORT.md).
The canonical statement's final paragraph identifies the inference at issue:
positive sizes and the noisy additive outcome model do not guarantee a
nonnegative variance-estimator bias for every generated population
([P027-T10 in work.json](work.json)). The explicit outcomes alternate in
sign, so they do not contradict the literal assertion about outcomes
proportional to the positive size vector.

Both the [Challenge docstring](SAP/P027a/Challenge/Part1.lean) and the
[T10WholeStatement docstring](SAP/P027a/Defs/WholeW1.lean) now say:

> This witness refutes the inference from x_k >= 1 and the noisy model y_k = beta*x_k + epsilon_k to conservativity for every realized finite population. It does not refute the literal assertion for outcomes proportional to the positive size vector.

The manifest records this scope in T10's `refutation_scope`. Its `whole`
decision remains correct: its mathematical statement establishes the
canonical counterexample and does not contradict that canonical assertion.
No additional Gaussian event probability is inferred from the canonical
note. The other declarations mentioned in this findings file (T6, T11, T12
and T13) have no open finding, and their decisions are retained. No finding
was rejected.

**Packaging and shared-definition stability.** Three inherited files exceeded
the brief's 300-line limit. They were split only between complete top-level
declarations, preserving their original namespace, declaration bodies and
proofs. The original module paths continue to import the moved parts:

- `Defs/WholeW1.lean` imports [Defs/WholeW1/Part1.lean](SAP/P027a/Defs/WholeW1/Part1.lean).
- `WH/W1/Helpers.lean` imports [WH/W1/Helpers/Part1.lean](SAP/P027a/WH/W1/Helpers/Part1.lean).
- `WH/W2/P/T13_L2.lean` imports [WH/W2/P/T13_L2Support.lean](SAP/P027a/WH/W2/P/T13_L2Support.lean).

These are file-layout changes, not new proofs or changes to shared
mathematical definitions. All theorem names and types are retained. Every
SAP source has both implicit-variable options. The Comparator configuration
was regenerated for the same ten theorem names, shared-definition route,
permitted dependencies and kernel commands; it still parses. The manifest's
mathematical decisions and proof statuses are retained, and its formatting
also respects the file limit. The report's opening counts now reflect the
whole-statement switch recorded above; earlier restricted-stage material is
marked as historical.

**Fresh verification.** All 36 SAP modules were recompiled serially in
dependency order with `sap-lean`; every module returned exit code 0. The
fresh `#print axioms` audit of all ten public theorems uses exactly
`propext`, `Classical.choice`, and `Quot.sound`, matching the manifest.
Results are in [scratch/fw1-validation.json](scratch/fw1-validation.json)
and [scratch/axioms.log](scratch/axioms.log).

The initial compiled snapshot was stale: its Solution still contained older
restricted theorem types, although the pre-edit sources and manifest already
contained the whole versions. It was therefore not used to attribute changes
to this revision. The full rebuild refreshed those artifacts. Reassembling
the split source sections and removing only the requested docstring addition
reproduced the exact SHA-256 of every pre-edit Lean source; all other source
files are byte-identical. Two fresh compiled declaration snapshots also
agree. No shared mathematical definition or proof source was changed.
JSON parsing, statement-name equality, both implicit-variable options, import
boundaries, token restrictions and the 300-line file limit were checked again.
The existing accepted [Comparator result](SAP/P027a/verification/comparator-result.json)
is historical evidence for its recorded snapshot; no new external-kernel
certification is claimed for this documentation/layout revision.
