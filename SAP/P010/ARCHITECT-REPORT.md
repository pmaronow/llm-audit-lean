19 whole, 0 restricted, 4 refuted, 0 omitted; 23 proved, 0 open glue tasks.

All 23 theorem names remain `SAP.P010.T1` through `SAP.P010.T23`. The four
remaining refutation labels are T1, T3, T5, and T13. Their docstrings begin
“The printed claim is false:” and state explicit counterexample facts. These
results refute printed assertions; they are no longer labelled `whole`.

The whole targets are T2, T4, T6–T12, T14–T23. There are no restricted or
omitted targets or open glue tasks. Project sources and
all comparator module and theorem names remain unchanged.

T21 and T23 prove the printed corollaries' nonimplications. They do not refute
those corollaries, so their restored complete statements are labelled whole.
T11 is also whole: it establishes the canonical counterexample to an explicit
formal reading of the weighting guidance, as explained in declaration review
round 2 below.
T7 and T9 likewise establish their canonical counterexamples and are whole
after round 4. The existing whole versions of T12 and T17 described below
were already present when round 4 began and are preserved without changes.

## Referee findings and dispositions

Every entry in both `findings.json` files was checked against `work.json` and
the definitions and project declarations. In the table, CW denotes
`correct_whole`, CR denotes `correct_restricted`, and NF denotes `not_faithful`.
The refutation relabellings implement the revised taxonomy without disagreeing
with the referees' mathematical assessments of those counterexamples.

| Target | A | B | Disposition |
| --- | --- | --- | --- |
| T1 | CW | CW | Counterexample preserved; relabelled refuted. |
| T2 | CW | CW | Complete empirical computation preserved; whole. |
| T3 | CW | CW | Both counterexamples and their shared observables preserved; refuted. |
| T4 | CW | CW | Validity, sharpness, attainment, zero trimming and both integral forms preserved; whole. |
| T5 | CW | CW | Finite sharp extrema and compatible tail witnesses preserved; refuted. |
| T6 | CW | CW | Bounds, sharp extrema, finite nonattainment and unboundedness equivalence preserved; whole. |
| T7 | CW | CW | All canonical four-state counterexample clauses preserved; whole after declaration review round 4. |
| T8 | CW | CW | All arm-by-arm identities preserved; whole. |
| T9 | CW | CW | Both canonical simulation designs, observable distributions and separated widths preserved; whole after declaration review round 4. |
| T10 | CW | CW | Observable-law invariance and all simulation components preserved; whole. |
| T11 | CW | CW | Attained logistic fit and incorrect transport distribution preserved; whole after declaration review round 2. |
| T12 | CR | CR | Historical finite-normalizer restriction superseded by the existing whole proof described below. |
| T13 | CW | CW | Negative printed upper bound and positive corrected bound preserved; refuted. |
| T14 | CW | CW | Maximization, attaining coupling, monotonicity and corrected bound preserved; whole. |
| T15 | NF | CW | Accepted A: moved the tail-mean identity inside the finite-branch guard. |
| T16 | CW | CW | Entire bounded witness calculation preserved; whole. |
| T17 | CW | CW | Round 3 restriction superseded by the existing whole proof, which imposes the observed passing requirement without a potential-passing premise. |
| T18 | CW | CW | Selected contrast identity preserved; whole. |
| T19 | CW | CW | Both component mean identities and their contrast preserved; whole. |
| T20 | CW | CW | Check/assignment independence preserved; whole. |
| T21 | NF | NF | Accepted both: supplied positive conditioning masses and all three integrability certificates; whole. |
| T22 | CW | CW | Conditional covariate balance preserved; whole. |
| T23 | NF | NF | Accepted both: supplied positive conditioning masses and all three covariate-restricted integrability certificates; whole. |

**A/T15.** The previous unguarded upper-tail equality included zero-mass tail
means when the trimming ratio exceeded one. The stated bounded-passer example
has ratio two; its quantile at two is infinite, so its upper-tail event is empty.
I agree with A's domain finding, although B did not flag it. The distribution,
passing-rate and trimming-share identities remain unconditional. The tail-mean
identity now joins the finite-branch target identity and inequality under
`trimmingRatio μ a < 1`. The proof only rearranges components of the existing
`observable_upper_bound_corrected_proof` declaration.

This retains the whole meaningful claim: the canonical text introduces the
corrected display for `r₁ < 1`, and its standing assumptions presuppose that the
conditional means exist. It does not require an equality between zero-event
mean conventions outside that domain. Sources: [canonical claims](work.json),
P010-T15 and `standing_assumptions`; [A's finding](referees/a/REPORT.md);
[quantile and tail definitions](SAP/P010/Defs/Part5.lean).

**A/T21 and B/T21.** Both are right: the previous disclosure of totalization
changed the meaning of conditional expectation rather than giving a faithful
restriction. The statement now requires integrability on both selected-arm
events and on the always-passer event, and explicitly positive mass for all
three conditioning events. The existing `selectionPopulation (1/2)` is the
witness. Its contrast remains one half and its always-passer effect remains
zero. The Cauchy/shift example cannot satisfy the new integrability conditions.
The theorem now establishes the entire canonical existence claim and is whole.

**A/T23 and B/T23.** Both are right for the same reason, now on the two
selected-arm events intersected with zero covariates and on the always-passer
event at zero covariates. The statement requires all three integrability
certificates and positive conditioning masses. The same existing finite
witness has constant zero covariates. Almost-everywhere event equality transports
its previously proved means to these events. The full ordinary-mean existence
claim is restored, so the former restriction is removed and the label is whole.

There is one numerical disagreement with an ancillary statement in
[A's T23 nonvacuity explanation](referees/a/findings.json): the two selected-arm
and zero-covariate events each have mass **1/3**, not 1/6. Each consists of two
atoms of mass 1/6. The always-passer event also has mass 1/3. This follows from
[the six displayed atoms](/home/ubuntu/sap/wt/ARCH-P010/AronowAudit/P010/P010_Population.lean:1104)
and [their weights](/home/ubuntu/sap/wt/ARCH-P010/AronowAudit/P010/P010_Population.lean:1113),
and is certified by `Bridge.selection_selected_mass` and the zero-covariate
event correspondence. B makes no contrary numerical claim. This correction
does not affect either referee's substantive integrability finding.

**T12 (historical restriction).** Both referees accepted the then-existing restriction. Bayes'
identities, reciprocal transport, its exact normalizer and scale cancellation,
and the entire positive finite-normalizer printed-odds formula and equality
characterization remain. The only omitted canonical clause is the final
assertion that infinite squared-density-ratio mass gives infinite printed
weighted mass and prevents normalization to a probability distribution.
The canonical finite-normalizer premise is already present in `work.json`;
no extra integrability premise is imposed on reciprocal transport.

## Definitions and bridges

All mathematical definitions remain under `SAP.P010` in the six numbered Defs
parts and the existing `Defs/WholeW1.lean`, importing only Mathlib and preceding
Defs modules. There are 113 shared definitions: the original 84 notions and
23 statement definitions, plus four notions and two whole statements in WholeW1.
No copied project-name module remains, including
compiled products. Every SAP Lean file now starts, after imports, with both
`set_option autoImplicit false` and `set_option relaxedAutoImplicit false`.
Previously inferred natural-number and universe binders are explicitly typed.

`Bridge/Part1.lean` retains 84 function correspondences proved by `rfl`.
`Bridge/Part2.lean` retains 23 statement correspondences proved by `Iff.rfl`;
T15's project-side proposition now has the same guard, and T21/T23's project-side
propositions include their finite-mean and positive-mass certificates. T17's
proposition now requires positive potential passing and concludes the corrected
all-arm observed-passing condition; its Solution applies the existing equivalence
in the sufficient direction. The name
mapping is in `scratch/P010BridgeMap.json`.

`Bridge/Part3.lean` adds only structural and arithmetic glue for the existing
witness. Its integrability adapter composes Mathlib's `integrable_dirac`,
`Integrable.smul_measure`, `integrable_finsetSum_measure`, and
`Integrable.restrict`. Its mass computation uses the existing
`finiteLaw_apply_real` certificate followed by exact finite arithmetic. The
remaining two helpers check the atoms' zero covariate and the resulting
almost-everywhere event identity. No distribution, moment calculation, or
statistical argument was newly proved.

T21 and T23 use the existing `selection_counterexample_corrected` certificate
for their witness's assumptions and contrasts. The narrower existential exports
`corollary_three` and `corollary_five` remain unused: their missing certificates
have not been silently attributed to those rows. The manifest records the
concrete witness and standard Mathlib supporting declarations instead. All
other row accounting is preserved. The 21 original Solution exports other than
T12 and T17 use their named Bridges. T12 and T17 use the existing WholeW1
assemblies over the same SAP definitions and project facts.

## Declaration review round 1

**SAP.P010.T10 — not_faithful/minor, accepted.** The reviewer correctly
identified an omitted qualification in the docstring. The canonical T10(ii)
and [T10Statement](SAP/P010/Defs/Part6.lean:154) require `lam ≠ 0` for mean
sensitivity. At zero lambda, the potential response in
[simulationSubject](SAP/P010/Defs/Part5.lean:142) is just the independent
noise, both passer mixtures reduce to the same Gaussian law, and both mean
formulas are zero regardless of feasible correlation. The revised docstring
explicitly requires `λ ≠ 0` and feasible correlations, and mentions the two
specified designs' unequal widths. Sources: [review finding](fw/round1/T10/r1g2/findings.json),
[canonical T10](work.json), and the definitions cited above.

This is a prose-only correction. T10 retains its full statement, proof,
theorem name, `whole` decision, and row accounting. At that round, every shared
definition and every Bridge and Solution source was byte-for-byte unchanged, as checked
against `scratch/P010DeclarationRound1Baseline.json`. The other entries in
the same findings file concern T6–T9, all marked faithful with no open items;
they require no changes. The manifest records the resolved T10 finding, and
the comparator configuration retains the required module and theorem names.

The full package was recompiled in dependency order, all target and Bridge
axioms checks were rerun, and the exact shared-declaration comparison and JSON
validation were repeated for this round.

## Declaration review round 2

**SAP.P010.T11 — label_wrong/minor, accepted (both issues).** The reviewer
correctly distinguishes the printed report of the procedure and its purpose
from the exact-distribution-matching assertion introduced separately as a
formal reading. The canonical target includes the complete counterexample to
that reading: the attained unique interior logistic fit, positive cells and
overlap, printed weights and masses, weighted share `27/28` rather than `1/4`,
and exact recovery by reciprocal odds. These are already all stated in
[T11Statement](SAP/P010/Defs/Part4.lean:64) and supplied by
[the existing counterexample](AronowAudit/P010/P010_Transport.lean:46) and
[logistic certificate](AronowAudit/P010/P010_Transport.lean:91).

T11 is relabelled from `refuted` to `whole`, and its docstring now names the
exact-distribution-matching reading and replication-membership coding. The
former opening, “The printed claim is false:”, overstated the result because
the counterexample does not contradict the factual report that the procedure
was used. Sources: [canonical T11, statement and definitions_needed](work.json)
and [the two reviewer issues](fw/round2/T11/r3g2/findings.json), T11 entry.

At that round, no clause, hypothesis, theorem name, proof, or row credit changed.
Both credited rows have final status `ok`. Every shared definition and every Bridge and
Solution source was byte-for-byte unchanged, checked against
`scratch/P010DeclarationRound2Baseline.json`. The same findings file marks
T6–T9 faithful without open items; those declarations require no changes.
The manifest records the corrected label and resolved issues; the comparator
retains the required module names, theorem names and kernel configuration.

For this round, the full package was recompiled in dependency order, all 23
target and 111 Bridge dependency checks were rerun, and exact shared-declaration
comparison and JSON validation were repeated. No shared definition changed in round 2.

## Declaration review round 3

**SAP.P010.T17 — not_faithful/major, accepted (both issues).** The canonical
target is the corrected Assumption 3: positive observed passing probability in
every arm. The former theorem equated observed and potential passing rates
and their positivity predicates, but neither required either predicate to hold.
For example, constant-false potential checks make every passing event empty
while allowing a probability population with independent, positive-probability
assignment. Both sides of the equivalence are then false. Thus the theorem was
true but the `whole` coverage claim was incorrect. Sources: [canonical T17,
statement](work.json), [review issues](fw/round3/T17/r4g4/findings.json), and
[passing predicates](SAP/P010/Defs/Part3.lean:35).

The revised T17 explicitly concludes, for every arm, that the probability of
observed passing conditional on that assignment is positive. It adds the
hypothesis that potential passing has positive probability in every arm,
retaining a probability law, per-arm ignorability and positive assignment
masses. T17 is now `restricted`: this verifies the requirement under the
stated sufficient condition rather than imposing it on unrestricted populations.
The docstring and manifest disclose the added condition. The former rate
identities and equivalence are removed from the Challenge because they were
not clauses of this canonical assumption. No separate characterization target
is added; [the brief](brief.md) permits only the recorded targets.
The unchanged `positivePassRates` definition remains the representation of the
corrected assumption; the new conclusion writes its probability formula explicitly.

The proof is glue alone: it applies the existing equivalence's right-to-left
direction in [nonzero_passing_corrected](AronowAudit/P010/P010_Population.lean:453).
The credited row remains usable with final status `ok`; no row credits change.
The probability and positive assignment hypotheses make the explicitly stated
conditional probabilities ordinary finite ratios with nonzero denominators.
No positivity is claimed from consistency and ignorability alone.

The only changed shared definition is `SAP.P010.T17Statement`, used by Challenge
declaration `SAP.P010.T17`; that declaration requires renewed review. The 84
underlying notions and all other statement definitions are unchanged. Its
Bridge is still `Iff.rfl`, now to the corresponding restricted project-side
proposition. Source and declaration snapshots are in
`scratch/P010DeclarationRound3Baseline.json`; the fresh exact-expression
comparison checks the unchanged declarations as well as the revised pair.
The same findings file marks T16 and T18–T20 faithful without open items, so
they require no changes.

The full package was recompiled in dependency order, all 23 target and 111
Bridge dependency checks were rerun, and exact Challenge/Solution comparison
and JSON validation were repeated. All 23 theorem names remain proved, with
no open glue tasks; comparator module names and configuration are preserved.

## Declaration review round 4

**SAP.P010.T7 — label_wrong/minor, accepted.** The canonical target itself
specifies the four-state counterexample, including clauses (a)–(f).
[T7Statement](SAP/P010/Defs/Part6.lean:92) establishes those clauses: the
population assumptions, common and always-passing events, failed joint-vector
independence, the `1/4` versus `1/8` factorization, both selected means `1/2`,
and the zero always-passer effect. It establishes the canonical counterexample
while refuting the specifically quoted printed proof step. T7 is relabelled
`whole`, and its docstring states this distinction and the corollary's valid
mean identity. Sources: [canonical T7](work.json) and
[T7 review finding](fw/round4/T7/r6g2/findings.json), T7 entry.

**SAP.P010.T9 — label_wrong/minor, accepted.** The canonical target specifies
the two simulation designs and their population comparison.
[T9Statement](SAP/P010/Defs/Part6.lean:104) includes both designs' assumptions,
passing rates, correlations, mixture laws, moments, width formulas, exact
rational enclosures and strict separation. The theorem establishes that
counterexample and does not contradict the canonical assertion. T9 is
relabelled `whole`; its docstring identifies the changed observable passer
laws and separated population widths as the counterexample to the printed
row comparison. Sources: [canonical T9](work.json) and
[T9 review finding](fw/round4/T9/r6g2/findings.json), T9 entry. These are
population widths, and the result does not contradict invariance at a fixed
observable law.

The reports for the two paths contain the same findings and blind reading.
Their T6, T8 and T10 entries are faithful without open items. Only T7/T9 labels,
docstrings and review metadata change in this round. All 113 shared definition
sources, all theorem headers, every Bridge, WholeW1 proof and Solution source
are unchanged against `scratch/P010DeclarationRound4Baseline.json`. No shared
definition changes, so these corrections do not trigger review of additional
declarations. The previously completed T12 and T17 whole versions are retained;
the current counts include those versions rather than their historical restrictions.

All 21 current SAP modules were rebuilt in dependency order, and all target,
Bridge and WholeW1 dependency checks and the exact shared-declaration comparison
were rerun. Manifest and comparator JSON validation passed; their module and
theorem names are unchanged. No new proof was written in this round.

## Verification

All six numbered Defs parts and their root, WholeW1 definitions and proofs,
all three Bridge parts and their root, Challenge and its root, and Solution
compile with `sap-lean` in dependency order,
with at most two Lean processes. The order is in `scratch/P010BuildOrder.json`.
All package source and configuration files remain below 300 lines.

`#print axioms` was rerun for all 23 Solution theorems, all 111 Bridge theorems,
and all seven existing WholeW1 proof and assembly theorems.
Only `propext`, `Classical.choice`, and `Quot.sound` occur.
`scratch/P010Axioms.log` records the output; the manifest records each target's
actual dependencies.

The isolated Challenge/Solution comparison checks exact serialized universe
parameters, theorem types, and the types and bodies of all 113 shared definitions.
It performs no normalization or proof-reference erasure. Its results are in
`scratch/P010Identity.json` and `scratch/P010Validation.json`.

Both JSON configuration files parse. The theorem names, module names, permitted
axioms, empty definition-name list, and requested external-kernel commands are
preserved. The existing [Palomar result](SAP/P010/verification/comparator-result.json)
records acceptance of all 23 theorems by all three kernels for the pre-round-4
snapshot, including the WholeW1 versions. That historical artifact is preserved.
Round 4 repeats compilation, dependency and exact-expression checks; it does
not claim a fresh three-kernel run for the changed docstrings and manifest.

The empirical counts remain supplied inputs, and T1/T2 concern unweighted
estimated bound intervals. T17's current whole statement imposes the corrected
observed passing condition without an extra potential-passing premise.
No target is asymptotic.

## Existing whole versions (present before round 4)

**SAP.P010.T12 (P010-T12) — whole, proved.**

Files: `SAP/P010/Challenge/Part1.lean`,
`SAP/P010/Solution.lean`, `SAP/P010/Defs/WholeW1.lean`,
`SAP/P010/WH/W1/Leaves.lean`,
`SAP/P010/WH/W1/P/T12_L1.lean`,
`SAP/P010/WH/W1/P/T12_L2.lean`,
`SAP/P010/WH/W1/Proofs/T12.lean`, and
`SAP/P010/manifest.json`. The export now states `SAP.P010.T12WholeStatement`
and uses `SAP.P010.WH.W1.T12_whole`.

Old restriction now removed:

> The canonical claim already requires a finite normalizer in clause (iii). Retain Bayes identities, reciprocal transport and scale cancellation, and the positive finite-normalizer printed-odds formula and characterization; drop only the final assertion that an infinite squared-density-ratio mass gives infinite printed weighted mass and cannot be normalized to a probability distribution.

The whole proof includes infinite printed weighted mass and the impossibility
of normalization by any finite nonnegative scalar.

**SAP.P010.T17 (P010-T17) — whole, proved.**

Files: `SAP/P010/Challenge/Part1.lean`,
`SAP/P010/Solution.lean`, `SAP/P010/Defs/WholeW1.lean`,
`SAP/P010/WH/W1/Leaves.lean`,
`SAP/P010/WH/W1/P/T17_L1.lean`,
`SAP/P010/WH/W1/Proofs/T17.lean`, and
`SAP/P010/manifest.json`. The export now states `SAP.P010.T17WholeStatement`
and uses `SAP.P010.WH.W1.T17_whole`.

Old restriction now removed:

> Verifies corrected Assumption 3 only for a probability law with per-arm ignorability, positive assignment masses, and the added hypothesis that potential passing has positive probability in every arm. The conclusion explicitly asserts positive observed passing probability in every arm; it does not impose the requirement on populations lacking the added hypothesis. The former characterization identities and equivalence were not canonical clauses and have been removed.

The whole proof imposes the observed passing requirement through the population
assumptions and proves that it is determined by the observed joint law, without
an additional potential-passing premise.

Validation: `python3 /home/ubuntu/sap/tools/rebuild_sap.py . P010` rebuilt all
21 modules from scratch with a clean token scan. The scratch file
`scratch/P010WholeAxioms.lean` imports `SAP.P010.Solution` and runs
`#print axioms` on both switched exports;
`scratch/P010WholeAxioms.log` records only `propext`, `Classical.choice`, and
`Quot.sound` for each. Compilation used one Lean process at a time.
