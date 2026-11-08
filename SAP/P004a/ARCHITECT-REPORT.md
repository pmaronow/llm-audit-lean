P004a covers exactly P004-T1 through P004-T15. Current decisions: 12 whole,
3 restricted, 0 refuted, 0 omitted. All 15 theorems have solution proofs;
there are no open glue tasks. The other work units are outside this package.

The strict certification reported a statement mismatch at T8. The cause was an inferred
universe-parameter name: the root-level Challenge inferred `u_1`, while the namespace and
section-variable context in Solution inferred `u_2`. Both statements were polymorphic,
but their exported constant expressions contained different level-parameter names.
scratch/t8-elaboration-contexts.log reproduces both contexts and shows the raw expressions.
The complete type audit also found the same latent issue at T15: inferred parameters
`u_1,u_2` in Challenge and `u_2,u_3` in Solution. It is repaired at the same time.

The repair explicitly uses `T8WholeStatement.{u}` in Challenge and Solution and propagates
the same level through `WH.W2.T8_whole.{u}` to the existing polymorphic `T8_assembly.{u}`.
T15 likewise uses `T15WholeStatement.{u,v}` and its existing assembly at `u,v`.
No proposition body, hypothesis, conclusion, target decision or restriction changed.
There is no weakening and no new mathematical proof. The only Lean edits are in
Challenge/Part1.lean, Solution.lean, WH/W2/Proofs/T8.lean, and WH/W1/Proofs/T15.lean. All shared definitions,
the mathematical assembly proof, and the proved leaves are unchanged.

The manifest records T8's and T15's explicit universe parameters. The Comparator configuration is
refreshed with the same 15 theorem names, no separately listed definitions, the same
three permitted dependencies, and the same con-ron and nanoda commands.

The 12 whole entries are T1, T2, T3, T4, T5, T8, T9, T10, T11, T13, T14 and T15.
The existing whole-proof library supplies T1, T3, T4, T5 and T15 from WH/W1, and T8,
T9 and T14 from WH/W2. Their Solution proofs continue to reuse those proved assemblies.
This certification repair adds no statistical or analytic arguments to that library.

- **P004-T6 — restricted.** Retain the actual integral union identity, marginal means, node effects, node-average area effect, range bounds, equal-mass mean formula, and positive-scale comparison and exact p-value invariance. Omit the two negative assertions in (b): an unweighted sum outside the bin-effect range, and non-identifiability from bin AMEs when node masses differ. Do not assert the application numbers, reported Monte Carlo p-value or substantive beneficial-effects conclusion.

- **P004-T7 — restricted.** Retain the full finite twenty-node adjusted-order reversal and spatial, homophily, nondegeneracy, cutoff-kernel and exact linearized-variance guards for the repeated-star witness. Replace the exact limiting coverage equality by an eventual upper bound with the same explicit value, strictly below 19/20, counting only realizations with positive treatment and control counts, positive adjustment trace and positive trace-square parameter. Omit the separate W1 spectral eigenvalue/trace/diagonal certificates, W2 block moments, W3 raw-variance, trace, variance-ratio and degrees-of-freedom limits, and the fitted-estimator Gaussian law. The guarded upper bound is not a conditional-on-validity coverage probability.

- **P004-T12 — restricted.** Retain the specific eight-node sharp-null Witness A and its exact positive-probability draw array, printed proportion, absolute exceedance count and corrected p-value, and Witness B with its exact rejection sum greater than 1/20. Omit the separate universal negative-observation rule, the signed-statistic size s/2 and decimal size approximations, and all of the seventeen-node, P=10000 Witness C and its exact lower bound. Witness B uses the permitted nonnegative statistic absolute HT; no failure for every finite P or for all sufficiently large P on one fixed design is asserted.

The definitions follow the shared Mathlib-only route. Challenge imports Defs and the
two WholeW definition modules; Solution imports those same compiled definitions through
its existing proof modules. Challenge has no project imports, and Solution has no direct
or transitive Challenge imports. No declaration is copied under a project-qualified name.

Bridge.toPopulation and fromPopulation preserve node sets, the measure, potential outcomes,
distance bands and nonempty-node certificates. Their inverse identities are reflexivity.
toSequence applies the adapter at every sample size. The circle-average, region, separation,
regularity, spatial-condition and point-effect correspondences use reflexivity or
propositional reflexivity. All fixed witness-population correspondences are reflexivity.
Finite scalar and table notions have matching bodies; the solution transports along them.
No bridge change was needed for the universe repair.

Positive spatial mass, finite mass and integrability guards remain in the average statements.
The finite inverse-information formulas require a positive sample size and invertibility.
The T8 interval probabilities count only nonempty-arm assignments; the Student comparison
uses positive degrees of freedom and quantile levels strictly between one half and one.
All guards and the full Student comparison remain intact. The T7 restricted event counts
only realizations with positive arm counts, adjustment trace and trace-square parameter.

Previous universe-repair validation completed on 2026-11-04, certificate stamp `20261104T190138Z`.
All 61 modules compiled with sap-lean in dependency order, followed by the changed wrappers
and both roots. A second fresh rebuild from the frozen snapshot also compiled all 61.
Existing proof leaves emit linter warnings; there are no compilation errors.

The Lean-derived types of all 15 Challenge/Solution theorems agree up to irrelevant bound
instance identifiers, including identical named universe parameters at T8 and T15.
scratch/certification-type-comparison.json records this check. scratch/Axioms.lean ran
the dependency command for every theorem; all 15 use exactly propext, Classical.choice and
Quot.sound, as recorded in the manifest. Both configuration JSON files parse and contain
exactly the unit's 15 targets and 15 corresponding proved theorems.

Strict certification passed the frozen-snapshot rebuild, complete manifest checks,
Lean-derived import-closure checks and theorem/definition comparison. All three kernels
accepted: con-ron with --verified and --jobs=2, nanoda, and Lean's default kernel. The
Comparator reported its final acceptance marker. The complete result and kernel log are
in SAP/P004a/verification/comparator-result.json and SAP/P004a/verification/comparator.log.

The runner's default certificate and git-worktree locations are read-only in this sandbox.
scratch/run_strict_certification.py uses the prescribed runner with three storage-only
substitutions: /tmp artifact storage, a fresh local shared clone of the same recorded base
HEAD, and deletion of that temporary checkout on completion. Snapshot hashing, fresh
compilation, target completeness, import closures, exports, comparison, all kernel commands
and all required acceptance markers are unchanged; control mode was not used. The original
runner hash and the exact three substitutions are recorded in
scratch/certification-runner-storage.json. No Lake command ran in this worktree.

At that certification, source hashes matched its snapshot. Comparison with the reported
failed snapshot confirmed only the four universe-annotation modules and the two JSON files changed;
all shared definitions and mathematical proof bodies are unchanged.

The supplied whole-proof library contains 17 pre-existing modules above the original
300-line cap; they are listed in scratch/certification-existing-size-exceptions.json.
The universe repair left those modules unchanged. The present review changes only
the attached docstrings in two of those existing definition modules; it does not restructure them.

## Declaration review round 1

Both findings are accepted after checking the canonical claims and the actual Lean
conclusions. There are no disagreements. Decisions remain 12 whole, 3 restricted,
0 refuted and 0 omitted; all 15 theorem names and proofs are preserved.

- **SAP.P004a.T5 — interpretation, minor.** The
  [T5 review finding](fw/round1/T5/r3g1/findings.json), under its T5 entry, correctly
  identifies an overbroad referent in both the Challenge docstring and the docstring
  attached to T5WholeStatement in Defs/WholeW1.lean. The canonical P004-T5 in work.json
  explicitly specifies the reading that an unweighted sum of bin Hajek contrasts equals
  the normalized change in the deforested share of their union. T5CaseStatement and
  T5RefinementStatement provide its three counterexamples and same-field refinement;
  they do not correct an empirical application value. Both docstrings now identify
  that interpretation expressly and add that no corrected empirical area effect is
  asserted for the application. All numerical descriptions remain unchanged.

- **SAP.P004a.T9 — tail-bound wording, minor.** The
  [T9 review finding](fw/round1/T9/r3g2/findings.json), under its T9 entry, correctly
  identifies unsupported optimality language in both the Challenge docstring and the
  docstring attached to T9WholeStatement in Defs/WholeW2.lean. T9TailsWhole asserts
  exact second and fourth moments, a symmetry identity, and explicit lower inequalities;
  it asserts no sharpness or optimality. I independently enumerated the N=1 design:
  the squared-sign-sum tail is 1, compared with the stated lower bound 9/16, and the
  remainder tail is 1/2, compared with the stated lower bound 9/32. The calculation is
  recorded in scratch/round1-n1-check.json. Both docstrings now say "exact moments and
  explicit finite tail lower bounds". No improved inequality or new proof was added.

These are documentation-only corrections in three modules. No Lean theorem statement,
definition expression, proof body, hypothesis or conclusion changes. The full source
audit in scratch/round1-source-audit.json checks unchanged code after removing comments
from every one of the 61 modules. The attached definition docstrings are synchronized
with the corresponding Challenge docstrings. No shared definition expression changes,
so this round does not require additional declarations to be reviewed for a changed
definition. The manifest records each resolution; the Comparator configuration retains
the same complete list of 15 theorems and the same three-kernel settings.

Round 1 validation completed with strict certificate stamp `20261104T194941Z`.
All 61 modules recompiled with sap-lean in dependency order; the build log is
scratch/round1-rebuild.log and the order is scratch/round1-build-order.json.
scratch/Axioms.lean reran the dependency command for all 15 solution theorems; every
result is exactly [propext, Classical.choice, Quot.sound], matching the manifest.
The five inspected definition types and values are byte-for-byte identical in the
before/after expression logs, including T5CaseStatement, T5RefinementStatement,
T5WholeStatement, T9TailsWhole and T9WholeStatement. Only their attached documentation
was edited. No definition dependency needs to be re-reviewed for changed Lean content.

The fresh frozen-snapshot build, target completeness, Lean-derived import closures,
theorem/definition comparison and all three external/default kernel checks passed for
all 15 theorems. The current result and kernel log are in
SAP/P004a/verification/comparator-result.json and comparator.log. The runner uses the
same storage-only adaptation documented above, now placing both the certificate and
fresh checkout under scratch, with no changes to certification checks or control mode.
scratch/round1-runner-storage.json records its exact substitutions and original tool hash.
The current manifest, Comparator configuration and all source hashes match this snapshot.
Both JSON files parse. The final audit is in scratch/round1-validation.json.

## Declaration review round 2

Both findings are accepted after independently checking the canonical claims in
work.json and the Lean statements. There are no disagreements. Decisions remain
12 whole, 3 restricted, 0 refuted and 0 omitted; all 15 theorems retain their names
and proofs. There are no open glue tasks.

- **SAP.P004a.T3 — residual normalization, minor.** The
  [T3 review finding](fw/round2/T3/r4g1/findings.json), under its T3 entry, is correct.
  w1ActiveR is the unnormalized residual sum. Both canonical clause W4 and
  T3AsymptoticStatement explicitly divide it by N=8r before asserting convergence in
  probability to 1/8. The Challenge docstring and the matching T3WholeStatement
  docstring in Defs/WholeW1.lean now say that N₁/N and R/N tend in probability to
  1/5 and 1/8. The unnormalized sum is no longer described as having that limit.

- **SAP.P004a.T15 — usual conditions, minor.** The
  [T15 review finding](fw/round2/T15/r4g3/findings.json), under its T15 entry, is correct.
  T15BandStatement already requires measurable radius maps and WellDefined. The
  latter explicitly requires measurable regions, positive finite band mass, and
  integrable outcome sections for every assignment. The Challenge docstring and
  the matching T15WholeStatement docstring in Defs/WholeW1.lean now both say:
  "The usual measure-theoretic conditions are assumed." Under the author's
  2026-11-04 decision these existence and measurability conditions are presupposed;
  the whole label remains correct. No substantive hypothesis has been added.

Only four docstrings in two modules changed. No theorem statement, shared definition
expression, proof body, hypothesis or conclusion changed, and no new proof was added.
scratch/round2-source-audit.json compares all 61 modules with their saved pre-edit
sources after removing comments. The two pairs of docstrings remain identical.
No shared definition expression changes require other declarations to be reviewed.
The manifest records both resolutions and preserves all row credits and restrictions.
The Comparator configuration retains exactly the same 15 theorem names, permitted
dependencies and external kernel commands.

Round 2 validation completed with strict certificate stamp `20261104T203708Z`.
All 61 package modules recompiled with sap-lean in dependency order. The build log
and order are scratch/round2-rebuild.log and scratch/round2-build-order.json.
scratch/Axioms.lean reran the dependency command for all 15 theorems, each reporting
exactly [propext, Classical.choice, Quot.sound], matching the manifest.
The before/after raw Lean type and value expressions of w1ActiveR,
T3AsymptoticStatement, T3WholeStatement, WellDefined, T15BandStatement and
T15WholeStatement are byte-for-byte identical, as are the T3 and T15 theorem types;
see scratch/round2-definition-expressions-before.log and its after counterpart.

The strict frozen-snapshot rebuild, complete-manifest check, Lean-derived import
closures, theorem/definition identity comparison and all three kernels passed for
all 15 theorems. SAP/P004a/verification/comparator-result.json and comparator.log
now hold the round 2 result. The prescribed runner uses the same three storage-only
substitutions described above, placing its record and fresh same-HEAD checkout
under scratch; no certification checks or kernel commands changed and control mode
was not used. The exact substitutions and original tool hash are recorded in
scratch/round2-runner-storage.json. Current source and metadata hashes match this
certified snapshot. Both JSON files parse, and the final validation summary is
scratch/round2-validation.json.

The inherited 17 modules exceeding the original line cap remain an existing package
issue; this round changes documentation in only one of those definition modules and
introduces no additional oversized module. No bridge or mathematical proof changes
were needed.

## Declaration review round 3

The finding is accepted after checking the canonical claim and the actual Lean
statement. There are no disagreements. Decisions remain 12 whole, 3 restricted,
0 refuted and 0 omitted; all 15 theorem names and proofs are preserved. There are
no open glue tasks.

- **SAP.P004a.T2 — usual conditions, minor.** The
  [T2 review finding](fw/round3/T2/r5g1/findings.json), under its T2 entry, is correct.
  T2AsymptoticStatement in Defs/Part3.lean explicitly assumes eventual WellDefined.
  In Defs/Part1.lean, WellDefined requires measurable averaging regions, positive
  finite averaging mass, and integrable outcome sections for every assignment.
  T2's Challenge docstring now adds: "The usual measure-theoretic conditions are
  assumed." These are the author's presupposed domain conditions, so the whole
  label remains correct. Independence, overlap, locality, rates, nondegeneracy and
  every other substantive hypothesis are unchanged.

Only that Challenge docstring changed. No shared definition, theorem statement,
hypothesis, conclusion, proof body or bridge changed, and no new proof was added.
The source audit in scratch/round3-source-audit.json compares all 61 modules with
their pre-edit hashes: every module's code after removing comments is identical,
and all definition and Solution sources are byte-for-byte unchanged. No shared
definition change requires other declarations to be reviewed. The manifest records
the resolution while retaining all row credits and restrictions. The Comparator
configuration retains the same complete list of 15 theorem names and kernel settings.

Round 3 validation completed with strict certificate stamp `20261104T211719Z`.
All 61 package modules compiled with sap-lean in dependency order; see
scratch/round3-rebuild.log and scratch/round3-build-order.json. scratch/Axioms.lean
reran the dependency command for all 15 solution theorems. Each reports exactly
[propext, Classical.choice, Quot.sound], matching the manifest.

The independent frozen-snapshot rebuild, manifest completeness, Lean-derived import
closures, exported theorem/definition identity comparison and all three kernels
passed for all 15 theorems. The current result and kernel log are
SAP/P004a/verification/comparator-result.json and comparator.log. The prescribed
runner uses the same three storage-only substitutions documented above; its record
and fresh same-HEAD checkout are under scratch. No checks or kernel commands were
changed, and control mode was not used. scratch/round3-runner-storage.json records
the exact substitutions and original tool hash. Current source and metadata hashes
match this snapshot. Both JSON files parse. The final validation summary is
scratch/round3-validation.json. The inherited line-cap issue described above is
unchanged; no oversized module was added or modified in this round.
