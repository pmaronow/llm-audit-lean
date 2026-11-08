Unit P016b packages exactly P016-T12 through P016-T21 from `work.json`.
There are **6 whole, 4 restricted, 0 refuted and 0 omitted** targets.
All **10** Solution theorems are proved and compile; there are **0 open glue tasks**.

| Target | Decision | Theorem |
| --- | --- | --- |
| P016-T12 | restricted | `SAP.P016b.T12` |
| P016-T13 | restricted | `SAP.P016b.T13` |
| P016-T14 | whole | `SAP.P016b.T14` |
| P016-T15 | whole | `SAP.P016b.T15` |
| P016-T16 | restricted | `SAP.P016b.T16` |
| P016-T17 | whole | `SAP.P016b.T17` |
| P016-T18 | whole | `SAP.P016b.T18` |
| P016-T19 | restricted | `SAP.P016b.T19` |
| P016-T20 | whole | `SAP.P016b.T20` |
| P016-T21 | whole | `SAP.P016b.T21` |

The restrictions are:

- **T12:** Omit clause (iv)'s raw KS statistic-value table
  `(1, 1/2, 1/2, 1/2, 1/2, 1)`, which is absent from the credited conclusions.
  Retain the complete p-value table and rejection-probability formula, directional
  mean monotonicity, both KS failures and all three exact-tail validity bounds.
  Both weak and strict cutoffs are stated. The KS failures are stated on the
  domain with both groups nonempty, using the already-exported four-unit witness.
- **T13:** The general tie-free law requires `0 ≤ α < 1`, matching its credited
  declaration; its admissible boundary and larger-level cases are omitted.
  The finite-design statement retains two-assignment fibers through its
  complement equality characterization and gives the number of distinct values.
  The five reported decimal approximations
  to the finite-design probabilities are omitted: both weak-cutoff sizes, both
  strict-cutoff sizes and the zero-p mass at `B = 1000`. Exact formulas, the
  stated rational bounds, all comparisons with `1/20` and positive zero-p mass
  remain. Both tie-free numerical counterexamples remain.
- **T16:** The control ECDF identities require a positive control-group size;
  the sample ECDF identity requires `n > 0`. These guards exclude division by
  zero where the canonical text calls the result a proportion. Pointwise
  adjustment identities and parameter dependence need no group-size guard and
  are retained, as is the joint-hypothesis correction.
- **T19:** Retain all mathematical clauses (a)–(f), including the actual median
  identity, its roots and global minimum, mean reductions and their balanced-
  design expectations, the matching characterization and the full T18 witness.
  Omit the empirical Normal-versus-Jittered-Geometric power ordering and
  simulation-specific powers (including the four quoted in the repair),
  the assertion that the actual simulation's two hypotheses have
  unequal expected adjusted mean shifts, and the simulation-data matching
  approximation `1.035312` and sample-mean approximation `10.069`.
  The constructed witness in (f) asserts no property
  of that simulated dataset.
  These empirical assertions occur in the canonical statement's quoted repair;
  its diagnostic note cannot remove them under the current claim-scope rule
  ([revise-ref2.md:23](/home/ubuntu/sap/wt/ARCH-P016b/revise-ref2.md:23)).
  The nonzero multiplicative parameter in comparisons (d)–(e)
  is their inherited domain condition. Recomputed powers and a revised
  calibration objective are recommendations, rather than proved conclusions.

T14 is whole: exact-tail clause (e) explicitly references canonical T12(iii),
whose finite-law domain has strictly positive weights. Its iid exchangeability
clause continues to allow zero-weight points. This distinction changes the
scope description and label, with no change to the theorem or its proof.

No targets are omitted. T13 and T15 are already counterexample claims in the
canonical text, so their decisions are respectively restricted and whole,
rather than refuted. T18 is an explicitly constructed population; its statement
does not identify that population with the paper's simulated data. T21 includes
the exact and sampled guarantees but makes no assertion about the reported
empirical rejection frequencies, which its canonical claim expressly excludes.

The definitions route uses six Mathlib-only modules under `SAP/P016b/Defs/`.
Each theorem's type is the shared `SAP.P016b.TkStatement` constant. Challenge
and Solution import the same compiled Defs modules. The Challenge imports only
Defs; Solution imports Defs, Bridge and the two required project modules.
Definitions are SAP-named and no project declaration is recreated under its
original qualified name.

`SAP/P016b/Bridge.lean` supplies the following correspondences:

- `toProjectLaw` copies the weight function and its nonnegativity and
  normalization certificates into the project's finite-law structure.
- The probability, iid probability, uniform-law, assignment-domain, group,
  ECDF, KS, adjustment, exchangeability, corrected-tail, mixture, median,
  discrepancy, witness-data and network-map correspondences all use `rfl`.
  Their bodies agree definitionally; the law adapter preserves every data field.
- `ks_not_effectIncreasingOnGroups` instantiates
  `AronowAudit.P016.t11_ks_witness`, the existing witness used by the credited
  KS failure proof. Two finite natural-number checks certify nonempty groups;
  substituting its exported values `1` and `0` gives each contradiction.
  This avoids a statement about empty-group ECDF extensions. The broader
  credited `t12_ks_not_effect_increasing` is therefore listed as unused.
- `exactValidity` applies the three credited `t12_*_valid` rows through the
  finite-law adapter. Its strict versions follow from the existing `mass_mono`
  declaration and the implication from a strict inequality to a weak one.

Solution otherwise uses instantiation, conjunction, definitional transport and
arithmetic simplification of exported bounds. T18's minimum certificate uses
the existing `t19_median_nonneg` row and the witness's exported treatment count.
T13's separate RSS identity is redundant with its finite-design row. T19's
separate nonnegativity row is redundant with its calibration-roots row. These
row choices and supporting declarations are recorded in the manifest.

Validation completed with `/home/ubuntu/sap/tools/sap-lean`, in dependency order,
for all six Defs parts, Defs root, Bridge, Challenge part, Challenge root and
Solution. The scratch checks `scratch/P016bCheckRows.lean` and
`scratch/P016bCheckSolution.lean` also compile. The latter runs `#print axioms`
for every Solution theorem; every result is exactly
`[propext, Classical.choice, Quot.sound]`, matching the manifest.

Both JSON files parse. The manifest covers each assigned target once, and its
theorem list agrees with `comparator.json`. All SAP files are at most 300 lines
and have both required implicit-argument options immediately after imports.
The token check passes outside the intended Challenge proof stubs. Tracked
project files are unchanged.

The orchestrator subsequently supplied
[a successful Comparator record](/home/ubuntu/sap/wt/ARCH-P016b/SAP/P016b/verification/comparator-result.json)
for the original snapshot: all ten targets were accepted by the three kernels.
Revision 2 changes docstrings and scope metadata only; the Defs, Bridge and
Solution source hashes still match that snapshot. The supplied certification
record is preserved as evidence for that snapshot, without claiming a fresh
external run for the revised metadata. The required local rebuild and all ten
`#print axioms` checks passed again after the revision.

## Round 1 referee findings and revision 2 actions

Every target in both reports was checked against the canonical statement and
the SAP proposition. The table covers all twenty findings records.

| Target | Referee A | Referee B | Action |
| --- | --- | --- | --- |
| T12 | correct restricted | correct restricted | Retain the disclosed missing raw KS table. |
| T13 | correct restricted | correct restricted | Retain the level and decimal restrictions; correct the description of fiber coverage. |
| T14 | restriction inaccurate | correct restricted | Accept A's cross-reference reading; relabel whole and explain the inherited domain. |
| T15 | correct whole | correct whole | Retain all three explicit witnesses. |
| T16 | correct restricted | correct restricted | Retain the positive sample and control-group guards. |
| T17 | correct whole | correct whole | Retain the general identities and both numerical comparisons. |
| T18 | correct whole | correct whole | Retain the complete witness and minimum certificate. |
| T19 | restriction inaccurate | restriction inaccurate | Correct the domain description; retain restricted with the precedence justification below. |
| T20 | correct whole | correct whole | Retain the additive identity and all four model clauses. |
| T21 | correct whole | correct whole | Retain adjustment recovery and all exact and sampled bounds. |

**A, T14:** Accepted. Canonical T14(e) ends with the explicit reference
“P016-T12 (iii)”
([work.json:302](/home/ubuntu/sap/wt/ARCH-P016b/work.json:302)).
That referenced clause specifies `q(z) > 0` at every point
([work.json:41](/home/ubuntu/sap/wt/ARCH-P016b/work.json:41)).
T14 does not give a separate exact-law domain overriding this reference.
`ExactValidity` uses precisely the referenced domain. T14 is now `whole`,
its manifest restriction is null, and its docstring describes positivity as
inherited. No Lean statement or proof change was needed. This disagrees with
B's conservative restricted reading for the same cited reason; the allowance
of zero weights in the separate iid clause is preserved.

**A and B, T19, empirical scope:** Disagree with the proposed relabelling.
The canonical **statement**, not merely its note, quotes the assertion that SSR
has greater Normal-outcome power, gives all four numerical powers, gives the
Jittered Geometric ordering and includes the approximation `1.035312`
([work.json:780](/home/ubuntu/sap/wt/ARCH-P016b/work.json:780)).
The referees exclude these using the later diagnostic note
([work.json:782](/home/ubuntu/sap/wt/ARCH-P016b/work.json:782)).
The current user instruction explicitly defines the claim as the canonical
statement together with `definitions_needed` and standing assumptions, and
says notes add no clauses and remove none
([revise-ref2.md:23](/home/ubuntu/sap/wt/ARCH-P016b/revise-ref2.md:23)).
All clauses (a)–(f) are proved, but that does not state these additional
empirical assertions. They cannot be restored by glue from the existing
mathematical declarations. T19 therefore remains `restricted`; its docstring
and manifest identify the omissions from the quoted canonical statement.

**A and B, T19, nonzero multiplier:** Accepted. Clause (d) already requires
`a ≠ 0`, and (e) compares the reductions in (d)
([work.json:780](/home/ubuntu/sap/wt/ARCH-P016b/work.json:780)).
The guard remains in the theorem, but the docstring and manifest now correctly
describe it as inherited, rather than an additional reason for restriction.
Positive half-size likewise makes the median and treated minimum meaningful.
Recomputing powers and redesigning the objective are recommendations; the
scope descriptions now distinguish them from the omitted empirical assertions.

**A and B, T13, fiber explanation:** Accepted as a clarification. Both findings
observe that the retained complement equality characterization already implies
two-assignment fibers. Removed the advertised loss of a separate cardinality
certificate from the restriction. The general `α < 1` premise still excludes
admissible canonical cases, and the five decimal approximations are still not
stated, so the decision remains `restricted`.

The other findings request no corrections, and the independent comparison
confirmed their decisions. In particular, T13 and T15 canonically assert
counterexample facts; the formalization establishes those facts rather than
refuting a positive canonical assertion. No target therefore changes to
`refuted`. All theorem names, statements, definitions and Solution proofs are
preserved. The comparator configuration was regenerated for the same ten
names. Both JSON files parse, all required options and line limits pass, and
there are no open glue tasks.

## Round 2 referee findings and actions

Both supplied round-two `findings.json` and `REPORT.md` files were read.
Neither round-two directory contains a `reading.md`; the reports describe
their comparison with the readings saved during the first review. Each of
the twenty findings records was checked against the current theorem's
definition and the canonical statement, definitions and standing assumptions.

| Target | Referee A | Referee B | Action |
| --- | --- | --- | --- |
| T12 | correct restricted | correct restricted | Keep the explicit raw-KS-table omission. |
| T13 | correct restricted | correct restricted | Keep the level and decimal restrictions and the retained complement fibers. |
| T14 | correct whole | correct whole | Keep the positive-weight domain inherited through T12(iii). |
| T15 | correct whole | correct whole | Keep all three local witnesses. |
| T16 | correct restricted | correct restricted | Keep both positive-size guards. |
| T17 | correct whole | correct whole | Keep both comparisons and their numerical instance. |
| T18 | correct whole | correct whole | Keep the complete constructed witness and global minimum. |
| T19 | restriction inaccurate | restriction inaccurate | Accept B's additional omitted-clause finding; retain restricted under the current explicit scope rule. |
| T20 | correct whole | correct whole | Keep additive inversion and every network-map clause. |
| T21 | correct whole | correct whole | Keep outcome recovery and all exact and sampled level guarantees. |

**B, T19, missing disclosure of the actual-data mean-shift assertion:**
Accepted. The quoted replacement states that the simulation's hypotheses
do not match expected adjusted mean shifts
([work.json:780](/home/ubuntu/sap/wt/ARCH-P016b/work.json:780));
`definitions_needed` identifies `mean(Y)` as the actual simulated outcome
mean, rather than the constructed witness's mean
([work.json:781](/home/ubuntu/sap/wt/ARCH-P016b/work.json:781)).
The theorem's general identities and constructed witness do not establish
that dataset-specific assertion. It is now named separately in the Challenge
docstring, manifest restriction and report. The empirical exclusion also names
the sample-mean approximation `10.069` from `definitions_needed`, and covers
all simulation-specific numerical powers. No proof or hypothesis was added.

**A and B, T19, proposed relabelling as whole:** Disagree under the current
governing instruction. This pass's rule, reproduced in
[revise-ref2.md:23](/home/ubuntu/sap/wt/ARCH-P016b/revise-ref2.md:23), says:
“A target's claim is its canonical `statement` together with `definitions_needed`
(and the work's standing assumptions).” It further says that its note and
finite lemmas “add no clauses and remove none.” The omitted powers, ordering,
actual-data mismatch and approximation are affirmative assertions in the
canonical statement's quoted replacement
([work.json:780](/home/ubuntu/sap/wt/ARCH-P016b/work.json:780)).
The note at line 782 cannot remove them. Accordingly all (a)–(f) are retained,
but T19 remains restricted. B expressly allows this resolution when the
governing instruction includes the quoted assertions; the newly disclosed
actual-data mismatch completes that resolution.

**A and B, T19, objection to the previous brief citation:** The reports say
their supplied brief contained a different instruction at line 30 and did
not establish the precedence rule. The current revision request now supplies
the rule explicitly. Replaced the report's disputed brief citation and the
manifest's unsupported standalone reference to it with the current rule,
quoted above and saved locally in `revise-ref2.md`. This justification no
longer depends on access to a different referee workspace's brief.

**A and B, T19, already-corrected domain descriptions:** Retained. Positive
half-size ensures the median positions and treated minimum exist; the
inverse-adjustment comparisons use `a ≠ 0` from (d)–(e). These are not reasons
for the empirical restriction. Recomputed powers and a changed calibration
objective remain recommendations, rather than mathematical conclusions.

The nine other targets had no adverse round-two findings. Independent
inspection confirmed the stated clauses and disclosed restrictions. In
particular, the counterexample theorems establish their canonical assertions;
none contradicts a positive canonical assertion, and none acquires a
`refuted` label. No theorem types, proofs or shared definitions changed.

All eleven SAP Lean modules were recompiled in dependency order through
`sap-lean`, followed by the scratch file containing all ten `#print axioms`
commands. The output, with expected Challenge-stub warnings summarized, is saved in
[scratch/P016bRound2Build.log](/home/ubuntu/sap/wt/ARCH-P016b/scratch/P016bRound2Build.log).
The final docstring clarification was followed by recompilation of the Challenge
part and root and another run of all ten dependency checks; its output is in
[scratch/P016bRound2Followup.log](/home/ubuntu/sap/wt/ARCH-P016b/scratch/P016bRound2Followup.log).
Every theorem still uses exactly `propext`, `Classical.choice` and `Quot.sound`.
The manifest and comparator configuration were regenerated and parsed for
the same ten theorem names. The definition/proof source hashes still match
the previously accepted certification snapshot. All options, import boundaries,
line limits and token checks pass; there are no open glue tasks.

## Whole versions (new proofs)

P016-T12, P016-T13 and P016-T16 now use their supplied whole statements and
proved `_whole` theorems. The current decisions are 9 whole and 1 restricted.
Only these three Challenge declarations and Solution theorems are switched;
the shared definitions and supplied proof files are unchanged.

- **P016-T12 (`SAP.P016b.T12`):** Challenge `SAP/P016b/Challenge/Part1.lean` now
  states `SAP.P016b.T12WholeStatement`; `SAP/P016b/Solution.lean` uses
  `SAP.P016b.WH.W1.T12_whole` from
  `SAP/P016b/WH/W1/Proofs/T12.lean`.
  Whole definition: `SAP/P016b/Defs/WholeW1.lean`;
  blueprint: `SAP/P016b/WH/W1/Leaves.lean`.
  Removed restriction: Omit clause (iv)'s raw KS statistic-value table (1, 1/2, 1/2, 1/2, 1/2, 1); retain the p-value table and full rejection-probability formula. State KS failures on the domain of nonempty groups using the already-exported four-unit witness.

- **P016-T13 (`SAP.P016b.T13`):** Challenge `SAP/P016b/Challenge/Part1.lean` now
  states `SAP.P016b.T13WholeStatement`; `SAP/P016b/Solution.lean` uses
  `SAP.P016b.WH.W1.T13_whole` from
  `SAP/P016b/WH/W1/Proofs/T13.lean`.
  Whole definition: `SAP/P016b/Defs/WholeW1.lean`;
  blueprint: `SAP/P016b/WH/W1/Leaves.lean`.
  Proved leaves: `SAP/P016b/WH/W1/P/T13_L1.lean` through `T13_L8.lean`.
  Removed restriction: Require 0 <= alpha < 1 in the general tie-free law, omitting admissible boundary and larger-level cases. Omit the five reported decimal approximations to the finite-design probabilities; retain exact mixture and zero-p formulas, positive zero-p mass, all comparisons with 1/20, and the complement equality characterization that retains the two-assignment fiber content.

- **P016-T16 (`SAP.P016b.T16`):** Challenge `SAP/P016b/Challenge/Part1.lean` now
  states `SAP.P016b.T16WholeStatement`; `SAP/P016b/Solution.lean` uses
  `SAP.P016b.WH.W1.T16_whole` from
  `SAP/P016b/WH/W1/Proofs/T16.lean`.
  Whole definition: `SAP/P016b/Defs/WholeW1.lean`;
  blueprint: `SAP/P016b/WH/W1/Leaves.lean`.
  Removed restriction: Require a positive control-group size for the control ECDF identities, and n > 0 for the sample ECDF identity, excluding empty-group and empty-sample total-division extensions. Retain all pointwise adjustment identities, parameter dependence and the joint-hypothesis correction.

For T16, the supplied `T16WholeStatement` is definitionally `T16Statement`.
Its nonempty-sample guards remain the domains of the empirical distributions;
the old restriction classification is removed without altering any definition.

Dependent-proof repairs: none. No other Solution proof uses T12, T13 or T16;
all other theorem declarations, docstrings, proofs and manifest entries remain
unchanged.

Validation: `python3 /home/ubuntu/sap/tools/rebuild_sap.py . P016b`
rebuilt all 25 unit modules from scratch and reported a clean token scan.
`scratch/P016bWholeAxioms.lean` imports `SAP.P016b.Solution` and runs
`#print axioms` on T12, T13 and T16. Each theorem depends on exactly
`propext`, `Classical.choice` and `Quot.sound`. Compilation ran
sequentially. The import boundaries and preservation of every other target
were verified. Per-target results are recorded in `switched.json`.
