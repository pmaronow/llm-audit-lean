P025a packages only P025-T1 through P025-T11 in namespace `SAP.P025a`.
The work is *Interval Estimation of Population Means under Unknown but Bounded
Probabilities of Sample Selection*, Biometrika 100(1), 235–240 (2013),
DOI 10.1093/biomet/ass064.

Counts: **2 whole, 7 restricted, 2 refuted, 0 omitted**. All **11** listed
Challenge theorems have compiled Solutions. There are **0 open glue tasks**.

| Decision | Targets |
| --- | --- |
| whole | P025-T6, P025-T9 |
| restricted | P025-T1, P025-T2, P025-T3, P025-T4, P025-T5, P025-T10, P025-T11 |
| refuted | P025-T7, P025-T8 |
| omitted | none |

Each restriction below also appears in the theorem docstring and in
[SAP/P025a/manifest.json](SAP/P025a/manifest.json).

**P025-T1 — restricted.** Retains the numerical counterexample, exact attainable interval, finite
design realization, and the general zero-cut and strict nonoptimality conclusions. Omits the
displayed all-weight residual decompositions for the numerical minimum and maximum, the general
sample-mean residual identity, the exact one-coordinate objective-change formula, and an explicit
independence assertion for the two inclusion indicators.

**P025-T2 — restricted.** Retains the numerical class-total witness, strict outcome order,
probability bounds, population mean, wrong printed cut and value, corrected endpoint values, global
box inequalities, and Assumption 2. Omits the sampling-design realization and independent
replication, the derivation of singleton classes and their true class weights, identification of the
upper first cut, the displayed residual decompositions for both extrema, and the general weighted
zero-cut and nonoptimality diagnosis.

**P025-T3 — restricted.** Retains all cut existence, last-cut inequalities, prescribed optimizers,
endpoint and full-range identities, explicit segment parameters, increments, separation, and
termwise residual conclusions. Omits the separate assertion that the ratio is continuous along the
segment between the two optimizers; the credited segment certificate exports attainment, not
continuity.

**P025-T4 — restricted.** Retains existence of both first corrected cuts, attainment of both global
endpoint values, and their infimum and supremum formulas. Omits both inequalities at the last valid
cut, both increment identities, and explicit feasibility, value identities, and optimality of the
prescribed threshold weight vectors; attainment is asserted through IsLeast and IsGreatest without
identifying the attaining vectors.

**P025-T5 — restricted.** Retains both numerical population and reweighted-prevalence witnesses, the
ratio inequalities, probability bounds, sample counts and rounding, interval memberships, both
rounded-input variants, and the seven separate stratum laws and marginals. Omits construction and
normalization of a joint independent product sampling design, linkage of that joint design to the
two populations, and assertions that every draw of that joint design has the stated counts and Hajek
estimates.

**P025-T10 — restricted.** Omits only the displayed residual equality for every feasible weight
vector and the uniqueness characterization of equality at (2,2,1,1). Retains the explicit design,
its marginals, class totals and sizes, true class weights, population mean, global minimum,
corrected cut and tested values, and erroneous or undefined printed display.

**P025-T11 — restricted.** Retains the normalized increment identity, equality of all threshold
values with the sample mean and the normalized singleton box at gamma = 1, strict-gamma equality of
the stationary and outcome-test index sets and pointwise tests, one-step persistence, and all two-
coordinate identities and boundary/strict-improvement conclusions. Omits alpha = beta and the
original-scale singleton box and threshold-vector identities, identification of both optimization
endpoints with the sample mean, existence and identification of the boundary first cut, existence
and equality of the strict-case first indices and the global threshold maximum, and the equal-
probability finite-population calibration and population-mean identities in part (B-iv).

The two `refuted` decisions negate the printed sample optimizer/range assertion
and the printed class optimizer/formula assertion, respectively. Each theorem
also retains the valid upper component. A false lower component refutes the
printed conjunction; T8 does not separately assert a resolution of the
unqualified sharpness sentence. Its absolute-information sharpness row is
therefore unused. The counterexample targets remain `restricted`, because their
canonical claims are already refutations or counterexample specifications.

The route is shared Mathlib-only SAP definitions in seven Defs parts. Both
Challenge and Solution import the same compiled `T1Statement` through
`T11Statement` definitions. Challenge has one part and imports only Defs;
Solution imports Defs, Bridge, and the three project modules supplying the
credited declarations. No pilot claim or target assigned to another unit is
asserted.

[Bridge.lean](SAP/P025a/Bridge.lean) supplies definitional correspondences for
means, ratios, boxes, threshold vectors, first-cut predicates, attainable sets,
endpoints, separation, numerical examples, binary formulas, quota laws, and the
pair objective. Every bridge is proved by `rfl`. The two generic project
threshold specializations also agree by `rfl`. Sampling witnesses use plain
sample maps and probability functions, with inclusion probabilities and class
totals expressed as finite sums. The bridges identify those data and sums with
the fields and functions of the project's two bundled designs, again by `rfl`;
no new sampling structure or product design is constructed.

All substantive mathematical conclusions come from the credited declarations.
The added steps instantiate those declarations, assemble conjunctions, rewrite
the bridges, and perform elementary algebra, sign checks, and concrete
arithmetic. T3 uses the exported separator to check the signs of the individual
residual terms. Its segment parameter comes from the existing segment
certificate and is transported to the original box by existing scaling facts.
T6's square-root criteria are rewrites of the exported squared criteria, and
its decimal expansions are given precise five-decimal rational brackets using
ordinary square-root identities and exact arithmetic.

Every displayed ratio is used with positive feasible weights on a nonempty
finite type, with positive masses where applicable, or with fixed positive
numerical denominators. The class endpoint definitions are used under those
nonempty positive-box assumptions. Binary odds use interior proportions and
positive selection probabilities. Quota marginals are specialized to the seven
positive population sizes and valid positive quotas. The literal printed tail
is represented by `Option`: cuts 0 and 1 give `none`, rather than a value from
truncated index subtraction. All first-cut rules use `Fin n`, the standing
valid search domain.

The final clause audit treats the continuity phrase in T3(d) as a separate
assertion. The credited segment certificate exports attainment, not continuity;
the continuity argument inside its proof is not an exported conclusion. That
is why T3 is restricted despite the review's overall full-coverage label.
Likewise, T4 is limited to its credited theorem's exported conclusions rather
than the stronger supporting theorem used internally in its proof. T5's
individual quota laws do not substitute for an exported joint design, and
T10's global inequality does not substitute for the missing uniqueness
characterization. No hypotheses were added from diagnostic notes.

Compilation succeeded using `/home/ubuntu/sap/tools/sap-lean` in dependency
order for all seven Defs parts, Defs, Bridge, the Challenge part and root,
Solution, and [scratch/P025aAxioms.lean](scratch/P025aAxioms.lean). The final
Solution was checked again after adding T6's precise decimal brackets. All
11 printed dependency lists are exactly `propext`, `Classical.choice`, and
`Quot.sound`; see [scratch/P025aAxioms.log](scratch/P025aAxioms.log).

Both JSON files parse. The target lists, theorem lists, row dispositions,
permitted dependency lists, shared statement names, import boundaries, required
options, and 300-line limit were checked. Every SAP file is below 300 lines;
there are no open glue plans. Existing input and project files were not edited.

[comparator.json](SAP/P025a/comparator.json) contains the requested modules,
all 11 theorem names, empty definition-name list, permitted dependencies, and
external-kernel commands. The Palomar Comparator is not exposed by the available
tools; `con-ron` and `nanoda_bin` are not on PATH.
The external comparator run has therefore not been performed; this report
records Lean compilation and dependency checks, not three-kernel certification.

## Whole versions (new proofs)

This section supersedes the earlier restricted-version descriptions for the seven targets below. The current decisions are **9 whole, 0 restricted, 2 refuted, 0 omitted**. Only the listed Challenge stubs and Solution declarations are switched; the supplied whole definitions, blueprints, and proofs are unchanged.

- **P025-T10** (`SAP.P025a.T10`) → `SAP.P025a.T10WholeStatement`.
  Files: [SAP/P025a/Challenge/Part1.lean](SAP/P025a/Challenge/Part1.lean), [SAP/P025a/Solution.lean](SAP/P025a/Solution.lean), [SAP/P025a/Defs/WholeW1.lean](SAP/P025a/Defs/WholeW1.lean), [SAP/P025a/WH/W1/Leaves.lean](SAP/P025a/WH/W1/Leaves.lean), [SAP/P025a/WH/W1/Proofs/T10.lean](SAP/P025a/WH/W1/Proofs/T10.lean), [SAP/P025a/WH/W1/P/T10_L1.lean](SAP/P025a/WH/W1/P/T10_L1.lean), [SAP/P025a/WH/W1/P/T10_L2.lean](SAP/P025a/WH/W1/P/T10_L2.lean).
  Old restriction removed: Omits only the displayed residual equality for every feasible weight vector and the uniqueness characterization of equality at (2,2,1,1). Retains the explicit design, its marginals, class totals and sizes, true class weights, population mean, global minimum, corrected cut and tested values, and erroneous or undefined printed display.

- **P025-T11** (`SAP.P025a.T11`) → `SAP.P025a.T11WholeStatement`.
  Files: [SAP/P025a/Challenge/Part1.lean](SAP/P025a/Challenge/Part1.lean), [SAP/P025a/Solution.lean](SAP/P025a/Solution.lean), [SAP/P025a/Defs/WholeW1.lean](SAP/P025a/Defs/WholeW1.lean), [SAP/P025a/WH/W1/Leaves.lean](SAP/P025a/WH/W1/Leaves.lean), [SAP/P025a/WH/W1/Proofs/T11.lean](SAP/P025a/WH/W1/Proofs/T11.lean), [SAP/P025a/WH/W1/P/T11_L1.lean](SAP/P025a/WH/W1/P/T11_L1.lean), [SAP/P025a/WH/W1/P/T11_L2.lean](SAP/P025a/WH/W1/P/T11_L2.lean), [SAP/P025a/WH/W1/P/T11_L3.lean](SAP/P025a/WH/W1/P/T11_L3.lean).
  Old restriction removed: Retains the normalized increment identity, equality of all threshold values with the sample mean and the normalized singleton box at gamma = 1, strict-gamma equality of the stationary and outcome-test index sets and pointwise tests, one-step persistence, and all two-coordinate identities and boundary/strict-improvement conclusions. Omits alpha = beta and the original-scale singleton box and threshold-vector identities, identification of both optimization endpoints with the sample mean, existence and identification of the boundary first cut, existence and equality of the strict-case first indices and the global threshold maximum, and the equal-probability finite-population calibration and population-mean identities in part (B-iv).

- **P025-T1** (`SAP.P025a.T1`) → `SAP.P025a.T1WholeStatement`.
  Files: [SAP/P025a/Challenge/Part1.lean](SAP/P025a/Challenge/Part1.lean), [SAP/P025a/Solution.lean](SAP/P025a/Solution.lean), [SAP/P025a/Defs/WholeW1.lean](SAP/P025a/Defs/WholeW1.lean), [SAP/P025a/WH/W1/Leaves.lean](SAP/P025a/WH/W1/Leaves.lean), [SAP/P025a/WH/W1/Proofs/T1.lean](SAP/P025a/WH/W1/Proofs/T1.lean), [SAP/P025a/WH/W1/P/T1_L1.lean](SAP/P025a/WH/W1/P/T1_L1.lean), [SAP/P025a/WH/W1/P/T1_L2V2.lean](SAP/P025a/WH/W1/P/T1_L2V2.lean).
  Old restriction removed: Retains the numerical counterexample, exact attainable interval, finite design realization, and the general zero-cut and strict nonoptimality conclusions. Omits the displayed all-weight residual decompositions for the numerical minimum and maximum, the general sample-mean residual identity, the exact one-coordinate objective-change formula, and an explicit independence assertion for the two inclusion indicators.

- **P025-T2** (`SAP.P025a.T2`) → `SAP.P025a.T2WholeStatement`.
  Files: [SAP/P025a/Challenge/Part1.lean](SAP/P025a/Challenge/Part1.lean), [SAP/P025a/Solution.lean](SAP/P025a/Solution.lean), [SAP/P025a/Defs/WholeW1.lean](SAP/P025a/Defs/WholeW1.lean), [SAP/P025a/WH/W1/Leaves.lean](SAP/P025a/WH/W1/Leaves.lean), [SAP/P025a/WH/W1/Proofs/T2.lean](SAP/P025a/WH/W1/Proofs/T2.lean), [SAP/P025a/WH/W1/P/T2_L1.lean](SAP/P025a/WH/W1/P/T2_L1.lean).
  Old restriction removed: Retains the numerical class-total witness, strict outcome order, probability bounds, population mean, wrong printed cut and value, corrected endpoint values, global box inequalities, and Assumption 2. Omits the sampling-design realization and independent replication, the derivation of singleton classes and their true class weights, identification of the upper first cut, the displayed residual decompositions for both extrema, and the general weighted zero-cut and nonoptimality diagnosis.

- **P025-T3** (`SAP.P025a.T3`) → `SAP.P025a.T3WholeStatement`.
  Files: [SAP/P025a/Challenge/Part1.lean](SAP/P025a/Challenge/Part1.lean), [SAP/P025a/Solution.lean](SAP/P025a/Solution.lean), [SAP/P025a/Defs/WholeW1.lean](SAP/P025a/Defs/WholeW1.lean), [SAP/P025a/WH/W1/Leaves.lean](SAP/P025a/WH/W1/Leaves.lean), [SAP/P025a/WH/W1/Proofs/T3.lean](SAP/P025a/WH/W1/Proofs/T3.lean), [SAP/P025a/WH/W1/P/T3_L1.lean](SAP/P025a/WH/W1/P/T3_L1.lean).
  Old restriction removed: Retains all cut existence, last-cut inequalities, prescribed optimizers, endpoint and full-range identities, explicit segment parameters, increments, separation, and termwise residual conclusions. Omits the separate assertion that the ratio is continuous along the segment between the two optimizers; the credited segment certificate exports attainment, not continuity.

- **P025-T4** (`SAP.P025a.T4`) → `SAP.P025a.T4WholeStatement`.
  Files: [SAP/P025a/Challenge/Part1.lean](SAP/P025a/Challenge/Part1.lean), [SAP/P025a/Solution.lean](SAP/P025a/Solution.lean), [SAP/P025a/Defs/WholeW2.lean](SAP/P025a/Defs/WholeW2.lean), [SAP/P025a/WH/W2/Leaves.lean](SAP/P025a/WH/W2/Leaves.lean), [SAP/P025a/WH/W2/Proofs/T4.lean](SAP/P025a/WH/W2/Proofs/T4.lean).
  Old restriction removed: Retains existence of both first corrected cuts, attainment of both global endpoint values, and their infimum and supremum formulas. Omits both inequalities at the last valid cut, both increment identities, and explicit feasibility, value identities, and optimality of the prescribed threshold weight vectors; attainment is asserted through IsLeast and IsGreatest without identifying the attaining vectors.

- **P025-T5** (`SAP.P025a.T5`) → `SAP.P025a.T5WholeStatement`.
  Files: [SAP/P025a/Challenge/Part1.lean](SAP/P025a/Challenge/Part1.lean), [SAP/P025a/Solution.lean](SAP/P025a/Solution.lean), [SAP/P025a/Defs/WholeW2.lean](SAP/P025a/Defs/WholeW2.lean), [SAP/P025a/WH/W2/Leaves.lean](SAP/P025a/WH/W2/Leaves.lean), [SAP/P025a/WH/W2/Proofs/T5.lean](SAP/P025a/WH/W2/Proofs/T5.lean), [SAP/P025a/WH/W2/P/T5_L1.lean](SAP/P025a/WH/W2/P/T5_L1.lean), [SAP/P025a/WH/W2/P/T5_L2.lean](SAP/P025a/WH/W2/P/T5_L2.lean).
  Old restriction removed: Retains both numerical population and reweighted-prevalence witnesses, the ratio inequalities, probability bounds, sample counts and rounding, interval memberships, both rounded-input variants, and the seven separate stratum laws and marginals. Omits construction and normalization of a joint independent product sampling design, linkage of that joint design to the two populations, and assertions that every draw of that joint design has the stated counts and Hajek estimates.

Dependent-proof repairs: none. The unchanged Solution proofs for P025-T6, P025-T7, P025-T8, and P025-T9 do not use any switched theorem. Their statements, proofs, docstrings, and manifest entries are unchanged.

Validation: `python3 /home/ubuntu/sap/tools/rebuild_sap.py . P025a` completed successfully from scratch: **34 modules rebuilt; token scan clean**. The scratch file `/tmp/p025a-whole-axioms.lean` imports `SAP.P025a.Solution` and runs `#print axioms` for all seven switched theorems. Every result is exactly `propext`, `Classical.choice`, and `Quot.sound`; output is in `/tmp/p025a-whole-axioms.log`. Lean compilation ran sequentially, and no Lake command was run.


## 2026-11-05 independently reviewed repair proposal

P025a Challenge T8 now records the feasible six-unit optimizer refutation; T5 has a reading-qualified docstring consistent with the unchanged mathematical statement. The canonical work packet and WH adjudication remain unchanged.

The source, accepted certificate, current canonical work packet, exact Defs/Challenge closure, and fresh normal full-unit declaration and omission reviews are bound in assure/remaining-repair-transactions-2026-11-05-v2/P025a/plan.json. Original adverse Opus findings and earlier review rows remain historical evidence. This entry does not accept a claim event, rewrite WH adjudication, enable whole promotion, perform A3 replay, collect, release, or push.
