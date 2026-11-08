P040 contains 5 targets: 5 whole, 0 restricted, 0 refuted, and 0 omitted.
All 5 Challenge theorems have compiled Solution proofs under their original
fully qualified names. There are 0 open glue tasks.

P040-T1 is whole. The exported theorem has type T1WholeStatement, which includes
the binomial/Wald component T1Statement and the actual standard normal .975
quantile's existence, uniqueness, enclosure in [1.9599,1.9601], and reconstructed
endpoints. It retains every canonical mass, coverage, exclusion, rounding,
multiplier-robustness and lower-bound-failure clause. The binomial sampling model
is already explicit in the canonical target; no patron generalization is added.

P040-T2 is whole: point estimate, tail identities, continuity, derivative and
positivity, monotonicity, unique endpoint roots and interval descriptions,
endpoint brackets and rounding, inclusion of .80, both uniform coverage
guarantees, and the cross-referenced method-free obstruction are retained.
The rounded numbers describe actual roots rather than replace the endpoints.

P040-T3 is whole for the canonical mathematical content P1 and P2: the estimate
rounds to .93 and the reconstructed Wald endpoints have the specified brackets,
rounding and upper-endpoint excess. The exact proportion identity reduces its
rounding to rational arithmetic. The survey counts are inputs, and no uniform
exact-coverage assertion is attributed to the printed nominal interpretation.

P040-T4 is whole: both actual adjusted regressions have the exact coefficients,
positive HC1 variances and squared statistics, Table 1 rounding, six-decimal
displays, both normal-reference integral brackets and rounding mismatches, and
the cross-referenced Student-t roundings. The numerical displays use rational
arithmetic and squared rational bounds on the exported witness values.

P040-T5 is whole: all design ranks and residual degrees of freedom, weekday
alias and reduced-column independence, Student-t(21) density and both printed
values, all eight actual statistic identities and bounds, non-significance
under both references, minimum comparisons and brackets, and the alternative
normal-reference rounding branch are included. Fitted-value-space equality
does not assert treatment-coordinate or robust-variance invariance.

The shared-definition route is used throughout. Defs/Part1 contains binomial
and Wald definitions, Part2 the exact-binomial and retained printed-arithmetic
statements, Part3 the exact data, regression quantities and reference integrals,
and Part4 the regression statements. Defs/WholeW1 adds T1's actual-normal-quantile
and completeness clauses. These modules import only Mathlib and earlier Defs
modules; both sides use their identical compiled definitions.

Bridge/Part1 and Bridge/Part2 transport binomial and regression conclusions by
direct applications of the project theorems. Their SAP and project definitions,
including the rounding predicates, agree definitionally. Solution assembles,
specializes and rewrites those conclusions, using elementary arithmetic.
The existing whole-T1 assembly in WH/W1/Leaves.lean also transports P033's
normal-quantile CDF certificate and enclosure and P053's strict monotonicity,
identifies the quantile's defining upper ray, and performs the finite-sum,
coverage and square-root comparisons. WH/W1/Proofs/T1.lean exports that assembly.
No proof or mathematical statement was added or changed during this review round.

Shared and cross-referenced components are identified in manifest.json.
T1 uses T3's reconstructed arithmetic and T2's observed tail identity; T2 uses
T1's obstruction; T4 uses the shared statistic, rank/df and Student-t rounding
results; T5 uses T4's actual-regression normal mismatch. T1's manifest also lists
the existing P033 and P053 quantile results used by its whole assembly. The
nine unadjusted-only rows miscredited to T4 remain unused as direct sources.
The duplicate listing of waldRadius_sq as both used and unused for T1 was removed;
its use in the whole assembly is now recorded consistently.

The exact binomial sums concern probabilities in [0,1], not the experiment's
randomized assignment of days. The quantile's defining set is proved nonempty
and bounded below, with its CDF equation and unique value stated. Fitted designs
have proved full column rank; the singular ten-column design is used only for
rank, range and residual degrees of freedom. The relevant variances and all
eight squared statistics are positive. Positive degrees of freedom and ordinary
finite-interval reference integrals avoid default branches. Neither reference
calculation claims an exact null distribution for an HC1 statistic.

## Declaration review round 1

The only open finding was restriction_inaccurate/minor for SAP.P040.T1:
[findings.json](fw/round1/T1/r3g1/findings.json), corroborated by the review's
[REPORT.md](fw/round1/T1/r3g1/REPORT.md). I agree. The docstring at
SAP/P040/Defs/Part1.lean:76 said that T1 omits the actual-normal-quantile
identification, but T1WholeStatement includes T1NormalQuantileSpecification at
SAP/P040/Defs/WholeW1.lean:113, and the exported Challenge uses that whole
statement at SAP/P040/Challenge/Part1.lean:20.

The corrected docstring explicitly calls T1Statement the base binomial and
Wald component and says the actual normal quantile clauses are added by
T1WholeStatement. Only this comment changed in Lean source. Every definition
body, theorem type and proof remains byte-for-byte unchanged. The other four
declarations have no findings. No restriction, omission or new proof is needed.
The stale initial restriction and counts in this report have been replaced by
the current five-whole status. The manifest records the completed round and
consistent source usage; comparator.json retains exactly the same configuration.

All 14 SAP Lean modules, including the whole-T1 modules, were recompiled with
sap-lean in dependency order, followed by scratch/P040AxiomCheck.lean. The fresh
output in scratch/P040Round1Compile.log lists exactly propext, Classical.choice
and Quot.sound for each of SAP.P040.T1 through SAP.P040.T5. Both JSON files parse,
all target names and proved statuses agree, and source options, import boundaries,
line limits and forbidden-token rules were checked.

The supplied verification/comparator-result.json records an accepted run for
all five theorems, and verification/comparator.log records acceptance by con-ron,
nanoda and the Lean kernel. Before this round's edits, every recorded snapshot
hash matched the workspace. That evidence is retained as the earlier certified
snapshot; its hashes are not rewritten. The present documentation and metadata
revision was rebuilt and dependency-checked locally without rerunning the external
Comparator. No mathematical declaration changed from the certified snapshot.
