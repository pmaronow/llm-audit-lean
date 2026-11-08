P021: Nonparametric Identification for Respondent-Driven Sampling.

Counts: **2 whole, 0 restricted, 0 refuted, 0 omitted**. Both listed theorems are proved;
there are **0 open glue tasks**. Every credited row is used.

- **P021-T1 — whole.** [T1Statement](SAP/P021/Defs/Part2.lean:41) retains the
  identification formula (2), both supported-stratum Bayes equalities (3), and the
  scaled and unscaled ratios (4). Its positivity, observable support, nonzero scale
  and profile values, and nonzero normalizer make every asserted ratio meaningful.
  Summation over positive-mass degrees implements the recorded standing convention.
- **P021-T2 — whole.** [T2WholeStatement](SAP/P021/Defs/WholeW1.lean:18) retains both
  consistency in probability for random populations and ordinary convergence for
  deterministic populations. It assumes the recorded common bounds, realized weak
  empirical convergence, mean ignorability, and sampling probabilities proportional
  to degree. Finite stages may have empty samples; the estimator is explicitly
  extended by zero there. The older guarded `T2Statement` remains unused and is not
  the statement of `SAP.P021.T2`.

No target is restricted, omitted, or refuted. There are no deferred proof plans.

The package uses ordinary Mathlib measures, integrals, finite sums, convergence in
measure under a probability measure, and ordinary filter convergence. The SAP
[definitions](SAP/P021/Defs.lean) and [whole T2 statement](SAP/P021/Defs/WholeW1.lean)
import only Mathlib and SAP Defs modules. Challenge imports those definitions and
Challenge parts only. Shared definitions are compiled once for both sides.

[Bridge.lean](SAP/P021/Bridge.lean) identifies the SAP state space, coordinates,
means, conditions, empirical averages, sample sets, estimator, weak convergence and
Proposition 1's full conclusion with the project notions. Every bridge proof is
`rfl` or `Iff.rfl`; no adapter or mathematical argument is needed.

[Solution.lean](SAP/P021/Solution.lean) instantiates
`AronowAudit.P021.proposition_one` for T1. The first Bayes equality is division
algebra with positive masses; (4) substitutes mean ignorability and cancels a common
nonzero scalar from finite sums. These are glue consequences of exported facts.
For T2, [the assembly](SAP/P021/WH/W1/Leaves.lean) instantiates
`AronowAudit.P021.corollary_one` and
`AronowAudit.P021.corollary_one_deterministic` through the Bridge; the final wrappers
preserve the same statement. There are no new mathematical proofs in this revision.

The finite-stage zero extension is explicit, rather than an assertion that an empty
sample has a defined fractional estimator. Positive degrees make each inverse-degree
weight finite. Under the stated hypotheses the limiting inverse-degree denominator
is positive, and the existing
[empty_sample_probability_tendsto](AronowAudit/P021/P021_RDS.lean:911) proves that
empty-sample probability tends to zero. The existing
[deterministic corollary](AronowAudit/P021/P021_RDS.lean:879) also permits empty finite
stages. Thus these extended values do not determine either consistency limit.
Compact support and probability laws ensure finite genuine means in T1; supported
mass and normalizer positivity exclude null-event conditional or final-ratio values.

All **10 SAP Lean modules** were rebuilt in dependency order with the supplied
`/home/ubuntu/sap/tools/sap-lean` wrapper. The required Challenge placeholders give
the only expected warnings. The build transcript is
[review-round1-build.log](scratch/P021/review-round1-build.log).
[CheckAxioms.lean](scratch/P021/CheckAxioms.lean) was rerun for both `SAP.P021.T1` and
`SAP.P021.T2`; each reports exactly `propext`, `Classical.choice`, and `Quot.sound`.
The refreshed output is in [axioms.txt](scratch/P021/axioms.txt).

Both JSON files were refreshed and parse. Their parsed values are unchanged:
[manifest.json](SAP/P021/manifest.json) still records both whole, proved targets and
all used rows, and [comparator.json](SAP/P021/comparator.json) still lists the same
modules, theorem names, permitted dependencies and external-kernel commands. Checks
cover target coverage, theorem-name agreement, import boundaries, both required
implicit-variable options, prohibited constructs and the 300-line file limit.

The supplied [Comparator record](SAP/P021/verification/comparator-result.json)
certifies both theorems for its earlier snapshot, with acceptance by all three
kernels in [comparator.log](SAP/P021/verification/comparator.log). That historical
record is retained unchanged. No new Comparator run is claimed for this revised
source snapshot; the current full rebuild and dependency checks were rerun.

## Declaration review round 1

- **SAP.P021.T2 / P021-T2 — minor dependent-definition documentation mismatch.**
  The [finding](fw/round1/T2/r3g1/findings.json) correctly identifies the obsolete
  nonempty-sample requirement in the `vhEstimator` docstring. I checked the active
  [random clause](SAP/P021/Defs/WholeW1.lean:19),
  [deterministic clause](SAP/P021/Defs/WholeW1.lean:31), and
  [Challenge docstring](SAP/P021/Challenge/Part1.lean:13): none requires nonempty
  samples at every stage. I also checked both existing project corollaries and the
  empty-sample probability theorem cited above. The reviewer is right.
  [The corrected docstring](SAP/P021/Defs/Part2.lean:24) now reads: “Equation (1),
  extended by zero on an empty sample. The T2 consistency statement allows empty
  samples at finite stages.” Definition bodies, theorem statements, proof terms,
  fully qualified theorem names, and both whole decisions are unchanged.
- **SAP.P021.T1 / P021-T1 — faithful, no finding.** Its statement and documentation
  require no correction.

The shared `vhEstimator` documentation changed, so **T2 is affected for renewed
declaration review**. T1 does not depend on `vhEstimator`. Removing comments from
all 10 SAP Lean sources gives identical hashes before and after this revision;
only the estimator docstring changed. The comparison is recorded in
[review-round1-checks.json](scratch/P021/review-round1-checks.json).
