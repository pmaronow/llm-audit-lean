P047: 3 targets; 2 whole, 1 restricted, 0 refuted, 0 omitted.
All 3 Challenge theorems have completed Solution proofs. There are 0 open glue tasks.

P047-T1 is whole. It includes the ATE conditional and unconditional means,
sample-average unbiasedness, contribution bound, exact exponential tail,
finite-sample coverage, deterministic endpoint width and exact root-n width
identity. It also includes the complete one-potential-outcome-mean component
under its weaker treated-arm assumptions. The latter estimator is defined
directly using the observed outcome.

P047-T2 is whole. It includes the limit of the supremum over all positive
sample sizes and laws sharing B and epsilon, the exact root-n exponential
tail bound, the variance upper bound, and the fixed-law normal limit,
including variance zero. A single supremum over the pairs of laws and
sample sizes represents the two suprema in the canonical claim.

P047-T3 is restricted. It retains the finite minimax error bound, failure
of uniform consistency, and the positive fixed-baseline interval-width
lower bound, including independent randomization, on the specified
uniform-covariate, binary-outcome model. It omits the explicit extension
to every containing model and a separate assertion that the concrete
baseline law belongs to that model. The completed credited theorem
states the quantitative bounds but does not separately state those two
clauses. The necessity of a restriction is expressed by the impossibility
bounds themselves; the canonical claim assigns no mathematical meaning
to testability or sufficiency. This is a positive impossibility result.

There are no omitted targets and no remaining proof tasks for the packaged
statements. All 70 credited rows are accounted for in the manifest; unused
supporting rows have individual reasons.

The shared-definition route is used. The three Defs parts import only
Mathlib and earlier Defs parts. Challenge and Solution import the same
compiled definitions, so their mathematical objects are identical.
The known-propensity results allow arbitrary real-covariate laws, which
includes the standing continuous-covariate setting.

The Bridge copies the fields of the SAP population structure to and from
the project structure. Both round trips are proved by cases and reflexivity.
Coordinate functions, identifying assumptions, sampling laws, ATE scores,
means, estimators, radii, intervals, the unknown model and the baseline
measure agree by reflexivity. The observed one-mean contribution and
estimator agree with their project counterparts by the credited
`armIPW_eq_observed` and `treatedEstimator_eq_observed_sum` identities.
The population suprema and infimum agree by set extensionality, using
the two field-copying adapters as existential witnesses in each direction.

T1 uses the two existing finite-sample aggregate theorems and the endpoint
width identity. Its remaining steps are conjunction, nonnegativity of the
radius, and division of the exported root-n width identity by positive
sqrt(n). T2 transports the existing asymptotic aggregate theorem. T3
transports the completed randomized impossibility theorem through the
supremum and infimum correspondences. The earlier unfinished impossibility
draft is not a dependency of any packaged theorem.

The positive B, epsilon and sample-size conditions guard all finite-sample
divisions. Bounded outcomes and overlap ensure genuine integrability and
finite score variance. The conditioning sigma algebra is the one generated
by the measurable covariate. The one-mean component adds no control-outcome
bound. Risk and coverage use bounded sets of probability values with the
same inserted 0 and 1 conventions as the project. T3 writes its width event
as lower endpoint plus 1/6 less than upper endpoint, avoiding subtraction
of infinite endpoints; for finite ordered endpoints this is the usual
width inequality.

Validation completed with the supplied `sap-lean` wrapper: all three Defs
parts, Defs root, Bridge, Challenge part and root, Solution, and
`scratch/P047Axioms.lean` compile. The three Solution dependency checks each
report exactly `propext`, `Classical.choice`, and `Quot.sound`. Both JSON
files parse and their target/theorem lists agree. Every authored SAP file
has at most 300 lines; the only proof placeholders are the three requested
Challenge stubs.

The comparator configuration requests both external kernels with the
specified commands. Palomar Comparator and those kernel executables were
not available on PATH, so no Comparator run or external-kernel certificate
was produced in this session.

## Whole versions (new proofs)

P047-T3 (`SAP.P047.T3`) is now whole, with type
`SAP.P047.T3WholeStatement.{u}` and proof
`SAP.P047.WH.W1.T3_whole`. This updates the earlier restricted-status account.

Files:

- `SAP/P047/Challenge/Part1.lean`: whole statement import, supplied docstring,
  and whole type; the Challenge stub remains `:= by sorry`.
- `SAP/P047/Solution.lean`: imports `SAP.P047.WH.W1.Proofs.T3` and uses the
  proved whole theorem directly.
- `SAP/P047/manifest.json`: records the whole decision, removed restriction,
  whole statement definition, proved status, and additional proof dependencies.
- Existing whole-proof sources: `SAP/P047/Defs/WholeW1.lean`,
  `SAP/P047/WH/W1/Helpers.lean`, `SAP/P047/WH/W1/Leaves.lean`,
  `SAP/P047/WH/W1/P/T3_L1.lean`, and `SAP/P047/WH/W1/Proofs/T3.lean`.

Old restriction now removed:

> Retains the finite minimax error bound, failure of uniform consistency, and the positive fixed-baseline interval-width lower bound, including independent randomization, on the specified uniform-covariate, binary-outcome model. Omits the explicit extension to every containing model and a separate assertion that the concrete baseline law belongs to that model. The necessity of a restriction is expressed by these impossibility bounds; the canonical claim gives no formal meaning to testability or sufficiency.

The whole proof identifies the concrete baseline as a member of the binary
model and extends the impossibility bounds to every containing model whose
mean effects exist. No other Solution proof uses `SAP.P047.T3`, so no
dependent-proof repairs were required.

Validation: `python3 /home/ubuntu/sap/tools/rebuild_sap.py . P047`
rebuilt all 13 modules from scratch and passed the forbidden-token scan.
`scratch/P047WholeAxioms.lean` imports `SAP.P047.Solution` and checks
`#print axioms SAP.P047.T3`; compilation reported exactly `propext`,
`Classical.choice`, and `Quot.sound`. All compilation was sequential,
with one Lean process at a time; no `lake` command was run.
The per-target result is recorded in `switched.json`.
