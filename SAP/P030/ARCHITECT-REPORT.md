P030: **10 whole, 4 restricted, 1 refuted, 0 omitted**. All 15 Challenge theorems
have compiled Solution proofs. There are **0 open glue tasks**.

The restricted targets are:

- **P030-T2**: retain the genuine no-effect ten-unit experiment, its actual
  conditional law, distance vectors, positive rank variances, exact correlations,
  strict order, rounding, inclusive tails, printed size 1/2 and corrected size zero
  for the stated levels. Omit the explicit midrank and centered-rank vectors,
  centered cross-product values, exact distance rank-square sums, and rational
  squared-correlation computations and comparisons. The outcome rank-square sum
  9/2 is retained.
- **P030-T5**: retain the same genuine experiment and conditional law, all three
  distinct exact correlations, definedness, the differing actual statistics,
  observed p = 1/3, and the general constant-statistic p = 1 implication. Omit
  the explicit midrank and centered-rank vectors, centered cross-product values,
  exact distance rank-square sums, and rational squared-correlation computations
  and comparisons. The outcome rank-square sum 9/2, strict order, and rounding
  are retained.
- **P030-T8**: retain all three counterexamples: the wrong table values under
  both moment divisors, reversal of a correlation ordering, and weak monotonicity
  without perfect correlation. Omit the explicit midrank and centered-rank
  vectors, centered cross-product values, exact observed distance rank-square
  sum, individual covariance and variance values under the two divisors, and
  rational squared-correlation computations and comparisons. Positive rank
  variances, exact correlations, rounding, all six wrong values under each
  divisor, strict ordering reversal, and both rank-square sums of the weakly
  monotone example are retained.
- **P030-T14**: omit only the parenthetical explicit outcome midrank vector
  (3/2, 4, 3, 3/2). Retain every other part of (a)-(g), including the actual
  adjacency outcome model, observed outcomes, conditional design and masses,
  all six distances and exact correlations with rounding, the two-assignment
  lower-tail count, the actual observed-data p = 1/3 with rounding, and negativity.

No target is omitted. P030-T4 is the refuted positive universal exactness claim.
T1, T2, T5, and T8 are already counterexample targets, so they are classified as
whole or restricted rather than as refuted positive assertions.

The route is shared Mathlib-only SAP definitions, in six Defs parts. Both the
Challenge and Solution import these same compiled definitions. Challenge imports
no project modules. Its 15 declarations and Solution's 15 declarations use the
same fully qualified names and the same statement definitions.

Bridge Part1 preserves every field of the SAP finite law in `toLaw`.
Probability, lower and upper tails, and the uniform law agree by reflexivity.
The remaining 59 correspondences, covering assignments, nulls, statistics,
midranks, the concrete designs, the printed assertion, inverse-square effects,
exposure, and the fixed-size objective, are also proved by reflexivity.
Proof fields in the independently named definitions are handled by proof
irrelevance; the Comparator will see only the shared SAP definitions in theorem types.

Bridge Part2 assembles existing design and numerical certificates. It transports
the table entries to the definitionally identical actual statistics. Its only
additional concrete work is evaluating three fixed outcome entries, exhibiting
the explicitly treated variant unit in each small design, and applying the
existing positive-rank-variance theorem to two unequal entries in each ordering
example. These are definitional evaluation, structural transport, and arithmetic;
no new rank-counting or correlation argument is supplied.

The Solution uses instantiation, conjunction, definitional transport, and simple
linear or rational arithmetic on exported results. The T3 union-bound chain
composes the existing event monotonicity, union bound, and both tail-validity
results. The strict inclusion example in T3 is the proved T1 statement; T6's
nonconstant-statistic witness comes from T5. T9 includes its concrete weakly
monotone example from the T8 row and its table values and rounding from T14 rows.
Thus the generic corrected claims do not drop those cross-target clauses.
The manifest identifies these supporting declarations. Auxiliary rows already
subsumed by selected results are listed as not separately used.

The narrower `five_correlations` row is used only for its exact exported
rank-square sums and correlations. The separate `five_rank_certificate` supplies
the T1 rank vectors and centered products. Computations local to an existing
proof are not treated as exported conclusions; this motivates the restrictions.

All probability denominators have nonempty supports. The concrete Spearman
examples include positive rank-square certificates and nonempty treated-variant
sets. Conditional exposure means are used only in the feasible treatment branches,
with nonempty conditional supports explicitly certified. T10 represents the
undefined self quotient with `Option` and uses positive off-diagonal distances
for the corrected sums. Its pre-normalization scope follows the canonical
definitions, which explicitly exclude mean normalization from the formal content.
T7 states fixed-outcome variation as a logical witness of interference; it does
not assert infallibility of statistical rejection.

All Defs parts and root, Bridge parts and root, Challenge part and root, and
Solution compiled with the required `sap-lean` wrapper in dependency order.
Every theorem was checked with `#print axioms` in
[P030Axioms.lean](/home/ubuntu/sap/wt/ARCH-P030/scratch/P030Axioms.lean).
The [recorded output](/home/ubuntu/sap/wt/ARCH-P030/scratch/P030Axioms.txt) lists
exactly `propext`, `Classical.choice`, and `Quot.sound` for every theorem.
All package files meet the 300-line limit. The
[manifest](/home/ubuntu/sap/wt/ARCH-P030/SAP/P030/manifest.json) and
[Comparator configuration](/home/ubuntu/sap/wt/ARCH-P030/SAP/P030/comparator.json)
parse as JSON and cover exactly the 15 unit targets.

Three-kernel certification has **not been run**: no Comparator tool is exposed,
and the Comparator command names, `con-ron`, and `nanoda_bin` are not on PATH.
The supplied configuration is ready for the external Comparator; Lean compilation
and the dependency checks above are not reported as external kernel certification.

## Whole versions (new proofs)

P030-T2, P030-T5, P030-T8, and P030-T14 now use their proved whole statements.
The current totals are **14 whole, 0 restricted, 1 refuted, 0 omitted**. The
restrictions described earlier in this report are removed for these four targets.

All four declarations are switched in [Challenge/Part1.lean](SAP/P030/Challenge/Part1.lean)
and [Solution.lean](SAP/P030/Solution.lean), using the Mathlib-only whole statements
in [Defs/WholeW1.lean](SAP/P030/Defs/WholeW1.lean) and the proved finite leaves and
assemblies in [WH/W1/Leaves.lean](SAP/P030/WH/W1/Leaves.lean). The corresponding
[manifest entries](SAP/P030/manifest.json) record the whole statements and the
project declarations used by these proofs, including the rank-weight formula,
table-enumeration transport, and positive-divisor correlation theorem where used.

- **P030-T2**: `SAP.P030.T2WholeStatement`, proved by
  `SAP.P030.WH.W1.T2_whole` in [SAP/P030/WH/W1/Proofs/T2.lean](SAP/P030/WH/W1/Proofs/T2.lean).
  Old restriction now removed: Omit the explicit outcome and distance midrank and centered-rank vectors, centered cross-product values, exact distance rank-square sums, and rational squared-correlation computations and comparisons. Retain the genuine no-effect population, actual conditional design and point masses, explicit distance vectors, outcome rank-square sum 9/2, positive distance variances, exact correlations, strict order, rounding, inclusive tails, printed size 1/2 for 0 < alpha <= 2/3, and corrected size zero.

- **P030-T5**: `SAP.P030.T5WholeStatement`, proved by
  `SAP.P030.WH.W1.T5_whole` in [SAP/P030/WH/W1/Proofs/T5.lean](SAP/P030/WH/W1/Proofs/T5.lean).
  Old restriction now removed: Omit the explicit outcome and distance midrank and centered-rank vectors, centered cross-product values, exact distance rank-square sums, and rational squared-correlation computations and comparisons. Retain the genuine no-effect population and conditional design, explicit distance vectors, outcome rank-square sum 9/2, positive distance variances, all three exact correlations and their strict order and rounding, two distinct actual conditional statistics, observed p = 1/3, and the general constant-statistic p = 1 implication.

- **P030-T8**: `SAP.P030.T8WholeStatement`, proved by
  `SAP.P030.WH.W1.T8_whole` in [SAP/P030/WH/W1/Proofs/T8.lean](SAP/P030/WH/W1/Proofs/T8.lean).
  Old restriction now removed: Retain all three counterexamples. Omit their explicit midrank and centered-rank vectors, centered cross-product values, the exact observed distance rank-square sum, individual covariance and variance values under the population and sample divisors, and rational squared-correlation computations and comparisons. Retain positive rank variances, the correct exact table correlations and rounding, all six wrong printed-formula values under each divisor, divisor dependence, strict ordering reversal, and the nonperfect weakly monotone example with its exact correlation and two rank-square sums.

- **P030-T14**: `SAP.P030.T14WholeStatement`, proved by
  `SAP.P030.WH.W1.T14_whole` in [SAP/P030/WH/W1/Proofs/T14.lean](SAP/P030/WH/W1/Proofs/T14.lean).
  Old restriction now removed: Omit only the parenthetical explicit outcome midrank vector (3/2, 4, 3, 3/2). Retain every other part of clauses (a)-(g), including the actual adjacency outcome model, observed outcomes and nearest distances, conditional supports and masses, all six exact reference correlations and rounding, exactly two lower-tail assignments, the actual observed-data p = 1/3 and its printed rounding, and negativity of every reference value.

Validation: `python3 /home/ubuntu/sap/tools/rebuild_sap.py . P030` rebuilt all
19 P030 modules from scratch and passed the token scan. The scratch file
[P030SwitchedAxioms.lean](scratch/P030SwitchedAxioms.lean) imports
`SAP.P030.Solution` and runs `#print axioms` on all four switched theorems.
The [recorded output](scratch/P030SwitchedAxioms.txt) reports only `propext`,
`Classical.choice`, and `Quot.sound` for each theorem.
