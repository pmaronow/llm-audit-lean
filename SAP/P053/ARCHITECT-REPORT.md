P053 packages all eight unit targets in `SAP/P053/`.

| Decision | Count |
|---|---:|
| whole | 6 |
| restricted | 2 |
| refuted | 0 |
| omitted | 0 |

All eight Solution theorems are proved. There are no open glue tasks.

The whole targets are T1, T3, T4, T5, T7 and T8. T1 retains all five canonical
clauses, including the explicit factor common to all outcome vectors with the
same total successes, ordered symmetric samples and their converse, and the
exact factorization criterion. T3 retains both finite examples, the complete
six-unit distribution, both sets of p-values and monotone invariance. T5 and T7
retain their expansions and every stated probability limit. T8 retains the
bound, constant-effect agreement, standard-deviation equalities, the explicit
heterogeneous sequence, all its specified finite formulas and all three
numerical limiting coefficients.

The restricted targets are:

- **P053-T2:** Both labelled and covariate counterexamples are retained, at four
  units and at every positive repeated block size, together with both failures
  of factorization. The repeated family has diverging sizes, allocation and
  success-fraction limits, and a uniform raw fourth-moment bound. The statement
  does not assert a full S5 regularity certificate or the repeated family's
  potential-outcome/effect variance and average-effect limits. The credited
  scaling declaration exports only the listed asymptotic checks. The review's
  proposed direct calculation of the remaining moments is not an exported
  result and was not added as a proof. This conservatively restricts the
  standing-regularity assertion while preserving every concrete counterexample.
- **P053-T6:** The variance comparisons, constant-effect approximations and
  sharp-null normal Wald limit and nominal rejection probability are retained.
  The Introduction's equivalence of FRT and Wald tests under local alternatives
  is dropped: the credited results do not compare conditional FRT distributions,
  quantiles, p-values or rejection rules. In addition, the ratio and studentized
  conclusions require eventual positivity of the OLS variance at every supported
  assignment. This added hypothesis excludes division by a zero estimated
  variance or its square root. The unstudentized variance conclusions have no
  added positivity hypothesis.

No target is omitted. T2 concerns the canonical counterexample to an unrestricted
reading of the guidance, so its decision is `restricted`, not `refuted`. Its
docstring identifies that reading and distinguishes the corrected table-statistic
claim. The interpretive power/optimality prose excluded by `definitions_needed`
is not asserted in T4, T5 or T8.

The route is shared SAP definitions plus a structural Bridge. Seven Defs parts
import only Mathlib and earlier Defs parts. Challenge imports only those shared
definitions. Solution imports the project declarations and never imports
Challenge. The project sources and pre-existing files were not edited.

`Bridge.toPopulation` preserves both arm sizes and both outcome vectors.
`toRegularity` and `fromRegularity` construct records from the identical ten S5
fields; there is no estimator-consistency or central-limit assumption in these
records. The named agreements for support, binary differences, ordered samples,
randomization probabilities, estimates, all three variance estimates and the
heterogeneous witness are each proved by reflexivity. All other transport in
Solution is definitional conversion through these adapters. The only additional
steps are conjunctions, instantiation, existing sample-cardinality certificates,
congruence of squaring for T7's standard-deviation inequality, and congruence of
square root and its value at zero for T8. No new statistical argument was used.

The narrower row `table_statistic_factors` is not used. T1 instead uses
`explicit_table_factor` to export the required dependence on the total alone.
Every credited row is accounted for in the manifest, including unused
auxiliaries. T3 additionally uses T2's existing support-cardinality fact.

Domain checks: positive arm sizes are explicit in the binary and real-outcome
finite claims; repeated examples require a positive block count. S5 regularity
requires both arms to have at least two units eventually, so all sample-variance
and pooled-variance divisors are valid in the asymptotic tail. A finite initial
prefix is irrelevant to the stated limits. `PositiveOLS` separately excludes
zero studentizing denominators in that tail. Normal critical values occur only
for levels strictly between zero and one; the project already proves the
corresponding Gaussian quantile identities. Gaussian masses are finite.

Validation: all Defs parts and root, Bridge, Challenge part and root, Solution,
and `scratch/P053Axioms.lean` compiled with the supplied `sap-lean` wrapper.
All eight assumption reports contain exactly `propext`, `Classical.choice` and
`Quot.sound`; the output is saved in `scratch/P053Axioms.log`. Both JSON files
parse; target/row inventories, theorem names, shared statement references,
import restrictions, required options and the 300-line limit were checked.

`comparator.json` contains all eight proved theorems and the requested external
kernel commands. Palomar and the external kernels were not run in this session;
their executables were not available on PATH. Compilation and assumption checks
are complete; no independent three-kernel certification is claimed here.

## Whole versions (new proofs)

- **P053-T2 (`SAP.P053.T2`)** now states `SAP.P053.T2WholeStatement` in
  `SAP/P053/Challenge/Part1.lean` and `SAP/P053/Solution.lean`, with the supplied
  docstring on the Challenge stub. Solution uses `SAP.P053.WH.W1.T2_whole` from
  `SAP/P053/WH/W1/Proofs/T2.lean`; its blueprint and proved leaf are
  `SAP/P053/WH/W1/Leaves.lean` and `SAP/P053/WH/W1/P/T2_L1.lean`, and its statement
  is defined in `SAP/P053/Defs/WholeW1.lean`. `SAP/P053/manifest.json` records the
  whole decision and the new proof declarations.
  The removed restriction retained both four-unit counterexample statistics,
  every positive repeated block size, both nonfactorization assertions, diverging
  population sizes, allocation/success-fraction limits, and a uniform raw
  fourth-moment bound, but omitted the repeated family's full S5 regularity
  certificate and potential-outcome/effect variance and average-effect limits.
  The whole statement supplies these omitted conclusions, the exact repeated
  population moments, and probability `1/6` for each four-unit assignment.

No other Solution proof uses the switched theorem, so no dependent proof repair
was required. All other targets retain their statements, docstrings, proofs and
manifest entries. The preceding report describes the original packaging; after
this switch there are seven whole targets and one restricted target (P053-T6).

Validation: `python3 /home/ubuntu/sap/tools/rebuild_sap.py . P053` rebuilt all
19 modules from scratch and passed the token scan. `scratch/P053WholeAxioms.lean`
imports Solution and runs `#print axioms SAP.P053.T2`; its output in
`scratch/P053WholeAxioms.log` contains exactly `propext`, `Classical.choice` and
`Quot.sound`. Lean processes ran sequentially, and Lake was never run.
