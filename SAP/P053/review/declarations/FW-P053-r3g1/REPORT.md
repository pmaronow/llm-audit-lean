# P053 statement review

All five declarations are **faithful**, with severity **none**. Each record
decision is `whole`, its restriction is null, and its docstring agrees with
the complete canonical claim. No step-2 conclusion changed after reading the
record. No source statement or definition was modified.

The order of review was preserved: the declarations and every supplied
closure entry were read first; `reading.md` was saved before opening
`claims.json`; `claim-stage.json` was saved and parsed before opening
`record.json`. Generated closure entries were inspected using Lean in
`scratch/ClosureCheck.lean`.

* **T1:** [Defs/Part3.lean:20](/home/ubuntu/sap/tasks/FW-P053-r3g1/SAP/P053/Defs/Part3.lean:20) contains every
  clause (a)-(e), including the factor common to all outcomes with the same
  total, both directions of the sample-symmetry statement, and the exact
  criterion. Integer floor only extends the factor outside its attainable
  image. Positive arms and valid success counts exclude harmful division or
  truncated subtraction. The compiled example has a nonconstant symmetric
  real statistic.
* **T2:** [Defs/WholeW1.lean:48](/home/ubuntu/sap/tasks/FW-P053-r3g1/SAP/P053/Defs/WholeW1.lean:48) supplies the
  complete finite and repeated counterexamples, the six masses, exact
  population moments, and full S5 certificate. Its `whole` label is correct:
  the canonical assertion is this counterexample to a specified reading,
  rather than the corrected table-statistic assertion. The docstring names
  the unrestricted reading precisely.
* **T3:** [Defs/Part4.lean:96](/home/ubuntu/sap/tasks/FW-P053-r3g1/SAP/P053/Defs/Part4.lean:96) includes all
  six-unit and four-unit cases and the universal strictly increasing
  transformation result. The upper tail includes ties and uses the full
  uniform design. Independent Lean proofs verify every stated p-value.
* **T4:** [Defs/Part4.lean:103](/home/ubuntu/sap/tasks/FW-P053-r3g1/SAP/P053/Defs/Part4.lean:103) has exactly
  the scalar domain, difference identity, and strict sign equivalence.
  Zero standard deviations and the balanced equality case are retained.
* **T5:** [Defs/Part5.lean:34](/home/ubuntu/sap/tasks/FW-P053-r3g1/SAP/P053/Defs/Part5.lean:34) states all
  three expansions and both scaled probability limits under S5. The Fisher
  formula, pooled OLS formula, finite-population variance divisor, and
  probability definitions agree with S4-S5. Eventual arm sizes follow from
  the divergent population size and interior allocation: eventually both
  arms exceed a fixed positive fraction of the total. No additional
  substantive assumption is present. An independently constructed sequence
  satisfies every S5 field with average effect one.

The reading tested for T2 is: for fixed binary sharp-null outcomes under
complete random assignment, every real statistic allowed to use labels and
fixed covariates factors through the difference in means on the whole
assignment support. Its conditions were checked individually:

| Condition | Witness check |
| --- | --- |
| Positive arm sizes | Two units per arm; `2m` per arm for `m>0`. |
| Binary outcomes and sharp null | Both potential outcomes are the same repeated zero-one vector. |
| Uniform complete assignment | All two-element subsets, or all `2m`-element subsets; the four-unit masses are `1/6`. |
| Supported witness assignments | A and B have the required size, and their repeated versions have size `2m`. |
| Admissible statistics and fixed covariates | The labelled indicator is `z_1*y_1`; the fixed covariate is `(1,0,1,0)` repeated by blocks. |
| One factor for the entire support | Equal difference-in-means values and unequal statistic values contradict that factor. |
| Standing asymptotic and usual measure conditions | Allocation `1/2`, variance limits `1/4`, zero effect limits, fourth-moment average one; finite discrete assignment spaces. |

The witnesses genuinely contradict that unrestricted reading. They do not
contradict the corrected claim concerning statistics of the table, and the
package does not describe them as doing so.

The following checks all exited successfully using the permitted `sap-lean`
command; at most two Lean processes ran together, and `lake` was never run:

* `scratch/ClosureCheck.lean`: every generated closure entry and the
  population/regularity structures.
* `scratch/Nonvacuity.lean`: a nonconstant symmetric T1 statistic, the T2
  counterexample and nonfactorizations, a positive repeated-block witness,
  the T3 count distributions and an admissible increasing transformation,
  both T4 sign cases and an equality case, and every field of a T5 S5
  instance.
* `scratch/PValues.lean`: full independent proofs of `SixInference` and
  `FourInference`, including the rejection distinction and all tied tails.

The substantive checks import definitions only and use no Challenge theorem.
No conclusion relies on a junk value. `findings.json` contains exactly the
five requested entries, with fingerprints copied from `closure.json`.
