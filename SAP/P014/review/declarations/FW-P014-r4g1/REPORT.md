All five declarations are faithful. T2, T8, T3, and T7 correctly receive
`whole`; T4 correctly receives `refuted`. Their docstrings describe their
statements accurately, and no restriction needs to be added.

The review followed the required order: `reading.md` was saved before either
metadata file was opened; `claim-stage.json` was saved before `record.json`
was opened. Every declaration in each supplied closure was read, including
the generated numeral-bound proofs printed in `scratch/BlindCheck.lean`.
No claim-stage conclusion changed after reading the record.

| Declaration | Main fidelity check |
| --- | --- |
| `SAP.P014.T2` | The actual finite binary assignment law is constructed from an arbitrary measurable random vector on a probability space. Both the assignment-law result and the score-law application are included, together with genuine conditional expectations, positive denominators, all four derivation steps, and unrestricted outside dependence. |
| `SAP.P014.T8` | The finite-sum identity brackets the whole difference and divides both sums by the same nonzero window size. Its arbitrary real entries cover both averaging definitions. |
| `SAP.P014.T3` | All five canonical parts are included: conditional uniformity, full-support uniformity as sufficient, fixed-outside assignment counting and masses, no interference, and necessity when equality holds for every outcome function. Finite assignment laws represent arbitrary laws of finite binary vectors. |
| `SAP.P014.T7` | The empty-window equivalence, diagonal obstruction, off-diagonal decomposition, local-randomization consequence, and all three example laws are included. Distinctness refers to subject indices. |
| `SAP.P014.T4` | Its explicit witness contradicts the canonical unbiasedness assertion itself under standing assumption R6. It satisfies both the formal local clauses and uniform local permutations, with positive arms; the expectation is 0 and the unweighted target is −1/18. |

The totalized definitions do not manufacture any substantive conclusion.
Relevant arm probabilities and counts are positive, probability measures keep
`toReal` away from infinity, finite-state measurable outcomes are integrable,
and factorial/binomial denominators are positive in the asserted ranges.
The only substantive empty-window case is T7's expressly intended equivalence.

Lean validation passed using `sap-lean`:

- `scratch/Nonvacuity.lean`: a probability measure on two equally likely
  outcomes, two distinct window scores, fixed interior count, common
  propensities, the exact assignment-law correspondence, conditional/full
  uniformity, no interference, equality for every outcome array in T3(e),
  a nonzero T8 instance, and the diagonal/distinct-pair probabilities in T7.
- `scratch/Counterexample.lean`: the complete T4 statement rebuilt from
  definitions without importing a Challenge stub, plus the remaining two
  finite no-ties examples. Exact rational arithmetic independently confirmed
  T4's four assignment masses and both targets.

T4's `different` entry in `claim-stage.json` records that it disproves the
canonical assertion; this agrees with the record's `refuted` decision.
T2's provenance notes about an omitted score application are stale: its
elaborated statement includes that application. Those notes do not change
the correct `whole` decision or introduce a restriction.
