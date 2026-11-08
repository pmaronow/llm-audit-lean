# Review of SAP.P013a.T6–T10

All five declarations are **faithful**, with severity **none**. Their `whole` decisions and docstrings accurately describe the statements. No step-2 conclusion was changed after reading the record.

`reading.md` was saved before opening the claims; `claim-stage.json` was saved before opening the record. I read every closure entry: 116 distinct dependencies, including 26 generated auxiliary declarations printed in `scratch/ClosurePrint.log`. Those auxiliaries supply typing, normalization, positivity or nonnegativity proofs, without substantive hidden assumptions. I also checked the corresponding dependency definition, proof passages and Table 2 in the [paper](https://arxiv.org/pdf/1305.6156); the preprint pagination differs from the journal pagination in the claims.

- **T6:** The corrected antecedent checks crossing edges in both directions and requires independence of whole exposure vectors. The diagonal-plus-symmetrization indicator, both count bounds, and Condition 5 ⇒ Condition 4 are present. The directed formulation preserves the claim's generality.
- **T7:** The specified construction includes every canonical finite identity, endpoint bound, nonconvergence assertion and subsequential limit. Its `whole` label correctly describes a theorem establishing the canonical counterexample.
- **T8:** All four canonical parts are present. Its quantification over arbitrary finite statistics generalizes the HT setting, which is why step 2 records `broader`; specialization recovers the entire canonical claim. It adds no pointwise positivity assumption on the estimated variance. The explicit zero extensions have no effect on the limiting law.
- **T9:** Both means, their contrast, the corrected coverage target, the positive-variance identity and the fixed-total simulation guidance are included. The simulation law contains independent draws and the signed-outcome cancellation factor. The lower-tail assumption belongs to the corrected coverage result referenced by the claim.
- **T10:** Both exact printed triples and the specified closed rounding bins are represented. Each estimate bin is separated from its possible endpoint-midpoint bin by exactly 0.001. Standard errors impose no further requirement on this impossibility claim.

For T7, the printed reading being contradicted is: under the stated randomization assumptions, conservative scaled variance estimation and vanishing variance of that scaled estimate guarantee a single scaled-estimate limit, a single variance-ratio limit and a limiting studentized normal law. The witness meets every relevant condition:

| Condition | Witness check |
|---|---|
| Fixed nested population; Conditions 1–2 | One outcome table on positive integers; observations select the assigned exposure's outcome. |
| Positivity and Condition 3 | Both marginals are 1/2; outcome bound 2 and reciprocal bound 2. |
| Local dependence | Independent fair coordinates; a genuine symmetric identity graph with row bound 1. |
| Joint-probability regularity | Every distinct-unit joint probability is 1/4. |
| Condition 6 and true-variance CLT | `N V_N = 4`; the standardized error is a normalized Rademacher sum. |
| Conservativeness and concentration | `E W_N = 4 + 4 b_N/N ≥ 4`, and `Var(W_N) ≤ 64/N → 0`. |
| Defined studentization | The first block guarantees a strictly positive estimated variance at every assignment. |

Odd/even endpoints yield scaled-estimate limits 4 and 8, ratio-square-root limits 1 and 1/√2, and normal variances 1 and ½. These contradict the asserted single limits. T7 makes no claim that this witness disproves the coverage conclusion.

`/home/ubuntu/sap/tools/sap-lean scratch/Check.lean` completed successfully. It constructs the sequence hypotheses together, exercises T8's finite-mean branch, and checks simulation and rounding instances. Global block independence/CLT facts are reused from certified T7; these are nonvacuity checks, not independent reproving of the audited theorems. Independent exact-rational enumeration checks all assignments for `N=1,...,10`, reproducing `E W_8 = 6` and `Var(W_8) = 4`, plus 32,768 directed-graph/subset cases. Results are in `scratch/finite-results.json`.

No result relies on an empty infimum, zero marginal, undefined moment, unbounded real lower limit or accidental square-root/logarithm convention. The zero-joint terms implement omission of impossible pairs. JSON structure, target uniqueness and fingerprints were checked with Python.
