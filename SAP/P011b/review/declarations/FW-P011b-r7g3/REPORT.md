All four reviewed declarations are faithful, with severity **none**. Every entry
in their supplied dependency closures was reviewed. `reading.md` was saved before
opening `claims.json`; `claim-stage.json` was saved before opening `record.json`.
The record required no change to the independent claim-stage conclusions.

| Declaration | Canonical coverage and record decision |
|---|---|
| `SAP.P011b.T25` | Whole: all five clauses, including exact discrepancies, strict and non-strict ordering, both maximizer equivalences, the bounded-data inequality and all three corrected formulas. |
| `SAP.P011b.T26` | Properly refuted: all canonical witnesses are stated and the quoted exact-calculation assertion itself is contradicted. |
| `SAP.P011b.T27` | Whole: compatible-set finiteness and nonemptiness, generic maximizer existence, sharp oracle comparison, matrix programs and the complete binary-edge reduction. The included `T22Statement` supplies the edge correspondence, count and unit-weight specialization. |
| `SAP.P011b.T28` | Whole: both inequalities and the sufficient equality condition at every truncated degree cap, with exactly the attached hypotheses. |

For T26, the printed reading is: on admissible input data the staged helpers
calculate exactly the paper's formulas (3.1) and (3.7). Its independent uniform
three-point family satisfies the dependency, valid-degree, nestedness,
boundedness, nondegenerate variance and homoskedasticity conditions. With unit
weights, the sample `(0,1,2)` occurs with probability `1/27`; the paper values are
`2/9` while the helper values are `1/3`. The reading and condition-by-condition
witness audit were written before reading the record, in
`scratch/ClaimChecks.md`. The other two exact examples and all their canonical
auxiliary computations are included as well.

The definitions have the prescribed normalizations, ordered double sums, simple
graphs, compatibility conditions and truncated caps. No conclusion is obtained
from an undefined quantity, default integral or infinite measure converted to
zero. The hypotheses are jointly satisfiable. The docstrings correctly describe
their statements, and the three `whole` labels and one `refuted` label are correct.

Validation: `/home/ubuntu/sap/tools/sap-lean scratch/Check.lean` completed with exit
code 0. It imports only `SAP.P011b.Defs` and independently checks the algebraic
counterexamples and their positive-probability sample, and constructs instances
for T25, T27 and every T28 hypothesis. The T28 instance has a strict upper bound
(`2/9 < 10/27`), so saturation is not silently assumed. The all-size family
conditions were also checked directly as finite product-law facts. No `lake`
command was used. `findings.json` and `claim-stage.json` were parsed and checked
for exactly one entry per assigned declaration and matching identifiers; all
findings fingerprints match `closure.json`.
