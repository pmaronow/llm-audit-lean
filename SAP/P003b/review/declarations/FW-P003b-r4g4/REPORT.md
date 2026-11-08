# Declaration review

| Theorem | Verdict | Severity |
| --- | --- | --- |
| `SAP.P003b.T36` | faithful | none |
| `SAP.P003b.T18` | faithful | none |

The blind expansion is preserved in `reading.md`. All 105 distinct declarations
in the two closures, including generated auxiliaries, were read and printed
successfully in `scratch/Closure.txt`. `claim-stage.json` was saved before
opening `record.json`; the record supplied no reason to change either
claim-stage conclusion. Both `whole` decisions and both docstrings are accurate.

T36 states the claimed arithmetic complexity under the canonical cost model.
It establishes that the signed constant-size selector returns the actual
feasible minimum and that its direct reuse interval enumerates exactly the
legal updates. It covers the literal first-feasible-j schedule and the full-j
schedule, finite draw and update bounds, a nonnegative charged cost and its
explicit envelope, a uniform bound for every positive n,K, and both forms of
asymptotics, including fixed positive K. The cost coefficients represent the
paper's arithmetic charges; they do not purport to measure Lean's exhaustive
list evaluation or bit complexity. This interpretation agrees with the
[paper's arithmetic-cost discussion](https://arxiv.org/pdf/2305.09906).

T18 includes every part of the corrected canonical claim: the conditional
finite arithmetic, rounded recommended budget, fixed-tolerance operation and
draw rates, (1.6) envelope, general cost bound, both dyadic shuffle lower bounds,
the obstruction to every fixed linear-polylogarithmic expected bound, and both
conservative-budget comparisons. Its upper-bound premises match the canonical
conditional assertion. Its lower bounds concern the analyzed full-shuffle
implementation. They support the corrected claim rather than refuting it.

For clarity, the printed reading challenged by those lower bounds is: the
analyzed balanced full-shuffle algorithm, with fixed positive tolerance below
alpha and the recommended budget, uses O(n polylog(n)) arithmetic operations.
The witness meets its conditions:

| Condition | Check |
| --- | --- |
| Finite fixed binary population and genuine observed input | The all-zero table produces `(0,n/2,0,n/2)` under every balanced assignment. A concrete n=16 instance compiles. |
| Positive balanced arms | n=2^r, m=n/2, r>=4; the expected lower bound additionally assumes r>=6. |
| Valid parameters and sample size | alpha=1/2, epsilon=1/8, K>0; the expected bound uses exactly the canonical threshold. At the recommended K that threshold holds for the asymptotic family. |
| Independent uniform draws within and across tests | Probability is uniform on all assignment-valued pool functions, giving the product law. A support point with repeated realized draws is an event under this law. |
| Fresh batches in the lower-bound argument | All n/4+1 tests in the first query use different pool coordinates, before any modulo wrap. |
| Analyzed shuffle implementation | Each of the K draws in each performed test contributes n-1 iterations. The corrected bracket has the same first midpoint n/4 as the canonical witness. |

Boundary checks found no substantive reliance on junk values. Feasibility
guards prevent clipped coordinates; lower-bound sample sizes are positive;
pool spaces are nonempty; finite expectations exist; and logarithms and real
powers have their ordinary meanings in the finite comparisons or eventually
in the asymptotic statements. Fixed-tolerance statements fix epsilon outside
the big-O quantifiers, as the canonical claim requires.

`scratch/Check.lean` compiles successfully. It constructs positive-arm designs,
actual selected bases and reuse steps, total-n families, a nonzero instance of
every balanced upper-bound premise, and a positive-probability actual-search
witness at n=16,K=2 costing at least 150 shuffle iterations. It also proves
that the expected-cost threshold is satisfiable. These checks do not invoke
the audited theorems. The native computation used for the concrete trace is
identified in the axiom output in `scratch/Check.log`.

Validation commands: `/home/ubuntu/sap/tools/sap-lean scratch/Closure.lean`,
`/home/ubuntu/sap/tools/sap-lean scratch/Check.lean`, and Python JSON/schema and
fingerprint checks. No `lake` command was run and the Lean checks ran
sequentially.
