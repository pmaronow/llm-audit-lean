All five declarations are faithful, with severity `none`.

The blind reading was saved in [reading.md](reading.md) before opening the
claims or record. Every declaration listed in the five closures was read,
including the two generated numeral-instance proofs, which were printed using
Lean. [claim-stage.json](claim-stage.json) records the independent comparison
against the canonical statements and definitions. Reading `record.json`
required no change to those conclusions.

| Declaration | Record decision | Assessment |
| --- | --- | --- |
| `SAP.P005b.T20` | `refuted` | Correctly affirms the valid exact part and refutes both the printed third-component sign identity and the literal logarithm-condition expansion. |
| `SAP.P005b.T21` | `whole` | Covers exact unbiasedness, the inverse-free expression, OLS identification, both population component expectations, and all stated proof identities. |
| `SAP.P005b.T22` | `whole` | Covers both unbiasedness conclusions, the inverse-free identity, and both armwise expectations under the main and weaker centered-covariate hypotheses. |
| `SAP.P005b.T23` | `whole` | Covers the slope and bias decompositions, equations (5) and (6), the covariance interpretation, and both vanishing consequences. |
| `SAP.P005b.T24` | `whole` | Covers both arm-slope decompositions, the bias expression, and the separate first-component expectations and their difference. |

Each declaration was compared separately against every clause of its canonical
statement. The definitions use uniform complete randomization, actual finite
means and covariances, and the printed regression coefficients. The all-assignment
nonsingularity hypotheses are the paper's standing assumptions. The only extra
arm-size guards in T21 apply to expressions (11) and (12), which themselves divide
by arm size minus one. The main unbiasedness statements and population component
moments still cover every nonempty arm. The docstrings accurately describe their
statements, and the record decisions are correct.

The scratch file [Nonvacuity.lean](scratch/Nonvacuity.lean) compiled successfully
with `/home/ubuntu/sap/tools/sap-lean scratch/Nonvacuity.lean`. Its examples use
definitions alone. They construct positive-dimensional populations with
nonconstant outcomes and verify standardization and nonsingularity on every
assignment. They also check a singleton treatment arm for T21, centered but
unstandardized data for T22, a balanced additive-effect model for T23, and the
legitimate dimension-zero, n=2 boundary of T24.

For T20, the compiled finite witness has n=5, d=1, m=2,
x=(-3/2,-1/2,0,1/2,3/2), yT=x² and yC=0. Its actual third-component expectation
difference is 21/320; the printed right side is -21/320. Both arm covariance
matrices are nonsingular under all ten assignments. For the asymptotic clause,
[counterexamples.md](scratch/counterexamples.md) gives the printed reading,
lists every condition, and checks an explicit one-dimensional sequence: the
remainder grows at least as n²-3 on an event of probability at least one half,
while the proposed rate is at most n^(-1/2). This sequence satisfies the moment,
standardization, assignment, invertibility, and literal logarithm conditions.
That sequence argument was checked mathematically; it was not compiled in Lean.
Both refutations therefore contradict canonical assertions under their printed
conditions.

No conclusion relies on division by zero, a singular-matrix inverse, an empty
design, or an out-of-domain analytic value. In T20, log(1)=0 is an ordinary
in-domain value. Supremum and square-root conventions at finitely many initial
sizes cannot affect its asymptotic assertion. `findings.json` contains exactly
the five requested entries and preserves their closure fingerprints.
