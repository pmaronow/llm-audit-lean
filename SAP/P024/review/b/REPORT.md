Audited eight targets: seven theorem stubs and one omitted target.

| Verdict | Count |
| --- | ---: |
| correct_whole | 3 |
| correct_restricted | 3 |
| restriction_inaccurate | 1 |
| not_faithful | 0 |
| vacuous | 0 |
| false | 0 |
| omission_ok | 1 |
| omission_questionable | 0 |

Severity counts: seven none, one minor, zero major.

**P024-T8 — restriction_inaccurate, minor.** The theorem is mathematically
sound and covers the mandatory canonical claim, but its declared restriction
misstates the difference from that claim. The canonical formal reading in
[claims.json](/home/ubuntu/sap/tasks/CHFID-P024-b/claims.json),
`P024-T8.canonical_claim.note`, already assumes a uniform fixed count
`1 <= m_b <= N_b-1` within each block and the resulting probability
`m_b/N_b`. The [docstring](/home/ubuntu/sap/tasks/CHFID-P024-b/SAP/P024/Challenge/Part1.lean:48)
and record entry describe those assumptions as additions and describe variable
counts and unequal propensities as omissions. Those alternatives are absent
from the canonical formal reading. The theorem actually retains its identity
and both unbiasedness conclusions while allowing more joint laws: fixed
counts and actual common marginals suffice without within-block uniformity.
The pooled-bias illustration is explicitly optional in the claim.

The correction is documentary: retain the theorem, mark T8 `whole` in the
record, and replace the restriction paragraph with an accurate scope statement.
The complete replacement docstring is in
[findings.json](/home/ubuntu/sap/tasks/CHFID-P024-b/findings.json).
For a concrete example of the extra generality, four units may receive the
treated set `{0,1}` or `{2,3}`, each with probability 1/2. The treated count
is always two and every marginal is 1/2, although the six two-subsets are
not jointly uniform. The theorem's identity and unbiasedness still hold.

The other record decisions agree with the claim-stage assessment. T5 accurately
discloses the omitted finite-sample bias remark and the failure-without-no-dominance
cross-reference. T6 accurately discloses its fixed-count restriction, including
counts on zero-mass assignments, and omission of Bernoulli assignment conditional
on nonempty arms. T7 accurately discloses replacement of the general event-mass
formula by positivity. T3 has `no_lean=true`; its intended-meaning and design
comparison questions do not specify an additional mathematical proposition.
T1 and T2 already address its precise necessity reading and before-after caution.
No step-2 verdict was changed after reading the record.

The blind reading was saved in
[reading.md](/home/ubuntu/sap/tasks/CHFID-P024-b/reading.md) before opening the
claims; [claim-stage.json](/home/ubuntu/sap/tasks/CHFID-P024-b/claim-stage.json)
was saved before opening the record. Definitions were followed through finite
sums, products, filters and cardinalities, real division, nonempty finite maxima,
and the ordinary real sequence limit in Mathlib. No theorem relies on division
by zero, truncated subtraction, an empty indexing type, an unnormalized
conditional expectation, or a hypothesis assuming its conclusion. The observed
potential-outcome branches and individual population weights match the canonical
renderings. The counterexamples refute the readings specified in the claims;
they do not decide which informal reading the paper's authors intended.

Verification used the supplied `sap-lean` wrapper, with one Lean process at a
time and no `lake` command. [scratch/Check.lean](/home/ubuntu/sap/tasks/CHFID-P024-b/scratch/Check.lean)
compiles while importing only `SAP.P024.Defs`, with no Challenge import or admitted
target used. It verifies nonempty overlap, fixed counts and actual marginals,
correlated blocked assignments, and a full bounded equal-cluster sequence with
maximum share `1/(k+2) -> 0`. A separate inspection confirmed the imported core
definitions used in these checks. The individual examples establish satisfiable
hypotheses; the universal statements were assessed mathematically by linearity,
finite rank counting, conditional exchangeability, and weighted variance/ratio
bounds. In particular, if `M=max_j w_j` and `S=sum_j w_j^2`, then
`M^2 <= S <= M`; for T5 both permitted designs bound the relevant normalized-total
variances by a constant times S, giving consistency with probabilities bounded
away from zero and one. Arbitrary empty-arm extensions are confined to an event
whose probability tends to zero.

[scratch/check_arithmetic.py](/home/ubuntu/sap/tasks/CHFID-P024-b/scratch/check_arithmetic.py)
passes exact rational checks for the timing values and variance, all dominant-cluster
allocations for K=2 through 10, conditional equal-size examples for K=2 through 7
at four interior probabilities, the unequal-size bias witness, and the canonical
16-allocation blocked example. Its results are saved in
[scratch/arithmetic-results.json](/home/ubuntu/sap/tasks/CHFID-P024-b/scratch/arithmetic-results.json).
