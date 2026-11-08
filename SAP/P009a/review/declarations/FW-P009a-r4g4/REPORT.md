# Review of SAP.P009a.T16 and SAP.P009a.T17

Both declarations are **faithful**, with severity **none**. They were reviewed
separately against their complete statement closures. `reading.md` was saved
before opening the canonical claims; `claim-stage.json` was saved before opening
the architect's record. The record did not change either claim-stage judgment.

**T16.** `Challenge/Part2.lean:84–92` and
`Defs/WholeW1.lean:9–43` state the complete corrected display: every design,
both arms, positive sample size and positive k; termwise mixing domination
including the diagonal; the [0,1/4] bound; self-dependence and the dependence-sum
identity; both full-pair inequalities; and the equivalent off-diagonal formula
with Bernoulli diagonal variances restored. The additional covariance identity
and absolute-gap bound are valid strengthenings. The finite probability model,
full-cube interference relation and mixing coefficient match the paper's notions.
The `whole` decision and docstring are accurate.

**T17.** `Challenge/Part2.lean:94–105` and
`Defs/WholeW1.lean:226–277` include both specified counterexamples, the universal
self-excluding incoming-count identity, all six probability-table rows on
t=0,1,2, and the likelihood-ratio discrepancies. The `whole` decision correctly
describes full coverage of this canonical counterexample claim. The docstring
correctly identifies the printed probability laws and identity being refuted
and explicitly excludes Lemma A12's inequality.

The printed reading is: under complete randomization, with
C_i<=min(m,n-m), the count of treated other incoming interferers has the two
displayed hypergeometric laws with draw count C_i, and their displayed
ratio-minus-one identity holds on positive support. The witnesses pass every
condition: n=4,m=2=floor((1/2)n); uniform probability 1/6 on the six allowed
assignments; the exact full-cube outcome functions; incoming count 2 for the
first designated unit and 1 for each unit of the second example; self-excluding
treated counts; regularity with k=2,q=4,s=1; and positive conditioning and ratio
denominators. They therefore contradict the printed assertions themselves.

`scratch/Nonvacuity.lean` compiles independent concrete instances using only
`SAP.P009a.Defs`. It checks T16's hypotheses and a nonzero covariance of 1/4,
and constructs both T17 experiments with their normalization, outcome schedules,
fixed-size design, regularity, marginal probabilities and no-spillovers property.
`scratch/check_witness.py` exhaustively checks the full sixteen-point cube with
exact rational arithmetic, including the interference graphs, all probability
tables and both counterexample discrepancies. Its output is
`scratch/witness-check.json`. No reviewed Challenge theorem is used by these
checks. `scratch/ClosureCheck.lean` successfully prints the structure fields and
every generated proof declaration in the closures; the latter only support
numeric literals and introduce no hidden hypothesis.

No junk convention affects either statement. T16's supremum is nonempty and
bounded and its size denominators are positive. T17's conditional and ratio
denominators are positive; self-interference guarantees incomingCount>=1 before
natural subtraction by one; and every use of the numeric printed hypergeometric
formula has nonnegative subtraction arguments and a positive binomial
denominator. Although that helper's natural subtraction would give incorrect
out-of-support values in unrestricted uses, this declaration only evaluates it
within the explicitly stated ranges. All random objects are finite, so the
usual measure-theoretic conditions hold automatically.
