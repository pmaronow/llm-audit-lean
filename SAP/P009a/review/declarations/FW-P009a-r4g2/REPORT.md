# Review of SAP.P009a.T6–T10

All five declarations are **faithful**, with severity **none**. Each states the
whole canonical claim. The `whole` decisions and null restrictions in
`record.json` are accurate, and the Challenge and definition docstrings describe
their statements correctly. No step-2 conclusion changed after reading the
record.

`reading.md` was saved before opening `claims.json`; `claim-stage.json` was saved
before opening `record.json`. Every declaration in the five elaborated closures
was read, including the structures, their fields and constructors, and all 14
generated proof auxiliaries. The latter were printed in
`scratch/BlindCheck.lean`. Proposition bundles such as `LimsupFiniteFacts` are
expanded conclusions, not hypotheses granting the results under review.

| Declaration | Clause and definition checks |
| --- | --- |
| T6 | Strict sub-limsup selection; the exact displayed outcomes with lambda equal to the limsup; unchanged designs; dependence formula, outcome bounds, EATE and HT identities; zero outcomes elsewhere; uniform regularity and inconsistency are all present. |
| T7 | Both canonical fair Bernoulli schedules, every finite regularity order, both diagonal graphs, exact estimands and estimator moments, the two-point standardized law, the continuous-CDF distance bound, and failure of normal convergence are present. |
| T8 | All canonical assumptions, including q = 2, and the true-standard-deviation normal limit are present. The positive eventual variance floor expresses the positive-liminf condition without an unbounded-real-liminf convention. Bounded incoming sets and positive Bernoulli configuration probabilities give bounded outcomes, so q > 2 is unnecessary. |
| T9 | Every r >= 1, the exact full-cube schedule and uniform fixed-size design, all marginal/moment bounds, parent sets, graph counts, outgoing counts, support count identity, generated-mask events and mixing coefficient 1/4 are present. |
| T10 | Ordered zero-dependence pairs, eventual bounded average dependence, vanishing exceptional fraction, the remaining maximum limit and its uniform formulation, eventual nonempty domains, and necessity of exceptions are present. Auxiliary rates in the audit history are not extra canonical clauses. |

The paper's construction agrees with `subsequenceResponse` after changing from
one-based to zero-based unit indexing; the preprint contains that display in
its Proposition 1 proof. [Paper and proof appendix](https://arxiv.org/pdf/1711.06399#page=49).
The original normal-approximation sentence and all-pairs mixing sentence also
match the canonical excerpts. [Article, Sections 6.3 and 5.3](https://pmc.ncbi.nlm.nih.gov/articles/PMC8372033/).

The printed reading tested for T7 is: independent Bernoulli assignment,
Assumption 1, and bounded maximum dependence suffice for the HT error divided by
its true standard deviation to converge to the standard normal law. The
witnesses meet each condition: the mass is the fair product mass; absolute
outcomes are bounded by one, giving uniform regularity at every finite order;
and the maximum dependence is one. Variances are positive, equal to 1/n^2.
The standardized statistic is exactly 2Z1-1 for both schedules, so its fixed
two-point law contradicts this canonical assertion. No independence or
well-definedness condition is violated.

The printed reading tested for T9 is: under complete randomization and bounded
average dependence, every pair with zero interference dependence has mixing
tending to zero. The witness meets each condition: n=4r+2, exactly n/2 units
are treated uniformly, all marginals are 1/2, full-cube outcomes lie in [0,1],
regularity holds uniformly, average dependence is 3-4/n<3, and the fixed pair
has disjoint incoming sets. Its majority/minority events depend on the
respective masks and coincide on design support. Their probabilities and
intersection probability are 1/2, giving discrepancy 1/4 and hence mixing
exactly 1/4. Thus the refutation concerns the canonical assertion itself.

Independent Lean checks compiled with the supplied `sap-lean` command:

* `scratch/Check.lean`: `t6_nonvacuity` constructs a growing fair-design family
  with all outcomes Z1, assignment bound k=2 and dependence density one;
  `t7_nonvacuity` checks the sparse family's printed hypotheses and positive
  variance; `t8_nonvacuity` constructs the identity-outcome fair Bernoulli
  sequence satisfying every CLT hypothesis, including n Var(HT)=1.
* `scratch/Half.lean`: `t9_finite_nonvacuity` constructs the actual six-unit,
  three-treated uniform design and schedule, checks all marginals, zero
  dependence for the exceptional pair, and the event discrepancy 1/4.
* `scratch/Complete.lean`: `t10_nonvacuity` constructs a growing sequence of
  uniform one-treated complete designs with identity outcomes and average
  dependence one, satisfying every antecedent of T10's universal implication.
  A regular sequence with a nonvanishing exceptional pair is supplied by the
  T9 family, whose generic properties were checked mathematically.

The five named checks use only `propext`, `Classical.choice`, and `Quot.sound`;
their axiom lists contain no `sorryAx`. Exact rational enumeration in
`scratch/finite_checks.py` additionally checks T6 for sizes 1–7 under both fair
and dependent designs, both T7 families and the T8 variance model for sizes
1–7, T9 for r=1,2, and singleton mixing under complete designs for sizes 2–9.
These finite computations support the witness arithmetic; they are not proofs
of the asymptotic conclusions. The elementary T6 nonattainment witness is
a_t=1-1/(t+1), which tends to one while remaining strictly below it.

All expectations in the claims are finite sums of real values. Arm and size
denominators are positive where used. T6's real limsup is bounded and its root
and ceiling have positive arguments. T7's standardizations and CDF suprema
have ordinary domains. T8 explicitly permits arbitrary initial zero-variance
values. T9's natural subtraction is guarded by the fixed-total support
identity. T10 permits initial empty pair sets but proves both relevant domains
eventually nonempty. None of the conclusions exploits a junk value.
