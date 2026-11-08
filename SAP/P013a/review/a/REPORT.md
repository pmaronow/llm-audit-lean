Reviewed all 14 targets and their 14 Challenge theorem statements. All architect
decisions are justified by the visible statements. No correction is required.

| Verdict | Count |
| --- | ---: |
| correct_whole | 10 |
| correct_restricted | 4 |
| restriction_inaccurate | 0 |
| not_faithful | 0 |
| vacuous | 0 |
| false | 0 |
| omission_ok | 0 |
| omission_questionable | 0 |

There are no non-`correct_*` findings and no omitted targets. Severity is `none`
for every finding. Here `false` would mean a false submitted theorem, not a
printed assertion that the submitted theorem correctly refutes.

The blind mathematical reading was saved in `reading.md` before opening
`claims.json`; the comparison was saved in `claim-stage.json` before opening
`record.json`. No step-2 classification was subsequently changed.

P013-T12 remains `different` in the literal claim comparison: it negates the
printed positive assertions. The record explicitly declares `refuted`, and the
Challenge docstring discloses exactly this purpose. Its `correct_whole` final
verdict accepts that refutation decision; it does not certify Proposition 4.1
as printed. The nonzero-total signed example has relative bias 7/9, exceeding
both the printed 4/9 bound and the requested target 1/2, although R=1 satisfies
the logarithmic rule. This is a counterexample inside the meaningful domain of
the printed formulas. The correct numerical threshold is separately retained
in T4; T12 does not claim that threshold is false.

All four declared restrictions occur verbatim in the corresponding Challenge
docstrings and accurately describe the statement changes:

| Target | Disclosed scope |
| --- | --- |
| P013-T1 | Omits the decimal evaluation at alpha=0.05 and states the pair-row bound as at most 2. Retains the actual paired model, finite identities, exact limits, and strict undercoverage formula. |
| P013-T2 | Adds one common outcome table under injective exposure labels with fixed comparison labels to the coverage implication and both rate implications. Omits the separate centered-concentration conclusions after those rates and the final counterexample assertion. Both standalone concentration-to-lower-tail implications remain unrestricted. |
| P013-T8 | Adds strict positivity of every realized variance estimate, at every size, only to the final expectation-limit/studentization implication. The lower-tail and coverage conclusions retain their original premises, and negative variance estimates count as noncoverage. |
| P013-T9 | Retains treated-mean consistency and the positive-variance studentization identity. Adds the common-table setup to mean consistency. Omits explicit contrast consistency, the coverage assertion, and relative-bias guidance. |

The extra hypotheses are jointly satisfiable. For T2, T8 and T9, take N=n+1
independent fair binary exposures and the fixed table y(i,0)=y(i,1)=1.
Reindex the 2^N assignments by `Fin (2^N)` for `ExperimentSequence`. All
marginals equal 1/2, the identity graph gives genuine C5 with row bound 1,
and C4's pair density equals 1/N. The contrast has target 0, estimate
(2/N) sum_i(2Z_i-1), and V=Vhat=4/N at every assignment. Thus NV=4,
N Vhat=4, every lower-tail and centered-concentration condition holds, and
the standard Rademacher CLT supplies the required normal limit. Both rate
clauses allow b=1/4. The treated mean has variance 1/N. This example also
realizes T8's added global positivity and expectation limit with c=s=4.
Other target-specific witnesses are recorded in `findings.json`.

The definition review found no convention that creates an invalid result:

* Strictly positive weights summing to 1 exclude empty design spaces. The
  asymptotic sequences always have N=n+1>0. Empty-set clauses in the graph
  definitions do not supply the shared-exposure sequence counterexample.
* The fixed outcome table and observed-outcome definition correctly implement
  properly specified exposures and consistent observed outcomes. Independent
  product designs implement independent whole-design simulated draws.
* Every positive marginal and simulation denominator used as an ordinary
  inverse is nonzero. Relative-bias conclusions are guarded by nonzero totals.
  Attained minima satisfy 0<p0<1, so log(1-p0) is strictly negative.
* Zero-joint terms agree with the paper's omitted-term convention: a zero
  joint is a sum of nonnegative indicator products with strictly positive
  weights, forcing that product to vanish at every assignment. An explicit
  mixed-sign zero-joint instance has true variance 4, E(Q)=2, A=-2 and
  E(A2)=2, so the correction is substantive.
* The positive-joint minimum in T2 is conditional at an empty domain. Under
  its symmetric graph and uniform row bound m, N>m+1 gives a distinct
  nonadjacent pair; the positive marginals make its comparison joints
  positive. The domain is therefore nonempty eventually, so free early
  values of b_n do not establish the rate or lower-tail conclusions.
* Both real liminf expressions concern probabilities in [0,1]. Normal
  quantiles occur only for 0<alpha<1, where the defining set is nonempty and
  bounded below. Mathlib's Gaussian parameter is variance, including the
  distinct subsequential variances 1 and 1/2 in T7.
* T11's hypotheses force |U|>=40 and 1<=n<=|U|, making the binomial
  denominator positive and the relevant natural subtractions nonnegative.
  T7 uses positive unit indices with nonnegative offsets inside their
  defined blocks. T1's pair-score subtraction is signed integer subtraction.

`/home/ubuntu/sap/tools/sap-lean scratch/Check.lean` completed successfully.
That file imports only the definitions and checks signed-model positivity and
expectations, a zero-joint population and its nonzero variance, an all-positive
joint instance, a complete-randomization parameter instance, both rounding
contradictions, and signed pair scores. Its successful log is
`scratch/lean-check.log`.

`python3 scratch/exact_checks.py` also completed successfully. Exact rational
enumeration checked the paired model at N=4,6,8; the block model at
N=1,2,4,5,6,8; both signed replicate examples; a mixed-sign zero-joint model;
six additional nonuniform signed-outcome designs for T13 and T14; and sampling
boundary cases and both probability-bound branches for T11. Exact integer
comparisons verified that 10,593 replicates pass the printed numerical bound
and 10,592 fail. Results are in `scratch/exact-checks.json`.

The asymptotic readings are consistent with the bounded independent-pair CLT
in T1, the bounded-degree dependency-graph CLT and pair-term second-moment
rates in T2, and Chebyshev concentration and two distinct subsequential
Slutsky limits in T7 and T8. These conditions do not assume coverage or a
studentized limit as a premise.

The supplied canonical transcription controls the claim comparison. The
[paper PDF](https://arxiv.org/pdf/1305.6156) also corroborates the printed
dependency clauses and the two WLS triples; its pagination differs from the
journal pagination in the package. Mathlib definitions were checked directly
in the permitted source tree.
