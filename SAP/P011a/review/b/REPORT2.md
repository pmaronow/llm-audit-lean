# P011a delta referee report

**14 targets: 2 correct_whole, 12 correct_restricted; 0 unresolved issues.**
All severities are `none`. No false, vacuous, not_faithful, restriction_inaccurate, or omitted targets.

The architect's revised decision counts are **1 whole, 10 restricted, 3 refuted**, all accepted.
The requested findings schema has no `correct_refuted` verdict. Accordingly T11 receives
`correct_whole` for its complete canonical counterexample, while T1 and T2 receive
`correct_restricted` for valid refutations with accurately disclosed exclusions. T14 is the
architect's sole `whole` target and receives `correct_whole`.

## Earlier findings

| Finding | Status | Verification |
| --- | --- | --- |
| My T1 finding: the α=0.05 decimal coverage evaluation was absent but undisclosed | **Fixed** | The revised Challenge docstring, lines 10–12, and `record2.json` expressly omit that evaluation while retaining the exact all-α formula. The new `refuted` label is justified by the actual cycle counterexample. |
| Other referee: T3, T4, T5, T6, T7, T8, T9, T12 impose additional observed-graph nesting | **Fixed by disclosure for all eight targets** | Each revised docstring and record states nondecreasing observed sizes and an injection preserving every adjacency Boolean at each step. This is exactly `Nested`, which remains a conjunct of `Scaling`. Existing exclusions for T4, T7 and T9 remain disclosed. |

For my own earlier finding: **1 fixed, 0 partly fixed, 0 not fixed**.

I agree with the other referee's nesting objection. My original `reading.md` described `Nested`
correctly, but my comparison with the canonical assumptions missed that it is additional:
S2 distinguishes the full graph from the observed induced graph, while S5 nests the full
graphs without requiring nested observed subsets. My previous whole verdicts for T3, T5,
T6, T8 and T12, and acceptance of the incomplete disclosures for T4, T7 and T9, were too broad.
The revised disclosures resolve that mismatch; the mathematical scope remains restricted.

Here is an independent example showing the distinction. Let the full graph at sample size n
be the matching consisting of the first n disjoint pairs, carrying independent fair signs.
These full graphs are induced nested. At odd n, observe one endpoint from each of the n pairs.
At even n, observe both endpoints of the first pair and one endpoint from n−2 other pairs.
There are exactly n observed vertices. The observed graph alternates between empty and one
edge. With θ=1 and actual full degrees d=1, all boundedness, dependency and positive-variance
conditions hold, with n Var(β̂)=1. An observed edge cannot embed into the following empty graph.
Thus the disclosed condition excludes actual canonical models and is a substantive restriction.

## Every changed label or disclosure

I reread all six Defs parts and the Challenge, comparing their mathematical content with the
saved blind `reading.md`. Every `T1Statement` through `T14Statement` and its component definitions
agrees with that reading. The detected changes concern labels and disclosures. No mathematical
statement change was found. No old source snapshot was retained, so this is a semantic comparison,
not an independent assertion of byte-for-byte identity.

| Target | Revised decision | Recheck |
| --- | --- | --- |
| T1 | refuted | The cycle law has scaled true variance 4, estimator limit 7/4, singleton compatibility, homoskedasticity, and strictly subnominal coverage. The sole excluded decimal evaluation is now disclosed. |
| T2 | refuted | At t=1 the scaled estimate tends to 19/15 against truth 29/15, with singleton compatibility and strict undercoverage; t=2 gives negative estimates with probability tending to one. All prior exclusions remain disclosed. |
| T3 | restricted | Exact observed induced-nesting premise disclosed; oracle bias expansion, iff criteria and finite clique assertions retain their previous content. |
| T4 | restricted | Exact observed induced-nesting premise added to the existing trace-condition/support exclusions. Deterministic matrices and the sign-matrix failure retain their meanings. |
| T5 | restricted | Exact observed induced-nesting premise disclosed for the general Scaling assertions. Finite PSD, correction, optimization and common-cap clauses remain intact. |
| T6 | restricted | Exact observed induced-nesting premise disclosed for general asymptotic conservativeness. Finite spectral, nearest-PSD, cycle and nonaffinity assertions remain intact. |
| T7 | restricted | Exact observed induced-nesting premise disclosed, alongside the prior clique-characterization and confidence-coverage exclusions. Supplied degree caps remain allowed to grow. |
| T8 | restricted | Exact observed induced-nesting premise disclosed. All corrected-class branches, equal-mean/clique sufficient cases, and the canonical cycle/path counterexamples remain. |
| T9 | restricted | Exact observed induced-nesting premise disclosed, alongside the prior OLS-example exclusions and explicit fitted-map measurability. Both prediction-error routes and the misspecified limit remain. |
| T11 | refuted | The auxiliary error tends to 1. Its absolute error is <3/2 with probability tending to 1, refuting the literal printed limit zero; it is >1/2 with probability tending to 1, refuting intended consistency. Proposition 2's one-sided assertion is preserved. |
| T12 | restricted | Exact observed induced-nesting premise disclosed. The finite moment/gap chain, tail bound and one-sided limit remain intact. |

T10, T13 and T14 retain their earlier scopes and decisions. T10's general-looking Scaling
clauses assert facts about the displayed fixed-mean/mixture families, rather than assuming
nesting to restrict an arbitrary family. The same distinction applies to the concrete families
in T1, T2 and T11. They need no additional nesting exclusion.

The sole architect `whole` decision, T14, still contains the certified LP bound and both variance
applications, the attained six-unit integer/fractional gap including doubled objectives and
variance values, the named integer witness, the inadequate-feasible-point example, and the
triangle gap. No canonical clause is newly dropped.

All 12 nonnull restriction texts match their Challenge docstrings after joining line-break
hyphens, and all three refutation docstrings begin with the stated declaration that the printed
claim is false. All theorem names and statement aliases match the revised record.

## Junk values, nonvacuity and checks

The concrete witnesses from `scratch/nonvacuity.md` remain valid. In particular the common
independent-sign family has n=k+1, β=0, covariance I, θ=1, empty graphs and zero caps.
It satisfies Scaling(1,1,1,2), Valid and homoskedasticity, with positive scaled variance 1.
An intercept-only design with true and fitted coefficient zero also satisfies both residual
prediction-error routes. All graph-maximizer premises have nonempty feasible sets.

Fresh Lean checks, importing only Defs, completed successfully:

- `scratch/DeltaCheck.lean`: proves `Nested` for the sign, alternating, arbitrary-parameter
  cycle and arbitrary-parameter path families; proves that a two-vertex edge cannot be
  induced-embedded into an empty three-vertex graph; and checks the negative cycle value −9/4.
- `scratch/RefutationChecks.lean`: proves that T1Statement and T2Statement imply the negation
  of universal printed oracle consistency. It also proves that T11Statement contradicts both
  readings of the auxiliary step. These are conditional logical entailment checks; they do
  not assume or inspect a Challenge/Solution proof of those statements.

Both were compiled with `/home/ubuntu/sap/tools/sap-lean`, exit code 0, with no diagnostics.
Their logs are `scratch/delta-lean-check.log` and `scratch/refutation-check.log`.

The source recheck retained every relevant guard: positive statistical sample sizes;
explicit zero-cap branches; finite probability laws and weighted moments under Scaling;
raw-coordinate integrability in MeanModel; measurable fitted maps; interior α for quantiles;
bounded bias and coverage sequences for real liminfs; symmetric spectral inputs; matching
feasibility before natural capacity subtraction; and positive rational denominator lcms.
The alternating auxiliary estimator has positive common variance and no edges, so its zero
correlation fallback supplies no spurious refutation. Coverage at t=1 in the path example
and at a=3/2 in the cycle example uses estimates positive with probability tending to one,
and therefore refutes the printed coverage reading as well as its clipped extension.

No changed label or disclosure introduces a new empty index, default integral, division by
zero, assumed conclusion, or incompatible hypothesis. The round-1 exact finite calculations
remain applicable to the unchanged mathematical content and were not claimed as new runs.

`findings2.json` contains all 14 targets using the original eight-field schema.
`scratch/delta-review.json` records the record-field changes, current source hashes, docstring
checks and successful Lean checks. The original reading and round-1 findings remain preserved.
No Solution, Comparator, external referee file, or path outside the permitted workspace and
Mathlib/tool locations was consulted.
