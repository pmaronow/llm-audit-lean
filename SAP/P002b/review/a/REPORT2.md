# P002b delta review

The two earlier findings are **fixed** under the remedies requested in round 1.
The revised package has no outstanding statement or scope-label finding.
It contains 14 Challenge theorems for 15 targets.

| Verdict | Count |
| --- | ---: |
| correct_whole | 11 |
| correct_restricted | 3 |
| restriction_inaccurate | 0 |
| not_faithful | 0 |
| vacuous | 0 |
| false | 0 |
| omission_ok | 1 |
| omission_questionable | 0 |
| **Total** | **15** |

All 15 severities are `none`. The two faithful refutations are counted as
`correct_whole` because the required findings schema has no separate refutation
verdict. The manifest's corresponding counts are 9 `whole`, 3 `restricted`,
2 `refuted`, and 1 `omitted`.

| Earlier finding | Status | Re-check |
| --- | --- | --- |
| P002-T26: an excluded descriptive sentence was incorrectly presented as a restriction | **fixed** | `record2.json` now says `whole`, its restriction is null, and the Challenge restriction sentence is gone. The mathematical proposition still contains every canonical algebraic clause (a)-(c). |
| P002-T28: omission relied on demanding the known erroneous Step 5 indexing, and no theorem covered the complete headline/no-intersection result | **fixed through an accurately restricted export** | A new T28 theorem uses the corrected recorded pairs, includes both covariate settings and the no-intersection branch, and discloses the remaining omission of termination for every prescribed admissible choice policy. This is the restricted-export remedy explicitly allowed by the earlier finding. |

For T28, universal policy termination remains unproved by the exported
statement. The earlier review finding is resolved by accurately narrowing the
claim, rather than by establishing that omitted assertion. Thus neither T22
nor T28 is relabelled whole.

The revised Defs and Challenge files were compared with the saved blind
[reading.md](/home/ubuntu/sap/tasks/CHFID-P002b-a/reading.md). The shared definitions
in Parts 1-4 and the 13 previously exported proposition types in Parts 5-6
retain their mathematical readings. T26 changes its docstring and decision,
without changing its proposition. The substantive addition is
[T28Statement](/home/ubuntu/sap/tasks/CHFID-P002b-a/SAP/P002b/Defs/Part7.lean:14),
imported by the Defs root and exposed as `SAP.P002b.T28` in the Challenge.
The architect's account of these scope changes agrees with the revised files.

The new T28 statement has the following precise reading. For every positive
simulation count M, observed quadratic Qf, family Qg indexed by `Fin M`, and
level 0<alpha<1, assume they arise from one actual observed dataset and its
simulated assignments, and assume everywhere-positive variance denominators
and nonnegative squared-statistic numerators for every curve. Put f=R_Qf and
g_m=R_Qg_m. Then all six assertions hold:

1. There exists a finite, strictly increasing list J containing exactly every
   crossing of two unequal simulated functions. Identical functions do not
   create crossings.
2. For every such complete list J, including an empty list, there exists an
   Algorithm 1/3 run. Its recorded gaps are exactly those determined by J,
   and its index choices are required to be critical only at the prescribed
   sample points.
3. Every Algorithm 1/3 run returns exactly the empirical confidence set.
4. For every nonempty complete J, there exists a completed finite corrected
   Algorithm 2/4 run.
5. Every completed corrected Algorithm 2/4 run returns exactly the empirical
   confidence set.
6. If a complete list J is empty, the empirical quantile-index set is nonempty
   at every real sample point. For every real sample point beta and every
   index m attaining the critical value there, the GLOBAL comparison set
   `{x : f(x) <= g_m(x)}` equals the empirical confidence set.

Here the returned set is the union of the recorded closed-interval comparison
pieces, and the empirical confidence set compares sqrt(f) with the empirical
quantile of the sqrt(g_m). The final clause quantifies over the full comparison
set in x; it does not merely certify the comparison at the chosen sample point.
For an empty J, `Algorithm1Run` uses the whole real line and sample zero, while
clause 6 also covers the paper's arbitrary sample-point choice.

This includes the required corrected indexing and no-intersection branch.
Both unadjusted and adjusted datasets are admitted through the existing
`DataGeneratedCoefficients` predicate. The extra full-rank conditions in its
adjusted branch are the domain of the paper's ordinary inverse formulas;
the centering condition is a standing assumption. Nonnegative numerator
conditions follow from squared contrasts for actual data and add no hidden
restriction. The sole lost assertion is termination for every prescribed
admissible Algorithm 2/4 selection policy, exactly as disclosed in the
[Challenge docstring](/home/ubuntu/sap/tasks/CHFID-P002b-a/SAP/P002b/Challenge/Part1.lean:54)
and [revised record](/home/ubuntu/sap/tasks/CHFID-P002b-a/record2.json:328).

T28 is mathematically credible on this domain: positive denominators make
the curves continuous; unequal ratios of quadratics meet at roots of a
nonzero polynomial of degree at most four, giving a finite crossing list.
Quantile ranks persist between crossings and at closed finite endpoints.
The absence of any crossings makes each selected quantile curve valid on
the whole line. The new statement includes list and run existence as
conclusions, so the correctness implications do not obtain their force only
from an assumed, potentially nonexistent completed execution.

The junk-value and nonvacuity checks for the addition found no problem:

- M>0 and 0<alpha<1 ensure that the empirical quantile candidate set is
  nonempty: its maximum value counts all M simulations. The fallback value
  in `mcCritical` is therefore unused.
- Every rational denominator is positive at every real hypothesis value;
  real division by zero does not represent an AR curve here. Nonnegative
  numerators and denominators make square-root comparisons faithful to the
  nonnegative squared statistics.
- Actual observed and simulated assignments lie in valid complete-randomization
  supports, making the arm means genuine means with positive denominators.
  Adjusted-arm inverses are guarded by full rank.
- Complete crossing lists contain real finite values in strict order. With
  J empty, `gapEndpoints` gives the single pair (-infinity,+infinity), and
  `gapSample` returns zero directly. Algorithm 2 uses its head only when J
  is nonempty and converts endpoints to reals only in the guarded finite
  continuation case. Identical curves and tied quantiles are handled by
  function equality and the full set of critical indices.

Concrete witnesses check both crossing branches. Retain the actual eight-unit
population with n1=4, all units compliers, and identical outcomes in both receipt
states:

    Y=(0,1,2,3,4,2,5,-3),
    O={0,1,2,3}, T0={0,1,2,4}, T1={0,1,4,5}.

Using T0 and T1 gives regular curves with complete crossing list `[0]`, as in
round 1. Using T0 twice gives TWO actual simulations whose curves are identical,
hence no crossing of distinct functions. For every real sample point their
critical value is sqrt(g_0) and their critical-index set is all of `Fin 2`.
Thus the no-intersection case has a nonempty simulation type, a nonempty
quantile-index set, and a genuine data-generated family. Empty J represents
the intended branch rather than vacuous model hypotheses.

[scratch/DeltaCheck.lean](/home/ubuntu/sap/tasks/CHFID-P002b-a/scratch/DeltaCheck.lean)
imports the revised Defs without importing Challenge. It includes the retained
independent data/regularity/nonempty-crossing checks, and additionally proves
for the repeated-assignment example:

- actual `DataGeneratedCoefficients`;
- `IntersectionList g []`;
- the critical-value and critical-index formulas at every real sample point;
- quantile-index nonemptiness;
- a whole-line `Algorithm1Run`;
- global confidence-set equality for either selected index;
- equality of that run's returned set with the empirical confidence set.

The adjusted branch is independently nonempty on the same observed data with
centered x=(-7,-5,-3,-1,1,3,5,7). Exact rational arithmetic rechecks its
coefficient vectors, everywhere-positive denominators, and full-rank
Grams on all 70 assignments. Using T0 twice again gives the empty-crossing
case. Using T0 and T1 retains the nonempty-crossing case. These checks are
recorded in
[scratch/arithmetic-evidence.json](/home/ubuntu/sap/tasks/CHFID-P002b-a/scratch/arithmetic-evidence.json).

T26's unchanged hypotheses also remain jointly satisfiable. For n=4, k=1,
n1=2, x=(-3,-1,1,3), y_i(0)=y_i(1)=x_i^3, all units compliers, and
S={0,1}, both arm Grams have determinant 1. Taking D=1_S gives receipt
contrast 1, adjusted Wald estimate 24, and determinant 1/16 for both IV
matrices. Its unconditional affine assertion, guarded Wald conclusions, and
IV product/ratio conclusions all have applicable instances. The canonical
target excludes the descriptive finite-union sentence, so its removal from
the restriction metadata is correct.

All target decisions were rechecked:

| Targets | Revised decision | Assessment |
| --- | --- | --- |
| T16, T17, T18, T19, T23, T24, T25, T27 | whole | The previously checked counterexample, bounds, exact identities, closed-gap statements, coverage and four-clause interval result are retained. |
| T26 | whole | All canonical algebraic clauses remain; the incorrect restriction label is fixed. |
| T20 | restricted | Positive oracle variance and invertible supported control Grams are still the two accurately disclosed additions to the probabilistic part. The finite part is retained. |
| T22 | restricted | Completed-run existence and all endpoint, length, coverage and set assertions are retained; universal policy termination is still accurately excluded. |
| T28 | restricted | The new six-clause statement covers both covariate settings and both crossing branches; only universal Algorithm 2/4 policy termination is excluded. |
| T21 | omitted | The supplied ordinary-limit claim is still not justified by an inner limsup bound. The earlier accepted omission remains justified. |
| T29, T30 | refuted | The unchanged propositions negate the actual printed universal nominal-limit assertions, with the original parameter spaces and coverage notions. These are faithful refutations. |

The last two judgments still have substantive nonempty counterexample
classes: T29 uses `(delta,r,A)=(0,1/4,1/2)`, whose fourth-moment bound forces
constant centered adjusted outcomes and coverage 1. T30 uses
`(k,delta,e,A,B,r)=(1,0,1/4,4,1/2,1/4)`, forcing zero population residuals
and worst-case coverage tending to 1 as singular-arm probabilities vanish
uniformly. Constant-additive-effect all-complier populations with centered
distinct bounded covariates supply models at every sufficiently large size
and every real LATE. Neither refutation needs empty infima or a parity
failure at r=1/2. Their detailed nonvacuity arguments are retained in
[findings2.json](/home/ubuntu/sap/tasks/CHFID-P002b-a/findings2.json).

Verification: the prescribed
`/home/ubuntu/sap/tools/sap-lean scratch/DeltaCheck.lean` exited successfully.
All 14 printed axiom checks contain only `propext`, `Classical.choice` and
`Quot.sound`, with no `sorryAx`. The result is in
[scratch/delta-lean-check.log](/home/ubuntu/sap/tasks/CHFID-P002b-a/scratch/delta-lean-check.log).
The exact rational checks pass with `python3 scratch/check_arithmetic.py`.
Python parses the final JSON and checks all 15 target IDs, all required
fields and verdict values, the 14 Challenge theorem names, the manifest
labels, and the reported counts. The original blind reading and round-1
deliverables are preserved.
