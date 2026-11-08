# P002b delta statement review

Both earlier adverse findings are **fixed**. No new statement, disclosure, junk-value,
or nonvacuity problem was found. The revised package has 14 Challenge theorems and
one omission across 15 targets.

| Verdict | Count | Targets |
| --- | ---: | --- |
| correct_whole | 11 | T16, T17, T18, T19, T23, T24, T25, T26, T27, T29, T30 |
| correct_restricted | 3 | T20, T22, T28 |
| omission_ok | 1 | T21 |
| restriction_inaccurate | 0 | |
| not_faithful | 0 | |
| vacuous | 0 | |
| false | 0 | |
| omission_questionable | 0 | |

All severities are `none`. The eleven `correct_whole` judgments comprise nine
whole positive/counterexample targets and two faithful complete refutations,
T29 and T30. Their record decisions remain `refuted`; the findings schema has
no separate successful-refutation verdict.

## Earlier findings

| Earlier finding | Status | Revised evidence |
| --- | --- | --- |
| T26: the restriction purportedly drops a sentence expressly outside the canonical target. | Fixed | `record2.json` now labels T26 `whole` with `restriction: null`. The Challenge docstring removes the inaccurate restriction. |
| T26: the nonzero receipt guard does not justify a restriction of the IV identity. | Fixed | The guard and theorem are retained, with the correct whole classification. Full-rank arms and IV cross-matrix invertibility force that contrast to be nonzero, so no clause of the canonical algebraic target is lost. |
| T28: the omission rationale incorrectly demanded the known shifted Step 5 indexing. | Fixed | The architect acknowledges the canonical corrected interpretation and exports T28 using `Algorithm2Run`'s recorded endpoint/index pairs. The old rejection rationale is withdrawn. |
| T28: no headline result or no-intersection branch was exported. | Fixed | The new T28 includes both covariate settings, existence of crossing lists and runs, correctness of every completed run, and the arbitrary-selection no-intersection branch. Its remaining policy-termination limitation is accurately disclosed. |

The T28 fix is an accepted **restricted** export. The earlier requested fix
explicitly allowed a genuine limitation to remain if precisely disclosed.
Universal termination under every prescribed Algorithm 2/4 choice policy is
therefore a declared scope limit, not an unresolved version of the earlier
unjustified omission.

## Comparison with the blind reading

The mathematical contents of all thirteen preexisting theorem propositions and
their shared definitions agree with `reading.md`. The only changed preexisting
target is T26's label and docstring. T28 is a new proposition in
`SAP/P002b/Defs/Part7.lean`, imported by the Defs root, with a new Challenge stub.

T26 still contains every canonical algebraic clause (a)-(c): affine adjustment
for every hypothesized effect; guarded Wald cancellation, zero studentization,
and set membership; and the IV product identity and ratio equality. The
descriptive finite-union sentence remains outside this target under the
explicit clarification in `claims.json`. There is no new mathematical
hypothesis or dropped clause.

T20 and T22 retain exactly their previously accepted restrictions. T21 remains
omitted for the previously accepted reason: an inner limsup result does not
establish the ordinary inner limit required by the canonical claim. T29 and
T30 still negate the precise printed universal nominal-coverage assertions.
Their earlier nonempty-class refutation witnesses continue to apply.

## Exact reading and scope of new T28

For every natural M, observed sextuple Qf, M simulated sextuples Qg, and real
alpha, assume:

- M is positive and 0 < alpha < 1;
- Qf and Qg are generated from one common observed dataset and valid complete
  randomization assignments, with monotone receipt and a nonempty complier set;
- in the adjusted case, the covariate dimension is positive, covariates are
  centered, and every observed/simulated arm Gram is invertible;
- each variance-denominator quadratic is strictly positive at every real beta,
  and each numerator quadratic is nonnegative at every beta.

Writing f and g for those squared AR functions, the conclusion is the
conjunction of six assertions, in this order:

1. There exists a finite, strictly sorted list J containing exactly all
   intersections of distinct simulated functions.
2. For every such complete J, an Algorithm 1/3 run exists, including when J is
   empty.
3. For every J and every Algorithm 1/3 run on J, its returned union equals the
   empirical confidence set.
4. For every complete nonempty J, a completed finite Algorithm 2/4 run exists.
5. Every completed finite Algorithm 2/4 run returns the empirical confidence
   set.
6. For every complete empty J, the empirical quantile index set is nonempty at
   every real sample point. For every sample point beta and every index m
   attaining its quantile, the global comparison set
   `{x : f(x) <= g_m(x)}` equals the empirical confidence set.

Thus the empty-crossing assertion covers every prescribed sample and every
admissible index, rather than one convenient index. It separately handles
Algorithms 2/4's immediate return when `Algorithm2Run` itself is unavailable
because that predicate requires a nonempty crossing list.

`Algorithm2Run` still describes completed finite executions. T28 does not state
termination for every prescribed sequence of admissible choices. The
restriction in the Challenge docstring and `record2.json` identifies precisely
this remaining omission. I found no other dropped clause or added hypothesis
relative to the canonical corrected algorithm domain.

## Truth, junk values, and nonvacuity

The new assertion has substantive content. Distinct rational quadratic curves
with everywhere-positive denominators can intersect only at roots of a
nonzero polynomial of degree at most four. Their finite union of crossing
sets therefore admits the sorted finite list that T28 now asserts exists;
finiteness is not silently assumed as an extra antecedent.

Positive M and an interior alpha guarantee an attained empirical critical
value. Nonnegative numerator values and positive denominators mean the square
roots represent absolute AR statistics, so the squared comparison in the
return sets is equivalent to the comparison in `mcSet`. Empty-candidate
fallbacks and square roots of negative values do not do any work. The
Algorithm 1/3 predicate assumes quantile validity only at the prescribed gap
sample, not on the whole gap. The Algorithm 2/4 predicate likewise does not
assume returned-set correctness. Existence assertions prevent the correctness
implications from relying on the absence of runs.

The sorted finite endpoints produce genuine gaps. `gapSample` handles the
whole line directly, and branches around infinite endpoints before using real
coordinates. `Algorithm2Step` likewise uses a finite crossing as its right
endpoint before constructing a next-piece sample. The existing zero-adjoined
maxima, extended-real coverage infima, and singular-OLS conventions are
unchanged and introduce no new issue in T28.

`scratch/DeltaChecks.lean` compiled successfully with
`/home/ubuntu/sap/tools/sap-lean scratch/DeltaChecks.lean`. It imports only
`SAP.P002b.Defs` and has no `sorry`, added axiom, or use of a Challenge theorem.
It provides these independent checks:

- **Nonempty crossings, unadjusted:** the eight-unit dataset from round 1 is
  rechecked, including joint data generation, regularity, and the exact complete
  crossing list J = [-4]. This is the nonempty-list domain for the Algorithm 2
  existence clause.
- **Empty crossings and a returned run:** with one simulated assignment equal
  to the observed assignment, it proves joint data generation and
  `IntersectionList g []`, computes the attained critical value for every beta
  at alpha = 1/2, and constructs a whole-line Algorithm 1 run with
  `returnedSet = mcSet`. Its quantile index is explicitly present. Thus the new
  empty-list assertions concern admitted data and a real run.
- **A genuine adjusted instance:** use n = 8, k = 1, n1 = 4, all compliers,
  y_i(0) = y_i(1) = i^2, covariates (-1,1,-1,1,-1,1,-1,1), observed assignment
  O = {0,1,2,3}, and simulated assignments O and T = {0,3,4,7}. The proof checks
  centering, all four augmented arm Grams equal to the identity, joint data
  generation, and regularity of both distinct curves. Their sextuples are
  (1,56,784,0,0,33) and (0,0,4,1/8,7,108), giving functions
  (beta+28)^2/33 and 32/((beta+28)^2+80). Both denominators are strictly positive
  everywhere. Hence the adjusted half does not rely on an impossible design,
  zero variance, singular inverse, or an empty covariate domain.

The adjusted example also has genuine crossings: putting t = (beta+28)^2,
equality reduces to t^2 + 80t - 1056 = 0. Its positive root is
4 sqrt(166) - 40, giving two real crossings. This last crossing calculation is
a mathematical check; the compiled checks establish its coefficients and
regularity.

## Validation

`findings2.json` contains exactly one object for every target in `claims.json`,
with the same schema as `findings.json`. Its fourteen non-null theorem names
agree with the revised Challenge and `record2.json`. The JSON was parsed and
its fields, verdicts, severities, target coverage, and counts were checked with
Python. The prior reading and claim-stage hashes remain unchanged. The earlier
findings and reports are preserved, and no supplied Defs, Challenge, claim, or
record file was edited. No `lake` command was run; only one Lean process was
used at a time in this review.
