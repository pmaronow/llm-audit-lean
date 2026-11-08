# Declaration review

All five declarations are **faithful**, with severity **none**. The five
`whole` decisions in `record.json` are correct. No claim-stage conclusion was
changed after reading that record.

The blind expansion and convention audit were saved in `reading.md` before
opening the canonical claims. Every closure entry was read, including generated
constructors, projections, matchers and numeral proofs. `claim-stage.json` was
saved before opening the architect's record.

| Declaration | Result of the comparison |
|---|---|
| T21 | Exactly the corrected Xi tail assertion: all size indices, empty suprema equal to zero, inner limsup, and existence of the ordinary outer right-hand limit. No positive residual-variance condition is added. |
| T22 | Every corrected interval/index pairing and both next-sample branches are preserved. Termination for every admissible policy is a conclusion. Closed-endpoint quantile persistence and both piece and union equalities are included. The theorem validly generalizes to all regular nonnegative quadratic-ratio families. |
| T23 | Corrected H.1 includes the squared critical value and every finite closed-gap endpoint. The nonempty crossing-list hypothesis is explicitly part of the canonical claim. The data-generation predicate uses one genuine observed dataset and the correct coefficient formulas. |
| T24 | All corrected OLS, contrast and guarded Wald identities are present. Full-rank arm Grams express the canonical uniqueness condition. Allowing arbitrary real responses and receipt vectors strengthens the algebraic result. |
| T25 | Baseline recovery, the true LATE, and both finite-sample coverage lower bounds are present. The quantiles use the full conditional randomization law, holding the observed response vector fixed. |

For T24, the docstring's “adjusted statistic” refers to the adjusted
difference-in-means contrast in equation (9), which the canonical standing
assumptions themselves call a statistic. It does not assert that the studentized
ratio is affine. This resolves the terminology question recorded during the
blind stage.

Zero-scale studentization, infinite attained quantiles and singular OLS fits
were examined separately. Their conventions agree with the claims. The
least-squares rule is stated in `Defs/Part2.lean:33`; it chooses a genuine
minimizer on singular arms. All randomization sample spaces here are finite,
so the resulting statistics are measurable for each fixed population. The
normal quantile's real infimum is nonempty and bounded below at the stated
levels. No claim is obtained from an inappropriate junk value, an encoded
conclusion, contradictory hypotheses, or an assumed termination result.

`/home/ubuntu/sap/tools/sap-lean scratch/Check.lean` exited **0**. It constructs
nonvacuity instances for every target, including positive residual variance for
T21, an explicit policy execution for T22, genuine generated curves and an
Algorithm 1 run for T23, and a nonzero Wald denominator for T24. T25 uses a
nonzero constant effect and proves baseline recovery directly. The named
scratch proofs have no `sorryAx` dependency and do not invoke the Challenge
theorems. The compiler output is saved in `scratch/Check.log`.

`findings.json` contains exactly the five requested declarations and their
fingerprints. Its clean entries have empty issue lists and require no fixes.
