All four declarations are **faithful**, with severity **none**, at their recorded scope.

| Declaration | Claim comparison | Record assessment |
| --- | --- | --- |
| `SAP.P001a.T16` | Narrower | The matching example, estimated-score equalities, bootstrap variance failure, intercept consistency, and weighted-sign variance identity are correct. The restriction accurately discloses the omitted design predicates, rate discussion, adjusted variance estimator, and standard-error/interval conclusions. |
| `SAP.P001a.T17` | Whole | The twelve-atom example includes its treatment-invariant structural placebo, conditional laws, population calculations, actual sample, iid realization, and conventional and robust test failures. |
| `SAP.P001a.T18` | Whole | The population CEF/BLP conclusion, added-linear-content interpretation, actual OLS and HC0 asymptotics, and feasible null Wald inference match the correction. The tested covariance rank condition is explicit. |
| `SAP.P001a.T19` | Narrower | The positive geometric masses give the claimed overlap counterexample. The quantitative bound and selected covariate are accurately disclosed omissions; the refutation label is justified. |

The blind reading and complete closure inspection were saved in `reading.md`
before the claims were opened. `claim-stage.json` was saved before opening the
record. No claim-stage conclusion changed after reading the record.

For T17, the printed reading is that the proposed regression test is calibrated
under conditional independence with a placebo unaffected by treatment, in the
standing iid setting. The witness meets these conditions: baseline and assignment
seed are independent; the placebo depends only on baseline; both placebo and
potential outcomes are conditionally independent of treatment given X; overlap
holds; observations are independently replicated; and all variables are bounded.
Linearity of the treatment CEF is absent from the printed premises. The nonlinear
CEF therefore does not invalidate this counterexample.

For T19, the printed reading is that failure of uniform two-sided positivity
implies incomplete population overlap, or equivalently that complete overlap
implies uniform positivity. Its conditions and the witness check are:

- A probability distribution and binary treatment with both arms present: the
  joint masses sum to one, with each arm having probability one half.
- The book's positive-mass conditional support: after setting X=k+1, both
  conditional arm masses are positive at every positive integer, so their
  supports coincide exactly.
- A defined conditional propensity: every denominator is positive, and the
  displayed ratio is strictly between zero and one at every cell.
- Usual measure and moment conditions: the space is countable and discrete,
  all events are measurable, and the geometric tails give finite moments.

The propensity tends to zero. Each offending cell has positive probability, so
the missing uniform margin persists under an almost-sure interpretation. This
contradicts the printed assertions themselves. Positivity implying complete
overlap remains compatible with the witness.

Independent Lean checks passed in `scratch/MatchingLaw.lean`,
`scratch/Nonvacuity.lean`, `scratch/NullInstance.lean`, and
`scratch/OverlapInstance.lean`. They construct the matching and placebo iid
experiments, check the actual 240-row counts, construct a nondegenerate placebo
null with nonsingular Gram and tested covariance, and independently prove the
full overlap-mass statement. These checks do not apply an audited theorem.
The matching L² premises are additionally justified analytically: statistics
are bounded, bootstrap variances are bounded, and measurable tie-breaking
representatives agree almost everywhere under the continuous score law.

No conclusion is encoded in a definition. Population integrability, finite
probabilities, positive denominators, and covariance rank exclude harmful
default values. Singular finite-sample inverse conventions are harmless for
the stated asymptotic claims. The docstrings describe their statements and
restrictions accurately. All 63 compiler-generated closure entries were also
inspected through `scratch/ClosurePrint.lean`; they add only numeric/indexing
proofs, scalar typeclass instances, the finite-law normalization proofs, and an
ordinary Option eliminator.
