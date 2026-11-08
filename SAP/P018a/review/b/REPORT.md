Statement audit of P018a

All 14 targets are accounted for. The statements support the architect's
decisions: **3 correct_whole, 11 correct_restricted**. There are no adverse
findings and no omissions.

| Verdict | Count |
| --- | ---: |
| correct_whole | 3 |
| correct_restricted | 11 |
| restriction_inaccurate | 0 |
| not_faithful | 0 |
| vacuous | 0 |
| false | 0 |
| omission_ok | 0 |
| omission_questionable | 0 |

Severity counts: none 14, minor 0, major 0.

| Target | Theorem | Record decision | Verdict |
| --- | --- | --- | --- |
| P018-T1 | SAP.P018a.T1 | restricted | correct_restricted |
| P018-T2 | SAP.P018a.T2 | restricted | correct_restricted |
| P018-T3 | SAP.P018a.T3 | restricted | correct_restricted |
| P018-T4 | SAP.P018a.T4 | whole | correct_whole |
| P018-T5 | SAP.P018a.T5 | restricted | correct_restricted |
| P018-T6 | SAP.P018a.T6 | whole | correct_whole |
| P018-T7 | SAP.P018a.T7 | restricted | correct_restricted |
| P018-T8 | SAP.P018a.T8 | restricted | correct_restricted |
| P018-T9 | SAP.P018a.T9 | restricted | correct_restricted |
| P018-T10 | SAP.P018a.T10 | restricted | correct_restricted |
| P018-T11 | SAP.P018a.T11 | restricted | correct_restricted |
| P018-T12 | SAP.P018a.T12 | restricted | correct_restricted |
| P018-T13 | SAP.P018a.T13 | restricted | correct_restricted |
| P018-T14 | SAP.P018a.T14 | whole | correct_whole |

There are no items outside `correct_*` / `omission_ok` requiring an issue or
fix. The eleven restrictions accurately describe the retained and dropped
assertions. Their wording also agrees exactly between `record.json` and
the theorem docstrings. The whole-claim decisions concern the mathematical
statements, not a promise to include every supporting lemma listed in a
claim's proof discussion. In T6 the symmetric-invertible GLS identity
actually covers more matrices than the positive-definite canonical case.

The review followed the required order. `reading.md` was saved before
opening `claims.json`; `claim-stage.json` was saved before opening
`record.json`. No stage-2 classification changed at stage 3. Each of the
fourteen entries in `findings.json` supplies an explicit nonvacuity instance
or the corresponding finite/model construction.

The scope changes that most affect interpretation are disclosed:

* T3 weakens the inverse-design conclusions from every N>=3 to every N
  above an unspecified threshold at least 3. Its eight-sign covariances
  are stated as finite sign expectations without a separate assertion
  identifying them with fitted OLS residual covariances.
* T5 assumes the centered-response independence and finite second moments
  needed for its intercept bound; it does not derive them for design (4).
* T7 retains the negative-estimate probability and finite witness while
  dropping the joint second-order limit and studentized-pivot claim.
* T8 adds eventual almost-sure strict positivity only to the pivot limit.
  This is stronger than positive limiting contrast variance. It is
  satisfiable: with continuous uniform[-1,1] units, X_ij=1 and
  Y_ij=U_i+U_j, the limiting contrast variance is 4/3 and the estimated
  variance is positive almost surely for every N>=4. Coverage and the
  vanishing probability of nonpositive estimated variance retain the
  canonical hypotheses.
* T10 retains the full corrected common-record-kernel and mean-overlap
  assumptions for repeated data; its weighted consistency result is
  restricted to symmetric single-record dyads. Its scale identities have
  explicit sample/population rank guards.
* T11 retains scalar target arithmetic without claiming the omitted
  conditional-moment identifications or repeated/two-regressor examples.
* T12 states its linearizations almost everywhere on nonsingular samples,
  requires positive observation counts where L is divided, and drops the
  sparse-moment statements and model checks.
* T13 drops the separate strict-concavity assertion while retaining an
  explicit unique global maximizer.

The definitions preserve the relevant mathematical objects. Dyads are
two-element unordered sets with distinct endpoints; overlap sums are
ordered and include the diagonal. Population residuals and fitted residuals
remain distinct. Population coefficients use the expected Gram, and
the targets use unconditional score covariance. The missing conditional
term in T2 is not assumed zero. In T1 the conditional covariances vanish
because the residuals are functions of the design; the sigma algebra,
integrability and finite-measure requirements for ordinary conditional
expectation are satisfied.

Mathlib's total operations do not supply spurious content here. All
population inverse uses that need an ordinary inverse have rank guards or
explicit positive determinants. Zero sample inverses supply an allowed
extension on singular samples in asymptotic statements. The probability
models are genuine probability measures, and the retained covariance
integrands have finite moments. The inverse-design infinite moment is an
extended nonnegative integral, not a nonintegrable real integral that
defaults to zero. Its operator-norm supremum is over a nonempty bounded
set for each finite matrix. Positive semidefiniteness guards the normal
law's variance conversion. The confidence-interval event explicitly
guards nonnegative variance. The finite denominator identities use N>=2
or N>=3; no conclusion depends on an empty dyad type. The norm changes
from Euclidean/operator to coordinate supremum norms do not change
convergence in fixed finite dimension.

Independent verification:

* `/home/ubuntu/sap/tools/sap-lean scratch/Check.lean` completed with exit
  status 0. It imports only `SAP.P018a.Defs`, proves a nonempty
  one-dimensional `Standing` instance and a nonempty logistic rank
  instance, and checks the displayed nonlinear determinants and logistic
  bread inverse. It uses no Challenge theorem or admitted proof.
* `python3 scratch/finite_checks.py` completed successfully using exact
  rational arithmetic. It recomputes the nonlinear population, score and
  projection moments; the GLS variance ratio; the logistic middle factors
  and covariance matrices; the N=8 negative-variance witness; all three
  eight-sign covariances; the scalar-sign expected meats by complete
  enumeration for N=4 through 8; and the geometric-weight variance limit.
  The results are saved in `scratch/finite-checks.json`. These checks
  support the finite constructions; they are not proofs of the general
  asymptotic statements.

The canonical published-form claims and standing assumptions in
`claims.json` controlled the comparison. The paper was also consulted
through its [preprint](https://arxiv.org/pdf/1312.3398); the
[publisher's record](https://www.cambridge.org/core/journals/political-analysis/article/abs/clusterrobust-variance-estimation-for-dyadic-data/D43E12BF35240100C7A4ED3C28912C95)
identifies the published article and pagination. No formalization,
Solution, Comparator, or proof source named in the record was inspected.
