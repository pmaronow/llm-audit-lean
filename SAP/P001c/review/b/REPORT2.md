# Delta review

The earlier T42 finding is **fixed**. No earlier finding is partly fixed or
unfixed, and no new issue was found. All 18 retained theorems remain correct
at their declared scope; the T47 omission remains justified.

| Findings verdict | Count |
| --- | ---: |
| `correct_whole` | 9 |
| `correct_restricted` | 9 |
| `restriction_inaccurate` | 0 |
| `not_faithful` | 0 |
| `vacuous` | 0 |
| `false` | 0 |
| `omission_ok` | 1 |
| `omission_questionable` | 0 |
| **Total** | **19** |

Severity: none 19, minor 0, major 0. Earlier issue dispositions: fixed 1,
partly fixed 0, not fixed 0.

The revised architect decisions have different counts: `whole` 8,
`restricted` 6, `refuted` 4, `omitted` 1. The requested findings schema has
no separate successful-refutation verdict. Accordingly, T41 receives
`correct_whole` for its complete canonical counterexample, while T44, T53
and T56 receive `correct_restricted` for their valid refutations with
disclosed omissions. This does not assert the truth of the printed claims
they refute.

## Earlier finding

| Target | Earlier issue | Disposition and evidence |
| --- | --- | --- |
| T42 | The docstring called the correlation range the "unit interval", ordinarily `[0,1]`. | **Fixed.** `SAP/P001c/Challenge/Part1.lean:34` now explicitly states `[-1, 1]`; the next line explicitly names the extreme values `1` and `-1`. The unchanged formal conclusion at `Defs/Part4.lean:71` uses that same interval. No further fix is needed. |

This was the only nonempty issue list in my earlier `findings.json`.
The architect's account of it is accurate. The other 18 entries recorded
accepted scope or omission decisions rather than defects requiring repair.

## Changes compared with the saved blind reading

I reread all shared definitions and all 18 theorem statements and compared
their expanded mathematical content with `reading.md`. No hypothesis,
quantifier, conclusion or shared-definition meaning has changed. The
theorem names, binders and Statement references still give the same readings.

The changed mathematical summaries are T42's range wording and the new
refutation openings for T41, T44, T53 and T56. Comparing `record2.json`
with `record.json` confirms exactly four decision changes: those four
targets are now `refuted`. All other record fields, including their
restriction descriptions, are unchanged. The four new openings accurately
describe the assertions targeted by the counterexamples.

## Whole-label clause checks

Every target still labelled `whole` was checked against the canonical
claim, including every substantive conclusion, rather than just the headline.

| Target | Canonical content retained |
| --- | --- |
| T42 | The correlation bound and both iff characterizations by positive-slope almost-sure affine relations. |
| T45 | The covariance equation alone fixes exactly the slope; adding the mean equation gives exactly both BLP coefficients; unique risk optimality is explicit. |
| T46 | The corrected CEF version `10X²`, the uniform moments and covariance entering the displayed coefficient calculations, slope `10`, intercept `-5/3`, and unique affine optimality. |
| T48 | All covariance entries, symmetry, variance diagonal, and the full double-sum variance rule. |
| T49 | The affine expansion through its definition, intercept at zero, every unit coordinate increment, and every coordinate partial derivative, with actual derivative certificates. |
| T50 | General finite-population PMFs and moments; the complete four-unit example; the corrected variance functional and precise plus-sign discrepancy; both empirical mean and variance identities. |
| T52 | The indicator expectation for every measurable set, and fixed-ordinate empirical-CDF consistency under IID sampling, including degenerate ordinates. |
| T55 | The corrected estimator sequences in both definitions, both centered equivalences, and the variance/standard-error equivalence for the actual finite-variance root-n limit law. |

The standing finite-moment convention accounts for the L² hypotheses.
The versions used for densities and conditional means remain consistent
with the canonical standing assumptions. No whole-labelled target has
silently lost a clause in this revision.

## Refutation-label checks

**T41:** On the three-outcome probability space with weights
`(1/2,1/2,0)`, all three variances are `1/4`. The two correlations are
`1` and `-1`, but neither corresponding affine relation can hold at every
outcome. In the positive case the first and third outcomes have the same
`X=0` and different `Y`; the negative case has the same obstruction.
The probability-one affine relations remain true. This refutes exactly
the two forward pointwise implications specified by the canonical claim,
without claiming that the bound or reverse implications fail. Every
clause of the canonical counterexample is retained.

**T44:** On two equally likely outcomes, take `X=Y=(-1,1)`.
The predictors `g₀(x)=x` and `g₁(x)=x+1` produce the displayed vectors
`(-1,1)` and `(0,2)`. Both covariances are one, while their risks are
zero and one. They are distinct affine predictors, so the covariance
equation cannot single out the BLP. The omitted uniform/Gaussian example
and general affine-covariance formula remain explicitly disclosed.

**T53:** The displayed law has masses `p_k=7/8^(k+1)` at `2^k`.
Its mean is `7/6`, second moment `7/4`, and variance `7/18>0`,
while its fourth-moment terms are `(7/8)2^k` and have infinite sum.
For the squared variable, whose mean is `7/4`, the centered terms satisfy
`(4^k-7/4)² p_k ≥ (16^k/4)p_k` for `k≥1`, so its variance is not finite.
Thus IID draws from this law satisfy the sample-variance theorem's
hypotheses but lack the finite variance needed to apply the cited WLLN
to their squares. This is the premise-inference gap identified in the
canonical target. The true convergence assertion itself is not refuted.
The stub's omission of formal realization, IID construction and a separate
centered-variance assertion is accurately disclosed; the normalized
moment sums provide the numerical witness.

**T56:** The constant functional `T≡7` has explicitly certified zero
Hadamard derivative, while its centered root-n statistic is identically
zero and is expressly shown not to converge to any positive-variance
centered normal law. This refutes the printed implication under its own
positive-variance definition of asymptotic normality. The quadratic
Bernoulli example still supplies differentiability, its value at the
population CDF, the exact second moment and the probability-zero limit.
The omitted CDF calculations, boundedness/nonconstancy assertions,
derivative identification, binomial law, scalar second-moment limit and
IID construction remain accurately listed in the docstring.

The latter three targets remain restricted relative to the full canonical
counterexample records even though their retained counterexamples suffice
for the asserted refutations.

## Remaining restrictions and omission

The six `restricted` decisions remain accurate and completely disclosed:

| Target | Restriction verified |
| --- | --- |
| T39 | Omits the general zero-correlation/non-independence counterexample for normal marginal laws; retains the finite normal-sum and full corrected bivariate-density results. |
| T40 | Omits the first-order differentiation calculation and certification of the drawn curve; retains the MSE theorems and all stated coin and doubled-loss values. |
| T43 | Omits joint differentiability and the zero-regressor-variance footnote. Its Hessian-value, determinant, CEF and residual conclusions require a supplied L² CEF version; neither existence nor separate second-differentiability certificates are asserted. |
| T51 | Retains the corrected eventual-level equivalence; omits a separate complementary-event limit formulation and explicit endpoint counterexample. |
| T54 | Retains both sample-variance theorem conclusions; omits the general integrable WLLN and intermediate corrected-proof limits. |
| T57 | Retains outer process convergence and the positive-variance scalar limit, given the specified bridge law, measurable scalar plug-ins and L² derivative image; omits bridge existence and the degenerate alternative. |

T47 remains omitted for the same reason accepted earlier: the record's
candidate rows impose globally Borel or marginal-law measurable
transformations beyond the canonical composition-measurable scope, and
are recorded as unusable. No new candidate or full-scope theorem has
been introduced. This remains `omission_ok` on the available evidence.

## Junk values, nonvacuity and checks

The revised descriptions introduce no new mathematical hypotheses or
definitions. All prior domain guards remain: probability measures,
finite second moments, positive correlation/regression denominators,
positive density parameters and sizes, bounded Hadamard directions,
and bounded tests for outer expectations. T53 still asserts divergence
using a nonnegative extended sum; it does not use Mathlib's real-variance
fallback for an infinite moment.

The newly labelled refutations have concrete witnesses: the two specified
finite probability spaces for T41/T44, the normalized countable law above
for T53, and an actual IID Bernoulli product for T56. No false assertion
is obtained from an impossible antecedent. T42 still has the nondegenerate
witness `X=Y=id` under `N(0,1)`. The witnesses for every other target,
including T57's positive-variance Bernoulli bridge/evaluation instance,
remain as described in `nonvacuity.md` and in the per-target JSON entries.

Both original scratch files were recompiled successfully against the
refreshed Defs:

```
/home/ubuntu/sap/tools/sap-lean scratch/Check.lean
/home/ubuntu/sap/tools/sap-lean scratch/Counterexamples.lean
```

They import only Defs and contain no `sorry` or axioms. They verify the
complete T41/T44 finite counterexamples, finite moments, the conditional-
mean witness, and genuine infinite IID Gaussian and Bernoulli instances.
Both exit statuses were zero; the results are recorded in
`scratch/referee2-check-results.txt`. At most two Lean processes ran
simultaneously, and `lake` was never run. The countable-law interpretation
of T53 and the full T57 bridge construction are mathematical checks,
rather than newly compiled Lean proofs.

`findings2.json` has one object per canonical target and was parsed and
schema-checked with Python. The original blind reading and round-one
outputs were preserved. No Solution, Comparator or source proof was read,
and the architect's compilation/certification claims were not treated as
substitutes for statement review.
