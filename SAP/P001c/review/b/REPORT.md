# Statement audit

All 18 exported statements are correct at their declared scope. Nine state
the whole canonical claim, nine have accurate, disclosed restrictions, and
the omission of T47 is justified on the supplied record. One minor docstring
wording correction is proposed for T42; no theorem statement needs a fix.

| Verdict | Count |
| --- | ---: |
| `correct_whole` | 9 |
| `correct_restricted` | 9 |
| `restriction_inaccurate` | 0 |
| `not_faithful` | 0 |
| `vacuous` | 0 |
| `false` | 0 |
| `omission_ok` | 1 |
| `omission_questionable` | 0 |
| **Total targets** | **19** |

Severity counts: none 18, minor 1, major 0. No target has an adverse
statement-faithfulness verdict.

## Audit order and scope

`reading.md` was saved before opening `claims.json`. The 18 per-theorem
verdicts in `claim-stage.json` were then saved before opening `record.json`.
No claim-stage verdict was changed after reading the record. The record's
18 theorem decisions and restrictions agree with the independent readings.

The audit used the supplied Defs, Challenge, canonical claims, record, and
the Mathlib definitions behind the statistical and analytic notions.
No Solution, Comparator, or underlying formalization was read. The paper
text supplied in `claims.json` was sufficient; no web search was used.

## Whole statements

T41, T42, T45, T46, T48, T49, T50, T52 and T55 cover their canonical
formal content. Their L² hypotheses express the standing finite-moment
convention. Probability measures, positive variance where division requires
it, and positive population/sample sizes protect the ordinary statistical
interpretations. Conditional means and densities are interpreted as versions,
as the standing assumptions permit.

**Minor wording issue, T42:** `SAP/P001c/Challenge/Part1.lean:32-33` says
correlation lies in the "unit interval", ordinarily `[0,1]`. The actual Lean
statement in `SAP/P001c/Defs/Part4.lean:71` correctly uses `[-1,1]`, so the
`correct_whole` verdict is unchanged. Replace that docstring sentence with:
"For square-integrable variables with positive variances, correlation lies
in [-1, 1], and its two extreme values characterize the corresponding
almost-sure affine relations."

## Disclosed restrictions

| Target | Scope retained and omissions checked against the docstring |
| --- | --- |
| T39 | Normal affine sums and corrected bivariate density, moments and independence at zero correlation; omits the general non-implication for normal marginal laws. |
| T40 | General MSE theorems and all coin and doubled-loss values; omits the first-order differentiation calculation and certification of the actual drawn curve. |
| T43 | First partials, normal equations and unique minimum; omits joint differentiability and the zero-variance footnote. Hessian values, determinant, CEF and residual conclusions require a supplied L² conditional mean. Second differentiability is not separately certified. |
| T44 | Complete symmetric two-point counterexample (a); omits illustration (b) and the general affine-covariance formula. |
| T51 | Correct eventual-level equivalence with `p<1`; omits the separate complementary-event limit formulation and an explicit endpoint counterexample. |
| T53 | Normalized power-tail weights, exact first/second moments, positive variance arithmetic and infinite fourth-moment sum; omits realization, IID construction and a separate variance-of-squares assertion. |
| T54 | Both sample-variance theorem conclusions under their original finite-positive-variance assumptions; omits the general integrable WLLN and intermediate proof limits. |
| T56 | Constant-functional refutation and quadratic differentiability, exact second moment and degenerate probability limit; the omitted CDF calculations, quadratic boundedness/nonconstancy, derivative identification, binomial law, scalar limit and IID construction are accurately listed. |
| T57 | Outer empirical-process limit and positive-variance scalar normal limit, given the specified probability bridge, measurable scalar plug-ins and L² derivative image; omits bridge existence and the degenerate alternative. |

T41 refutes pointwise affine dependence while retaining nonzero variances
and probability-one dependence, exactly as required. T44 refutes covariance
uniqueness for the book's affine class. T56 excludes every positive-variance
Gaussian limit for the constant statistic. T53 concerns the missing fourth-
moment hypothesis in the cited proof step; neither it nor T54 purports to
refute the true sample-variance consistency theorem.

## T47 omission

The record identifies three candidate results as unusable at the canonical
scope: two add marginal-law measurability, and the third restricts transformations
to globally Borel functions. The canonical definition of a function of a
random variable only requires its composition to be a random variable.
Those stronger transformation assumptions are not supplied by the canonical
statement. The omission therefore avoids assigning full-scope credit to a
result with extra hypotheses, and is accepted on the evidence available here.
The candidate source rows themselves were outside the permitted audit files
and were not inspected.

## Nonvacuity and verification

`nonvacuity.md` gives witnesses for every target, including a nondegenerate
Bernoulli bridge and evaluation functional satisfying every T57 antecedent.
The bridge hypotheses specify support and finite-dimensional laws; they do
not assume the asserted empirical-process convergence.

Two scratch files, importing only Defs, compiled successfully with `sap-lean`.
They check the full T41 and T44 counterexamples, finite-population moments,
and genuine infinite IID Gaussian and Bernoulli constructions. The Gaussian
example also inhabits T43's supplied-CEF antecedent. Details and successful
exit statuses are in `scratch/check-results.txt`. Only one Lean process ran
at a time, and `lake` was never run.

No assertion relies on division by zero, an empty index family, a nonintegrable
Bochner integral's fallback value, an unbounded conditional supremum, or an
empty defining infimum. The zero-sample empirical measure affects only a
finite initial term of asymptotic statements. The fourth moment in T53 is
properly asserted as an infinite nonnegative extended sum.

The assessment is of statements and their scope. The scratch checks cover
the specified witnesses and counterexamples; they are not a separate Lean
proof of every universal Challenge statement. In particular, T57's full
bridge nonvacuity construction was checked mathematically.
