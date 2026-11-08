# Palomar statement referee report: P001c

All 18 formal statements are correct at their stated coverage: nine whole and
nine accurately disclosed restrictions. The sole omitted target, T47, is
justifiably omitted. One minor docstring wording correction is recorded for T42;
its formal statement is correct and whole.

| Verdict | Count |
| --- | ---: |
| correct_whole | 9 |
| correct_restricted | 9 |
| omission_ok | 1 |
| restriction_inaccurate | 0 |
| not_faithful | 0 |
| vacuous | 0 |
| false | 0 |
| omission_questionable | 0 |
| **Total targets** | **19** |

Severity counts: 18 none, 1 minor, 0 major. There are no targets with an adverse
formal-statement or omission verdict.

## Minor documentation correction

**P001-T42 — correct_whole, minor.**
`SAP/P001c/Challenge/Part1.lean:32–33` calls the correlation range the “unit
interval,” conventionally [0,1]. The formal statement in `Defs/Part4.lean`
correctly asserts membership in [-1,1]. For example, X standard normal and Y=−X
give correlation −1. This is a prose error, with no missing restriction or error
in the theorem.

Replace that descriptive sentence with:

> For square-integrable variables with positive variances, correlation lies in
> [-1,1], and its values 1 and -1 characterize the corresponding almost-sure
> affine relations.

The audited input files were left unchanged; the correction is supplied in
`findings.json`.

## Review against the record

The nine whole targets are T41, T42, T45, T46, T48, T49, T50, T52 and T55.
The corresponding decisions are supported by the blind readings and canonical
claims. In particular, finite second moments implement the standing expectation
convention, positive variances guard correlation and regression denominators,
positive sample sizes guard empirical-law normalization, and the asymptotic
statements retain their intended quantifier order.

For each restricted target, both the record and the Challenge docstring accurately
describe the retained content and the omitted assertions or additional inputs:

| Target | Restriction verified |
| --- | --- |
| T39 | Retains nontrivial independent normal sums and the corrected bivariate density conclusions. Omits the general non-implication from zero correlation to independence for normal marginal laws. |
| T40 | Retains the general MSE theorems and all specified coin-loss values and scale formulas. Omits the differentiation calculation and certification of the actual figure. |
| T43 | Retains the partials, normal equations and unique minimum. Omits joint differentiability and the zero-variance footnote; the Hessian, CEF and residual block requires a supplied square-integrable CEF version, without asserting existence or separate second-differentiability certificates. |
| T44 | Retains counterexample (a). Omits example (b) and the general covariance formula. The retained example still refutes the printed uniqueness assertion. |
| T51 | Retains the exact corrected eventual-level equivalence with p<1. Omits separately exporting the complementary-event limit equivalence and a p=1 counterexample. |
| T53 | Retains normalized nonnegative masses, exact finite first and second moments, positive variance arithmetic, and an infinite extended-real fourth-moment sum. Omits a measure-space realization, IID draws and a separate squared-variable variance assertion. |
| T54 | Retains both sample-variance theorem conclusions under finite positive variance. Omits the general integrable WLLN and the intermediate limits in the repaired proof. |
| T56 | Retains the constant counterexample, including its zero derivative and exclusion of positive-variance normal limits, and the quadratic example's differentiability, exact moment and probability limit. The CDF calculations, quadratic boundedness/nonconstancy, F(0), derivative identification, binomial law, scalar moment limit and IID construction are accurately listed as omitted. |
| T57 | Supplies a probability bridge with tangent support and finite-dimensional Gaussian laws, a measurable scalar plug-in and an L² derivative image with positive variance. Omits bridge existence and the degenerate alternative. Both the outer empirical-process limit and scalar normal limit remain conclusions. |

No step-2 verdict was changed after reading the record.

## T47: omission justified

The canonical transformation scope is Definition 1.2.2: g(X) and h(Y) need only
be measurable compositions. The rejected rows require global Borel or
marginal-law measurability of the transformations. These conditions do not
follow in general from composition measurability on an arbitrary probability
space, so those rows cannot be credited as the whole claim.

This is a substantive distinction. `nonvacuity.md` gives a mathematical model
with independent uniform X,Y but composition-measurable non-Borel transforms
g(X)=h(Y)=C, where C is a fair binary variable. Then
E[h(Y)|g(X)]=C, whereas E[h(Y)]=1/2, and the transformed BLP is the identity.
Thus silently restoring the full composition-only statement would be unsound.
The record makes no theorem claim for this target. Its omission is appropriate;
a future restricted theorem would need to disclose stronger measurability.

## Method and verification

`reading.md` was saved before opening `claims.json` or `record.json`.
`claim-stage.json` was saved before opening `record.json`. It contains one
assessment for each of the 18 actual theorem stubs. `findings.json` contains one
entry for each of the 19 canonical targets, including the omission.

The blind reading traces every SAP definition through the relevant Mathlib
definitions. Checks addressed the integral and variance totalizations, pushforward
measurability, nonzero denominators, real rather than truncated subtraction,
finite and divergent series, bounded suprema, existence of integrable majorants,
and empty-index cases. No totalization or empty type supplies a spurious result.
The pointwise counterexample in T41 uses a null outcome intentionally and still
has positive variances. The counterexamples T44 and T56 refute the printed
readings identified in their claims.

`scratch/Check.lean` imports only the supplied Defs and compiles successfully
with `/home/ubuntu/sap/tools/sap-lean scratch/Check.lean` (exit code 0, no
diagnostics). It verifies normalized weights, nonconstant Gaussian L² and
positive-variance instances, the added conditional-mean hypotheses, actual IID
product spaces, the Bernoulli sampling assumptions, the uniform/Gaussian input
model, a nondegenerate root-n limit, and the evaluation Hadamard derivative.
`nonvacuity.md` supplies instances for all targets and a complete mathematical
joint instance for T57's bridge and positive-variance hypotheses. The full T57
bridge instance is a mathematical verification, not a separately compiled Lean
proof. No Solution or Comparator proof was inspected.

Both output JSON files were parsed with Python and checked for required fields,
valid verdicts, unique target IDs and complete target/theorem coverage.
