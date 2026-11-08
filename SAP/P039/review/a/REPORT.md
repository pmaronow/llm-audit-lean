# P039 statement audit

Seven targets: **4 correct_whole, 3 correct_restricted; 0 adverse findings**.

| Verdict | Count |
| --- | ---: |
| correct_whole | 4 |
| correct_restricted | 3 |
| restriction_inaccurate | 0 |
| not_faithful | 0 |
| vacuous | 0 |
| false | 0 |
| omission_ok | 0 |
| omission_questionable | 0 |

All severities are `none`. Every target has a theorem. There are no items
outside `correct_*` / `omission_ok` to report.

The blind reading was saved in [reading.md](reading.md) before opening
`claims.json`. The comparison was saved in [claim-stage.json](claim-stage.json)
before opening `record.json`. Reading the record changed no step-2 judgment.
The architect's seven decisions agree with the independent comparison.

The three restrictions are accurate and disclosed in both the record and each
Challenge docstring:

* **T3:** retains both exact OLS witnesses and Gaussian-null discrepancy, but
  uses nominal analytic tail expressions without identifying them with Student
  probability tails. It also omits the general tail identities, intermediate
  bound and bounding calculations, and informal decimal approximations.
* **T4:** retains all linear algebra (a)–(e) and the covariance part of (f), with
  explicit coordinate and pairwise-product integrability. It omits the general
  Gaussian-to-Student laws and consequent non-Student characterization. The
  empirical nonlinear application (g) was already outside the canonical formal
  claim. No Student-law conclusion is assumed as a premise.
* **T7:** omits the significance stars and the alternative RMSQ = sqrt(SSE/n)
  reading with its sqrt(13/14) comparison. It retains the complete conventional
  nested-fit inequality, four-bin contradiction, exact bound and gap, and
  corrected coefficients and SE displays.

The paper's quarter description, residual-plot context, maximum-effect wording,
and note 15 were also checked against the relevant passages on pp. 128, 136–139,
141–142 of the [paper PDF](https://bpb-us-e1.wpmucdn.com/sites.northwestern.edu/dist/b/3288/files/2019/10/2016-Cohen-et-al.-Extremism.pdf).
Canonical counterexamples T1, T3 and T5 establish their requested assertions;
none contradicts its own canonical claim. T5 explicitly distinguishes the
signed-order reading of the maximum-effect guidance from the magnitude rule.

Independent verification used only the provided definitions, canonical claims,
Mathlib sources, and paper:

* [scratch/CheckNonvacuity.lean](scratch/CheckNonvacuity.lean) compiles with
  `/home/ubuntu/sap/tools/sap-lean` and imports only `SAP.P039.Defs`. It checks
  positive income normalizers, a full-rank six-observation design containing an
  intercept with the tested regressor outside its span, and actual sample sizes.
* [scratch/audit_checks.py](scratch/audit_checks.py) uses exact rational normal
  equations and exhaustive finite enumeration. It checks all 64 score constants,
  all 85 regression-input constants against the canonical tables, both income
  witnesses, four regression witnesses, all maxima and margins in both samples,
  and the corrected regression cells and numerical bound. Results are saved in
  [scratch/check-results.json](scratch/check-results.json).
* A 64-point uniform sign-vector probability space satisfies every covariance
  premise of T4, including finite moments, and has residual covariance M of rank
  four. The positive-SSE deterministic instance exercises the guarded t clauses.
* The Gaussian witness uses actual product normal probability measures and
  measurable rational/square-root maps. Its three positive residual degrees of
  freedom give finite inverse-chi-square and squared-Student moments. No measure
  pushforward fallback or nonintegrable-integral convention supplies a result.

No hidden conclusion premise, empty sample, harmful natural subtraction,
singular inverse, or relevant zero denominator was found. The inconsistent four
printed bins in T7 are the intended impossibility conclusion; the actual nested
data satisfy the other three neighboring bounds with corrected A1 SE about .94.
