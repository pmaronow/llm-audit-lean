# Palomar P033 statement audit

18 targets: **12 correct_whole, 3 correct_restricted, 3 omission_ok; 0 adverse findings.** All severities are `none`.

| Verdict | Count |
| --- | ---: |
| correct_whole | 12 |
| correct_restricted | 3 |
| restriction_inaccurate | 0 |
| not_faithful | 0 |
| vacuous | 0 |
| false | 0 |
| omission_ok | 3 |
| omission_questionable | 0 |

There are no targets outside `correct_*` and `omission_ok` that require a correction.

The blind reading was saved in `reading.md` before opening `claims.json`. The claim comparison was saved in `claim-stage.json` before opening `record.json`. Reviewing the record caused no changes to the step-2 classifications.

The three restrictions are accurate and disclosed verbatim in the corresponding challenge docstrings:

- **P033-T1:** omits the four one-side probability identities for the linear intercept, its estimated bias, their covariance and the corrected intercept. Deterministic coefficient certificates, full-estimator laws and variances, coverage, WLS rows and the realized significance comparison remain.
- **P033-T2:** omits an explicit higher differentiability conclusion. The functions are still the specified affine/quartic functions; continuity, polynomial identities, identical conditional laws, coverage, study-count non-identification and the variance identity remain. The restriction concerns the stated conclusion, not a nonsmooth replacement model.
- **P033-T5:** adds `dE != dI` and `0 < sd` to the general count-scaling clause. Its concrete binary witness and all its numerical conclusions remain.

The omissions **P033-T16–T18** are justified: these are empirical diagnoses, descriptions of the survey/reanalysis workflow, and published numerical summaries. The supplied definitions and toy constructions do not provide the empirical data and fully specified original procedures needed to certify those assertions. Each omission is assessed separately in `findings.json`. The source-derived numbers used in the mathematical targets are treated as stipulated premises, as standing assumption S7 directs.

The definitions use the ordinary Gaussian variance parameter, probability product measures, finite uniform populations, and conventional sample variance where its divisor is nonzero. The probability-law clauses include measurability; L2 conditions or the bounded/Gaussian constructions ensure finite moments. The caliper densities have finite unit integral, all conditional-probability denominators are positive where used, the quantiles and honest half lengths have nonempty bounded-below defining sets in their actual uses, and the finite sample/cluster witnesses are nonempty. The zero variance estimates arise from residual cancellation with positive true variances. The four natural overlap subtractions have genuinely nonnegative differences.

The fixed-score Gaussian examples are pointwise witnesses. Their statements and record labels do not claim validity over a maintained smoothness class, empirical refutation of the survey diagnosis, or certification of arbitrary clustered covariance models. None is labelled `refuted`.

Verification: `scratch/Check.lean` imports only `SAP.P033.Defs` and compiles with `/home/ubuntu/sap/tools/sap-lean scratch/Check.lean`. It checks genuine Gaussian probability measures, a standard-normal law premise, positive-variance independent Gaussian cluster premises, smoothness of the polynomial model, a binary sample, a nonnegative normalized integrable caliper density with positive window mass, and nonempty overlapping cluster sets. The density instance has conditioning probability `(2401/12500)^19 > 0` for 19 draws all in the stated caliper. Additional concrete instances are recorded per target.

`scratch/check_numeric.py` independently passes 47 checks: exact rational WLS determinants and rows, variances and covariance, observed fits, enumeration of the 1024 cluster-sign outcomes, representative shrinking-design formulas, exact binomial tails, and all stated Gaussian quantile/root/power enclosures. Gaussian calculations use a 100-digit Decimal CDF series and bisection; these numerical checks supplement the statement audit and are not Lean certificates. Results are in `scratch/numeric-results.json`.

No Solution or Comparator source was read, no `lake` command was run, and Lean processes were run one at a time. Both requested JSON audit files parse, cover the required theorem/target sets, and agree with these counts.
