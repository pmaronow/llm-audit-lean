# Palomar statement referee report: P011b

Audited all 14 targets and their Challenge statements. Verdicts: **10 correct_whole; 4 correct_restricted; 0 requiring correction; 0 omissions.** All severities are `none`.

| Verdict | Count |
| --- | ---: |
| correct_whole | 10 |
| correct_restricted | 4 |
| restriction_inaccurate | 0 |
| not_faithful | 0 |
| vacuous | 0 |
| false | 0 |
| omission_ok | 0 |
| omission_questionable | 0 |

There are no non-`correct_*` / non-`omission_ok` items to report.

## Accepted restrictions

- **P011-T15:** The two star counterexamples and exported regression, saturation, expectation and probability-limit facts are correct. The docstring accurately identifies the unexported covariate-sum/Gram identities, separate centre conditional-law/range assertions, and coordinate mean-offset identities. Its coverage statement explicitly uses `sqrt(max(V1,0))` and makes no equivalence assertion for the partially defined printed interval.
- **P011-T16:** Scaling is explicitly imposed even on finite exact identities. The docstring correctly lists the unexported weighted-mean and OLS coefficient/target identities, raw consistency and maximal-conservativeness criteria, equal-mean corollary, estimator-shift and intercept/slope specializations, and perturbation inequality with convergence of its bound. The retained moving-bias limit, residual and centered-vector identities, and final residual conclusions match the canonical claim on that domain.
- **P011-T19:** The factorization, sample-variance remainder limit and consistency under vanishing mean spread are correct. The unexported factor-ratio identity, equal-mean specialization, and insufficiency assertion are disclosed. Positive common variance at every size matches the canonical domain.
- **P011-T24:** Only formal content (i) is exported. The omitted observed-data correction, homoskedasticity index correction, all statistical and scope assertions of (ii), and edge-set typography correction are fully disclosed.

All 14 architect decisions agree with the independently saved claim-stage assessment. The four restriction strings in `record.json` exactly match the Challenge docstrings. No step-2 verdict was changed after reading the record. No target is recorded as omitted.

## Verification and nonvacuity

The blind expansion is saved in `reading.md`; the pre-record comparisons are saved in `claim-stage.json`; per-target results and nonvacuity evidence are in `findings.json`.

`/home/ubuntu/sap/tools/sap-lean scratch/Nonvacuity.lean` passed with exit status 0 and no diagnostics, importing only the definitions. It checks nonempty upper-edge coordinates at n=3, graph compatibility, existence of all real-valued Dirac moments, full rank and uniform Gram regularity of the intercept design at every positive n, a compatible maximizer with strictly positive sample variance, and an exact helper discrepancy.

`python3 scratch/exact_checks.py` passed. Its rational enumeration independently checks both star block laws and constants, the path correlations, the strict fair-sign event probabilities, the unique three-vertex optimizer, and the positive-mass three-point witness. Results are saved in `scratch/exact_results.json`; mathematical joint family instances and the probability-limit arguments are detailed in `scratch/nonvacuity.md`. The exact finite computations support those arguments; they are not a replacement for the asymptotic reasoning.

The mathematical definitions and their domains were checked through the Mathlib definitions. In particular: all relevant sample-size denominators are positive; raw moment existence is stated separately from weighted moments; covariance matches the genuine centered-integral covariance where required; zero-variance correlations use the canonical convention; the quantile is used only for 0<alpha<1; and the complete-graph zero-V1 example uses no division by V1. The independent-sign intercept family satisfies every T16 hypothesis and its conditional design bounds, and it satisfies T19 with strictly positive common variance at every size.
