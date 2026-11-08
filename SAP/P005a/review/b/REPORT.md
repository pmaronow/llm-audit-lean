# Palomar statement audit: P005a

14 targets; 13 Challenge theorems. The blind reading was saved before claims.json was opened, and claim-stage.json was saved before record.json was opened. No step-2 verdict was changed after reading the record.

| Verdict | Count |
|---|---:|
| correct_whole | 2 |
| correct_restricted | 11 |
| restriction_inaccurate | 0 |
| not_faithful | 0 |
| vacuous | 0 |
| false | 0 |
| omission_ok | 1 |
| omission_questionable | 0 |

There are no items classified as restriction_inaccurate, not_faithful, vacuous, false, or omission_questionable. No fixes are requested.

## Scope decisions

Whole: P005-T6 and P005-T13.

Restricted: P005-T1, T2, T3, T4, T5, T7, T9, T10, T11, T12 and T14. Each retained mathematical conclusion agrees with the canonical claim. The Challenge docstrings disclose the omitted computations or conclusions and the applicable extra scopes. The eleven restriction texts match record.json. T9 retains only logarithm facts; it does not certify the estimator expansion.

P005-T8: omission_ok. The record identifies the available expansion row as conditional on the unproved proposition Tropp2011RowSampling. That premise is absent from the canonical hypotheses. Omitting the expansion instead of adding the cited result as an assumption is justified on the available evidence. The canonical text itself identifies a matrix concentration argument as a substantial input; no unconditional replacement is visible in the supplied Challenge/Defs. The external formalization was not inspected, so the assertion that this is the only credited row is assessed from the record, not independently certified. The logarithm equivalences remain in T9.

## Mathematical checks

The finite uniform assignment law, arm-size covariance divisor, population centering, residuals, both OLS slope formulas, bias weights and quantifier order of observed-outcome factorization agree with the supplied paper definitions. The supremum defining kappa is over a nonempty finite set at every substantive population size. All finite expectations use nonempty designs; all asserted inverse-dependent regressions have determinant or positive-variance conditions. Singleton covariance arms are mathematically zero and do not use division by zero. Positive-dimensional examples exist for every universal theorem, so empty coordinate types do not do the work.

The custom stochasticO has the correct epsilon / constant / threshold order on the varying finite probability spaces. Mathlib IsBigO is an eventual absolute-value bound. Eventual standardization, common moment/allocation constants, initial-size conventions and positive-dimension requirements were checked explicitly. The positive square-root rates cannot vanish through an empty-population convention. The d=1 logarithm endpoint in T7 is the ordinary log(1)=0 and is the intended defect of the printed condition.

scratch/Check.lean compiled successfully using /home/ubuntu/sap/tools/sap-lean, importing only Defs. It checks a nonzero-dimensional standardized population, nonempty size-2 and size-4 designs, a nonzero arm determinant, the signed third-moment coefficients, and the honest singleton covariance case. No Solution theorem was imported.

scratch/audit_checks.py independently recomputes every retained numerical expectation/variance in T1, T3, T5, T10 and T12 with exact rational arithmetic, including all 12870 assignments for T3. It also checks all-assignment positive arm variances, representative universal formulas including boundary arm sizes, and the spike-sequence remainder for n=6,8,10,12. Results are in scratch/exact-results.json. Finite checks support the calculations; they are not substituted for the universal or asymptotic statements. The asymptotic claims were also checked against their mathematical content and nonvacuity constructions in findings.json.

The author rule permits narrower statements. This assessment approves only the retained, disclosed scopes; it does not claim that all canonical clauses or the omitted estimator expansion have been formalized.

## Artifacts

* reading.md: saved blind mathematical reading of all thirteen theorems.
* claim-stage.json: saved pre-record comparison, thirteen objects.
* findings.json: final assessment, fourteen objects in claims.json order.
* scratch/: independent Lean and exact-arithmetic checks.
