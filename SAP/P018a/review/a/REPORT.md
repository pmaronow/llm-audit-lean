# Statement audit of P018a

All 14 targets have a Challenge theorem. The architect's decisions are supported by the statements: three cover the full canonical mathematical content, and eleven are correct with accurately disclosed restrictions.

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

Severity: 14 none, 0 minor, 0 major. There are no adverse findings to list and no fixes required.

T4, T6 and T14 cover the full canonical content. T6's covariance and GLS identities and T14's incidence identity are valid generalizations; their `broader` labels in `claim-stage.json` record those extensions, while `correct_whole` in `findings.json` records full coverage. No claim-stage classification was changed after reading the record.

For T1–T3, T5, and T7–T13, the restriction text in `record.json` matches the Challenge docstring and accurately describes the retained content, omitted assertions and added premises. In particular, T5 discloses the independence and finite-moment premises for its variance bound; T8 discloses eventual almost-sure strict positivity for its normal pivot; T10 discloses the narrower symmetric single-record weighted model; and T12 discloses almost-everywhere linearizations and positive total record counts. All dropped subclaims are treated as restrictions, rather than as proofs of the full canonical claims. No target is marked omitted.

`reading.md` was saved before opening `claims.json`. `claim-stage.json` was saved and parsed before opening `record.json`. The reading follows the SAP definitions through Mathlib's matrix inverse, covariance, variance, integrals, conditional expectation, Gaussian law, independence, measurability and finite-dimensional norms. The relevant probability laws are proper; actual dyads are nonempty at the stated finite sizes; rank and integrability protect the retained ordinary statistical formulas. Infinite inverse moments use extended nonnegative integrals. The asymptotic singular-sample extensions do not determine the probability limits.

Validation: `/home/ubuntu/sap/tools/sap-lean scratch/Check.lean` completed successfully using only Defs. It verifies a nonvacuous Standing instance, three dyads at N=3, the logistic design/bread determinants and the six-dyad structural premises. Its named Standing proof has only the standard axioms `propext`, `Classical.choice` and `Quot.sound`. `python3 scratch/exact_checks.py` passed independent rational integration and finite calculations for the nonlinear moments, logistic witness, GLS comparison, negative N=8 slope estimate, exhaustive eight-sign covariance values, sign-meat formulas, and concentrated-weight/repetition coefficients and event bounds. Analytic instances for the remaining quantified premises are recorded per target in `findings.json`. These checks assess statements; they do not inspect or re-certify Solution proofs.
