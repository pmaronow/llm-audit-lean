# P043 statement audit

All six architect decisions are supported: **2 correct whole, 3 correct restricted, 1 justified omission**. No inaccurate restrictions, unfaithful statements, vacuous statements, false statements, or questionable omissions were found.

| Verdict | Count |
|---|---:|
| correct_whole | 2 |
| correct_restricted | 3 |
| restriction_inaccurate | 0 |
| not_faithful | 0 |
| vacuous | 0 |
| false | 0 |
| omission_ok | 1 |
| omission_questionable | 0 |
| **Total** | **6** |

| Target | Theorem | Assessment |
|---|---|---|
| P043-T1 | SAP.P043.T1 | Correct restricted: the omitted explicit statewise cancellation, integer-knowledge, and conditional support arm-mean equalities are accurately listed. The defined witnesses themselves satisfy those omitted equalities. |
| P043-T2 | SAP.P043.T2 | Correct whole: arbitrary probability laws, exactly five integrable potentials, all comparisons and null implications, linear and ratio formulas, and the net-channel sign condition. |
| P043-T3 | — | Omission justified: the canonical passage is contextual empirical and interpretive prose; the mathematical witnesses and repair do not certify those clauses. |
| P043-T4 | SAP.P043.T4 | Correct restricted: the universal normalized nonnegative weighted-average assertion and exact five-type increaser probabilities are omitted as disclosed. Both witnesses and full-law nonidentification remain. |
| P043-T5 | SAP.P043.T5 | Correct restricted: finite populations; identification/covariance results retain the outer monotonicity and positive-first-stage premises. Arbitrary-model signed value-set membership, the particular down-type equality, and separate nonidentification are omitted as disclosed. |
| P043-T6 | SAP.P043.T6 | Correct whole: corrected observation/stratum indicators, their identities, and the equivalent stratum-intercept equation. |

There are no items outside `correct_whole`, `correct_restricted`, and `omission_ok`, so no corrections are required. All severities are `none`.

## Audit order and evidence

`reading.md` was saved before opening `claims.json`. `claim-stage.json` was saved and parsed before opening `record.json`. No step-2 judgment was changed after reading the record. Canonical statements, their definitions, and standing assumptions determined scope; audit-history notes were not used to remove clauses. In particular, T5 remains restricted even though its note says a finite population suffices.

The counterexample docstrings correctly identify the readings they refute. T1's witnesses violate D≥0 and refute an unconditional extension, while leaving the paper's contextual conditional intact. T4 refutes the stated reading of the IV guidance under assignment independence, exclusion, consistency and a positive first stage. Neither theorem is presented as a refutation of an empirical estimate.

The definitions were followed into Mathlib's Bernoulli law, probability-measure class, integrability predicate and Bochner integral. Assignment is an independent product law and consistency/exclusion are encoded directly in the observed responses. Probability weights sum to one, assignment probabilities are nondegenerate, fixed increaser events have positive probability, and T5 filters its conditional effects to positive-probability margins. No conclusion is assumed by a hypothesis. The one-stratum regression and nonempty sample cases prevent empty-index conventions from doing the work.

`/home/ubuntu/sap/tools/sap-lean scratch/Check.lean` exited successfully. It imports only Defs and proves concrete nonvacuity instances for T2, T5 and T6, a mixed-sign channel example, and the three IV increaser probabilities. `python3 scratch/exact_checks.py` passed an independent exact-rational enumeration of all fixed finite populations, checking their numerical and distributional assertions. General mediation and IV formulas were also checked algebraically against their expanded definitions. No Solution or Comparator file was read, and `lake` was never run.
