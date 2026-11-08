# P034 statement audit

Five targets reviewed: **5 correct_whole; 0 correct_restricted;
0 restriction_inaccurate; 0 not_faithful; 0 vacuous; 0 false;
0 omission_ok; 0 omission_questionable.**

Severity counts: **none 5; minor 0; major 0.**

There are no adverse findings or questionable omissions.

| Target | Theorem | Verdict | Architect's decision |
|---|---|---|---|
| P034-T1 | SAP.P034.T1 | correct_whole | whole: accepted |
| P034-T2 | SAP.P034.T2 | correct_whole | whole: accepted |
| P034-T3 | SAP.P034.T3 | correct_whole | whole: accepted |
| P034-T4 | SAP.P034.T4 | correct_whole | whole: accepted |
| P034-T5 | SAP.P034.T5 | correct_whole | whole: accepted |

## Order and scope

The expanded mathematical reading was saved in `reading.md` before opening
`claims.json`. The comparison against canonical statements, definitions and
standing assumptions was saved in `claim-stage.json` before opening
`record.json`. No step-2 classification changed after reading the record.
Audit-history notes were not used to add or remove canonical clauses.

T4 is marked `broader` in the claim-stage comparison because its two
conditional contrast identities allow arbitrary real factor values, beyond
the required binary values. This true polynomial extension retains every
canonical conclusion, so the final verdict and the architect's full-coverage
decision are both `correct_whole`.

T1 and T3 prove the canonical constructed counterexamples. They do not
contradict the canonical claims themselves. Their docstrings describe the
complete-case-OLS justification and averaged-effect interpretation,
respectively, and do not assert that the actual survey estimates or printed
numerical table entries are false.

## Verification

All SAP definitions were expanded, including rational event conditioning,
the missing-outcome observation maps, real regression coefficients, general
event measures and integrals, independence, finite-vector L2, and the
Gaussian-square p-value. Positive finite weights and event probabilities
prevent totalized division from supplying T1's conclusions. For T2,
measurability and finite second moments ensure that the outcomes and all
required design products are integrable. Randomization and positive
potential completion give positive arm events. The common covariate law in
both completed arms gives orthogonality; multiplying the normal equations
by `(-p,1,0)` gives `p(1-p)β_T=p(1-p)τ`, with `p(1-p)>0`.

`python3 scratch/audit_checks.py` passed independent exact-rational checks
of the finite worlds, their independence and dependence assertions, all
observed-data cells, the sample's moments and Pearson statistic, and every
table percentage and count sum. Results are saved in
`scratch/exact-checks.json`.

Both scratch Lean commands completed successfully:

* `/home/ubuntu/sap/tools/sap-lean scratch/Check.lean` verifies every T2
  hypothesis in a four-point probability space with a varying covariate,
  nonzero effect and nonsingular Gram matrix.
* `/home/ubuntu/sap/tools/sap-lean scratch/Algebra.lean` independently
  proves T3Statement, T4Statement, T5Statement, and the p-value at zero.

These checks import only Defs, not the Challenge stubs. The printed axiom
dependencies contain no `sorryAx`. The general identification result was
also reviewed mathematically; this statement audit does not replace the
Comparator's proof certification.

`claim-stage.json`, `findings.json` and the exact-check output were parsed
and their target coverage and verdict counts checked with Python.
