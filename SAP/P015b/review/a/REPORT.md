# Referee report

All 12 targets have Challenge stubs. The three whole decisions, seven restricted decisions and two scoped refutation decisions in the architect’s record are supported by the statement audit. The refutations are classified below as `correct_restricted`, because that is the output category for their valid, explicitly disclosed scope.

| Verdict | Count |
| --- | ---: |
| `correct_whole` | 3 |
| `correct_restricted` | 9 |
| `restriction_inaccurate` | 0 |
| `not_faithful` | 0 |
| `vacuous` | 0 |
| `false` | 0 |
| `omission_ok` | 0 |
| `omission_questionable` | 0 |

There are no non-`correct_*` findings and no omitted targets.

## Record review

| Target | Architect decision | Assessment |
| --- | --- | --- |
| P015-T9 | `whole` | Whole: the exact group example, arbitrary-vector formula and raw-data GLS are all present. |
| P015-T10 | `restricted` | Restriction accurate: all four finite-matrix obligations are retained; separate causal and optional asymptotic assertions are excluded explicitly. |
| P015-T20 | `whole` | Whole under the brief’s population-leverage interpretation; every requested rational and rounding is present. |
| P015-T14 | `restricted` | Restriction accurate: only the unconditional-display impossibility is retained; the corrected conditional model is explicitly excluded. |
| P015-T21 | `restricted` | Restriction accurate: the score formula is confined to the full-rank domain; the unrestricted affine identity and full-rank root result are retained. |
| P015-T11 | `whole` | Whole: genuine Taylor polynomials, all degrees, exact radius, unique fit and the treatment-equation error are present. |
| P015-T15 | `restricted` | Restriction accurate: standard Borel space, eventual sample rank, explicit integrability, and the missing conditional-product/counterexample components are disclosed. |
| P015-T22 | `restricted` | Restriction accurate: the actual-estimator limit is retained on the stated stronger space, rank and integrability domain. |
| P015-T23 | `restricted` | Restriction accurate: the actual fitted-weight mean is used with the disclosed regularity, eventual rank, positive sum and integrability conditions. |
| P015-T24 | `restricted` | Restriction accurate: the actual-estimator limit and four population identities are retained; the independence and intermediate-ratio statements are expressly excluded. |
| P015-T18 | `refuted` | Refutation justified: the valid logistic implication and a causal, genuine square-link ML counterexample refute the universal scaling assertion. The named-family substitution assessment is expressly excluded. |
| P015-T17 | `refuted` | Refutation justified: positive variance is proved on the declared domain, while the small-weight, zero fitted-weight and multivalued missing-pair examples refute the stated general implications. |

## Scope and validation

`reading.md` was saved before opening `claims.json`; `claim-stage.json` was saved before opening `record.json`. No step-2 verdict was changed after reading the record. Only the permitted definitions, challenge, claim/record files and Mathlib sources were used; no Solution or Comparator was read.

The eventual almost-sure sample-rank assumptions are stronger than nonsingularity with probability tending to one. They exclude nondegenerate iid binary-treatment sampling, whose all-equal-treatment event has positive probability at every finite sample size. This is substantial but accurately disclosed, and the continuous iid constructions in the findings satisfy every premise. It is therefore a restriction, not a vacuous domain.

The finite identities listed in the brief as proof lemmas are not all separate exported conclusions. The retained numbered algebraic content and headline limits are assessed as such; no proof of an auxiliary identity is inferred from a row name in the record. The record consistently describes these as supporting lemmas. This does not alter any saved step-2 scope judgment.

Validation completed:

- `/home/ubuntu/sap/tools/sap-lean scratch/Nonvacuity.lean` passed with no errors or `sorry`. It checks nonempty full-rank matrix premises, positive cell denominators, the leverage determinant, a normalized small-weight example, and interior square-link parameters/probabilities.
- `python3 scratch/exact_checks.py` passed. It independently checks rational matrix inverses, raw GLS, coordinate pooling, all leverage numbers and roundings, weight normalizations, IPW expectation/variance, fitted sample residuals, and both square-link ML derivatives.
- `scratch/audit_details.md` gives full-hypothesis nonvacuity constructions, an all-degree Taylor bound, the ML-branch strict-concavity/implicit-derivative argument, and why the positivity counterexamples contradict the printed readings. The finite numerical Taylor check is not used as a universal proof.
- `claim-stage.json` and `findings.json` parse with Python and contain exactly one matching entry per target; all required verdicts, severities and fields were checked.
