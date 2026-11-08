# P042 statement audit

All six targets are **correct_restricted**. No mathematical error, vacuity, undisclosed restriction, or incorrect claim of refuting the printed empirical results was found.

| Verdict | Count |
| --- | ---: |
| correct_whole | 0 |
| correct_restricted | 6 |
| restriction_inaccurate | 0 |
| not_faithful | 0 |
| vacuous | 0 |
| false | 0 |
| omission_ok | 0 |
| omission_questionable | 0 |

Severity: none 6, minor 0, major 0. All six canonical targets have a theorem; no target is omitted. There are no items requiring correction.

## Order and comparison with the record

`reading.md` was saved after reading all Defs and Challenge files and following the probability definitions into Mathlib, before opening `claims.json` or `record.json`. `claim-stage.json` was saved before opening `record.json`. Every stage-two verdict was `narrower`; none was changed after reading the record. The audit treated `statement`, `definitions_needed`, and standing assumptions as the claim, without using the audit-history notes to remove clauses.

All six architect decisions are `restricted` and agree with the independently identified scopes:

| Target | Accurate, disclosed scope |
| --- | --- |
| P042-T1 | Both complete finite witnesses and exact coverage at 49/25 are retained. Only the assertion that using the standard normal quantile preserves thresholds 19 and 24 is omitted. |
| P042-T2 | General clauses (i)–(viii) and variance-based half-width identities are retained. Historical application, covariance estimation, numerical recalculations, staged-size and overlap bounds, inference labels, and rejection of the old GGL-only certification are omitted. |
| P042-T3 | All fixed and DerSimonian–Laird numerical calculations and rounding bounds for z in [1.9599,1.96] are retained. Containment of the standard normal quantile in that interval is omitted. The refutation concerns the fixed-effects reading of Note 5. |
| P042-T4 | Fixed-effects rounding, positivity, conditional stochastic variance, and alternative numerical calculation are retained. Normal-quantile containment and implementation/disclosure of the textual and replication-program repairs are omitted. |
| P042-T5 | Only the two unconditional variance readings are refuted. Historical point estimates, treatment counts, intervals, significance, and the qualitative assertions about sizes, scales and treatments are explicitly omitted. |
| P042-T6 | Every formula in formal reading (a), (b1)–(b4) is retained, under its stated finite-population/contact model. Broader assignment designs and a separate general distributional independence assertion are omitted. The model assumptions already appear in the canonical formal reading. |

The inspected pooling, randomization, and Note 5 passages agree with the transcriptions used in the audit. In particular, the paper gives verbal pooling guidance; the unconditional variance formulas are supplied by the audit reading. The Challenge docstrings preserve that distinction. See the corrected [article copy, pp. 30–31 and 40](https://cpb-us-e1.wpmucdn.com/sites.northwestern.edu/dist/b/3288/files/2019/10/2013-GMA-Field-Experiments-Turnout.pdf).

## Definition and nonvacuity checks

`MemLp` at exponent 2 supplies measurable finite second moments on the stated probability spaces. Thus the uses of Mathlib's Bochner integral, real-valued variance and covariance have their intended statistical meanings; nonintegrable-integral and infinite-variance fallback values do not establish these results. Positive variances and nonempty pools guard precision-weight denominators. Positive feasible group sizes guard all sample and population denominators, including natural N−1 and N−m. In `coverageCount`, natural truncated subtraction implements the intended lower endpoint max(0,2x−r).

The finite laws use actual nonempty allocation sets and uniform averages. The fourth label in the three-arm definition correctly represents the unallocated remainder when group sizes sum to less than N. The independent-arm law needs only pairwise independence for its second-moment conclusions, a sound generalization. The covariance bound's equality clause has exactly the canonical common-factor hypothesis. No hypothesis assumes the pooled-variance, rounding or CACE conclusion. The CACE identity is a ratio of expectations; it asserts no unbiasedness of the sample ratio.

Nonempty, positive-variance instances are detailed for every target in `findings.json`.

## Verification

- `/home/ubuntu/sap/tools/sap-lean scratch/Check.lean` completed successfully, without warnings or errors. It imports only `SAP.P042.Defs`, enumerates the six-person moments and allocation counts, checks a positive complier count, proves square integrability and variance 1 for an actual probability-space sign, and constructs a pooling-variance counterexample using the SAP definitions.
- `python3 scratch/check_exact.py` completed successfully. It independently enumerates the six-person witness; computes the binomial convolution, exact coverage fraction and bounds; checks every fixed and random-effects fraction and endpoint inequality using rational arithmetic; and verifies explicit stochastic, remainder-arm and contact-model instances. Results are saved in `scratch/exact-results.json`.
- The two binomial coverage probabilities are approximately 0.8886829667422668 and 0.9546954675333121. The claimed exact fractions and strict comparisons pass.
- All JSON deliverables were parsed with Python, and target/theorem coverage, verdict values and counts were checked.

These checks support the statement audit. They do not use Solution proofs or claim to implement any omitted historical or editorial repair.
