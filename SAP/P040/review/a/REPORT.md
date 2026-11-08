All five architect decisions are supported. There are no adverse findings, omitted targets, or changes to the saved step-2 judgments.

|Verdict|Count|
|---|---:|
|correct_whole|4|
|correct_restricted|1|
|restriction_inaccurate|0|
|not_faithful|0|
|vacuous|0|
|false|0|
|omission_ok|0|
|omission_questionable|0|
|Total targets|5|

|Target|Theorem|Assessment of the record|
|---|---|---|
|P040-T1|SAP.P040.T1|Correctly restricted: only the assertion that the exact normal .975 quantile lies in [1.9599,1.9601] is omitted.|
|P040-T3|SAP.P040.T3|Correctly whole: the canonical retained mathematical content is P1 and P2.|
|P040-T2|SAP.P040.T2|Correctly whole: includes actual unique endpoints and uniform coverage of both exact confidence rules.|
|P040-T4|SAP.P040.T4|Correctly whole: identifies the actual adjusted regressions, HC1 statistics, and both normal rounding mismatches.|
|P040-T5|SAP.P040.T5|Correctly whole: includes both residual degrees of freedom, all eight fitted statistics, Student reference values, significance conclusions and minima, and the normal alternative.|

T1's declared restriction is accurate and complete. Its Challenge docstring explicitly names the omitted quantile assertion, retains the full multiplier range and both coverage calculations, and identifies the exact finite-sample calibration reading being challenged. It does not claim to refute the paper's nominal approximate-confidence interpretation. The canonical T3 statement explicitly retains only the estimate and reconstructed Wald arithmetic; neither its historical audit note nor the P3 interpretation mentioned in definitions_needed adds an exact-coverage assertion. T4's mismatch concerns the expressly defined normal-reference calculation. None of these targets is mislabelled as a refutation of its own canonical assertion.

The manipulation-check passage, the normal-reference description in Methods, the two reported reference values, and the relevant Table 1 entries agree with the canonical transcriptions at the cited locations. See the [paper, pp. 3–5](https://springerplus.springeropen.com/counter/pdf/10.1186/s40064-016-2303-5#page=3). The audit uses the 30 rows specified in standing assumption S6(d), rather than interpreting the article's trial duration as the regression sample size.

The definition audit found no vacuity or reliance on totalized exceptional cases. The count space has 16 elements, the multiplier interval contains 1.96, the probability parameter domain contains .8 as well as its endpoints, and both regression index types and outcome types are inhabited. Binomial weights are nonnegative and normalized on [0,1]. All invoked matrix inverses are nonsingular, variance denominators are positive, and residual-degree subtraction is ordinary 30−2 or 30−9. Positive Student degrees of freedom make the real-power bases and Gamma denominators positive. All reference integrands are continuous on the finite intervals used. Endpoint existence and regression nondegeneracy are asserted conclusions, not assumptions used to make the results vacuous.

For T2's coverage claim, fix p in [0,1]. If there is a count with inclusive upper tail below alpha, take the smallest such count: the probability of the upper-tail rejection event is its own tail probability, hence below alpha. The analogous largest count for a lower-tail rejection has probability below alpha. Empty rejection sets have probability zero. The union bound gives equal-tailed coverage at least 1−2/40, and the single rejection event gives one-sided coverage at least 1−1/20. This argument includes the degenerate binomial laws at p=0 and p=1. A grid of numerical examples is only a supplementary check.

The independent exact-rational checks in `scratch/audit.py` reproduce every data row, ranks 2/9/9, Gram determinants 224 and 323086400, positive HC1 variances and all eight exact squared statistics, the binomial obstruction and Wald coverage fractions, and root brackets by rational bisection. Rational squared comparisons at both multiplier-range endpoints, together with monotonicity of radius in positive z, verify the full-range Wald membership patterns. The normal and Student reference values and every stated decimal enclosure were corroborated by 80-digit Decimal series calculations; these numerical calculations are not claimed as Lean proofs or certified interval arithmetic. Results are saved in `scratch/audit-results.json`.

`/home/ubuntu/sap/tools/sap-lean scratch/Check.lean` completed with exit code 0. It checks explicit nonvacuity witnesses, the multiplier range, count-14 mass, proportion rounding, positive witness variances and exact statistic identities, and the recorded day/treatment totals. It imports only `SAP.P040.Defs`; no Challenge theorem or Solution proof is used. The broader finite-sum scratch attempt exceeded its tactic budget; the final successful scratch file contains the selected nonvacuity checks, while the full finite sums were checked independently in rational Python arithmetic. No `lake` command was run, and no more than one Lean process was run at a time.

The blind reading was saved in `reading.md` before opening `claims.json`. The per-theorem comparisons were saved in `claim-stage.json` before opening `record.json`. The final per-target decisions are in `findings.json`; no restriction or omission was inferred from historical notes or from the record in place of the canonical claim.
