# P009b statement audit

All 17 targets are acceptable at their declared scope: **8 correct_whole, 9 correct_restricted**. No false, vacuous, unfaithful, or inaccurately disclosed statement was found. No target was omitted. Every finding has severity `none`.

| Verdict | Count |
|---|---:|
| correct_whole | 8 |
| correct_restricted | 9 |
| restriction_inaccurate | 0 |
| not_faithful | 0 |
| vacuous | 0 |
| false | 0 |
| omission_ok | 0 |
| omission_questionable | 0 |
| **Total** | **17** |

There are no items requiring a correction. The whole targets are T18, T19, T25, T28, T30, T31, T32, and T33. These judgments concern the canonical mathematical claims, including their corrections and counterexamples, rather than endorsement of the paper's misprinted formulas.

The restrictions are substantive and accurately disclosed in both the record and the respective theorem docstrings:

| Target | Retained scope and disclosed exclusions |
|---|---|
| T20 | Both pointwise witness inequalities and eAVG ≤ C2². The aggregate proof chain and arbitrary supplied-indicator formulation are absent; the inputs are outcome-induced indicators, positive sizes, and pairings without fixed points. |
| T21 | All aggregate values and exact numerical discrepancies for the specified six-unit example. The individual contributing pairs and their conditional covariances are absent; convergence is not refuted. |
| T22 | Aggregate finite formulas, centre difference and bound, and corrected-centre convergence. Individual conditional covariances, the separately stated printed-centre convergence, and the three limiting regimes are absent. The convergence clause requires common regularity constants and q ≥ 4. |
| T23 | All twelve sampling integrals of signed bias, design variance, and MSE, plus the complete-design ratio identity. Integrability of each integrand is explicit. Universal fixed-baseline/support identities, ratio divergence, and identification with a joint sampling/assignment variance are absent. |
| T24 | The complete finite complete-interference exception for both designs and estimators, with fixed arbitrary baselines. The blanket empirical claim for other settings and certification of Monte Carlo entries are absent. |
| T26 | Mixing identities for supplied exponents, the exponent-one formula, positive normalized limit, and failure of little-o. The potential bound, maximal-order argument selecting exponent one, and the separately stated p=1/2 and p=1/3 comparisons are absent. |
| T27 | Atom bounds, finite approximation, and the error bound and limits for supplied minimizers. Existence of a minimizing sequence, the separate exponential-limit assertion, and the heavy-atom example are absent. |
| T29 | Every moment-chain link and the stronger absolute covariance endpoint, for natural powers. Non-natural powers are excluded. |
| T34 | Half-difference identity, endpoint and two-arm bounds, k ≥ 2, and Lemma A17. Both intermediate first-moment inequalities and the separately displayed weighted proof-chain equalities are absent. |

`reading.md` was saved before opening `claims.json`. `claim-stage.json` was then saved and parsed before opening `record.json`. The record check changed no stage-2 scope verdict. All 17 architect decisions agree with those independent judgments, and all nine declared restriction texts occur verbatim in their own theorem docstrings. There are no omitted targets whose justification requires assessment. Unused proof-helper rows in the record are not omitted claims; the Solution and Comparator were not inspected.

Definition checks found no convention that does the substantive mathematical work. Every operative conditional probability has a positive conditioning probability; T18 additionally protects the event probabilities in its likelihood ratios. Its natural subtractions are used within their nonnegative ranges. Positive sample sizes and diagonal interference give n·dAVG > 0 where needed. T30's real suprema are over nonempty bounded sets, and the symmetric nonnegative dependence matrix makes the unit-Rayleigh supremum the intended largest eigenvalue. The finite-law mixing supremum is also nonempty and bounded. The special mixing convention 0^0=0 agrees with Definition 9. Every occurrence of Hajek in a substantive population assertion has both arms nonempty on the design support. T23 assumes integrability of all twelve Bochner integrands explicitly. No limsup occurs.

Nonvacuity instances are recorded separately for every target in `findings.json`. They include positive-size complete and paired experiments, a growing bounded regular one-source study, a growing common-assignment study, an explicit minimizing sequence for T27, and an integrable two-unit sorted-pairing model for T23. Thus neither empty unit sets nor unattainable optimization hypotheses account for the conclusions.

Verification used `/home/ubuntu/sap/tools/sap-lean scratch/Check.lean`, which exited successfully and imports only the definitions. It checks normalized two-unit laws, Bernoulli/complete/paired design hypotheses, simultaneous regularity, the incoming-count condition, and sharp-law/distance examples. The final compiler output is in `scratch/lean-check.log`. No `lake` command was run, and at most one Lean process ran at a time.

Independent rational-arithmetic checks in `scratch/audit_checks.py` also exited successfully; results are in `scratch/check-results.json`. They reproduce the six-unit indicator/witness counterexample and all six-unit variance-gap values; check 84 one-source models for n=1,...,7, including their individual conditional covariances; check 240 count/arm and 284 supported-vector/arm cases of T18 for n=2,...,9; check the complete-interference support and MSE identities for both designs at n=2,4,6; and check T20 for all 4,100 reflexive directed indicator arrays at n=2,4 with the specified swap pairings. These finite checks supplement the statement analysis; they do not stand in for the general theorems.

For the two more substantial retained assertions, there are independent mathematical checks. In T22, conditioning on the source assignment makes the remaining outcome-square terms independent. The common moment bound bounds the deterministic baselines uniformly, and the variance of the normalized BER fluctuation is bounded by a constant times (n+b²)/[n+b(b−1)]², which tends to zero uniformly over 1≤b≤n. In T23, balanced complete-design signs give sampling-averaged variance 4 Var(X_i+U_i)/n=58/(3n). For paired randomization the error differences contribute 49/(3n), and adjacent Uniform[0,3] spacings have second moment 18/[(n+1)(n+2)], giving the remaining 36/[n(n+1)(n+2)]. The fixed design mean is zero and EATE is one, so the signed biases and MSE increments follow.

Both requested JSON outputs were parsed with Python 3 and checked for exactly one entry per target, correct theorem names, allowed verdicts, and complete required fields.
