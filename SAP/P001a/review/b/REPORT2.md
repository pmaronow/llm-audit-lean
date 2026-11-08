Revision 2: **both earlier major findings are fixed**. All 19 targets are acceptable at their declared scopes; no new adverse finding remains.

| Findings verdict | Count |
| --- | ---: |
| correct_whole | 3 |
| correct_restricted | 16 |
| restriction_inaccurate | 0 |
| not_faithful | 0 |
| vacuous | 0 |
| false | 0 |
| omission_ok | 0 |
| omission_questionable | 0 |

The revised record has 2 `whole`, 8 `restricted`, and 9 `refuted` decisions. All labels are justified. `findings2.json` retains the requested original verdict vocabulary: the complete T3 counterexample remains `correct_whole` although its record decision is now `refuted`; the other eight accepted refutations remain `correct_restricted` because their diagnostic omissions are still disclosed. Together with record-whole T2 and T10, this gives the counts above. No invented `correct_refuted` verdict is used.

| Earlier finding | Disposition | Revised evidence |
| --- | --- | --- |
| T8: zero-extended sampled log objective and parameter-dependent exceptional sets | **Fixed** | `Defs/Part3.lean:198–200` supplies one measurable common observation set, true joint probability one, and positivity for every fitted parameter at every point of that set. The restriction docstring now discloses it. |
| T12: the same defect in its independent compact-consistency clause | **Fixed** | `Defs/Part4.lean:73–75` adds the same premises for the fitted mixture, with matching disclosure. Its separate normality/efficiency clause remains unchanged and already had common-set positivity. |

All components of both earlier findings are resolved. `Real.log 0 = 0` remains the underlying Mathlib convention, but the new premises prevent zero arguments simultaneously at all candidate parameters on one full-probability sample event. The prior diagonal-zero example is excluded: for each outcome y in [1/4,3/4], candidate t=y would have zero density, so a common positive set would have to exclude that entire interval, which has true probability 1/2. Neither correction assumes consistency, normality, efficiency, or any other conclusion.

I compared every revised definition and theorem with the saved blind `reading.md`. The mathematical changes are the three new common-set premises in T8's second clause and T12's second clause. Their conclusions are unchanged. The other T8 clauses (the KL identity, compactness-to-separation, and true-model identification) and the other T12 clauses (nonidentification and the combined normality/efficiency result) retain their previous content. T17 moved from Defs Part4 to Part5 without a mathematical change. No other change of mathematical content was found; the nine refutation labels and their docstrings were reviewed separately below. The original blind reading and first-round output files were preserved.

The new quantified data in each changed consistency clause are a set commonS of covariate/outcome pairs, its measurability, its true joint probability one, and positivity for all parameters in Theta at all points of commonS. This is one fixed set; it does not depend on a sample size, realized sample, or chosen estimate. IID equality of laws transfers membership in this measurable set to each observation. Intersecting the countably many observation events then yields a single full-probability event on which every observation has positive density at every candidate parameter. Thus both the supplied estimate and data-dependent competitors use ordinary positive-density logarithms there. This avoids the invalid interchange of an uncountable parameter quantifier with an almost-everywhere quantifier.

The changed statements remain nonvacuous. For both, use a genuine one-coordinate parameter t in [1/4,3/4], an independent one-coordinate fair-sign covariate, a Bernoulli(1/2) true outcome, and reference measure delta_0+delta_1. The set commonS=R^1 times {0,1} is measurable and has true probability one; every candidate Bernoulli density is at least 1/4 there. For T12 take one component of weight one. The clipped sample mean maximizes likelihood. For positive n the uniform log error is bounded by log(3) times the sample success-proportion error, and the zero-sample bound can be assigned log(4). These are finite real envelopes satisfying the stated limits. The strongest unchanged T12 clause also admits this regular model: its information is 4, the information inverse is 1/4, and the ordinary sample mean has regular influence Y−1/2 with that covariance. Detailed nonvacuity instances for every target appear in `findings2.json`.

The zero-sample uniform-envelope restriction remains material and correctly disclosed in both targets. T12 also still discloses the joint QMD premise for normality and efficiency and its explicit local integrability premise for the squared square-root-density remainder. The repairs introduce no nonintegrable integral, unbounded real supremum, empty index set, or zero denominator that supplies a conclusion. Exceptional finite-sample OLS conventions elsewhere have unchanged asymptotic scope and were already covered by the first review.

Every revised label was checked against the canonical claim, rather than inferred from the architect's report:

| Target | Revised decision | Assessment |
| --- | --- | --- |
| T1 | refuted | The normalized finite-second-moment CDF perturbations have directions tending uniformly to zero while their mean quotients stay one, contradicting the printed Hadamard-differentiability implication. Positive perturbation scales and genuine summable masses supply the witness. The omitted diagnostic identities remain disclosed. |
| T2 | whole | Both canonical clauses remain: the empirical mean identity and finite-positive-variance CLT, and the finite-variance zero-direction counterexample. It does not falsely credit the CLT to a functional derivative. |
| T3 | refuted | The explicit negation of the printed PDA contract and the bounded independent gap-law example still exhibit two C1 CEF extensions with different derivatives at the covariate mean. It is also the complete canonical counterexample. |
| T4 | restricted | The derivative-gated equality-on-U assertion and use of global integrable measurable CEF versions are disclosed exactly as before. |
| T5 | refuted | The supplied least-squares fit exists in the stated iid experiment. The local integrated-L2 failure along fourth-power sample sizes contradicts the printed sufficient degree rate. Measurable-selection existence and the separate endpoint bound remain disclosed omissions. |
| T6 | restricted | Stable-Gram consistency, envelope-rate sufficiency, arbitrary-interval cubic stability and the explicit [0,1] finite bounds retain their stated scope. The fit-selection and general-interval finite-bound omissions remain accurate. |
| T7 | refuted | The unique clipped MLE converges to 1/2 and not either unique fixed-covariate KL target. The positive four-atom experiment satisfies the intended hypotheses; omitted derivative formulas and exact KL gaps are still disclosed. |
| T8 | restricted | The added common-set hypothesis fixes the earlier defect and is disclosed. The other retained clauses and all-size envelope limitation remain accurate. |
| T9 | refuted | Unbounded likelihood on the specified positive sample (1,2,3) rules out the printed unrestricted maximizer. All scales and rates are positive. Missing quantitative path bounds remain disclosed; the general positive-sample result remains in T10. |
| T10 | whole | Both canonical clauses remain: unboundedness/nonattainment on every nonempty positive sample, and compactness, likelihood continuity and attainment on every nonempty stated restriction. The extra empty-sample compact case is harmless. |
| T11 | refuted | Two distinct full parameters give the same normalized iid experiments, and an attained MLE selection fails consistency at a truth. This refutes the canonical unqualified full-vector claim; it does not claim to refute a version that assumes identification and uniqueness. Omitted mass rewritings and the separate upper bound remain disclosed. |
| T12 | restricted | The standalone consistency clause is now repaired and disclosed; the independent nonidentification and stronger combined regular normality/efficiency clauses retain their earlier scopes. |
| T13 | refuted | Valid for the canonical universal bias-only calibration reading: the explicit admissible unbiased design has positive sampling-variance limit and inconsistent bootstrap variance. These imply failure of the corresponding consistent scaled standard-error assertion. The docstring explicitly confines the reading and does not refute a literal hedged “likely” assertion or empirical table entries. The second-moment premises are satisfiable in the bounded design. |
| T14 | restricted | The bounded hot-deck example and fixed-score/response weighted-sign variance identity retain their disclosed scope, including a meaningful no-responder case. |
| T15 | restricted | It continues to assert true-score failure and intercept consistency only. It does not claim the full estimated-score refutation or a literal refutation of the hedged footnote. |
| T16 | restricted | Estimated-score failure, common-translation donor/statistic identities and the conditional control-reuse variance identity retain their scope. The added L2 premises and omitted inference claims remain disclosed. |
| T17 | refuted | The actual conditional-independence null has nonzero placebo coefficient and F/Wald rejection probabilities tending to one. The full-rank positive twelve-atom experiment gives a genuine counterexample to the canonical test-size reading. The 240 quantities remain expressly risk arithmetic, and no sample certificate or pre-treatment predicate has been added. |
| T18 | restricted | The population CEF/least-squares result and its counterexample without linear specification are unchanged. Asymptotic inference conclusions remain outside its disclosed scope. |
| T19 | refuted | Positive normalized countable arm-cell masses give complete discrete overlap with no uniform positive propensity margin. This refutes the printed converse/failure implication in the canonical reading; it does not refute positivity implying overlap. The explicit rate and selected index remain disclosed omissions. |

The revised record and architect report accurately account for both earlier adverse findings. All sixteen non-null restriction fields match the Challenge docstrings verbatim, all nineteen theorem names agree, and all nine `refuted` docstrings carry the stated refutation prefix. The prefixes alone were not treated as evidence of a mathematical refutation.

Verification: `/home/ubuntu/sap/tools/sap-lean scratch/DeltaCheck.lean` passed with exit code 0 and no output. It imports only Defs and proves common-set transfer to all iid observations, positivity of each finite likelihood and the ordinary sample-log identity, and a nontrivial positive-dimensional Bernoulli instance of both added positivity premises. No Challenge or Solution theorem is used. Lean checks were sequential and no `lake` command was run. `findings2.json` was parsed and checked with Python for all 19 target entries and the original schema. No adverse item remains to list and no fix is requested.
