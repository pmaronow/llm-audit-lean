# P001a: revision 2 delta review

| Finding verdict | Count |
| --- | ---: |
| correct_whole | 3 |
| correct_restricted | 16 |
| restriction_inaccurate | 0 |
| not_faithful | 0 |
| vacuous | 0 |
| false | 0 |
| omission_ok | 0 |
| omission_questionable | 0 |
| **Total** | **19** |

There are no outstanding adverse findings. All nineteen decisions in `record2.json` are acceptable at their declared scopes: **2 whole, 8 restricted, 9 refuted, 0 omitted**. All nine refutation labels are accepted.

`findings2.json` retains the original verdict vocabulary, which has no `correct_refuted` value. T3 remains `correct_whole` because its canonical claim is itself the complete PDA counterexample; the architect now correctly labels its relation to the printed assertion `refuted`. The other eight refutations retain `correct_restricted` because their disclosed counterexample clauses are incomplete relative to the full canonical counterexamples. These findings do not relabel the manifest or credit those eight with clause completeness. The two manifest `whole` targets are T2 and T10.

## Earlier findings and repair disposition

My round-1 `findings.json` recorded **zero adverse findings**. Consequently there were no earlier requested fixes to classify as fixed, partly fixed, or not fixed. All previously accepted omissions remain disclosed; no omitted clause is represented as having been restored.

My earlier approvals of T8 and T12 nevertheless missed the real logarithm faithfulness problem identified by the other referee and acknowledged in `architect-report.md`. Parameterwise positivity almost everywhere does not imply simultaneous positivity for a parameter selected from the observations. Since `Real.log 0 = 0`, maximizing the formal sum of logarithms could cease to mean maximizing an ordinary likelihood, even though every fixed-parameter probability law remained unchanged. The old formal argmax implications need not be false for this objection to matter.

| Reported defect | Disposition in revision 2 | Remaining related restrictions |
| --- | --- | --- |
| T8: parameter-dependent density zeros permit a sample-selected zero inside the formal log objective | **Fixed.** A measurable set of true observation probability one now has positive density simultaneously for every fitted parameter. | The all-natural-sample-size finite envelope, including sample zero, and the previously declared identity hypotheses remain. |
| T12: the same defect in standalone compact log-likelihood consistency | **Fixed.** The analogous common observation set and simultaneous positivity premise are added for the fitted mixture. | Sample-zero objective/Hessian envelopes, QMD as a premise also of normality, and local squared-remainder integrability remain. |

Thus the two additional defects reported in the architect's response are fixed, with **0 partly fixed and 0 not fixed**. This conclusion comes from inspecting the revised premises and checking their consequences; it does not rely on the architect's assertions about proof certification.

## Changed mathematical statements

The comparison baseline is the saved blind `reading.md`. All shared definitions retain their recorded meanings. T8 and T12 are the only mathematical statement changes identified. The other changes concern labels, docstrings, and moving T17's definition from Part4 to Part5.

In T8's second clause, after the parameter set is supplied, the revised statement additionally quantifies:

1. `commonS`, a set of covariate/outcome pairs;
2. its measurability;
3. `(mu.map (X_0,Y_0)) commonS = 1`;
4. **for every observation in commonS and every parameter in Theta**, strict positivity of that fitted density.

These are extra antecedents. The IID, normalization, domination, integrability, separation, estimator, error-envelope and exact/approximate maximization hypotheses and the conclusions are retained. The entropy identity, compactness-to-separation and true-model clauses are unchanged. The last sentence of the revised restriction text accurately discloses the common-set addition.

T12 adds precisely the analogous four antecedents to its **standalone compact-consistency clause**, with the fitted density replaced by `mixtureFamily p g`. Its zero-weight nonidentification and combined normality/efficiency clauses are unchanged. In particular, the latter already imposed positivity for every fitted parameter on one measurable observation set of true probability one. The revised restriction text correctly limits the new addition to standalone consistency.

By IID equality of laws, each observation falls in commonS almost surely. Intersecting these events over the countable observation indices gives one probability-one event. On that event positivity holds for **all fitted parameters simultaneously**, including any sample-selected estimate. Every positive-sample likelihood is then positive and its ordinary real logarithm equals the sum of the logarithms of its factors. This removes the specific use of the totalized logarithm at a fitted zero. No uncountable intersection of parameterwise probability-one events is assumed.

The diagonal-zero example described in the architect's report is excluded for the correct reason: if the candidate density at observation y and parameter t vanishes whenever y=t, common positivity forces commonS to avoid every candidate t. It cannot have true probability one when that parameter set has positive true observation probability. Merely adding another parameterwise a.e. premise would not establish this.

## Every target and revised label

| Target | Revised decision | Delta assessment |
| --- | --- | --- |
| T1 | refuted | Same geometric witness. Uniform zero-direction convergence and unit mean quotients contradict the continuous linear Hadamard derivative's required value at zero. The missing diagnostic identities and abstract negation remain disclosed. |
| T2 | whole | Unchanged. Both canonical clauses are present: empirical mean identity and finite-positive-variance CLT, plus the finite-variance zero-direction witness. T1's additional diagnostic clauses are not requirements of T2. |
| T3 | refuted | Same complete counterexample. One jointly continuous bounded law admits C1 CEF extensions with arbitrary derivatives at its covariate mean, contradicting distribution-determined PDA. Its `correct_whole` finding concerns completeness of this canonical counterexample. |
| T4 | restricted | Unchanged. Equality on U remains gated by an existing coordinate derivative; global measurable integrable CEF versions are used. Both restrictions are disclosed. |
| T5 | refuted | Same uniform/Gaussian least-squares example. The stated degree meets the printed rate but its local L2 error has a positive probability lower limit. A least-squares fit exists; the supplied-fit and missing endpoint-result qualifications remain disclosed. |
| T6 | restricted | Unchanged. Stable-Gram consistency and sufficient rates are present; the finite sharp bounds remain confined to [0,1], and the supplied envelope/fit qualifications are disclosed. |
| T7 | refuted | Same nondegenerate four-atom example. The unique pooled MLE converges to the marginal success probability, not either unique fixed-covariate KL target. Omitted derivative formulas and the exact KL gap remain disclosed. |
| T8 | restricted | Added common measurable full-probability positivity. The reported defect is fixed; the new restriction and all earlier restrictions are disclosed. |
| T9 | refuted | Same actual sample (1,2,3) and positive-scale collapse path. Unbounded likelihood contradicts existence of an admissible maximum. Missing quantitative/path bounds remain disclosed. |
| T10 | whole | Unchanged. Both canonical clauses are present: nonattainment for every nonempty positive sample, and continuity/compact attainment on every stated nonempty restricted domain. |
| T11 | refuted | Same normalized identical experiments at distinct full parameters, with attained MLE selections. No estimator can be consistent at both truths, refuting the specified full-parameter claim. The omitted upper bound and binomial rewriting remain disclosed. |
| T12 | restricted | Added common positivity to standalone consistency only. The reported defect is fixed; the new and retained restrictions are disclosed. |
| T13 | refuted | Same exactly unbiased hot-deck variance counterexample. The label is valid **only for the universal bias-only calibration reading expressly selected by the canonical claim**. The revised opening qualifies this, and its restriction excludes the literal hedge and empirical numbers. It does not certify that the ordinary-language word “likely” is false. |
| T14 | restricted | Unchanged. Hot-deck variance failure and conditional weighted-sign identities retain the declared L2 premises and omissions. |
| T15 | restricted | Unchanged. Only true-score failure and additive-intercept consistency are credited; no unproved estimated-score failure or literal hedged-footnote refutation is claimed here. |
| T16 | restricted | Unchanged. Estimated-score matching equality, variance failure and the conditional variance identity retain the declared premises and omissions. |
| T17 | refuted | Same conditional-independence null with a nonzero population placebo coefficient and asymptotic rejection probability one. This contradicts the specified test interpretation. The finite 240-observation arithmetic remains explicitly population-risk arithmetic, with no new actual-sample claim. |
| T18 | restricted | Unchanged. The population zero-placebo-coefficient result and failure without a linear CEF are present; robust-test asymptotics remain omitted and disclosed. |
| T19 | refuted | Same positive countable arm masses give complete discrete overlap but no uniform propensity margin, refuting the specified converse. The explicit rate and selected violating cell remain omitted and disclosed. |

Each `whole` label was checked for both clauses of its canonical formal content. Each `restricted` label retains an accurate omission/addition list. A `refuted` label records an actual failure of its canonical printed reading; it does not silently restore omitted counterexample diagnostics. Every non-null restriction in `record2.json` matches its actual Challenge docstring after whitespace normalization, and every refutation docstring has the required opening.

## Changed-statement nonvacuity and junk-value checks

Both common-set repairs have a positive-dimensional nondegenerate instance. Take K=tau=1, constant covariate zero, nuX=delta_0, outcome dominating measure kappa=delta_0+delta_1, true success probability 1/2, candidate success probabilities t in [1/4,3/4], and commonS consisting of all covariate/outcome pairs with outcome 0 or 1. Its true probability is one; the candidate densities t and 1-t lie in [1/4,3/4] on it, simultaneously for all candidates. They normalize to one against kappa. T12 uses this as a one-component mixture of weight one. None of the dimensions, parameter sets, observation spaces or experiments is empty.

Use iid fair binary outcomes and the clipped sample mean as the measurable maximizer. For n>0 the uniform log-objective error is bounded by `|sampleMean-1/2| log 3`, tending to zero by the LLN. At n=0 choose envelope log 4. The population objective `(log t + log(1-t))/2` is genuinely finite, continuous and separated at 1/2. Thus the new premises coexist with every standalone consistency hypothesis; they do not assume consistency itself. The prior normality/efficiency Bernoulli instance, including positive information and genuine square-root remainder integrability, also remains available.

The common-set hypotheses are imposed using equality to one in the measure itself, not a real conversion of infinity. IID supplies measurability of the observation maps and a probability pushforward. The log-zero issue is excluded on one common probability-one sample event; n=0's totalized mean still causes the already disclosed stronger finite population-objective bound. Normalization, fixed-parameter integrability and the protected extended KL identity are unchanged. No new unbounded supremum/liminf, truncated subtraction, singular inverse, unprotected integral or circular antecedent was introduced. Existing nonvacuity instances for all other targets remain recorded in `findings2.json`.

`/home/ubuntu/sap/tools/sap-lean scratch/DeltaCheck.lean` completed successfully with exit code 0 and no diagnostics. It imports only Defs and contains no `sorry` or added axioms. Its checks establish:

* transfer of the common probability-one set to all observation indices simultaneously;
* simultaneous positivity for every candidate parameter;
* the positive log-product/sample-log-likelihood identity;
* measurable full support, strict common positivity, conditional normalization and nondegenerate fair probabilities in the K=tau=1 Bernoulli instance;
* exclusion of the diagonal-zero model by common positivity.

Only one Lean process ran at a time and `lake` was not used. Neither Solution proofs, external comparator certification, nor the unchanged long Poisson matching and polynomial instability arguments were independently re-proved in this delta review. Confidence remains correspondingly lower for those unchanged asymptotic assertions. The round-1 artifacts and supplied sources were preserved; only the new review outputs and scratch check were written.
