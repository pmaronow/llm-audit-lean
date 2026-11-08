# Revision 3 delta review

19 targets: 18 theorem stubs and one omission. No outstanding statement or disclosure issue was found.

| Verdict | Count |
| --- | ---: |
| correct_whole | 7 |
| correct_restricted | 11 |
| restriction_inaccurate | 0 |
| not_faithful | 0 |
| vacuous | 0 |
| false | 0 |
| omission_ok | 1 |
| omission_questionable | 0 |

All severities are `none`. The architect's decisions are 7 whole, 9 restricted, 2 refuted and 1 omitted. The findings schema has no `correct_refuted` value; the two valid partial refutations, T103 and T104, are counted as `correct_restricted`, preserving their disclosed scope. The new T102 verdict accounts for the change from round 2's counts.

## Earlier findings and their status

| Earlier finding or judgment | Status in this revision |
| --- | --- |
| Round 1 T108: infinite-sequence hypothesis undisclosed under whole | **Fixed.** The restricted label and explicit omission of arbitrary finite iid families and a change-of-space transfer remain accurate. |
| Round 1 T113: requested whole relabeling because an audit note said nuisance integrability was implicit | **Not fixed as requested; objection withdrawn in round 2 and remains withdrawn.** The current governing rule explicitly confirms that the note supplies no hypothesis. The restricted label accurately describes the retained nuisance-integrability premise. |
| Round 2 acceptance of T96 and T99 as refuted | **Superseded by the current claim rule; revised labels are correct.** Their canonical statements already assert the recorded counterexamples, which the theorems establish in full. They are now whole and have no false-claim opening. |
| Round 2 acceptance of T102 as a full refutation | **Superseded by the current claim rule; revised scope is correct.** The theorem negates an identification reading of guidance. It is now restricted, names the reading, discloses omitted content, and has no false-claim opening. |

There were no adverse findings in `findings2.json`. The prior files are preserved; this report supersedes their label treatment where the new instruction requires it. In particular, T102's earlier classification relied on treating the audit-history interpretation of the guidance as the canonical assertion itself. The current instruction expressly distinguishes these. No Lean proposition has been weakened to obtain these verdicts.

## Comparison with the saved reading

I read all current Defs and Challenge declarations and compared their mathematical content with `reading.md`. All eighteen theorem propositions, including their shared definition bodies, hypotheses, quantifier order and conclusions, still match that reading. The changed material is documentation and decisions. Relative to revision 2, the relevant changes are T96, T99, T102 and the T113 record clarification; relative to the original reading, the already reviewed T103, T104 and T108 notices also remain in force. The `PDAWellDefined` comment now describes an identification reading rather than calling it the printed assertion.

Claims were assessed from `statement`, `definitions_needed` and standing assumptions. Neither `note` nor `finite_lemmas` supplied a clause or hypothesis.

| Target | Current decision | Result of re-check |
| --- | --- | --- |
| T96 | whole | The fixed eighteen-unit sample, unique global logit ML fit, fitted probabilities, observed fractions, score arithmetic, both estimates and nonzero gap cover the canonical counterexample. Grouped counts and sums encode the specified raw units. The quoted erroneous equality is the counterexample's context, not an assertion the canonical counterexample endorses. |
| T97 | restricted | Positive real arm masses, arbitrary outcome sums and a positive common normalization are correctly disclosed. Raw-unit regrouping, raw-data plug-in identities and quantifier transport remain explicitly omitted. |
| T98 | restricted | True-score weight and sample-mean expectations and reciprocal comparisons remain. Omitted estimator, fitted-score convergence and efficiency content, plus pointwise binarity/overlap for the infinite sequence, are disclosed. |
| T99 | whole | The canonical two-atom law, ignorability, both positivity bounds, propensity, weighted effect, ATT, their inequality and normalization are all present. Its whole label correctly concerns the counterexample assertion. |
| T100 | whole | All propensity-mean and weighted-effect identities, normalization and equality characterization remain present under the canonical finite-effect hypotheses. |
| T101 | restricted | The corrected relative-complement identity is retained; the erroneous-union characterization, equivalent conditions and three illustration equalities remain explicitly omitted. |
| T102 | restricted | Correctly names and negates the distributional identification reading. It discloses omission of the fixed-CEF population-PDA definition identity and discrete partial slopes, and retains the differentiable chosen-estimator sample formula. It does not announce a contradiction of the printed definition itself. |
| T103 | refuted | The canonical assertion (A) expressly promises a maximizer for every sample. Its negation within the actual positive-scale mixture directly contradicts that assertion. The omissions of (B), efficiency and plotted-fit assessment remain disclosed. |
| T104 | refuted | Canonical (A) and (B) jointly imply the equivalence the theorem negates. Thus this contradicts the canonical assertions, even though the exported theorem does not separately identify the failed direction. The partial-scope notice accurately says so. |
| T105 | omitted | Justification unchanged: no exported predicate for informational completeness and the credited negation reportedly lacks binary treatment. Omission remains acceptable on the visible evidence. |
| T106 | whole | Linearity, variance formula and affine rules, standard-deviation rules and standardized Chebyshev are all present with their finite moments. |
| T107 | restricted | Only iterated expectation remains; every total-variance and best-prediction component is explicitly omitted. The credit history is not used to alter the canonical claim. |
| T108 | restricted | Infinite measurable iid sequences and positive-size initial segments are explicitly distinguished from arbitrary finite families on their given space. Separate moment scopes remain correct. |
| T109 | whole | Weierstrass, population minimizer existence at every degree and eventual mean-square approximation for every minimizing family cover the canonical content, with finite-risk hypotheses and the paper's PMF/PDF support convention. |
| T110 | whole | The likelihood's unique sample-mean maximum, including endpoint samples, the count identity and the 2/3 example are present. |
| T111 | restricted | Retained population integrability of respondent regressions in both MAR parts and the fixed nondegenerate estimator evaluations are disclosed accurately. |
| T112 | whole | Balance, preservation of MAR and uniform conditional-response positivity are all present; indicator-based conditional independence needs no outcome moment. |
| T113 | restricted | The separate integrability premise on m(X) really excludes correct-propensity cancellation cases allowed by the canonical formula. The audit note adds no contrary hypothesis. |
| T114 | restricted | Population membership, width, every-value sharpness and final numerical ATE bounds remain; all four individual potential-outcome sample estimates and their imputation interpretation are explicitly omitted. |

For T104, let O mean equal arm supports and P mean uniform two-sided positivity. Assertion (A) gives P→O; assertion (B), ¬P→¬O, gives O→P by contraposition. Together they give O↔P for every eligible law. The exported negation therefore contradicts their conjunction without relying on the audit note or assigning any unspecified condition to (C).

## Nonvacuity and junk values

No changed mathematical proposition was found. The following witnesses check that the revised descriptions still concern genuine quantities and admissible cases.

**T96 and T99.** The eighteen-unit example has positive sample size, positive counts in both arms of all cells and interior fitted probabilities. Its logistic log arguments are positive. It can be realized by iid covariates and cell-constant potential outcomes. The ATT example has normalized weights 3/4 and 1/4 and positive conditioning and normalization denominators. Its weighted effect is 1/4 and ATT is one. Neither counterexample uses an empty sample or a division-by-zero convention.

**T102.** Identify the one-coordinate covariate space with R. Give X density one half on [-2,-1]∪[1,2], zero elsewhere, and take independent Y uniform on [-1,1]. Both variables and X's coordinate are integrable, and the pair has a joint density. The covariate mean is zero. Two conditional-mean versions are m0=0 and m1(x)=x when |x|<1/2 and zero otherwise. They agree on the entire positive-density set and are differentiable at every such point, including the interval endpoints. At mean zero their actual derivatives are zero and one. The reading's common-derivative conclusion fails with no totalized derivative or nonintegrable expectation. For the separate sample component, n=1 and a constant or linear chosen estimator satisfy its derivative premise. This shows failure of the named identification reading, not failure of the meaning of a chosen extension's derivative.

**T103.** At n=1, y=1, choose normal weight one, normal mean one and positive normal scale s, with unused component scales and rate positive. Likelihood is 1/(s sqrt(2pi)), unbounded as s decreases to zero. Each valid parameter still has finite likelihood. Zero scales and lognormal values at nonpositive data are not used to produce the refutation.

**T104.** Put m_k=2^(−k−1), t_k=4^(−k−1), c_k=m_k−t_k. The joint masses are nonnegative and summable, with positive totals 1/3 and 2/3 summing to one. Both supports are all natural numbers, every denominator is positive, and propensity t_k/m_k=2^(−k−1) has no positive uniform lower bound. This is a genuine probability law, which can be embedded in a real-valued discrete covariate model.

**T108.** The infinite product of fair Bernoulli spaces satisfies all sequence and moment hypotheses with variance 1/4. A single fair draw on a two-atom space is a genuine excluded finite-family case, as checked in round 1. Its exclusion remains disclosed.

**T113.** In the retained theorem, constant X, Y=1, fair response and p=1/2 give examples of both branches with the other nuisance incorrect: m=1, q=1/3 for the regression-correct branch, or m=3, q=p=1/2 for the propensity-correct branch. For the excluded case, let X,U be independent uniforms on (0,1), Y=0, R=1 below X=1/2 and R=1_{U<1/2} above, p=q equal to one below and one half above, and m(x)=1/x on (0,1/2), zero elsewhere. Response probabilities are 3/4 and 1/4, MAR holds and p>1/4. The combined augmented score is pointwise zero, but E|m(X)|=∫_0^(1/2)dx/x diverges. Its displayed expectations therefore exist without the extra nuisance moment. No score denominator vanishes and no nonintegrable integral is assigned a default value. This supports the restricted label under the current explicit rule.

Other nonvacuity instances from the prior reviews remain valid and are retained per target in `findings3.json`.

## Validation and limits

Checked all eighteen theorem names and universe annotations against `record3.json`, all nine restricted notices and their stated omissions, and the two remaining false-claim notices. T96, T99 and T102 no longer contain a false-claim notice. Current Defs remain Mathlib-only through their shared imports.

The mathematical statements are unchanged, so no additional Lean process was needed. The successful prior `scratch/Check.lean` and `scratch/DeltaCheck.lean` checks are preserved; this review does not represent them as a new certification of the revised files. The density and countable-law witnesses above are mathematical checks. The architect's reports of underlying credit status and external certificates were not independently audited; this task concerns statement fidelity.

Python parsed `findings3.json`, checked the exact required schema, nineteen unique canonical target IDs, all eighteen theorem mappings, permitted verdicts and severities, and agreement with these report counts. There are no adverse findings requiring a fix.
