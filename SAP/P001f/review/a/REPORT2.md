# Delta referee report

19 targets: 18 theorem stubs and one omission. No outstanding statement or disclosure issue was found in revision 2.

| Verdict | Count |
| --- | ---: |
| correct_whole | 8 |
| correct_restricted | 10 |
| restriction_inaccurate | 0 |
| not_faithful | 0 |
| vacuous | 0 |
| false | 0 |
| omission_ok | 1 |
| omission_questionable | 0 |

All severities are `none`. The fixed output schema has no `correct_refuted` verdict: `correct_whole` includes the full recorded refutations T96, T99 and T102; `correct_restricted` includes the explicitly partial refutations T103 and T104. The architect's decision counts are separately 5 whole, 8 restricted, 5 refuted and 1 omitted.

## Earlier findings

| Earlier finding | Implementation status | Current disposition |
| --- | --- | --- |
| T108: infinite iid sequence incorrectly labeled whole | **Fixed.** The record now says restricted, and the docstring explicitly discloses initial-segment scope and the absent arbitrary-finite-family transfer. | correct_restricted |
| T113: proposed whole relabeling based on nuisance-integrability note | **Not fixed as requested:** the architect declined the whole relabeling and clarified the restriction. **I withdraw the earlier objection after re-evaluation.** | correct_restricted; no remaining issue |

For T108, the theorem still states exactly the infinite-sequence assertion read in `reading.md`. `record2.json` and `SAP/P001f/Challenge/Part1.lean:98` now describe that restriction completely. Separate first-moment, second-moment and positive-variance scopes remain intact. The original nonvacuity and finite-extension obstruction still apply.

For T113, my previous reasoning treated `claims.json`'s `canonical_claim.note` assertion of implicit nuisance integrability as an added hypothesis. That was the source of the earlier proposed whole classification. Re-reading `canonical_claim.statement` and `definitions_needed`, the displayed statement requires expectations of Y and of the complete augmented score and describes the nuisance regression as an arbitrary measurable approximation. It does not separately display an expectation of that regression. The standing convention guards expectations in a statement; finiteness of the two displayed expectations does not entail finiteness of the nuisance regression's separate expectation. The architect's cancellation example establishes this distinction without using a default integral value.

Specifically, let X,U be independent uniforms on (0,1), Y=0, and

    R = 1                     if X < 1/2,
        1_{U < 1/2}           otherwise;
    p(X) = q(X) = 1           if X < 1/2,
                  1/2         otherwise;
    m(x) = 1/x                if 0 < x < 1/2,
           0                  otherwise.

Response and nonresponse probabilities are 3/4 and 1/4. The constant outcome satisfies MAR, p is the true response propensity, and p>1/4. Where m is nonzero, R=p=1, so the augmented score is m+(0−m)=0. Elsewhere m=0 and the score is again zero, including the nonresponse sentinel multiplied by zero. Both displayed expectations exist and equal zero, but

    E|m(X)| = integral from 0 to 1/2 of dx/x = infinity.

For δ>0 the truncated integral equals log(1/2)−log δ and grows without bound as δ decreases to zero. Every denominator in the score is either one or one half. The real-valued regression is defined to be zero at x=0; its divergence is an integrability fact, not division by zero. Thus the current theorem excludes a genuine correct-propensity case of the displayed statement. The revised docstring at `SAP/P001f/Challenge/Part1.lean:136` accurately states this restriction. The contradictory diagnostic note does not justify my earlier expansion of the displayed hypotheses. The revised `correct_restricted` judgment supersedes my earlier T113 recommendation; the old review files have been preserved.

## Revised statements and labels

I compared all eighteen current declarations and the shared definitions they use with the corresponding sections of `reading.md`. No change in mathematical hypotheses, quantifier order, definitions or conclusions was found. The changed theorem documentation concerns T96, T99, T103, T104, T108 and T113. The substantive delta is disclosure and classification.

| Target | Revised documentation or decision | Re-check |
| --- | --- | --- |
| T96 | refuted; false-claim notice added | The same full eighteen-unit counterexample refutes the printed finite-covariate IPW/poststratification equality. Unique logistic ML fit and unequal estimator values remain asserted. |
| T99 | refuted; false-claim notice added | The same normalized two-atom law satisfies conditional ignorability and both positivity bounds, while the unnormalized effect 1/4 differs from ATT 1. This refutes the printed unnormalized equality. |
| T103 | refuted; the partial scope paragraph is retained as Scope | The actual positive-scale mixture refutes universal maximizer existence (A). Consistency, efficiency and plotted-fit claims remain explicitly omitted. |
| T104 | refuted; false-claim notice added and partial Scope retained | The countable-mass equivalence negation refutes the unqualified identification of overlap with uniform positivity. The docstring expressly avoids claiming a separate proof of (A), an explicit directed refutation of (B), resolution of hedged (C), or the regional example. |
| T108 | restricted; infinite-sequence disclosure added | Correct and complete disclosure of the unchanged domain restriction. |
| T113 | restricted; comparison with displayed expectations clarified | Accurate for the unchanged theorem, for the reasons above. No circular hypothesis or new restriction has been inserted into the Lean proposition. |

T102's existing refuted decision and notice remain correct: its negated contract retains the joint-density premise and differentiation assumptions at positive-density points. A one-dimensional covariate on two separated intervals, independent centered continuous Y, and two conditional-mean versions differing only within the gap give different derivatives at the mean. Its separate estimator formula remains guarded by actual differentiability and positive sample size.

The five remaining whole decisions cover every canonical component: T100 includes the propensity mean, all weighted-effect identities, normalization and equality characterization; T106 includes all expectation, variance, standard-deviation and Chebyshev assertions; T109 includes Weierstrass, least-squares minimizer existence at every degree and eventual approximation for every minimizing family; T110 includes the sample mean, unique Bernoulli maximum, endpoints and the 2/3 example; T112 includes balance, preservation of MAR and conditional response positivity.

The other restricted decisions retain the accurately disclosed omissions from round 1: T97's raw-unit identities and quantifier transport; T98's estimator and asymptotic/efficiency components with its pointwise sequence profile; T101's union characterization and illustration; T107's total variance and best prediction; T111's explicitly retained respondent-regression integrability and fixed estimator evaluations; T114's four individual potential-outcome sample bounds and imputation interpretation. T105's omission and its justification are unchanged and remain acceptable on the visible evidence.

## Junk values, nonvacuity and validation

No changed proposition introduced a new totalization or vacuity issue. The reclassified refutations retain these concrete admissible witnesses:

* T96: positive counts in both arms of all three cells, interior fitted propensities, positive n=18, and a realizable iid sample. Logistic likelihood logs have positive arguments.
* T99: weights 3/4 and 1/4, positive conditioning and normalization probabilities, and nonzero ATT.
* T103: n=1, y=1, normal weight one, normal mean one, and positive normal scale s approaching zero. Likelihood 1/(s sqrt(2pi)) is unbounded, while every valid parameter gives a finite value. No zero-scale parameter is used.
* T104: m_k=2^(−k−1), t_k=4^(−k−1), c_k=m_k−t_k. Both supports are all natural numbers, arm totals are 1/3 and 2/3, every cell denominator is positive, and propensities 2^(−k−1) tend to zero.

T108 remains nonvacuous under the infinite product fair-Bernoulli law with positive variance. T113 has nonvacuous examples in both retained branches, with the other nuisance deliberately incorrect, as recorded in `findings2.json`. The excluded cancellation model above separately verifies the accuracy of its restriction.

`/home/ubuntu/sap/tools/sap-lean scratch/DeltaCheck.lean` completed successfully, with deprecation warnings only. It imports only `SAP.P001f.Defs` and contains no `sorry` or new axiom. It verifies positive propensity, binary response, pointwise cancellation using the actual SAP censored-outcome formula, and integrability and zero integral of the complete score. The product-law probabilities and divergence calculation above are mathematical checks, not claimed to be fully Lean-certified by that scratch file. The original `scratch/Check.lean` and its round-1 checks were preserved.

All eighteen theorem names, their universe annotations, record mappings, restricted notices and five false-claim notices were checked. Python parsed `findings2.json` and verified its required schema, exactly one object per canonical target, all theorem mappings, verdict and severity values, and agreement with this report's counts. No outstanding issue or further correction is requested.
