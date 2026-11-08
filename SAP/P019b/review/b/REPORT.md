# Palomar statement audit: P019b

| Verdict | Count |
| --- | ---: |
| correct_whole | 7 |
| correct_restricted | 4 |
| restriction_inaccurate | 0 |
| not_faithful | 0 |
| vacuous | 0 |
| false | 0 |
| omission_ok | 0 |
| omission_questionable | 0 |
| **Total targets** | **11** |

There are no adverse findings. All eleven targets have a theorem; no target was omitted. The four retained restrictions are accurate and disclosed in the corresponding Challenge docstrings. No step-2 verdict was changed after reading the record.

## Comparison with the architect's record

| Target | Final verdict | Assessment |
| --- | --- | --- |
| P019-T12 | correct_whole | The canonical note explicitly limits this target's formal content to the corrected population identity and assigns the inference sentence to T21. The theorem covers that scope exactly. The record's `restricted` label is conservative: its description accurately says which part of the longer quotation is retained. No mathematical assertion is misrepresented. |
| P019-T13 | correct_restricted | The common-observable counterexample is retained. The docstring accurately enumerates the omitted numerical cell and marginal tables, separate direct/list means, observable-atom table and pointwise class description. Sharing the actual law and observable variables establishes the required common-observable comparison. |
| P019-T14 | correct_whole | All five parts of the canonical general calculation, with all independence and interior-probability hypotheses, are present. |
| P019-T15 | correct_whole | The Gaussian planning event, both tails, omitted-tail bound and equality case, and the total-N=100 null example all agree with the target. This concerns normal planning power. |
| P019-T16 | correct_restricted | The Binomial baseline, printed capped increment, independent mixture and population contrast are accurately specified. The docstring discloses omission of all rejection probabilities, power curves and the liar/false-confessor mechanisms. Nothing retained purports to certify the approximate simulation results. |
| P019-T17 | correct_restricted | Lemma 1 and the exact excess/strict inequality are retained. The conditional-engagement inequality is not expressly concluded. The positive false-confession premise is an equivalent reformulation of failure of the defined almost-sure monotonicity; it does not strengthen that premise. The record accurately identifies the absent formulation and inequality. |
| P019-T18 | correct_whole | This is the actual unconditioned sampling-variance limit with equation (3), under the maintained Assumptions 1–4, for every fixed empty-cell completion. |
| P019-T19 | correct_whole | Root-n tightness, centered Gaussian convergence, the printed plug-in variance consistency, positivity and all nominal Wald coverage limits are present. |
| P019-T20 | correct_whole | Both actual variance limits and their strict comparison are present for arbitrary fixed completions. |
| P019-T21 | correct_whole | The population identity, studentized Gaussian limit and interior p-value CDF limits give the stated null inference. |
| P019-T22 | correct_restricted | Both mathematical implications are retained. The causal interpretation and the design claim about randomized assignment and question order are absent, exactly as the record and docstring disclose. |

T12 was already classified `whole` in `claim-stage.json`, before the record was opened. Its canonical note says that the formal target is the first sentence; the longer quoted p-value assertion is separately T21. This explains the difference between the final classification and the architect's conservative label without revising the blind reading or stage-2 comparison.

## Definitions and truth checks

The finite law allows arbitrary real atom probabilities, rather than imposing equal weights or rational probabilities. Finite support does not lose any joint distribution of the paper's bounded list counts and binary variables: any such joint distribution can be represented by its finitely many value tuples. The factorization predicates express full independence of the indicated joint variables from treatment. Assumptions are imposed on positive-mass atoms, the finite-space version of almost-sure assumptions.

All population conditional denominators used in the retained statements are positive under their premises. Explicit positive cell probabilities in nondegeneracy make the paper's conditional variances well defined. The conditioning in the estimator definitions concerns sample cells; the sampling law itself is always the full IID product law. Fixed real completions, including negative variance completions, affect events whose probabilities vanish. There is no unbounded limsup, empty-type escape, truncated variance denominator, or integral of a nonintegrable test function doing the work.

The normal law's second parameter is variance. Its measure is finite, bounded continuous test functions are integrable, and the quantiles occur at probabilities strictly between zero and one. Nonpositive estimated variances give statistic zero and p-value one, as disclosed. The positive population limiting variances prevent that completion from determining asymptotic inference.

The population identities follow by independence and conditioning on Y. In T17, the exact error is P(X=0,Y=1). In T15, the Gaussian rejection event splits into two disjoint tails; V−S=(p1−p2)²/2 gives the stated tail bound. In T16, the capped increment loses one only at W=4, whose probability is 16/625. For the asymptotic targets, finite-support ratio-mean expansions, the classical IID central limit theorem and variance consistency give the claimed limits. The actual variance limits additionally use boundedness and exponentially rare small cell counts. For T20, the efficiency gap contains the strictly positive confessor-variance contribution. I found no counterexample or conclusion-shaped premise.

Paper context was checked against the [published article PDF](https://alexandercoppock.com/aronow_etal_2015.pdf), particularly Sections 2–4 and the CNN wording in Appendix A.1. The exact audit scope, including the corrected and derived targets, is the supplied `claims.json`.

## Nonvacuity and validation

`scratch/Nonvacuity.lean` imports only `SAP.P019b.Defs` and contains no `sorry`. It compiled successfully with:

```text
/home/ubuntu/sap/tools/sap-lean scratch/Nonvacuity.lean
```

The compiled checks establish:

* All standing assumptions for the explicit CNN study, including full treatment independence for every test function and positive conditional variances in every cell.
* Every T14 hypothesis for the truthful CNN labeling, with a positive reader-only share.
* A separate uniform eight-atom study satisfying Assumptions 2–4 with false-confession probability 1/2, prevalence zero and combined functional 1/2. Thus T17's second implication is independently nonvacuous.
* A valid parameter instance for T15 and the exact T16 interior-mixture value 3109/3125 at affected share 1/5.

The CNN instance has combined variance coefficient 7/6, standard coefficient 3/2, and positive gap 1/3. Its beta and delta variance coefficients are respectively 4 and 3/4. It therefore supplies a nondegenerate common instance for the asymptotic antecedents as well as the population results. These checks establish satisfiability; this audit does not replace the package's proof certification.

`reading.md` was saved before `claims.json` was read; `claim-stage.json` was saved and parsed before `record.json` was read. Both output JSON files were parsed with Python, and the findings were checked for exact one-to-one coverage of the eleven canonical targets.
