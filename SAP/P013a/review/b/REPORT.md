All 14 targets were reviewed. There are **10 correct whole statements or complete refutations**, **4 correct restricted statements**, and **0 adverse findings**. All architect decisions agree with the independent statement audit. No target is omitted.

| Verdict | Count |
| --- | ---: |
| correct_whole | 10 |
| correct_restricted | 4 |
| restriction_inaccurate | 0 |
| not_faithful | 0 |
| vacuous | 0 |
| false | 0 |
| omission_ok | 0 |
| omission_questionable | 0 |

Every severity is `none`. There are no items outside `correct_*` or `omission_ok` requiring a corrective statement or docstring.

The blind mathematical readings were saved in [reading.md](reading.md) before either metadata file was opened. The independent comparisons were then saved in [claim-stage.json](claim-stage.json) before opening `record.json`. No step-2 judgment was changed after reading the record. The per-target results, nonvacuity instances and confidence assessments are in [findings.json](findings.json).

| Target | Architect decision | Assessment |
| --- | --- | --- |
| P013-T1 | restricted | Correct. The decimal coverage approximation is omitted and the exact row sum is replaced by a bound. Both changes are expressly disclosed; the explicit family and exact limits remain. |
| P013-T2 | restricted | Correct. NestedPopulationSetup is added to exactly the coverage and two rate implications. Separate centered-concentration conclusions after the rates and the final counterexample assertion are omitted. The record and docstring list all these changes. |
| P013-T3 | whole | Correct. Both signed-outcome refutations and the zero-total absolute-bias refutation use the specified genuine randomization and simulation laws. |
| P013-T4 | whole | Correct. The exact expectations, repaired absolute and relative bounds, sign specialization, logarithmic rules and integer threshold all remain. |
| P013-T5 | whole | Correct. The theorem exposes vacuity of the printed graph definition using actual nonconstant exposures and a positive-size sequence that fails C4. Its own hypotheses are not vacuous. |
| P013-T6 | whole | Correct. Both edge directions, genuine vector independence, the directed and symmetric counts, and C5 implying C4 are represented. |
| P013-T7 | whole | Correct. The fixed common-table block family has the stated finite identities and distinct subsequential limits; it refutes the specified proof steps. |
| P013-T8 | restricted | Correct. Strict positivity of every realized variance estimate is added only to the final expectation-limit/studentization implication. This and the permitted negative-estimate coverage convention are accurately disclosed. |
| P013-T9 | restricted | Correct. The common-table premise is added to mean consistency, and contrast consistency, coverage and bias guidance are omitted. The retained algebraic identity has the stated positive denominators. |
| P013-T10 | whole | Correct. The closed-bin midpoint contradictions establish exactly the two claimed rounding incompatibilities. |
| P013-T11 | whole | Correct. Uniform sampling of n-element subsets supplies both counts, the ratio and every numerical consequence, including the boundary n=N−39. |
| P013-T12 | refuted | Correct. The theorem negates both printed guarantees on the valid nonzero-total domain. `correct_whole` records a faithful complete refutation; it does not label the printed proposition true. |
| P013-T13 | whole | Correct. The total and contrast expectation/variance identities and the full cross-exposure covariance expansion match the claim. |
| P013-T14 | whole | Correct. The positive-joint, missing-joint and corrected-conservativeness cases use the paper's explicit zero-joint convention. |

The shared nonvacuity sequence for T2, T8 and T9 consists of N independent fair binary assignments with both outcomes equal to 1 for every unit, using one fixed infinite outcome table. Its identity dependency graph has row bound 1, its comparison probabilities are 1/2, and its distinct-unit joints are 1/4. The contrast has variance V=4/N and the variance estimate is identically Vhat=4/N. Thus NV=NVhat=4, centered concentration and all lower-tail premises hold, and the ordinary Rademacher central limit theorem supplies the normal premise when required. Every size can be encoded by a finite ordinal sample space. This also makes the added common-table and strict-positivity restrictions visibly satisfiable.

The minimum-positive-joint domain in T2 can be empty at N=1. Its rates are asserted only eventually. For the rate hypotheses, any sufficiently large population has a pair of distinct units outside the uniformly bounded symmetric graph neighborhood; their positive comparison marginals and independence give positive joints. Consequently the unregulated value of b at empty domains cannot manufacture an asymptotic conclusion.

All probability sums are finite, with strictly positive normalized support weights. Coverage sequences lie in [0,1], so the real liminf is bounded and has its usual meaning. Gaussian parameters were checked against Mathlib: the second parameter is variance. The normal critical value uses a nonempty lower-bounded quantile set for 0<alpha<1. The paired score subtracts in the integers. Valid block offsets and the degree-39 counting hypotheses protect the natural subtractions. Relative-bias statements are guarded by a nonzero total; simulated probabilities have strictly positive denominators. Zero-joint terms in the variance estimator implement the convention expressly stated by the paper, and impossible joint indicators vanish throughout the positive-weight support.

[scratch/Check.lean](scratch/Check.lean) compiled successfully with `/home/ubuntu/sap/tools/sap-lean scratch/Check.lean`. It imports only Defs and proves nonempty design support, the signed example's positivity and attained minimum, its total and the **generic** simulated estimator expectation 2/9, and the nontrivial zero-joint values Var(H)=4, E v=2, A=−2, E A2=2. This identifies the signed counterexample with the actual estimator used in the refuted universals.

[scratch/exact_checks.py](scratch/exact_checks.py) completed successfully; [scratch/exact_checks.json](scratch/exact_checks.json) records the results. Its exact rational computations check paired populations at N=4,6, block populations at N=1,4,6,8, the variance/covariance/correction identities, both signed one-replicate examples, the finite graph equivalences and bounds, the integer replicate threshold, and degree-39 ratio inequalities for 40≤N≤150. These computations support the finite identities; the asymptotic judgments additionally use the paired characteristic-function limit, the Rademacher central limit theorem, the bounded dependency graph central limit argument, concentration and the explicit odd/even block subsequences.

The external source check confirmed the complement membership symbols in the dependency definition, the two WLS triples and the Section 9 exposure-probability descriptions in the [arXiv copy of the paper](https://arxiv.org/pdf/1305.6156). The supplied canonical claims determine the audit scope and journal locations.
