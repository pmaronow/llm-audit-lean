# Delta referee report

**15 targets: 10 correct_whole, 5 correct_restricted, 0 adverse verdicts. Both earlier findings are fixed; no new statement problem was found.**

| Verdict | Count |
| --- | ---: |
| correct_whole | 10 |
| correct_restricted | 5 |
| restriction_inaccurate | 0 |
| not_faithful | 0 |
| vacuous | 0 |
| false | 0 |
| omission_ok | 0 |
| omission_questionable | 0 |

The unchanged output schema has no `correct_refuted` verdict. Full, faithful counterexample targets receive `correct_whole`; T12 receives `correct_restricted` because it still explicitly omits canonical clause (d). These verdicts assess the theorem's scope and do not mean that the refuted printed assertion is true. The revised manifest has 5 `whole`, 4 `restricted`, and 6 `refuted` decisions; all these labels are justified at their disclosed scope.

## Earlier findings

| Target | Earlier finding | Status | Revised evidence |
| --- | --- | --- | --- |
| P006-T2 | The restriction omitted the missing independent-estimation implementation of vector conditional unbiasedness. | **Fixed** | The Challenge docstring and record2.json now explicitly say the vector condition is assumed directly, both sufficient implementations are omitted, and T6 concludes a different treated-residual condition. |
| P006-T3 | Both optimizer witnesses govern every conclusion, an extra condition not disclosed for identities, zero-policy values, and best-response nonnegativity. | **Fixed** | Both revised restrictions explicitly place every conclusion under supplied ATT and welfare maximizers, state the resulting exclusions, and specifically disclose the welfare-optimizer premise for nonnegativity. |

The mathematical restrictions in T2 and T3 remain. Their revised disclosures accurately describe those restrictions; neither finding requires the architect to enlarge the theorem once this scope is explicit. Relevant sources are [T2's restriction](/home/ubuntu/sap/tasks/CHFID-P006a-b/SAP/P006a/Challenge/Part1.lean:13), [T3's restriction](/home/ubuntu/sap/tasks/CHFID-P006a-b/SAP/P006a/Challenge/Part1.lean:19), and [the optimizer binders](/home/ubuntu/sap/tasks/CHFID-P006a-b/SAP/P006a/Defs/Part5.lean:114). The account in architect-report.md agrees with the revised sources.

## Mathematical delta and ordinary-expectation check

I compared all shared definitions and all 15 proposition definitions with the mathematical expansion saved in [reading.md](/home/ubuntu/sap/tasks/CHFID-P006a-b/reading.md). T10 is the only proposition with changed mathematical content. The other changes concern docstrings and decision labels.

In [T10Statement](/home/ubuntu/sap/tasks/CHFID-P006a-b/SAP/P006a/Defs/Part5.lean:260), the general expectation formula now quantifies over a finite-moment probability law D and an admissible policy pi. The marginal-invariance identity now requires both laws D,D' to be finite-moment probability laws and the common policy to be admissible; equality of their (X,Y1) pushforwards remains its other premise. Previously the first identity had no moment or policy guard, and the second required only a measurable policy. The closed singleton counterexample and its other conclusions are unchanged.

These guards match the canonical setting: potential outcomes have finite absolute moments and policies are measurable functions into [0,1]. They do not drop any counterexample clause. Pointwise the one-unit sample-reward expectation over the treatment coin equals pi(X)Y1. Since 0<=pi<=1, its absolute value is bounded by |Y1|. Hence the guarded expectation is an ordinary finite integral, and the invariance comparison also has ordinary finite expectations on both sides.

[scratch/DeltaCheck.lean](/home/ubuntu/sap/tasks/CHFID-P006a-b/scratch/DeltaCheck.lean) independently compiles this integrability implication for arbitrary measurable C and the exact sample-integrand reduction. It also compiles a joint instance of the new guards: D is the point mass at ((),2,1), D' is the point mass at ((),3,1), and pi is constant one. The treated-data marginals agree. Under D, expected ATO is 1, welfare is -1, and regret on the singleton feasible class is 0. The reward image for that regret is the nonempty bounded singleton {-1}; neither an empty supremum nor a default integral supplies the refutation. The command `/home/ubuntu/sap/tools/sap-lean scratch/DeltaCheck.lean` exited 0. No Challenge theorem or Solution theorem was used in the scratch proof, and at most one Lean process was running.

The prior nonvacuity constructions for T2 and T3 still apply because their hypotheses have not changed: a one-unit Bernoulli experiment with a one-point covariate, zero baseline and estimator, and constant effect one satisfies full Standing, vector unbiasedness, and the other estimator conditions. On the full admissible class, constant one supplies both maximizing witnesses. The open treatment-probability class [0,1) still demonstrates the additional T3 restriction; the revised disclosure now accounts for it.

## Labels and canonical coverage

| Target | Revised decision | Delta assessment and retained mathematical scope | Verdict |
| --- | --- | --- | --- |
| T1 | refuted | The actual zero-on-empty rewards give 3/4 at the printed rule and 19/20 at a feasible alternative, refuting both printed best-response rules and their conditional-mean proof displays. The exact optimum, polynomial identity and welfare gaps remain. | correct_whole |
| T2 | restricted | Both implementation omissions, all other enumerated omissions, direct vector-moment assumption and stronger estimator-integrability requirements are now disclosed. The retained identities and threshold optimization content match the prior reading. | correct_restricted |
| T3 | restricted | The global estimator moments and simultaneous attained-maximizer premises are now disclosed for every retained conclusion. The omitted concrete printed-regret comparison remains identified. | correct_restricted |
| T4 | refuted | Pointwise-unbiased bounded estimator witnesses have biased evaluated means and actual ATT/TT best responses with positive regret; one also has zero private heterogeneity. These refute the printed inferences and ensuing regret statements under pointwise unbiasedness alone. | correct_whole |
| T5 | refuted | With common baseline and identical covariate/reference laws, the shared pointwise-unbiased estimator gives maximum scores 0<5/8 despite effects 1/4>1/8. This refutes both printed ranking properties under the stated estimator reading. | correct_whole |
| T6 | whole | All four qualified clauses remain: per-policy TT and welfare identities; argmax equality and zero regret for arbitrary feasible classes; the unrestricted positive-effect rule; and independent estimation as a sufficient implementation with treated-residual integrability. | correct_whole |
| T7 | whole | All qualified clauses remain: the weighted score identity, positive-effect optimizer, and the almost-sure treatment characterization and welfare optimality of every maximizing policy. No integrability of irrelevant untreated estimator evaluations is added. | correct_whole |
| T8 | restricted | The global evaluated-estimator moments and implementation/supporting-result omissions remain accurate. Per-policy identities still precede optimizer hypotheses; regret requires the supplied maximizers. | correct_restricted |
| T9 | whole | The denominator identity, strict comparison, both exact numerical interval calculations, table-only bounds and corrected rounding intervals remain. The numerical inputs are hypotheses, as in the canonical arithmetic claim. | correct_whole |
| T10 | refuted | The new guards have the canonical ordinary-expectation meaning. The nondegenerate invariant reward on an always-treated singleton still has zero regret under every finite-moment law, refuting printed unbounded regret and the withholding step. | correct_whole |
| T11 | whole | The exact every-M/exists-law-and-best-response quantifiers, shifted-law construction, welfare and regret formulas, and tie example excluding an every-best-response conclusion remain. | correct_whole |
| T12 | refuted | The two probability laws with common support refute the printed absolute-continuity premise's sufficiency for the required density. Clause (d)'s treatment-model completion is still explicitly omitted. | correct_restricted |
| T13 | whole | All five qualified clauses remain: own-agent score identity, change of measure, attained positive-part optimal score, integrated dominance/uniform ranking, and nonnegative-effect relative ranking. The density direction and moment guards are correct. | correct_whole |
| T14 | restricted | Integrability of both positive parts and the real-integral-only scope remain accurately disclosed; the other score identities remain assigned to their named targets. | correct_restricted |
| T15 | refuted | Both pairs of models have the same observation law and different untreated means despite strictly positive treatment, and singleton private covariates give zero heterogeneity. This refutes identification and the inference licensing Lemma 3. | correct_whole |

T12's refutation concerns the asserted availability of the density under the printed direction, not failure of rankings after supplying a genuine density. T15's refutation concerns untreated identification and the positivity step, not a regret inequality with an already well-defined selected mean. The revised docstrings identify these precise printed assertions, so the `refuted` labels do not overstate the counterexamples.

The remaining junk-value checks agree with the original audit: Experiments have positive sample size; the nonempty-sample ratios have positive denominators; threshold cell masses and beneficiary counts used as divisors are positive; the density in T13 is finite almost everywhere under its probability and absolute-continuity hypotheses; and T15's maximum-deviation range is exactly the bounded nonempty singleton {0}. No changed hypothesis makes a theorem vacuous. No target is omitted, and no new issue or further fix is required.
