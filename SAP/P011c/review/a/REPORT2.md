# P011c delta statement review

**13 targets: 5 correct_whole, 7 correct_restricted, 1 omission_ok.** All other verdict counts are zero. All 13 severities are `none`; no unresolved issue or requested fix remains. The five `correct_whole` verdicts comprise the sole positive `whole` decision T29 and four valid `refuted` decisions, T31, T32, T33 and T35. They do not certify the printed positive assertions as true.

My first review contained no adverse findings, so there were no outstanding fixes requested by this referee. I rechecked all thirteen earlier assessments. I accept all six scope findings described in `architect-report.md`; **six are fixed, zero partly fixed, zero not fixed**. In particular, I correct my earlier `correct_whole` assessments of T37, T38 and T40 to `correct_restricted`, and my earlier assessment that the restriction lists for T34, T36 and T39 were complete. This correction is grounded in canonical S2/S5 and the actual `Nested` definition, not merely in the architect's acceptance of the other referee's conclusions.

## The scope distinction I missed

Canonical S2 observes an arbitrary subset of the vertices of the full graph, with n observed vertices and N>=n full vertices. S5 nests the **full graphs**. Neither requires successive observed samples or their induced dependency graphs to nest. The SAP Model's G is a graph on exactly the n observed vertices; the revised [Model comment](/home/ubuntu/sap/tasks/CHFID-P011c-a/SAP/P011c/Defs/Part1.lean:57) makes that explicit.

[Nested](/home/ubuntu/sap/tasks/CHFID-P011c-a/SAP/P011c/Defs/Part2.lean:24) additionally requires both nondecreasing sample sizes and, for every k, an injection from the k-th observed vertex set into the next one preserving every Boolean adjacency. This is an induced graph embedding. [Scaling](/home/ubuntu/sap/tasks/CHFID-P011c-a/SAP/P011c/Defs/Part2.lean:31) includes that conjunct. My [blind reading](/home/ubuntu/sap/tasks/CHFID-P011c-a/reading.md:30) recorded the condition correctly, but my claim comparison failed to distinguish it from the source's full-graph nesting. The revised disclosure and three relabelings correct that error.

The extra condition is a real exclusion. For each positive n let H_n be empty if n is odd and a perfect matching if n is even. Let the full graph at n be the disjoint union of H_1,...,H_n, observing just the newest block H_n. These full graphs nest, but an edge in H_(2m) cannot embed into empty H_(2m+1). This failure occurs infinitely often. Give every full-graph coordinate an independent uniform +/-1 outcome and unit weight. On the observed block beta=0, n Var(betaHat)=1, degrees are at most 1, and the printed numerical assumptions hold with constants (1,1,1,2). Homoskedasticity also holds. Taking R=H_n and caps equal to its degrees gives valid constraints and a unique compatible graph. The statistic 1/n is Borel and satisfies both T39 antecedents. Thus the missing implication cannot be supplied by the other statistical assumptions.

The architect repairs the package by accurately describing this smaller proved domain. No removal of the extra hypothesis is claimed or required for a properly labeled restricted result.

## Target-by-target delta

| Target | Earlier verdict | Revision and recheck | Final verdict |
|---|---|---|---|
| T29 | correct_whole | No requested fix; all three canonical clauses remain covered | correct_whole |
| T30 | omission_ok | No requested fix; the unchanged omission remains justified | omission_ok |
| T31 | correct_whole | No requested fix; unchanged negation refutes the printed universal consistency claim | correct_whole |
| T32 | correct_whole | No requested fix; unchanged negation refutes the combined contract, with its logical scope disclosed | correct_whole |
| T33 | correct_whole | No requested fix; unchanged refutation uses the printed, uncovered negative-estimate convention | correct_whole |
| T34 | correct_restricted | Scope disclosure fixed; P3-only omissions and additional observed-graph nesting are all stated | correct_restricted |
| T35 | correct_whole | No requested fix; unchanged combined OLS refutation has nonsingular integrable mean-model instances | correct_whole |
| T36 | correct_restricted | Scope disclosure fixed; omitted nonconsistency assertion remains disclosed | correct_restricted |
| T37 | correct_whole | Label and disclosure fixed; both conservativeness conclusions remain, with an added nesting restriction | correct_restricted |
| T38 | correct_whole | Label and disclosure fixed; CLT and eventual positive variance remain, with an added nesting restriction | correct_restricted |
| T39 | correct_restricted | Scope disclosure fixed; Borel-only restriction and both conditional implications remain | correct_restricted |
| T40 | correct_whole | Label and disclosure fixed; both printed coverage conclusions remain, with an added nesting restriction | correct_restricted |
| T41 | correct_restricted | No requested fix; missing decomposition and positive-size normalization remain accurately disclosed | correct_restricted |

## Comparison with the saved mathematical reading

The revised Defs and Challenge theorem types have the same mathematical bodies, hypotheses, quantifier order, and conclusions as those expanded in `reading.md`. The revisions affecting this review are disclosure comments on Model/Nested/Scaling, six Challenge docstrings, and the three manifest decisions T37/T38/T40. There is no new numerical convention, additional mathematical hypothesis, or removed conclusion relative to the earlier Lean statements. The change is that the existing additional hypothesis is now acknowledged as a restriction relative to the canonical text.

I checked the complete revised docstrings and `record2.json`, including preservation of the previous restrictions:

* [T34](/home/ubuntu/sap/tasks/CHFID-P011c-a/SAP/P011c/Challenge/Part1.lean:28): only P3 is retained; P1, P2, P4 and P5 are expressly omitted; unnecessary homoskedasticity is removed; both added size monotonicity and observed induced embeddings are disclosed.
* [T36](/home/ubuntu/sap/tasks/CHFID-P011c-a/SAP/P011c/Challenge/Part1.lean:43): the complete displayed Proposition 2 limit is retained; the introductory nonconsistency assertion is omitted; both parts of the extra nesting condition are disclosed. No equality of individual means is imposed.
* [T37](/home/ubuntu/sap/tasks/CHFID-P011c-a/SAP/P011c/Challenge/Part1.lean:51): both limits remain and supplied caps are still unrestricted; its sole added source-domain restriction is now disclosed and its decision is `restricted`.
* [T38](/home/ubuntu/sap/tasks/CHFID-P011c-a/SAP/P011c/Challenge/Part1.lean:59): cdf convergence at every real threshold and eventual positive variance both remain; the additional scope condition is disclosed and its decision is `restricted`.
* [T39](/home/ubuntu/sap/tasks/CHFID-P011c-a/SAP/P011c/Challenge/Part1.lean:67): both clipped coverage implications remain; raw-space Borel measurability, exclusion of completion-only statistics, lack of an a.e.-version transfer assertion, and the extra nesting condition are all disclosed.
* [T40](/home/ubuntu/sap/tasks/CHFID-P011c-a/SAP/P011c/Challenge/Part1.lean:77): both printed interval guarantees remain; the extra condition is disclosed and its decision is `restricted`. Both estimates remain everywhere nonnegative.

These six restriction lists are now complete. T41's unchanged restriction correctly omits the exact matrix decomposition and states its normalized inequality only for positive n, while PSD and fixed-correction maximizer equivalence still include zero size. The omission of T30 still avoids crediting a feasibility helper as an objective-preserving computational classification, NP-hardness result/refutation, or PTAS.

## Nonvacuity and junk-value checks

For the six updated disclosures use the retained family n_k=k+1 with independent uniform +/-1 raw coordinates, unit weights, G=R empty, and d=0. All sizes are positive, strictly increasing and unbounded; the empty observed graphs have induced embeddings at every step. The product laws are probability measures, beta=0, |X_i|=1, and Var(betaHat)=1/n_k. Thus Scaling holds with (1,1,1,2), including its additional Nested conjunct. Weighted-coordinate variances are 1. Validity holds and the empty graph is the unique compatible graph for every outcome, so the optimizer hypotheses are everywhere satisfiable.

This gives a nondegenerate common instance for T34, T36, T37, T38 and T40. For T39 the Borel statistic V_k=1/n_k is the exact variance; scaled consistency and one-sided conservativeness both hold with empty positive-error events. The two implications are therefore substantive. This is a mathematical construction of the full asymptotic family, not a claim that a Lean Family instance was compiled.

The revised text introduces no junk values. The relevant safeguards remain:

* Scaling's almost-everywhere bound gives finite moments of all weighted coordinates. MeanModel explicitly requires ordinary integrable raw expectations, and T29's variance identity explicitly requires L2 raw coordinates.
* Family sizes and T29 sample sizes are positive. T38 separately concludes eventual positive variance, so its standardized tail does not use division by zero. T41 restricts only its normalized form to positive size.
* Degree truncation uses min(d_i,n-1) with positive row size. The capacity matrix's subtraction is over the reals. Both V2 estimates have nonnegative factors and sample variance.
* Every coverage probability lies in [0,1], so the real liminf is bounded and has its ordinary meaning. Every critical value occurs with 0<alpha<1, where the normal-cdf level set has a finite real infimum.
* T39 retains the prescribed nonnegative clipping. The negative-estimate exclusion in the printed V1 intervals is explicit. For maximizers, validity gives a nonempty finite compatible set; the selected objective value is its finite maximum of continuous functions and hence measurable even without a measurability assumption on the graph-valued selector.

## Labels and unchanged refutations

T29 remains the sole positive `whole` decision. Its first conjunct groups the linear representation with the mean-model condition, but this does not lose the unconditional algebraic clause: for every design D one may instantiate the theorem with a Dirac-zero model and coefficient vector zero, which satisfies the mean model for that same D. Its pointwise-for-all-y conclusion then yields the representation for arbitrary outcomes. The remaining clauses are unbiasedness under the correct finite mean model and the covariance-sum variance identity under finite second moments. The scratch delta check verifies this logical extraction from the statement type without importing a Challenge stub.

The four refutations remain correct. The smaller nested-observed-graph counterexample domain is sufficient: a counterexample there that also satisfies the printed full-graph assumptions refutes the printed universal guarantee. The earlier C4 witness does exactly that. It uses disjoint four-cycles, alternating means s_i=+/-1, independent noise +/-1/4, unit weights, R=G, and d=2. The full graphs themselves can be these same nested cycle unions. It has n Var(betaHat)=1/16, equal weighted variances, and n V1<=-5/16 on its entire support. Thus the absolute-error and underestimation events at epsilon=1/4 have probability one, and printed coverage is zero. The design with rows (1,s_i), fixed coefficients (0,1), and the intercept coefficient has Gram matrix n I_2 and unit olsTheta weights, furnishing the integrable nonsingular OLS witness for T35.

T32's negated combined contract does not separately assert failure of its homoskedastic specialization, as its docstring says. T35's negated conjunction does not separately assert failures of both components or establish anything about the vignette's realized errors. The `refuted` decisions correctly preserve those scopes.

## Validation

The statement and definition bodies were re-read against the saved blind reading; old and new manifest entries were compared field by field. All previously acceptable restrictions and omission explanations were rechecked, rather than accepting the architect's report as evidence of their correctness.

The scratch checks use only `SAP.P011c.Defs`. `scratch/DeltaCheck.lean` checks that Fin 2 injects into Fin 3 while an observed edge cannot embed into an empty successor, and that T29's type entails its pointwise representation without a mean-model restriction on the arbitrary design. `scratch/Check.lean` rechecks the finite C4, variance-estimator, Gram-matrix, integrability and capacity instances against the revised Defs. Both completed with exit code 0; neither contains `sorry`. At most two Lean processes ran concurrently; no `lake` command was used. Full statistical nonvacuity instances above are justified mathematically.

`findings2.json` parses and has exactly one object for every target in `claims.json`, with the same eight-field schema as the previous findings. The target-to-theorem mapping matches `record2.json`, including null for T30. Historical review files were preserved. No Solution, Comparator or external worktree source was read, and no proof-certification conclusion is drawn from the architect's account.
