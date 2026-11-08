# P022 delta review

All six earlier findings are **fixed**, including fixes by accurate restriction declarations. All five mathematically changed theorem statements were rechecked. No new statement, disclosure, junk-value, or nonvacuity issue was found.

| Findings verdict | Count |
| --- | ---: |
| correct_whole | 12 |
| correct_restricted | 6 |
| restriction_inaccurate | 0 |
| not_faithful | 0 |
| vacuous | 0 |
| false | 0 |
| omission_ok | 0 |
| omission_questionable | 0 |

All 18 severities are `none`. The manifest's decision counts are **10 whole, 6 restricted, 2 refuted, 0 omitted**. The findings schema has no `correct_refuted` verdict, so the two accepted full refutations, T5 and T18, use `correct_whole`. This means complete and correct handling under the newly authorized `refuted` decision; it does **not** mean the affirmative printed assertions were proved.

## Earlier findings

| Target | Status | What resolved the finding |
| --- | --- | --- |
| T18 | Fixed | The unchanged negative statement is now labeled `refuted`. The docstring identifies the printed assertion as false. Its negated quantifier order and reciprocal witness really refute that assertion. |
| T1 | Fixed | The retained witness-A statement is now `restricted`. The record and docstring enumerate the omitted witness-B assertions and A's omitted boundedness/UI, individual CDF/left-CDF values, finite probability identities, and partition proof-step assertion. |
| T5 | Fixed | The theorem now includes the missing universal equality characterization, as well as `choose(4,2)=6`. The original explicit counterexample remains. Its `refuted` label is appropriate. |
| T7 | Fixed | The statement still gives the two infinite limsups. The `restricted` declaration now lists the omitted finite calculations, centered-error/rate statements, convergence in probability, probabilities tending to one, and full divergence of the scaled sequence. |
| T9 | Fixed | The `restricted` declaration now lists the missing shifted-weight-sum and translation-invariance assertions, along with the separate witness calculations. The negative-output example and general discrepancies remain correct. |
| T17 | Fixed through a changed statement | The revised theorem has substantial added hypotheses and a guarded coverage clause. These are explicitly listed in the restriction. The earlier recommendation to label the **old** type whole no longer applies to this new type. |

Fixed: 6. Partly fixed: 0. Not fixed: 0. T1, T7, and T9 resolve their findings by disclosure, rather than by adding the omitted mathematical assertions; that is permitted by the task.

For T17, the old canonical note and the statement's optimality wording explain the earlier scope disagreement. The present verdict does not require settling that disagreement: the newly added hypotheses create an actual restriction, and the current record and docstring accurately list them. The omission of the narrowest-interval assertion is also expressly disclosed. I did not treat the architect's account of the old statement as a substitute for reading the new type.

## Statements changed since the blind reading

The shared statistical definitions from Parts 1–3 retain their mathematical meanings. Part 4 adds two existence predicates. Global changes to the auto-implicit options and relocation of T10 to Part 6 do not change the mathematical assertions. The mathematical theorem-type changes are exactly T5, T6, T8, T10, and T17.

### T5: full equality characterization restored

[Defs/Part5.lean:93](SAP/P022/Defs/Part5.lean#L93) retains the entire previous constant-one counterexample and adds:

* `Nat.choose 4 2 = 6`;
* for every valid design, every real population vector `y`, and every real threshold `x`, the sampled treatment-CDF variance equals `(N−m)/(4(N−1)m)` **if and only if** `F_y(x)=1/2`.

No `m<N` hypothesis is missing: `k>=2` and `m+k<=N` force it. Consequently `(N−m)/((N−1)m)>0`. The corrected variance identity reduces the characterization to `G(1−G)=1/4`, equivalent over the reals to `G=1/2`. The example with `G=0` refutes the printed equality, while an evenly split population at threshold zero realizes `G=1/2`. All denominators are positive. The refutation and the ancillary canonical assertion are both present.

### T6: positive bound for the reciprocal implication

[Defs/Part5.lean:108](SAP/P022/Defs/Part5.lean#L108) changes only the finite implication that concludes a CDF-distance lower bound by dividing by `8NC²`. This implication now additionally assumes `C>0`. The decomposition, probability budget, and absolute integral bound still allow `C=0`. The fixed-parameter conditional limit assembly is unchanged.

The record and docstring disclose the new hypothesis in exactly that location, retain the previous disclosures about selected K functions and constants, and state that the separate lower-endpoint allocation is not asserted. Thus the restriction is accurate and complete.

The positive-threshold implication has a nonempty meaningful domain. With `N=4,m=k=2,C=1`, population outcomes `y1=(0,0,1,1)`, `y0=(0,1,0,1)`, and permutation `(0,2,1,3)`, the observations are `(0,1)` and `(1,1)`. The last integral term is `−4/3`; the threshold `x=1` satisfies its antecedent, and the control CDF distance is `1/2`. This was checked exactly. At `C=0`, zero outcomes still instantiate the other finite clauses without a reciprocal division.

### T8: ambient population restricted to its intended domain

The variance-substitution clause now says **for every natural N with `m+k<=N`**, and both endpoint sides, the midpoint substitution equals the sharp variance estimate ([Defs/Part5.lean:216](SAP/P022/Defs/Part5.lean#L216)). The preceding partition, rank, mean, covariance, and overlap assertions are unchanged.

This removes only the old extraneous calls with invalid population sizes. With `m,k>=2`, the guard implies `N>=4`, so both `N` and `N−1` are positive. Every canonical valid-design case remains. The `whole` label remains correct; no restriction disclosure is needed for enforcing the standing population domain. For example, `m=2,k=3,N=5` and nonconstant samples give a genuine unequal-grid instance.

### T10: valid sizes throughout the limit

The fixed-observation limit now runs over `N=r+(m+k)` for every natural `r` ([Defs/Part6.lean:21](SAP/P022/Defs/Part6.lean#L21)). This enumerates **every** valid size `N>=m+k`; it is not a sparse subsequence. The limit remains `s²(a)/m+s²(b)/k`.

The fixed-arm true-variance approximation also states `m,k>=2` explicitly. These inequalities were already implied by eventual equality to valid design arm sizes, so they introduce no further substantive restriction. The earlier declared omissions—the exact actual-variance remainder and the special observed-data formulas/examples—remain accurate. The `restricted` label is correct.

For `m=k=2,a=b=(0,1)`, the shifted limit begins at `N=4` and tends to `1/2`. Fixed-arm nested populations with bounded nonconstant periodic outcomes, or the previously compiled all-zero sequence, satisfy the approximation hypotheses. No zero arm size or invalid population prefix is used.

### T17: explicit functionals and positivity assumptions

[Defs/Part6.lean:129](SAP/P022/Defs/Part6.lean#L129) now quantifies, in order, the sequence, joint probability law, allocation limits, conditions 1–3, bounded third moments, nonsingularity, and then these additional hypotheses:

1. `LawFunctionalsDefined H`: for **every compatible law J**, both first coordinate moments, second coordinate moments, centered squares, and the centered coordinate product are integrable. The covariance image over compatible laws must also be nonempty, bounded above, and bounded below.
2. The limiting upper bound is strictly positive.
3. For **every row q and every actual assignment**, the estimated upper variance is strictly positive.

The conclusions remain the positive gamma range, the scaled true-variance limit, and the studentized standard-normal limit. The coverage conclusion now quantifies `alpha` with `0<alpha<1` and additionally assumes `NormalCriticalDefined alpha`: the normal critical-value set is nonempty and bounded below. Both the literal coverage limit and its nominal lower bound are inside this guard.

The new predicates in [Defs/Part4.lean:54](SAP/P022/Defs/Part4.lean#L54) and [Defs/Part4.lean:68](SAP/P022/Defs/Part4.lean#L68) expand to exactly those ordinary Mathlib conditions. They do not replace integrals, extrema, or quantiles with special defaults. The docstring and record list all the added assumptions and the omitted optimality assertion. This is an accurately disclosed `restricted` theorem, not a whole statement of the original unconditional corollary.

The all-row estimate positivity is a genuine restriction. Four initial all-zero units followed by periodic corners satisfy the original asymptotic hypotheses and have the same nonsingular limiting law, but their first-row upper estimate is zero. This example explains why the new label must remain restricted.

## Joint nonvacuity of the new T17 hypotheses

Use the existing **cornerWitness**, **cornerLaw**, `theta=1`, and `rho=1/2`.

Periodic frequencies establish weak convergence and convergence at the marginal atoms. Outcomes lie in `{0,1}`, giving uniformly bounded third moments. The limit has covariance matrix `diag(1/4,1/4)`, so it is not concentrated on a line.

Every compatible law has Bernoulli(1/2) marginal coordinates and hence is supported on `{0,1}²`. All required coordinate and centered integrals are integrals of bounded functions on this finite support. If `t=J{(1,1)}`, its masses at `(0,0),(0,1),(1,0),(1,1)` are `t,1/2−t,1/2−t,t`, with `0<=t<=1/2`. Its covariance is `t−1/4`. Thus the covariance image is precisely `[-1/4,1/4]`, nonempty and bounded, with both ends attained. The limiting upper variance is `1`, the true-variance limit is `1/2`, and gamma is `1/2`.

The finite positivity hypothesis holds for **all** rows and assignments. Every row contains all four corner units, and full sampling partitions every unit into treatment or control. If the observed treatment outcomes were constant `a` and the observed control outcomes constant `b`, every unit would lie on `y1=a` or `y0=b`. No such pair of lines covers all four corners. Therefore at least one observed sample variance is positive.

For binary observed success fractions `p,q`, the upper sharp covariance is `min(p,q)−pq>=0`. The two marginal coefficients `(N−m)/m` and `(N−k)/k`, the marginal-variance correction, and `N−1` are positive. Hence the estimated upper variance is strictly positive. This proves the required universal finite positivity, rather than merely extrapolating from finitely many enumerations.

Finally, the standard normal CDF tends to zero and one at the two ends of the real line and is monotone. For every `0<alpha<1`, these properties make `{x : 1−alpha/2<=Phi(x)}` nonempty and bounded below. The corresponding general `NormalCriticalDefined` result was compiled in Lean. Thus every additional hypothesis, including the coverage guard, can hold together in a nondegenerate example.

## Other labels and unchanged assertions

T1, T7, and T9 have unchanged mathematical statements and now carry complete restriction disclosures. Their retained counterexamples still refute the printed readings. In T7, `q=4r` represents `N=4(r+1)`, the same cofinal sequence of positive multiples of four; its first zero-threshold event is legitimately certain.

T18 has unchanged mathematics and a corrected `refuted` decision. Its negation covers functions selected from the law before the sequence and allocation parameters. The reciprocal witness defeats even sequence-dependent finite constants, so it refutes the printed reading without exploiting a stronger quantifier restriction.

The unchanged `whole` statements T2, T3, T4, T11, T12, T13, T14, T15, and T16 retain their first-review verdicts. T8 remains whole after its valid-domain change. T10 and T6 retain their accurately disclosed restricted scope. All theorem names in `record2.json` match current Challenge stubs.

## Verification and scope

* Read every revised Defs and Challenge file, the saved blind readings, canonical claims, earlier findings, `record2.json`, and the architect's account. The first-review artifacts were preserved.
* `scratch/DeltaCheck.lean` compiled with `/home/ubuntu/sap/tools/sap-lean`; `scratch/delta-check.log` is empty. It imports **Defs only**. Checks include the restored T5 characterization from its variance identity; strict coefficient positivity; T6's reciprocal denominator; valid N domains; the redundancy of T10's explicit arm-size assumptions; nonemptiness of the covariance image; the normal-critical guard for every valid alpha; and the line-cover contradiction and positive-variance-expression steps used above.
* `python3 scratch/delta_finite_audit.py` passed **5,860 exact rational assertions**, including **90** equality-characterization instances and **1,905** corner-population assignments at `N=4,...,12`. It also checks the nonzero T6 last-term example and finite compatible-law moments. Results are in `scratch/delta-finite-result.json`. Its finitely enumerated checks supplement the all-row mathematical argument above.
* `findings2.json` was parsed with Python and checked against all 18 canonical targets, required fields, verdict/severity enums, revised decision labels, and report counts. The old six issue-bearing targets each have a status in the table above.

No false or vacuous theorem was found. The changed statements use proper finite denominators; the new limiting-law and critical-value predicates ensure their defining integrals and extrema have the intended meanings. CDF suprema remain bounded and scaled probability limsups remain in `ENNReal`. No new junk convention or hypothesis assuming the CLT/coverage conclusion was found.

This is a statement audit. Original proof rows, Solution sources, and external certification claims were not used as evidence for the theorem readings. No SAP source, canonical claim, or architect record was edited, and no `lake` command was run.
