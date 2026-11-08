All six adverse findings from round 1 are **fixed**. There are no partly fixed,
unfixed, or new adverse findings. The scope condition remains in the statements
and is now accurately disclosed; the three affected `whole` labels have changed
to `restricted`.

| Verdict | Count |
| --- | ---: |
| correct_whole | 5 |
| correct_restricted | 7 |
| restriction_inaccurate | 0 |
| not_faithful | 0 |
| vacuous | 0 |
| false | 0 |
| omission_ok | 1 |
| omission_questionable | 0 |

The five `correct_whole` review verdicts comprise T29 and four valid refutations
(T31, T32, T33, T35). The latter have decision `refuted` in `record2.json`;
these verdicts affirm the refutations, not the positive printed assertions.

I compared the revised Defs and all twelve statement bodies with `reading.md`,
then checked their docstrings and `record2.json` against `claims.json`.
The mathematical definitions, theorem hypotheses, quantifier order, conclusions,
and theorem names retain the readings saved in round 1. The revision changes
disclosure comments and manifest metadata. In particular, `Nested` still means
nondecreasing sample sizes and an induced embedding of each observed graph into
its successor. Its new comment, the `Scaling` comment, and the `Model` comment
now distinguish this condition from nesting of full graphs. The architect's
account of our six findings agrees with the actual revised files.

| Earlier finding | Status | Verification |
| --- | --- | --- |
| P011-T34: incomplete P3-only restriction | Fixed | The docstring at [Challenge/Part1.lean:28](/home/ubuntu/sap/tasks/CHFID-P011c-b/SAP/P011c/Challenge/Part1.lean:28) and revised record retain only P3, list omitted P1, P2, P4, P5, state that homoskedasticity is unnecessary, and explicitly add sample-size monotonicity and observed-graph induced nesting. |
| P011-T36: incomplete restriction | Fixed | The docstring at [Challenge/Part1.lean:43](/home/ubuntu/sap/tasks/CHFID-P011c-b/SAP/P011c/Challenge/Part1.lean:43) and revised record disclose both the omitted introductory nonconsistency assertion and the added monotonicity/nesting condition. The displayed conservativeness conclusion is retained. |
| P011-T37: incorrect whole label | Fixed | The decision is now `restricted`. The docstring at [Challenge/Part1.lean:51](/home/ubuntu/sap/tasks/CHFID-P011c-b/SAP/P011c/Challenge/Part1.lean:51) and record disclose monotonicity and induced nesting. Both conservativeness conclusions remain, with no bound on supplied degree caps. |
| P011-T38: incorrect whole label | Fixed | The decision is now `restricted`. The docstring at [Challenge/Part1.lean:59](/home/ubuntu/sap/tasks/CHFID-P011c-b/SAP/P011c/Challenge/Part1.lean:59) and record disclose monotonicity and induced nesting. Both cdf convergence at every real threshold and eventual positive variance remain. |
| P011-T39: incomplete Borel restriction | Fixed | The docstring at [Challenge/Part1.lean:67](/home/ubuntu/sap/tasks/CHFID-P011c-b/SAP/P011c/Challenge/Part1.lean:67) and record retain the raw-Borel requirement and exclusion of completion-only statistics, add monotonicity/nesting, and retain both clipped-coverage implications. |
| P011-T40: incorrect whole label | Fixed | The decision is now `restricted`. The docstring at [Challenge/Part1.lean:77](/home/ubuntu/sap/tasks/CHFID-P011c-b/SAP/P011c/Challenge/Part1.lean:77) and record disclose monotonicity and induced nesting. Both printed-interval coverage conclusions remain. |

The added wording matches the actual predicate at
[Defs/Part2.lean:24](/home/ubuntu/sap/tasks/CHFID-P011c-b/SAP/P011c/Defs/Part2.lean:24):
it requires, for each row, an injection that preserves and reflects every
adjacency entry. It requires no nesting of recruitment graphs, caps, weights,
or outcome laws. The revised disclosure adds none of those conditions. All six
docstrings explicitly identify the distinction from the printed assumption on
full graphs. This repairs the earlier disclosure failures under the permitted
`correct_restricted` verdict.

The other seven target assessments remain supported:

| Target | Revised decision | Re-check |
| --- | --- | --- |
| P011-T29 | whole | All three canonical components are present: the OLS linear representation, unbiasedness under the integrable correct mean model with nonsingular Gram matrix, and the general finite-second-moment covariance-sum variance identity. The representation is law-independent and holds for every raw outcome. Its placement alongside `MeanModel` does not remove designs: a zero-mean Dirac model supplies that premise for any design, yielding the universally quantified representation. |
| P011-T30 | omitted | The omission remains justified on the available evidence. The canonical note permits it, and the credited feasibility helper alone does not establish the computational-classification claim. No surrogate theorem is presented as that claim. |
| P011-T31 | refuted | The unchanged negation concerns the printed n-scaled oracle-consistency assertion. An actual counterexample satisfies both full-graph and observed-graph nesting, so the extra nesting condition does not invalidate the refutation of the broader printed assertion. |
| P011-T32 | refuted | The unchanged negation refutes the combined general conservativeness contract. Its docstring correctly says it does not separately assert failure of the homoskedastic specialization. |
| P011-T33 | refuted | The unchanged negation refutes coverage of the printed interval, explicitly counting negative-estimate realizations as undefined and uncovered. |
| P011-T35 | refuted | The unchanged negation concerns the combined variance and printed-coverage guarantee for an actual correctly specified OLS coefficient. It does not claim separate refutations of each conjunct or infer the vignette's realized errors. |
| P011-T41 | restricted | The exact decomposition remains omitted and the normalized form requires n>0; both restrictions remain disclosed. PSD and constant-shift invariance still include size zero. The capacity subtraction is real subtraction, and all maximizers, including ties, are preserved. |

No formal statistical statement changed, so the existing nonvacuity and
totalization analysis continues to apply. I rechecked it against the revised
definitions rather than treating new comments as hypotheses.

For all six repaired positive targets, a common nonvacuity family has
n_k=k+1, independent fair-sign raw outcomes, unit weights, empty observed and
recruitment graphs, and zero caps. The sizes are nondecreasing and the empty
observed graphs embed inducedly into their successors. Every row has beta=0,
weighted variance 1, and var(betaHat)=1/n_k. Scaling holds with constants
(1,1,1,2); validity and homoskedasticity also hold. The empty graph is the unique
compatible maximizer for every raw outcome. For T39, the deterministic Borel
statistic V_k=1/n_k satisfies both premises exactly. Thus the now-disclosed
restriction has nondegenerate admissible instances.

For the four refutations, use n_k=4(k+1), disjoint K_{2,2} blocks, signs
s=(1,1,-1,-1) per block, independent fair signs epsilon_i, theta_i=s_i, and
Y_i=2+s_i epsilon_i. Then weighted X_i=2s_i+epsilon_i, beta=0,
n_k var(betaHat)=1, and Scaling holds with (3,2,1,2). Both full and observed
graphs nest. Taking R=G and d_i=2 forces the unique compatible graph. The exact
identity

```
n V1 = -3 - (4/n) sum_i s_i epsilon_i
            + (2/n) sum_{unordered edges} epsilon_i epsilon_j
            - 3 betaHat^2
```

implies n V1 -> -3 in probability, since independent bounded block sums
concentrate and E[betaHat^2]=1/n. It refutes consistency and conservativeness;
printed coverage is at most Pr(V1>=0), which tends to zero. For the OLS target,
take design rows (1,s_i), coefficient vector (2,0), and the slope coefficient:
D^T D=n I_2 and its `olsTheta` row equals s. All means and second moments are
ordinary finite moments. These witnesses still refute the printed readings.

The remaining definition checks also retain their safeguards:

* All statistical divisions use positive sample sizes. OLS Gram invertibility
  excludes the singular-matrix inverse convention. T38 includes eventual
  positive variance for its standardization.
* Scaling's measurable bounded weighted coordinates have finite moments;
  T29 explicitly requires integrable raw means or finite second moments where
  needed. No integral of a nonintegrable function supplies a statistical value.
* Probabilities lie in [0,1], so conversion to real values discards no infinite
  mass and coverage liminfs are bounded. Normal quantiles occur only for
  0<alpha<1, where the defining real infimum is finite and ordinary.
* T39 uses the disclosed Borel statistics and clipping. The printed events in
  T33/T35 exclude negative estimates. T40's two estimates are everywhere
  nonnegative. Arbitrary maximizing graph selectors have measurable objective
  values because these values are finite maxima of continuous functions.
* Natural subtraction in min(d_i,n-1) is the intended degree truncation for
  positive n. The capacity matrix uses real subtraction. Nonempty capacity
  examples exist: K_{2,2} with h_i=3 gives the nonzero PSD matrix 2I+A.

The existing scratch check was rerun successfully against the refreshed
compiled definitions with
`/home/ubuntu/sap/tools/sap-lean scratch/Check.lean`. It imports only Defs and
checks finite graph degrees and quadratic forms, a negative V1 value, the
nonempty capacity example, exact OLS Gram matrices and slope weights, an
integrable mean model, compatibility, and the failed embedding that motivated
the earlier findings. The full asymptotic witnesses above are mathematical
constructions; this report does not present them as newly compiled Lean proofs.

`findings2.json` uses the same schema as `findings.json`, has exactly one object
for each of the 13 canonical targets, and has been parsed and checked with
Python. No original review artifact, Defs file, or Challenge file was edited.
