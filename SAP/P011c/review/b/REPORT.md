The audit covers 13 targets and 12 theorem stubs. Counts:

| Verdict | Count |
| --- | ---: |
| correct_whole | 5 |
| correct_restricted | 1 |
| restriction_inaccurate | 3 |
| not_faithful | 3 |
| vacuous | 0 |
| false | 0 |
| omission_ok | 1 |
| omission_questionable | 0 |

Six targets have major statement-fidelity issues. No retained Lean assertion was
found false or vacuous. The five `correct_whole` results include four correct
**refutations** (T31, T32, T33, T35), consistent with the record's `refuted`
decisions; they do not affirm the false positive printed claims.

The blind reading was saved in `reading.md` before opening `claims.json` or
`record.json`. The claim comparison was then saved in `claim-stage.json` before
opening `record.json`. No step-2 reading or classification was changed after
reading the record. Findings below use the supplied canonical claim and standing
assumptions, particularly the distinction between the full graph and its
observed induced subgraph in S2 and S5.

The shared issue is at
[Defs/Part2.lean:21](/home/ubuntu/sap/tasks/CHFID-P011c-b/SAP/P011c/Defs/Part2.lean:21).
`Nested F` requires induced embeddings between successive **observed** graphs:
for each k there is an injection e with
`G_k(i,j) = G_(k+1)(e(i),e(j))` for all i,j. `Scaling` includes this as its first
conjunct. These graphs have n observed vertices and are the oracle adjacency
graphs in V1 and V2; they cannot instead mean the full N_n-vertex graphs.

Canonical S5 nests the **full** graphs G. Neither S2 nor S5 requires the observed
vertex sets to nest. The extra induced nesting of the observed graphs therefore
needs disclosure. A concrete excluded family establishes the distinction:

* Let H_m have m vertices, with no edges for odd m and a perfect matching for
  even m. Let the full graph at sample size n be the disjoint union of
  H_1,...,H_n. These full graphs are nested, even as induced subgraphs, with
  N_n=n(n+1)/2 >= n.
* Observe only the newest block H_n. Label its vertices 1,...,n, as S2 permits
  for each sample. Give all vertices independent fair-sign outcomes and observed
  weights theta_i=1. Then beta_n=0, |theta_i Y_i-beta_n|=1 almost surely,
  observed degrees are at most 1, n var(betaHat_n)=1, and |theta_i|<2.
  All printed scaling conditions hold with (c1,c2,c3,c4)=(1,1,1,2).
* Take R_n=H_n and the actual full degrees as caps. The constraints are valid
  and force a unique graph, hence a maximizer for every raw outcome. All
  weighted variances are 1. For T39, choose the deterministic Borel statistic
  V_n=1/n; both conditional premises hold exactly.
* The observed graph H_2 is an edge while H_3 is empty. No induced embedding
  exists. This last fact is also checked in Lean in `scratch/Check.lean`.

Thus the issue persists with nondegenerate variance, genuine full-graph nesting,
homoskedasticity, actual degrees, valid constraints, a unique maximizer, and a
Borel statistic. Assuming nested observed samples would remove the issue, but
that additional convention is absent from the supplied canonical assumptions.

The affected decisions are:

| Target | Verdict | Reason and correction |
| --- | --- | --- |
| P011-T34 | restriction_inaccurate | P3 alone is correctly retained, but its docstring and record omit the added observed-graph nesting. Add this restriction, or remove the unnecessary `Nested F` antecedent when stating the finite degree bound. |
| P011-T36 | restriction_inaccurate | Omitting the nonconsistency assertion is accurately disclosed. The additional observed-graph nesting is not. Add it to the restriction, or prove the displayed limit without it. |
| P011-T37 | not_faithful | Both conservativeness conclusions are correct, but the `whole` decision misses the stronger observed-graph nesting hypothesis. Mark restricted and disclose it, or remove that premise. |
| P011-T38 | not_faithful | The CLT is correctly formulated, including eventual positive variance, but is quantified only over the more restricted observed-nested families. Correct the decision and docstring, or prove it without this premise. |
| P011-T39 | restriction_inaccurate | The Borel restriction is accurately disclosed, but induced nesting of observed graphs is an additional undisclosed restriction. The excluded family above already has Borel V and satisfies both premises, so the Borel disclosure does not cover the problem. |
| P011-T40 | not_faithful | Both variance estimates are nonnegative and both coverage claims are correct on the stated formal domain. The `whole` decision fails to disclose the extra observed-graph nesting. Mark restricted and disclose it, or remove it. |

The explicit replacement docstring text for each target is in `findings.json`.
No Defs or Challenge file was edited. Removing `Nested F` is a mathematically
sound stronger-statement repair for these six results: their numerical,
dependency, homoskedasticity and coverage arguments do not use nesting.

Nonvacuity and the four refutations were checked independently of the record.
For a common admissible positive family, take n_k=k+1, independent fair-sign
coordinates, theta_i=1, empty G_k and R_k, and d_i=0. Its sizes and graphs nest,
its true scaled variance is exactly 1, and it satisfies Scaling (1,1,1,2), Valid,
and Homoskedastic. The empty graph is the unique maximizer for every outcome.
The statistic V_k=1/n_k makes both T39 premises hold identically. In particular,
positive limiting variance has not made the asymptotic antecedents empty.

For all four refutations use n=4(k+1) and disjoint K_{2,2} blocks. Let
s=(1,1,-1,-1) on each block, let epsilon_i be independent fair signs, and set
theta_i=s_i and Y_i=2+s_i epsilon_i. Then X_i=theta_i Y_i=2s_i+epsilon_i,
beta=0 and n var(betaHat)=1. All full and observed graphs genuinely nest;
Scaling holds with (3,2,1,2). Set R=G and d=2, so G is the unique compatible
graph for every outcome, not merely almost surely. Equal weighted variances
also hold.

Writing S=I+A gives S s=-s and S 1=3 1. Since betaHat=sum_i epsilon_i/n,

```
n V1 = -3 - (4/n) sum_i s_i epsilon_i
            + (2/n) sum_{unordered edges} epsilon_i epsilon_j
            - 3 betaHat^2.
```

The three random remainder terms tend to zero in probability: block sums are
independent and bounded, and E[betaHat^2]=1/n. Consequently n V1 -> -3 while
n var=1. The absolute error exceeds 2 with probability tending to one (T31);
the underestimation exceeds 1 with probability tending to one (T32); and every
printed coverage is bounded by Pr(V1>=0), which tends to zero (T33).

For T35 take a two-column design with rows (1,s_i) and fixed b=(2,0).
The Gram matrix is n I_2 and the slope row of olsTheta is exactly s, so this
same construction is an integrable, correctly specified, unbiased OLS example.
It refutes both components of the combined contract. T32's formal negation
does not separately state that the homoskedastic specialization fails, exactly
as its docstring warns; a witness to the combined contract is sufficient for
the recorded decision.

The positive homoskedastic limits have the expected mathematical content. With
Z_i=X_i-beta, bounded-degree dependency makes
`n^(-1) sum Z_i^2 - E[n^(-1) sum Z_i^2]` tend to zero in mean square.
Subtracting `(betaHat-beta)^2` gives sample variance approaching the common
weighted variance plus nonnegative mean dispersion. Cauchy-Schwarz and
dependency give `n var(betaHat) <= commonVariance * gFactor`, with
`1 <= gFactor <= 1+c2`. Maximization and degree truncation preserve the required
upper bounds. The CLT centers each summand at its own expectation; it does not
assume equal coordinate means. T39 then has the ordinary Slutsky and one-sided
coverage implications. The six findings concern scope and disclosure rather
than these facts.

Other definition checks found no totalization or emptiness shortcut: all
statistical sample sizes are positive; weighted moments under Scaling are
finite; T29 expressly has the required finite moments or integrable means and
Gram invertibility; normal quantiles are used only for 0<alpha<1; probabilities
are in [0,1], so real liminfs are bounded; and optimal objective values are
measurable finite maxima even if selectors are not assumed measurable.
Printed coverage explicitly excludes negative variance estimates. T41's real
capacity subtraction and positive-size normalization are correct, its missing
decomposition is disclosed, and nonempty capacity examples exist. T30 is
reasonably omitted: an auxiliary feasibility encoding alone cannot replace the
computational classification, and the canonical note explicitly allows this
omission.

Validation used only Defs imports, never the theorem stubs as proofs.
`/home/ubuntu/sap/tools/sap-lean scratch/Check.lean` completed successfully,
checking finite degrees and quadratic forms, a negative V1 value, a nonempty
capacity instance, exact OLS Gram matrices and slope weights, an integrable
mean-model instance, compatibility, and the failed observed-graph embedding.
An independent exact rational enumeration of the 16 one-block sign outcomes
gave var(betaHat)=1/4, E[4 V1]=-15/4, and second moments 4 for each of the
centered block sums used above. Full asymptotic witnesses are mathematical
constructions here, not claimed as newly compiled Lean proofs. All output JSON
files were parsed with Python and checked for complete, unique target coverage.
