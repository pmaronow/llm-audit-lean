# Blind reading

This file was written before opening `claims.json` or `record.json`. It reads the five Challenge statements, their docstrings, and every source definition in their elaborated closures. Indices below are zero based. The closure's generated proof declarations provide graph symmetry/zero diagonal, index bounds, probability-measure instances, positive sample sizes/growth, outer-measure instances, and valid numeral instances; they add no statistical assumptions.

## SAP.P011b.T20

The theorem has no parameters or hypotheses. Its conclusion is a conjunction of facts about an explicitly specified sequence, and the negation of a universally quantified assertion.

Here are the definitions appearing in that assertion, unfolded. A graph on `Fin n` is a Boolean function `a(i,j)` with `a(i,j)=a(j,i)` and `a(i,i)=false`. Its real adjacency entry is 1 when the Boolean is true and 0 otherwise; its degree is the natural-number sum of these indicators. A graph A is compatible with R and natural caps d if every true entry of R is a true entry of A and every degree of A is at most its cap.

A model consists of a probability measure P on the Borel space `Fin n → ℝ`, deterministic real weights θ, a graph G, an observed graph R, and natural degree caps d. Write X_i(y)=θ_i y_i, B(y)=n⁻¹∑_i X_i(y), μ=∫B dP, E(f)=∫f dP, and Var(f)=∫(f−∫f dP)² dP. The covariance C_ij is `∫(X_i−∫X_i)(X_j−∫X_j) dP`. The common-variance predicate says C_ii=C_jj for all i,j. Write s²(y)=n⁻¹∑_i(X_i(y)−B(y))², v=n⁻¹∑_i C_ii, and ρ_ij=0 if v=0, otherwise C_ij/v. The auxiliary estimate is

`V*(y) = s²(y)/n · (1 + n⁻¹∑_i∑_j a_G(i,j)ρ_ij)`.

Graph dependency means that for every two disjoint finite vertex sets S,T with no G edge between them, the random vectors `(y_i)_{i∈S}` and `(y_j)_{j∈T}` are independent under P, in Mathlib's `IndepFun` sense. This is independence of vectors, not merely zero pairwise covariances.

A family is a sequence of positive natural sizes n_k tending to infinity and a model at each size. It is nested when sizes are nondecreasing and, for every k, there exists an injection of its vertices into the next set preserving all graph entries. No coupling of probability laws across k is required by this definition. `Scaling(F,c1,c2,c3,c4)` means, in order: this nesting, four positive real constants, graph dependency at every k, almost surely `|X_i−μ_k|≤c1` simultaneously for all i at each k, degree(G_k,i)≤c2, convergence `n_k Var(B_k)→c3`, and `|θ_ki|<c4` for all k,i. `Valid F` says G_k is compatible with R_k,d_k at each k. Probability of E means the real value of P(E), i.e. `ENNReal.toReal (P E)`.

For the fixed witness, n_k=k+1. At size n, a uniformly chosen Boolean vector in `Fin n → Bool` is mapped to signs `y_i=1` for true and −1 for false. The law is the measure associated with the pushforward of `PMF.uniformOfFintype`; hence its coordinates are independent fair signs. θ_i=1, G=R is the empty graph, and d_i=0. Let p_n(ε) be the probability of the strict inside event `|nV*−n Var(B)|<ε` in this model.

The first conjunct (`signCertificate`) states all of the following:

1. This family satisfies Scaling with `(c1,c2,c3,c4)=(1,1,1,2)` and is Valid.
2. For every natural n, if n>0 then the model is homoskedastic, μ=0, n Var(B)=1, E(B²)=1/n, and, for every real vector y whose coordinates are all ±1, `nV*(y)=1−B(y)²` and `|nV*(y)−n Var(B)|=B(y)²`.
3. For every real ε>0, for every natural n>0, `1−1/(nε)≤p_n(ε)`, and `p_(k+1)(ε)→1` as k→∞.
4. `p_2(1/2)=1/2`, `p_4(1/2)=7/8`, and `p_16(1/2)=32631/32768`.
5. It is false that for every ε>0 the sequence `p_(k+1)(ε)` tends to zero.

The second conjunct negates `printedSignAssertion`. That assertion quantifies first over every family F and every four real constants; then assumes Scaling F with those constants, Valid F, and homoskedasticity at every k; and then asserts for every real ε>0 convergence to zero of `P_k(|n_k V*_k−n_k Var(B_k)|<ε)`. The theorem asserts this universal statement is false.

The third conjunct (`signDetails`) says: for every natural n>0, the sign model has graph dependency; every raw coordinate has expectation zero and C_ii=1; almost surely all `|X_i−μ|=1`; and for every sign-valued vector, `nV*=s²=1−B²`.

Junk-value audit: real division is total and gives zero for a zero denominator. The asserted witness results and limits use n>0 or n=k+1, and the family type also enforces positivity, so n=0 does not enter those results. `signModel 0` itself exists, with its singleton empty input vector, but is not used for a positive-size assertion. The explicit zero-variance branch of ρ avoids an undefined correlation; the witness has v=1. Bochner integrals would return zero for nonintegrable integrands in an unrestricted model. Scaling has no separate integrability clause, but its almost-sure uniform bound around the finite real μ makes each weighted coordinate bounded at each size, and thus integrable with all moments under the probability law. In particular, the actual sign witness is finite-valued and integrable; no such default supports the counterexample. Probability's `toReal` could send ∞ to zero in general, but every model law is a probability measure. Empty S or T in dependency gives an ordinary constant empty vector. Uniform laws require a nonempty finite source, including the singleton source for n=0. No logarithm, root, real power, infimum, supremum, limsup, liminf, truncated subtraction, or partial-function default occurs in the mathematical statement. Natural-to-real casts are exact; the auxiliary numeral proof terms only validate the finite and rational literals.

The docstring describes this as a refutation of a printed limit-zero display by fair signs, including exact inside-event probabilities and limit one. The blind reading alone does not establish which printed assertion is canonical.

## SAP.P011b.T21

Quantifiers, in order: an implicit natural n; a proof n>0; a model m of size n; a proof of graph dependency; a proof that all weighted coordinate variances coincide; and, for every index i, a proof that `y↦θ_i y_i` belongs to Mathlib `MemLp` with exponent 2 under the model law. Thus the last assumption includes almost-everywhere strong measurability and finite second moment. All conclusions are under these assumptions.

A model, graph, dependency, expectation, variance, covariance, weighted variables X_i, mean B, s², v and ρ have the fully unfolded meanings given in T20's section. In particular dependency concerns the raw coordinate vectors, homoskedasticity concerns the weighted outcomes, and ρ=C_ij/v with the zero branch. `V2(G,X)` is `s²/n · (1+n⁻¹∑_i∑_j a_G(i,j))`. `V*` includes ρ in the double sum as in T20.

The general conclusion is the conjunction

`n Var(B) = v · (1 + n⁻¹∑_i∑_j a_G(i,j)ρ_ij)`,

`∀ i,j, ρ_ij≤1`, and `∀ real vectors y, V*(y)≤V2(G,X(y))`.

It also asserts a fixed, separate witness, independent of the quantified m. In general `pathModel(t,b)` has size 3b. A uniform array `Fin b → Fin 2 → Bool` gives independent fair signs U_r,V_r for each block r. Index i has local position i mod 3 and block floor(i/3). Its three outcomes are `(t+U_r, −2t+(3/5)U_r+(4/5)V_r, t+V_r)`. Weights are one; G and R consist of disjoint copies of the three-vertex path 0—1—2; caps are the local path degrees (1,2,1). The block graph puts an edge exactly when block indices agree and the two local positions are adjacent. The statement uses only t=0,b=1, so the law has four equally likely outcome vectors.

For this fixed witness it asserts homoskedasticity, graph dependency, all C_ii=1, `ρ_01=3/5`, `ρ_12=4/5`, `ρ_02=0`, and both `3 Var(B)` and `v(1+∑_ij a_G(i,j)ρ_ij/3)` equal 29/15. Thus two adjacent correlations really are different.

Junk-value audit: n>0 protects all sample-size denominators in the general identities. The general model may have v=0: ρ is then defined to be zero, including on the diagonal. With the stated finite second moments and equal variances this is the degenerate case of almost surely constant weighted coordinates, whose covariances and Var(B) are zero. It is an explicit extension of correlation at zero variance, not a positive-variance correlation value. The fixed witness has v=1. Finite second moments ensure the means, variances and covariance products are integrable, including the weighted sample mean; there is no Bochner junk value. The path law is finite. `localIndex` and `blockIndex` use natural remainder/division by q under q>0; here q=3. For b=0 their input index type is empty, so no invalid block index is evaluated. All used literals `0,1,2 : Fin 3` and `0,1 : Fin 2` are within bounds. The PMF source is nonempty even when b=0. Empty vertex subsets in dependency are harmless. No other listed transcendental, order-limit, infinity-conversion, or partial-function convention appears in this closure.

The docstring advertises the pairwise correlation identity and oracle upper bound, the unequal path correlations, and the usual measure-theoretic conditions including finite second moments. It does not claim a shared scalar correlation.

## SAP.P011b.T22

The theorem quantifies over an implicit natural n and then n>0. A graph, real adjacency, degree, mean and centered data have the T20 meanings. A binary edge vector is a Boolean function on the subtype `Edge n={(i,j)∈Fin n×Fin n : i<j}`. Its symmetric graph `fromUpper(a)` has entry a(i,j) if i<j, a(j,i) if j<i, and false on the diagonal. `toUpper(A)` restricts a graph to i<j. The upper objective U(a,w) is the finite sum of w_e over true a_e. The upper degree D(a,i) counts true edges incident to i. A compatible graph contains R and satisfies the natural caps d. `Maximizes(R,d,f,A)` means A is compatible and every compatible B has f(B)≤f(A); it does not stipulate existence separately.

For data x∈ℝⁿ let c_i=x_i−n⁻¹∑_j x_j, s²=n⁻¹∑_i c_i², and q(M,c)=∑_i∑_j M_ij c_i c_j. Then `V1(A,x)=(∑_i c_i²+q(a_A,c))/n²`. The conclusion is the conjunction of the following seven clauses (all quantifiers are internal to their own clause):

1. The map a↦fromUpper(a) is bijective from all Boolean upper edge vectors to all symmetric zero-diagonal Boolean graphs.
2. For every a and then every x, `q(a_fromUpper(a),c)=2 U(a,(i,j)↦c_i c_j)`.
3. For every a and then every i, `degree(fromUpper(a),i)=D(a,i)`.
4. For every graph R, caps d and binary a, compatibility of fromUpper(a) is equivalent to `(∀e, R_e=true → a_e=true) ∧ (∀i, D(a,i)≤d_i)`.
5. For every R,d,a,x, maximizing V1 over compatible graphs at fromUpper(a) is equivalent to compatibility of that graph and `∀b, compatibility(fromUpper(b)) → U(b,c_i c_j)≤U(a,c_i c_j)`.
6. For every a and x, `n² V1(fromUpper(a),x)=n s²+2U(a,c_i c_j)`.
7. For every a, `∑_i∑_j a_fromUpper(a)(i,j)=2U(a,1)`, and the cardinality of Edge n is `n(n−1)/2` (natural arithmetic).

Junk-value audit: n>0 excludes the zero denominators in mean, variance and V1; n=1 is allowed and Edge 1 is empty. Its unique Boolean vector maps to the unique empty graph and all objectives are empty sums equal to zero. The n−1 in the edge count is truncated natural subtraction, but n≥1 makes it the intended count, and the product n(n−1) is always even so natural division by 2 is exact. Caps need not admit any compatible graph: in that case both sides of the maximizer equivalence are false rather than a chosen default optimizer. No supremum, choice of maximizer, integration, roots, logs, real powers, extended-real conversion, or partial-function defaults are used.

The docstring says binary edges and symmetric adjacency matrices describe the same finite programs, objectives and maximizers. The exact objective comparison includes the necessary factor of two and the additive diagonal term, rather than asserting numerical equality of the upper objective and the entire variance estimate.

## SAP.P011b.T23

The theorem has no outer parameters or hypotheses. It first asserts explicit facts about two real vectors and two fixed graphs on Fin 3, then gives a universally quantified optimality statement.

A graph is a symmetric Boolean 3×3 matrix with false diagonal. Real adjacency is its 0/1 indicator; degree counts its true entries. Compatibility with R,d means all R edges are present and degrees are bounded by d. The empty graph has no edges. `edge12` has just 0—1, and `edge23` has just 1—2 (names use one-based vertex labels). The mean is the sum divided by 3; c_i is the coordinate minus that mean. `nonzeroRule(x)` is the symmetric zero-diagonal graph with an edge i—j exactly when i<j and c_i c_j≠0, then reflected to the lower triangle. `upperSum(f)=∑_i∑_{j:i<j}f(i,j)`; this counts each unordered pair once. These definitions use the same explicit `fromUpper` reconstruction described in T22.

For x=(-2,1/2,3/2) the statement asserts mean zero and pair products c_0c_1=−1, c_0c_2=−3, c_1c_2=3/4. The nonzero rule is not compatible with empty R and all caps 1. The graph edge23 is compatible with these constraints and has upper edge-product objective 3/4. It further asserts that every upper edge of the nonzero rule is true and every degree equals 2.

For z=(0,1,−1) it asserts mean zero, c_0c_1=0, edge12 has entry (0,1)=true, and the nonzero rule has that entry false. Consequently that rule is not compatible with R=edge12 and all caps 2.

Finally, for every graph A on Fin 3, and then every proof that A is compatible with empty R and caps 1, the upper edge-product objective for x is at most 3/4; if it equals 3/4 then A=edge23. Together with edge23's displayed compatibility and objective value, this states unique optimality for the upper objective. The definition takes the compatibility proof as an argument, but it is not an encoded extra assumption inside the objective.

Junk-value audit: the only sample-size denominator is the nonzero real number 3 and the fractional data denominators are 2 and 4. Fin 3 literals are all in range. Comparison with zero is ordinary real comparison under classical decidability. Empty upper sums have their usual zero value. No integration, real power, logarithm, square root, extended-real conversion, extremum default, truncated subtraction, or partial-function default occurs. The counterexamples are finite deterministic optimization instances; they assert no sampling process or asymptotic statistical conclusions.

The docstring explicitly refutes the interpretation that a nonzero-product instruction itself supplies a data-determined feasible or optimal assignment. It does not call the canonical printed assertion false. Whether that interpretation is the canonical claim is deferred until step 2.

## SAP.P011b.T24

Quantifiers, in order: an implicit natural n (with no positivity hypothesis), graphs R and G on Fin n, natural caps d_i, and a proof that G contains every R edge and degree(G,i)≤d_i for all i. Graphs are by type symmetric Boolean matrices with false diagonal. Their real adjacency entries are 0 or 1 and their natural degrees count ones.

`ProgramFeasible(R,d,A)` is `(∀i,∑_j a_A(i,j)≤(d_i:ℝ)) ∧ (∀i,j,a_R(i,j)≤a_A(i,j))`. `Compatible(R,d,A)` instead uses edge inclusion as Boolean implication and natural-number degree inequalities. The conclusion is: for every graph A on Fin n these two predicates are equivalent, and G satisfies ProgramFeasible. Thus symmetry, zero diagonal and binary entries are ambient type conditions on A, not missing constraints for arbitrary real matrices. The true-graph feasibility clause uses exactly the given compatibility hypothesis; it does not assume the conclusion of the equivalence.

Junk-value audit: n=0 is allowed; there is a unique empty graph and empty cap vector, all universal constraints hold, and the equivalence and feasibility have their ordinary empty-system meanings. The natural-to-real cast of d and the finite adjacency sums preserve the exact integer inequalities. There are no sample-size divisions, truncated subtractions, integrals, powers, logarithms, roots, extended-real conversions, infima/suprema, order limits, or partial-function defaults.

The docstring explicitly restricts the result to graph feasible-set equivalence and true-graph feasibility under valid constraints. It says that observed-data tuple correction, the Assumption 3 index-set correction, all of content (ii) including its covariance bound and statistical scope, and an edge-set typography correction are omitted. No conclusion about those topics is present in the statement.
