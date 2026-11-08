# Blind reading

This file was saved before opening `claims.json` or `record.json`. The sources read were the three target docstrings and statements in `Challenge/Part1.lean`, every entry of their closures in `closure.json`, and the relevant Mathlib definitions. `scratch/BlindCheck.lean` prints the generated proof dependencies and the structures. No canonical claim or architect decision has informed this reading.

## SAP.P011c.T39

### Objects, definitions, and assumptions

The theorem asserts the proposition called `T39WholeStatement` (`Defs/WholeW1.lean:58–65`). Its quantifiers, in order, are: every family F; every four real constants c1,c2,c3,c4; an implication from `WholeScaling F c1 c2 c3 c4`; every sequence of real statistics V; an implication from their rowwise a.e. measurability; then the conjunction of two implications, one for consistency and one for conservativeness.

Here is the complete mathematical expansion of the SAP notions used.

* F has a size sequence n_k in the natural numbers, with n_k>0 for every natural k and n_k tending to infinity. Monotonicity is not required. Each row has its own `Model n_k`. The generated constructor `Family.mk` simply packages these data and proofs; `size` and `model` are projections.
* A `Graph n` is a Boolean matrix a on `Fin n × Fin n`, constrained by a_ij=a_ji and a_ii=false. `Fin n` means the natural indices strictly below n. The degree of i is the finite sum of 1 over its true adjacencies. Thus these are simple undirected graphs and degree is a natural number.
* A `Model n` packages a Borel measure μ on the finite Cartesian space R^n, a proof μ(R^n)=1, fixed real weights θ_i, a true observed dependency graph G, a known-edge graph R, and natural degree caps d_i. `Model.mk` constructs exactly this structure; `law`, `theta`, and `G` select its fields. R and d impose no condition in T39.
* For y in R^n, the weighted coordinate is x_i(y)=θ_i y_i. `average x` is (sum_i x_i)/n; `betaHat m y` is b(y)=(sum_i θ_i y_i)/n. `expectation m f` is the real Bochner integral of f with respect to μ. `beta m` is β=∫b dμ. `var m f` is ∫(f−∫f dμ)^2 dμ, so write v=∫(b−β)^2 dμ.
* `VariableDependency μ G X` requires, for EVERY pair of finite vertex sets S,T, that if S and T are disjoint and every cross adjacency G_ij for i in S,j in T is false, the random vectors (X_i)_(i in S) and (X_j)_(j in T) are independent under μ in Mathlib's `IndepFun` sense. This means independence of their generated sigma algebras (equivalently factorization of probabilities of Borel rectangle preimages here). The subtype indices in the vectors range precisely over the indicated finite sets. `Dependency m` specializes X_i(y)=y_i. This is independence of entire separated subvectors, not merely zero covariance or pairwise independence.
* `WholeScaling F c1 c2 c3 c4` is the conjunction: all four c's are strictly positive; every row satisfies the preceding dependency property; for every k, μ_k-almost every y satisfies |θ_ki y_i−β_k|≤c1 for every i; every row's vertex degree, cast to R, is ≤c2; n_k v_k tends to c3; and |θ_ki|<c4 for every k,i. There are no cross-row laws, independence conditions, graph embeddings, or equal-individual-mean assumptions. The almost-sure bound centers every coordinate at the single row target β_k.
* `scaledTrue F k` means n_k v_k. `probability m E` means (μ(E)).toReal, the real version of the measure of E.
* `InProbability F T a` means: for every real ε>0, μ_k{|T_k−a_k|>ε}, converted to R, tends to zero. Here T_k=n_k V_k and a_k=n_k v_k.
* `Conservative F V` means: for every real ε>0, μ_k{n_k(v_k−V_k)>ε}, converted to R, tends to zero. This is a one-sided condition after multiplication by sample size.
* `Phi t` is Mathlib's cdf of `gaussianReal 0 1`, the real normal probability law of mean zero and variance one. Thus it is the standard normal probability of (−∞,t]. `normalQuantile α` is the real infimum z_α=inf{t in R : 1−α/2≤Phi(t)}.
* `coverage m V α` is μ{|b−β|≤z_α sqrt(max(V,0))}, converted to R. This is the coverage of the symmetric closed interval with this half-width, explicitly clipping a negative variance estimate to zero.
* `ConservativeCoverage F V` means: for every real α satisfying 0<α<1, 1−α≤liminf_(k→∞) coverage(m_k,V_k,α). The real liminf is the supremum of the eventually valid lower bounds.

For each row, V_k is an arbitrary function R^(n_k)→R. `AEMeasurable (V k) μ_k` means there exists a Borel measurable function g_k with V_k=g_k almost everywhere. It permits every completion-measurable real version on the raw space. No integrability of V is assumed or required to form these coverage probabilities.

### Conclusion

For all data just quantified and satisfying those hypotheses, BOTH of the following hold:

1. If n_k V_k−n_k v_k tends to zero in probability in the rowwise sense above, then, for every real α with 0<α<1, the clipped interval coverage tends to exactly 1−α.
2. If V satisfies the one-sided scaled condition above, then, for every such α, the clipped interval's coverage has limiting inferior at least 1−α.

The two branches have separate antecedents; neither is an unconditional assertion of consistency or conservativeness. No CLT is an extra hypothesis in this statement. The docstring calls the rowwise numerical/dependency conditions Assumption 2, describes the clipping and completed-law measurability, and expressly disclaims observed-graph nesting and sample-size monotonicity.

### Total values and edge cases

* Real division by zero is zero in Lean. Averages would be zero at n=0 because the finite sum is empty and /0=0, but `Family.positive` excludes that case in every use here. Natural-to-real casts of n and degrees are exact; there is no integer subtraction in these definitions.
* The Bochner integral of a nonintegrable function is defined to be zero. This affects the unconditional definitions of expectation, β and variance. In the hypotheses here, weighted coordinates are measurable and a.e. bounded in absolute value by c1+|β_k|, a finite real number even before integrability is established. On a probability space this gives integrability and all their second moments. Their finite averages and squared centered averages are integrable as well. Thus the integral's undefined-integrand default cannot supply the statistical quantities under `WholeScaling`. No raw unweighted moment is used unless it appears through a weight.
* `Measure.real E` uses `ENNReal.toReal`; toReal(∞)=0. Every μ_k is a probability measure, so even its outer measure of any set is at most one and is finite. Thus this default cannot matter. Measures are evaluated on arbitrary sets using outer measure; the a.e. measurable statistics yield completion-measurable coverage/error sets, with their usual completed probabilities.
* `Real.sqrt` is zero on a negative argument. In this theorem its argument is max(V,0), so it is always nonnegative and this extension is not used. V itself may be negative. Its clipping is a substantive stated convention.
* The real `sInf` in z_α is totalized even for an empty or unbounded-below set (the real default is zero). The theorem only uses 0<α<1. For those α the standard normal cdf is continuous, strictly increasing from zero to one, and the defining set is nonempty and bounded below, with a strictly positive finite infimum. Thus the default does not enter.
* Real `liminf` can have a totalized value when the set of eventual lower bounds is empty or unbounded above. Here coverage lies in [0,1]. There are eventual lower bounds and they are bounded above, so its ordinary real limiting inferior exists. All limits run over natural `atTop`, a nontrivial filter.
* Vertex sets S or T may be empty; the associated random vector is constant on a singleton product and its independence condition is harmless. n itself is never zero. There is no log, rpow, supremum over an optimization problem, partial-function default, or choice of an undefined inverse in this closure.
* `WholeScaling._proof_1` is the generated proof of the outer-measure-class instance for each row law; `normalQuantile._proof_1` proves that the numeral 2 is at least two. The printed proof terms introduce no additional hypotheses or defaults.

## SAP.P011c.T40

### Objects, hypotheses, and quantifier order

The theorem asserts `T40WholeStatement` (`Defs/WholeW1.lean:74–87`). Quantifiers and implications, in order: every family F and four real c's; `WholeScaling F c1 c2 c3 c4` implies; rowwise homoskedasticity implies; `Valid F` implies; every graph selection A_k(y); its pointwise maximizing property implies the conjunction of measurability, pointwise nonnegativity, and two asymptotic coverage assertions.

The complete meanings of Family, Model, Graph, degree, weighted coordinates x_i=θ_i y_i, the average b(y), β, variance v, expectation, dependency, `WholeScaling`, `probability`, `Phi`, `normalQuantile`, and `scaledTrue` are exactly the expansions given above for T39. In particular n_k is always positive and tends to infinity, μ_k is a Borel probability law on R^(n_k), the common-target coordinate bound is |θ_ki y_i−β_k|≤c1 a.e., degrees of G are uniformly bounded by c2, n_k v_k→c3>0, and weights satisfy |θ_ki|<c4. Graphs and sizes need not be nested or monotone.

The additional SAP definitions expand as follows.

* `adjacency A` is the real matrix a_ij=1 if the Boolean adjacency is true and 0 otherwise. Its diagonal is zero and it is symmetric.
* `covariance m i j` is ∫(x_i−∫x_i dμ)(x_j−∫x_j dμ)dμ. `Homoskedastic m` says these diagonal covariance entries are equal for every i,j. It requires equal weighted variances and does not require equal weighted means.
* `Compatible R d A` means every known edge R_ij=true is also an edge of A, and degree_A(i)≤d_i for every vertex. `Valid F` means the true observed graph G_k is compatible with its row's R_k,d_k, for every k. This supplies an actual feasible graph in every row.
* For x in R^n, `centered x i`=x_i−(sum_j x_j)/n, and `sampleVariance x`=s²(x)=(sum_i (x_i−average(x))²)/n. The divisor is n, not n−1.
* `V2 A x`=s²(x)/n times (1+(sum_i sum_j a_ij)/n). The double adjacency sum is over ordered pairs and equals the sum of all vertex degrees.
* `truncatedDegree d i`=min(d_i,n−1) as a natural number. `V2prime d x`=s²(x)/n times (1+(sum_i min(d_i,n−1))/n), with these natural counts cast to real numbers.
* `Maximizes R d f A` means A is compatible and, for EVERY graph B compatible with R,d, f(B)≤f(A). Ties are all included. No supremum or default maximizer is used.
* `printedCoverage m V α`=μ{V(y)≥0 AND |b(y)−β|≤z_α sqrt(V(y))}, converted to R. A negative estimate explicitly counts as uncovered.
* `PrintedConservativeCoverage F V` says that for EVERY real α with 0<α<1, 1−α is at most the real liminf of these printed-coverage probabilities.

The selector is quantified as A: for every k, a function from R^(n_k) to Graph(n_k). For EVERY k and EVERY y (not just almost every y), its chosen graph must maximize B↦V2(B,weighted(m_k,y)) over the compatible graphs. No measurability of this graph-valued selector is assumed. Supplied natural degree caps d_ki have no uniform bound as k varies.

### Conclusion

For all the preceding data and hypotheses:

1. For every k, BOTH y↦V2(A_k(y),weighted(m_k,y)) and y↦V2prime(d_k,weighted(m_k,y)) are Borel measurable real functions.
2. For every k and EVERY y, BOTH of these variance estimates are nonnegative.
3. For each of the two sequences of estimates separately and for every 0<α<1, its printed-interval coverage has liminf at least 1−α.

The theorem does not assert exact limiting coverage or consistency of either estimator. The docstring agrees with these four conjuncts and says arbitrary maximizing selectors, unrestricted supplied caps, and unequal weighted means are allowed.

### Total values and edge cases

* All T39 conventions concerning real integrals, finite measures and toReal, quantile infima, and bounded coverage liminf apply here, with the same protections. Covariance integrands are integrable because the weighted coordinates have bounded second moments under `WholeScaling`.
* Every division in the sample variance, V2 and V2prime has denominator n_k or a product of such positive real numbers. Their n=0 totalizations are never used.
* The subtraction n−1 in `truncatedDegree` is truncated natural subtraction. Since n_k≥1, it equals the intended maximum simple-graph degree. At n=1 it is zero and both formulas remain ordinary well-defined quantities. Supplied degree caps are natural numbers, so no negative-cap interpretation is possible.
* All other subtractions in centered coordinates, covariance, probabilities and bounds are real subtractions. No hidden truncation affects them.
* `printedCoverage` uses the total real square root, but also explicitly requires V≥0. Moreover this theorem concludes V≥0 at EVERY outcome, so the square-root extension to negative arguments has no bearing on its intervals.
* The class of compatible graphs is nonempty since it contains G_k by Valid. It is finite, so there is a pointwise maximizer. At s²=0 every compatible graph can tie, but each gives the same zero objective. In general all maximizing selectors have the same maximum value, allowing the value to be Borel measurable even if the selector is not. No `sSup` of an empty or unbounded feasible set is used.
* The families have nonempty vertex types. Empty subsets in the dependency definition are harmless as in T39. There is no log, rpow, matrix inverse, or partial-function default in this closure. The generated WholeScaling and normalQuantile proof dependencies are the instance/numeral proofs described above.

## SAP.P011c.T41

### Objects, definitions, and full statement

The theorem asserts `T41WholeStatement` (`Defs/WholeW1.lean:97–109`), a conjunction of THREE independent universally quantified assertions. It involves no probability spaces, random variables, expectations, or asymptotic sequences.

Here n ranges over ALL natural numbers, including zero. A `Graph n` is a symmetric Boolean matrix on `Fin n` with false diagonal. `adjacency R` is its real 0/1 matrix a, and `degree R i` is the natural number d_R(i)=sum_j 1_(R_ij=true). These sums count ordered vertex incidences; each edge contributes one to each of its two endpoint degrees.

`oracleMatrix R`=I+a, where 1 in the matrix type is the identity matrix. For a natural-valued function h on Fin n, `recruitmentCapacityMatrix R h` is

    M = I + a + diag((h_i : R) − (d_R(i) : R)).

Both casts occur BEFORE subtraction: this is real subtraction, with possible negative diagonal corrections. `quadratic M x` is sum_i sum_j M_ij x_i x_j over all ordered pairs, exactly the real quadratic form x^T M x. `PSD M` requires BOTH symmetry M_ij=M_ji for all i,j AND nonnegativity of this quadratic form for EVERY real vector x. It is not merely entrywise positivity or a statement for one vector.

The first conjunct quantifies EVERY n, EVERY R:Graph n, EVERY h:Fin n→N, and concludes the matrix identity

    M = (a + diag(d_R)) + diag(1 + h_i − 2 d_R(i)).

The displayed casts to real numbers are understood in this formula. The first summand is the signless Laplacian. This identity has NO capacity hypothesis.

The second conjunct separately quantifies EVERY n,R,h. If for EVERY i the REAL inequality 2 d_R(i)−1≤h_i holds, then BOTH (a) M is PSD and (b) if n>0, for EVERY δ:Fin n→R one has 0≤(δ^T M δ)/(n:R). The capacity hypothesis does not use truncated natural subtraction. Positivity of n is required only in part (b), not for PSD.

For the third conjunct, `Compatible R d A` requires R's edges to be in A and every degree of A to be ≤ the supplied natural cap d_i. `Maximizes R d f A` means this compatibility AND f(B)≤f(A) for EVERY compatible B. The third conjunct quantifies EVERY n, R:Graph n, d:Fin n→N, f:Graph n→R, c:R, and A:Graph n, in that order, and concludes

    Maximizes R d (B ↦ f(B)+c) A  iff  Maximizes R d f A.

The same real c is added for all B. There is no restriction on f, sign of c, feasibility of A, or sample-size positivity. In particular this statement preserves all ties and uses the same feasible set on both sides. It does not itself specify which statistical diagonal correction to add or compute an optimizer.

The docstring describes an accepted repair, a decomposition, the sufficient capacity condition, normalized quadratic nonnegativity, and preservation of maximizers by a graph-independent constant. These assertions have exactly the quantifier separation above: the identity and maximizer equivalence are unconditional, whereas PSD is conditional on the capacity inequality.

### Total values and edge cases

* At n=0, Fin n is empty. There is a unique graph/matrix/vector/function of each indicated shape. Degree and quadratic sums are empty sums (zero), matrix equality and symmetry are componentwise vacuous, and all quadratic forms are zero. The capacity inequalities are vacuous and PSD is true. The normalizing expression would be 0/0=0 in Lean, but its conclusion is guarded by 0<n, which is false at zero. Thus no interpretation of an actual division by zero is asserted.
* The real subtraction h_i−d_R(i) in the capacity matrix and 2d_R(i)−1 in the capacity condition do not use natural truncation. The hypothesis at an isolated vertex is −1≤h_i, which is automatically true for a natural h_i; this corresponds to the diagonal remainder 1+h_i≥0. All casts are exact.
* Maximization is a direct universal comparison, not an `sSup` or an arbitrary choice. If no compatible graph exists, both sides of the equivalence are false. This special case does not exhaust the theorem: compatible graphs and maximizers readily exist, including at size zero and with R empty and caps zero.
* The matrix numeral 1 denotes I, not an all-ones matrix. There are no logarithms, square roots, rpow, means, integrals, toReal conversions, liminf/limsup, partial functions or other totalized analytical operations in this closure.
* `T41WholeStatement._proof_1` is only the generated proof that numeral 2 is at least two. The remaining closure entries (`Compatible`, `Graph`, `Maximizes`, `PSD`, adjacency, degree, oracleMatrix, quadratic, recruitmentCapacityMatrix) have all been explicitly expanded above.
