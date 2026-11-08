# Blind reading

This file was written before opening `claims.json`, `record.json`, `earlier.json`, or `architect-report.md`. Sources read: the five target docstrings in `SAP/P044/Challenge/Part1.lean`, all source declarations listed in their closures, and the elaborated output in `scratch/ClosurePrint.out`. The latter prints all 91 distinct closure declarations, including generated proof auxiliaries, recursors, matchers, instances, and structure projections/constructors. No target proof was used to interpret its statement.

The generated numeric auxiliaries establish facts such as `AtLeastTwo 16` and `NeZero 8`; they do not impose additional hypotheses. The Exposure constructors, recursor, case eliminator, constructor indices, decidable equality and four-element Fintype implement an ordinary four-element enumeration. The generated matchers perform exhaustive case analysis on that enumeration. `FiniteDesign.mk` requires a real mass function with nonnegative entries summing to one; its `mass` projection returns that function. These are genuine constructions, not new probability assumptions.

## SAP.P044.T6

The theorem is the conjunction below, with no global hypotheses. Each universal clause has its own binders and hypotheses; in particular the network assumptions in one clause do not scope over the others.

Use the following completely expanded mathematical notation. Vertices are `Fin N` (integers 0 through N−1). A network is an arbitrary Boolean array A(i,j); no symmetry is built into its type. Its degree is d_i=Σ_j 1[A(i,j)=true]. Its two-walk count is q_i=|{j : j≠i and there exists k with A(i,k)=A(k,j)=true}|: it counts distinct endpoints of length-two walks, excludes i, and does not exclude immediate neighbors. Put a_i=d_i+q_i+d_i q_i, first in the natural numbers and then cast to the reals when needed. For any real vector B, the four outcomes are Y_i(00)=B_i, Y_i(11)=2B_i, Y_i(10)=3B_i/2, Y_i(01)=5B_i/4. The contrast between labels u,v is N⁻¹Σ_i(Y_i(u)−Y_i(v)). Let μ be the product of the Gaussian probability measures N(0,1) and N(1,1/16), whose second parameters are variances, not standard deviations. Write H=√(2/π). For real a, F_a(g,e)=a|g|+e. The population probability measure is the finite product μ^N on vectors x_i=(g_i,e_i), so all pairs are independent across i and g_i,e_i are independent within each pair. Its baseline vector is B_i(x)=a_i|g_i|+e_i. The comparison baseline law is the pushforward of N(0,1) by absolute value.

The asserted clauses are:

1. For every natural N, every B:Fin N→ℝ, and every i:Fin N, all four displayed outcome formulas hold.
2. For every real a≥0, ∫F_a dμ=aH+1 and Var_μ(F_a)=a²(1−2/π)+1/16. Here variance is Mathlib's extended integral of the squared centered norm, converted to a real number.
3. Under N(0,1), ∫|g|=H and ∫|g|²=1.
4. For every real a, F_a is in L²(μ), meaning it is almost everywhere strongly measurable and has finite L² seminorm.
5. For every N>0 and every B:Fin N→ℝ, the contrasts of 11,10,01 against 00 are respectively the arithmetic mean of B, half that mean, and a quarter of that mean.
6. For the fixed three-vector B=(−5/8,9,21/4), those three contrasts are 109/24,109/48,109/96, and the mean of that vector is 109/24. This clause does not itself identify B with a draw of a particular network generator.
7. For every N>0 and Boolean A with A(i,i)=false for every i, the μ^N expectation of the 11-versus-00 contrast of the generated baseline is 1+H(Σ_i a_i/N).
8. For every N>0 and A with false diagonal and d_i≥1 for every i, the same expectation identity holds, the expectation is at least 1+H, and H<1. Neither of these network clauses requires symmetry.
9. For every type Ω with a measurable space, every N>0, every probability measure P on Ω, and every B:Ω→Fin N→ℝ such that each coordinate is almost everywhere measurable and its pushforward under P is the absolute-standard-normal law, the expectation of the 11-versus-00 contrast is H, and H<1. Coordinate independence is not assumed in this comparison clause.
10. For every N>0 and every Boolean A (without even a diagonal hypothesis), the generated contrast in clause 7 is Bochner integrable under μ^N.
11. For every measurable Ω, N>0, probability measure P and coordinatewise half-normal B as in clause 9, the comparison contrast is Bochner integrable under P.

Junk-value audit: real division is total with x/0=0, but all population means/contrasts here have N>0; the first, pointwise clause needs no division by N and is empty of vertices when N=0. All literal rational denominators are positive. Gaussian variances 1 and 1/16 are positive; the Gaussian definition's zero-variance Dirac branch is not used. Real.sqrt is the nonnegative square root (and is zero for nonpositive inputs); its only input is 2/π>0. Bochner integrals default to zero for nonintegrable functions; clauses 4,10,11 and the finite moments of the Gaussian laws prevent this from affecting these assertions. Variance converts ∞ to zero via ENNReal.toReal, but the L² assertion prevents infinite variance here. Pushforwards have a zero-measure convention for unsuitable measurable maps; absolute value is continuous, and the HasLaw hypotheses include a.e. measurability. Finite product measures have no infinite-index issue. Degree and two-walk counts use natural addition/multiplication without subtraction and have exact real casts. There are no logs, rpow, partial-function defaults, suprema/infima, limsups/liminfs, or unbounded extrema.

The docstring describes corrected baseline moments, multiplier effects, a three-coordinate calculation, and the population expectation/scale comparison, with integrability of the displayed averages.

## SAP.P044.T7

There are no hypotheses or free parameters: this is a conjunction of explicit finite calculations. Both vertices i and bank rows r range over Fin 8. A(i,j) is true precisely when (i+1) mod 8=j or (j+1) mod 8=i. The assignment in row r treats vertex i precisely when (i+r) mod 8 belongs to {0,1,3}. Thus r=0 treats vertices 0,1,3. Its treated-peer count is Σ_j 1[A(i,j) and z_r(j)]. Its exposure f(r,i) has first bit z_r(i) and second bit the indicator that this count is positive. The four labels are 11,10,01,00.

Define c_i(a)=|{r:f(r,i)=a}| and c_ij(a,b)=|{r:f(r,i)=a and f(r,j)=b}|. Every expectation in this statement is the exact rational sum (1/8)Σ_r of the displayed statistic. The exact marginal is p_i(a)=c_i(a)/8; the exact joint is c_ij(a,b)/8. The smoothed marginal is w_i(a)=(c_i(a)+1)/9. The returned joint is v_ij(a,b)=(c_ij(a,b)+1[i=j])/9 when a=b, and c_ij(a,b)/8 otherwise. Outcomes are fixed across vertices: Y_i(11)=2, Y_i(10)=3/2, Y_i(01)=5/4, Y_i(00)=1. For weights v_i(a), the reported mean in row r is (1/8)Σ_i 1[f(r,i)=a]Y_i(a)/v_i(a); the reported contrast subtracts two such means. The target contrast is (1/8)Σ_i(Y_i(a)−Y_i(b)). These formulas unfold every estimator used below.

The full conjunction, including the embedded T7Statement, asserts:

1. Every vertex has a neighbor, and the eight assignments are pairwise distinct (injective as a map of rows).
2. For every i and a, the counts c_i(a), ordered 11,10,01,00, are (2,1,3,2), the exact marginals are (1/4,1/8,3/8,1/4), and the smoothed weights are (1/3,2/9,4/9,1/3). All exact marginals are positive. For every i the smoothed weights sum to 4/3.
3. For every row r and a, the smoothed reported means are (3/2,27/32,135/128,3/4); the exact-weight reported means equal the corresponding Y_0(a).
4. For vertices 0,1 and first label 11, the four joint counts indexed by the second label 11,10,01,00 are (1,0,1,0). The returned joint entries are (1/9,0,1/8,0), whose sum is 17/72. The returned marginal w_0(11)=1/3 differs from that sum. The exact joint entries are (1/8,0,1/8,0), whose sum is 1/4; also 1/8+1/8=1/4.
5. The expected smoothed contrast 11−00 is 3/4 while its target is 1.
6. Every row treats three vertices. In every row the numbers of vertices at each exposure are (2,1,3,2). This row-count assertion appears twice in the conjunction.
7. For every row, the smoothed contrasts of 11,10,01 against 00 are 3/4,3/32,39/128. Their respective differences from the targets are −1/4,−13/32,7/128. The targets of 10−00 and 01−00 are 1/2 and 1/4.
8. For every row, exact-weight contrasts are 1,1/2,1/4.
9. The exposure vector at row 0 is (11,11,01,10,01,00,00,01).
10. For every a, the arithmetic mean of the outcome vector equals Y_0(a).

The bank is a deterministic exhaustive list for the uniform eight-profile design in the expectations. No claim of independent random bank rows appears in this statement.

Junk-value audit: arithmetic is in ℚ. The denominators 8 and 9 and all relevant marginal/smoothed weights are positive; the theorem explicitly states marginal positivity, so inverse weights are never division by zero. The two branches of the returned-joint formula have denominators 9 and 8, including for zero joint counts, which therefore produce legitimate zeros. Counts are exact natural cardinalities, cast without loss into ℚ. Modular arithmetic has positive modulus 8. Fin 8 and the exposure enumeration are nonempty. Array literals are length-indexed total functions with no out-of-range/default access. No integrals, ∞ conversions, truncated subtraction, extrema, limits, roots, logs, or partial functions occur.

The docstring describes this bank's calculations, biases, and explicit joint/marginal inconsistency, and assumes usual measure-theoretic conditions for the finite laws.

## SAP.P044.T8

This theorem conjoins two independently quantified statements.

First, for every pair of natural numbers R,N, every finite type D with decidable equality, R>0, N>0, every array f:Fin R→Fin N→D, every pair of real arrays y,w:Fin N→D→ℝ, every a:D, and the hypothesis w_i(a)>0 for all i, the following hold. Let c_i(a)=|{r:f(r,i)=a}|, c_ij(a,b)=|{r:f(r,i)=a and f(r,j)=b}|, p_i(a)=Σ_r 1[f(r,i)=a]/R, and p_ij(a,b)=Σ_r 1[f(r,i)=a and f(r,j)=b]/R. The exact expectation of a row statistic T is (1/R)Σ_r T(r); the mean statistic with an array of weights v is (1/N)Σ_i 1[f(r,i)=a]y_i(a)/v_i(a); let s_i(b)=(c_i(b)+1)/(R+1).

1. For every i,j,b, p_i(a)=c_i(a)/R and p_ij(a,b)=c_ij(a,b)/R.
2. The expectation of the fixed-w mean statistic equals (1/N)Σ_i y_i(a)p_i(a)/w_i(a).
3. If all p_i(a)>0, its exact-p counterpart has expectation (1/N)Σ_i y_i(a).
4. The expectation of the s-weight mean minus (1/N)Σ_i y_i(a) is (1/N)Σ_i y_i(a)(c_i(a)−R)/(R(c_i(a)+1)).
5. For every i, (c_i(a)/R)/s_i(a)−1=(c_i(a)−R)/(R(c_i(a)+1)); if c_i(a)<R, this value is negative. This is a multiplier statement, not a claim of negative total bias for arbitrary signed outcomes.
6. If |D|≥2, for every i the sum Σ_b s_i(b)=(R+|D|)/(R+1)>1.

Second, for every type Ω with a measurable space, probability measure μ on Ω, natural number R (including zero), real p∈[0,1], functions D:Ω→Bool and C:Ω→ℕ, with D a.e. measurable of Bernoulli law assigning p to true and 1−p to false, C a.e. measurable of binomial(R,p) law, D and C independent under μ, and 0<p<1, the following hold. The real random variable 1[D=true]/((C+1)/(R+1)) is integrable and its integral is 1−(1−p)^(R+1), which is strictly less than one. A binomial law is the distribution of the number of successes among R independent Bernoulli(p) trials, equivalently mass choose(R,c)p^c(1−p)^(R−c) on c=0,…,R. The formal assumptions specify the count's law and its independence from D; they do not explicitly construct the underlying bank trials.

Junk-value audit: division is in ℝ. R,N are positive in the first part. w_i(a)>0 excludes zero fixed denominators. p-weights may be zero at other labels, but only label a is used in the unbiasedness clause, guarded by its own positivity hypothesis. Smoothed denominators and numerators are positive since R,c are naturals; thus zero counts are meaningful and do not create zero inverses. All differences c_i(a)−R in bias formulas are real differences after casts, not truncated natural subtraction. In the second part, R may be zero, but C+1,R+1 remain positive and the expectation is then p; no degeneracy is hidden. D as an input a:D and R>0,N>0 with f make empty D impossible in the first part; the normalization clause explicitly guards |D|≥2. The count variable's ℕ type makes negative counts impossible and binomial law confines it almost surely to 0,…,R. The Bochner integral's zero convention is excluded by the explicit integrability conclusion; the HasLaw hypotheses include a.e. measurability and independence is explicit. Natural powers have no out-of-domain convention. No ∞ conversions, roots, logs, extrema, limits, or partial functions occur.

The docstring describes exhaustive probabilities and finite-expectation formulas together with the independent with-replacement binomial calculation.

## SAP.P044.T9

The theorem is a conjunction with no global hypotheses. For natural N, a treatment profile is a Boolean function on Fin N, a network A is a Boolean N×N array, and an outcome schedule y is Fin N→(Fin N→Bool)→ℝ. For vertex i, an other-coordinate profile u has domain {j:Fin N | j≠i}. Inserting own treatment a means the function which is a at i and u(j) elsewhere. No-interference means: for every i, every Boolean a, and every pair of other-coordinate profiles u,v, the two outcomes at i after inserting a agree. Interference means there exist i,a,u,v for which they disagree.

The embedded T9Statement asserts:

1. For every N and every y, interference is equivalent to the negation of no-interference.
2. For every N and y, no-interference is equivalent to: for all i and all complete profiles z,z′, equality z_i=z′_i implies y_i(z)=y_i(z′).
3. For every N,A,z,i, the natural sum Σ_j 1[A(i,j)=true and z_j=true] equals the cardinality of the corresponding set of vertices.
4. For every N,A,i with A(i,i)=false and profiles z,z′ agreeing at every j≠i, those counts agree.
5. For every N,A,z,i, exposure 11 is equivalent to z_i=true and the count positive; 10 to z_i=true and count zero; 01 to z_i=false and count positive; 00 to z_i=false and count zero.
6. For every N,i,z, inserting z_i into the restriction of z to all other vertices reconstructs z.

The additional clauses use an ordered n-coordinate vector for the other units when the population has n+1 vertices. The Mathlib order isomorphism `finSuccAboveOrderIso i` sends Fin n to the complement of i in Fin(n+1) in increasing order. Ordered deletion restricts z along this map; ordered insertion uses its inverse at every j≠i and inserts a at i. Ordered no-interference and interference use these insertions with, respectively, universal equality and existential inequality as above.

7. For every n,i:Fin(n+1),z, ordered insertion of z_i into the ordered deletion reconstructs z.
8. For every n and schedule y on n+1 vertices, ordered no-interference iff no-interference; ordered interference iff interference; ordered interference iff not ordered no-interference; ordered no-interference iff invariance under all profile changes preserving z_i.
9. Define an r×c and s×t pair of matrix shapes to be composable iff c=s. For every natural N, shapes (1,N) and (N,1) are composable; shapes (1,N) and (1,N) are composable iff N=1; if N>1 the latter are not composable.
10. Map a Boolean b to the natural number bit(b)=1 if true and 0 otherwise. For every N,A,z,i, the sole entry of the 1×N adjacency-row times the N×1 treatment-column over ℕ equals Σ_j bit(A(i,j))bit(z_j), and this equals the treated-peer count.
11. For every N,A,z,i and every label d, the corresponding product predicate is equivalent to exposure=d. The product predicates, in label order 11,10,01,00, are bit(z_i)1[count>0]=1; bit(z_i)1[count=0]=1; (1−bit(z_i))1[count>0]=1; (1−bit(z_i))1[count=0]=1. Exactly one label satisfies its predicate. The exposure is also restated as the nested if selecting the two Boolean bits.

Junk-value audit: the natural subtraction 1−bit(z_i) is applied only to 0 or 1 and agrees with ordinary subtraction; it does not truncate a negative number. No subtraction of N−1 is used to model dimensions: n+1 handles the positive-population cases, and n=0 gives an empty other-unit vector with a genuine order isomorphism. For N=0 the original universal clauses about vertices are empty, no-interference is true and interference false, as their definitions require; there is no claimed nonempty witness for interference on that population. The ordered insertion inverse is evaluated only in the complement of i and has no partial/default branch. Matrix composability is a dimension equality, and no ill-typed row-times-row product is assigned a numerical junk value. All other matrices and finite sums are total and well typed. No divisions, integrals, logs, roots, ∞ conversions, limits, or extrema occur.

The docstring describes these logical and dimensional corrections, the unique exposure labeling, the own-treatment invariance on a zero diagonal, and the absence of symmetry/no-isolate requirements.

## SAP.P044.T10

This is a conjunction of four separately quantified statements. A community assignment c takes vertices to an arbitrary type C; the clauses that test equality require decidable equality on C. All graph objects below are Mathlib SimpleGraphs, hence undirected and loopless. Their edge finset consists of unordered pairs (Sym2), each edge counted once. The within-community edge finset filters the edges by existence of endpoints i,j representing the pair and satisfying c(i)=c(j).

1. For every natural N, type C with decidable equality, real s, real vector t, c:Fin N→C and i,j:Fin N, if c(i)≠c(j), then s t_i t_j 1[c(i)=c(j)]=0. There are no bounds on s,t and no assertion that this formula is a probability for arbitrary inputs.
2. For every finite type Ω, type C with decidable equality, natural N, real probability mass P_ω≥0 with Σ_ωP_ω=1, family of decidable simple graphs G_ω on Fin N, and family of assignments c_ω, assume for every i,j that Σ_ω 1[G_ω.Adj(i,j) and c_ω(i)≠c_ω(j)]P_ω=0. Then for every ω with P_ω>0 and every edge i,j of G_ω, c_ω(i)=c_ω(j). This is a support statement, not a construction of a graph distribution.
3. For every N>0, type C, decidable simple graph G on Fin N and c:Fin N→C, assume every vertex has positive natural degree and every adjacent pair has equal community. Then Σ_i degree_G(i)=2|E(G)|; N≤2|E(G)|; |E(G)|>0; |E_within(G,c)|=|E(G)|; their real ratio is one; and that ratio minus 7/10 is 3/10.
4. For every finite Ω, type C, N>0, probability mass P as above, decidable simple-graph family G_ω, and assignments c_ω, assume every vertex of every G_ω has positive degree and all edges of every G_ω are within communities. These hypotheses quantify over all ω, including zero-mass ones. Then Σ_ωP_ω(|E_within(G_ω,c_ω)|/|E(G_ω)|)=1; (Σ_ωP_ω|E_within(G_ω,c_ω)|)/(Σ_ωP_ω|E(G_ω)|)=1; and each of those two ratios minus 7/10 equals 3/10. Thus both expectation of a ratio and ratio of expectations are included.

Junk-value audit: all expectations are finite sums of reals and so have no nonintegrability convention. FiniteDesign cannot exist on empty Ω because its empty sum would have to be one. N>0 plus positive degree in clauses 3,4 forces a nonempty edge finset (and effectively N≥2); thus every ratio has positive denominator. The expected edge count in clause 4 is positive because P is nonnegative with total mass one and every graph has at least one edge. Zero-mass graphs do not cause a default value since they too satisfy the stated degree assumption. Clause 2 needs no degree hypothesis or ratio, and can have empty edge sets. Natural degrees/cardinalities cast exactly to ℝ; subtraction of 7/10 is real. Quotient representatives of unordered edges are handled by an existential predicate invariant under swapping endpoints, not a default endpoint selector. There are no Bochner integrals, ∞ conversions, natural truncated subtractions, roots, logs, limits, extrema, or partial functions.

The docstring explicitly restricts the consequences to finite graph laws satisfying zero crossing marginals or accepted-graph no-isolate/no-crossing conditions. It explicitly disclaims constructing a generator law or deriving those law hypotheses from source code and its rejection loop.
