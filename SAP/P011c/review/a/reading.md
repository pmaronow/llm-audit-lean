# Blind reading of the Challenge statements

Saved before opening `claims.json` or `record.json`. This reading uses the theorem types, all four Defs files, and the Mathlib definitions they invoke. Challenge docstrings are not used to supply unstated hypotheses or conclusions.

## Common objects and conventions

Write `[n] = {0,...,n-1}` (`Fin n`). A `Graph n` is exactly a symmetric Boolean adjacency array on `[n]` with false diagonal: a labelled finite simple undirected graph. Write `a_A(i,j)` for its real 0/1 adjacency matrix and `deg_A(i)` for its natural-number degree. All sums below include every indicated vertex; double sums are over **ordered** pairs, counting each undirected edge twice. Matrix `1` is the identity matrix, not the all-ones matrix.

For graphs `R,A` and natural caps `d_i`, compatibility means both `E(R) ⊆ E(A)` and `deg_A(i) ≤ d_i` for every vertex. `Maximizes(R,d,f,A)` means that A itself is compatible and that, for **every** compatible graph B on the same labelled vertex set, `f(B) ≤ f(A)`. It is not a hypothesis merely that some maximum exists.

For a real vector x, put

* `xbar = (Σ_i x_i)/n`, `z_i = x_i-xbar`, and `s²(x) = (Σ_i z_i²)/n` (denominator n, not n−1).
* `Q(M,x) = Σ_i Σ_j M_ij x_i x_j`.
* `V1(A,x) = [Σ_i z_i² + Σ_ij a_A(i,j)z_i z_j]/n² = Q(I+a_A,z)/n²`.
* `V2(A,x) = [s²(x)/n][1+(Σ_ij a_A(i,j))/n]`.
* `V2prime(d,x) = [s²(x)/n][1+(Σ_i min(d_i,n−1))/n]`.
* `g(m) = 1+(Σ_ij a_G(i,j))/n` for the model's true graph G.

The `n−1` inside `min` is natural subtraction (zero at n=0). Real division is total, with division by zero zero. These conventions exist in the definitions, but every Family row has positive n, and T29 explicitly requires positive n. No positive semidefiniteness or nonnegativity of V1 is built in.

A `Model n` consists of a probability measure μ on the real coordinate space `ℝ^[n]`, a deterministic real weight vector θ, graphs G and R, and natural caps d. The measurable space on the coordinate space is the product of the Borel σ-algebras on ℝ. The Model structure itself imposes **no** compatibility, dependency, moment, or homoskedasticity condition. For a raw outcome y set `X_i(y)=θ_i y_i`, `hatβ(y)=Σ_i X_i(y)/n`, and `β=E_μ hatβ`.

`E_μ` is Mathlib's real Bochner integral. Without integrability it is defined to be zero; it is not an extended-real expectation. `var(m,f)=E_μ[(f−E_μ f)²]`. The matrix `covariance(m)` has entries `E_μ[(X_i−E_μ X_i)(X_j−E_μ X_j)]`. Separately, `covOf(m,f,g)=E_μ[fg]−E_μ[f]E_μ[g]`. Under the explicit finite-moment hypotheses these are ordinary variances/covariances.

`Dependency(m)` says: for **every ordered pair** of finite vertex subsets S,T, if S and T are disjoint and there is no G-edge between any i∈S and j∈T, the random vectors `(y_i)_{i∈S}` and `(y_j)_{j∈T}` are independent. `IndepFun` means independence of their generated σ-algebras, equivalently product probabilities for all measurable preimages. This is independence of the vectors, not just pairwise uncorrelatedness. `Homoskedastic(m)` means `Var_μ(X_i)=Var_μ(X_j)` for **all** vertices i,j; means may differ.

A `Family F` consists of sizes `n_k>0` for all k∈ℕ with `n_k→∞`, and a separate Model `m_k` at every k. Define `S(F,c1,c2,c3,c4)` to be the following full expansion of `Scaling`, with constants fixed across all rows:

1. `n_k` is nondecreasing; for every k there is an injection `e_k:[n_k]→[n_(k+1)]` preserving **all** G-adjacencies (an induced graph embedding).
2. All four real constants c1,c2,c3,c4 are strictly positive.
3. `Dependency(m_k)` for every k.
4. For every k, for μ_k-almost every y, **all** vertices i satisfy `|X_ki(y)−β_k| ≤ c1`. The centering is the scalar row-average expectation β_k, not `E X_ki`. This gives finite second moments of the weighted coordinates; it does not require finite moments of unweighted y_i with θ_i=0.
5. For every k and vertex i, `deg_(G_k)(i) ≤ c2` as a real inequality.
6. `n_k Var_(μ_k)(hatβ_k) → c3`.
7. For every k and i, `|θ_ki| < c4` (strict).

There is no consistency requirement on the laws, means, weights, R, or d between rows. The embeddings in (1) need only exist; they need not be a chosen coherent family. `Valid(F)` means that G_k is compatible with `(R_k,d_k)` for every k, as defined above. It imposes no uniform bound on the supplied caps d.

For a row event E, `P_k(E)=μ_k.real(E)=(μ_k(E)).toReal`. A probability measure makes this finite and in [0,1] for every set; for a nonmeasurable set this is the measure's outer-measure value, not an additional measurability assumption. Define:

* `IP(F,T,a)` means: **for every** real ε>0, `P_k(|T_k(y)−a_k|>ε)→0`.
* `Cons(F,V)` means: **for every** real ε>0, `P_k(n_k[Var(hatβ_k)−V_k(y)]>ε)→0`.
* `v_k=n_k Var(hatβ_k)` and `O_k(y)=n_k V1(G_k,X_k(y))`.

Let `Φ(t)` be the cdf of Mathlib's `gaussianReal 0 1` (mean zero, **variance** one). Let `q_α=inf{t∈ℝ:1−α/2≤Φ(t)}`. All coverage assertions quantify only over 0<α<1, where this is the usual finite positive normal critical value. Define

* `C_k(V,α)=P_k(|hatβ_k−β_k|≤q_α sqrt(max(V_k,0)))`.
* `Cprint_k(V,α)=P_k(V_k≥0 and |hatβ_k−β_k|≤q_α sqrt(V_k))`.
* `CC(F,V)` means: **for every** α with 0<α<1, `1−α≤liminf_k C_k(V,α)`.
* `PCC(F,V)` means the same inequality with Cprint.

`Real.sqrt` itself returns zero on negative inputs. Cprint expressly excludes those inputs; C clips them and counts equality at a zero radius. All liminf sequences here lie in [0,1], so Mathlib's conditionally complete real `Filter.liminf` has the ordinary meaning; it is the supremum of eventual lower bounds. `Tendsto ... atTop (𝓝 a)` is the ordinary sequential limit as k→∞. `∀ᶠ k in atTop` means for all sufficiently large k.

For a real `n×p` matrix D and b∈ℝ^p, `MeanModel(m,D,b)` means that **every raw coordinate** y_i is integrable under μ and `E y_i=(Db)_i` for every i. Define `ols(D,y)=(DᵀD)⁻¹Dᵀy` and `olsTheta(D)=n(DᵀD)⁻¹Dᵀ`. The inverse is Mathlib's adjugate/determinant inverse (zero when singular); every statistical assertion using it assumes the Gram determinant is nonzero.

Finally, `PSD(M)` means symmetry plus `Q(M,x)≥0` for **every** real vector x. For a graph R and natural h define `K(R,h)=I+a_R+diag(h_i−deg_R(i))`, with subtraction **in ℝ**, including when h_i<deg_R(i).

## Individual theorem readings and quantifier order

### SAP.P011c.T29

This is a conjunction of two separately universal assertions.

First, for **every** pair of natural numbers n,p, if n>0, then for **every** Model m of size n, every real n×p matrix D, and every real p-vector b, if `det(DᵀD)≠0` and `MeanModel(m,D,b)`, then both:

* for every coefficient j∈[p] and **every** raw vector y∈ℝ^n, `ols(D,y)_j=(Σ_i olsTheta(D)_(j,i)y_i)/n`;
* for every j∈[p], `E_μ[ols(D,y)_j]=b_j`.

Second, for **every** natural n, if n>0, then for **every** Model m of size n, if every raw coordinate y_i belongs to L²(μ),

`Var_μ(hatβ)=[Σ_i Σ_j θ_i θ_j (E[y_i y_j]−E[y_i]E[y_j])]/n²`.

There are no graph, degree, independence, homoskedasticity, or asymptotic assumptions in either conjunct. The two Model quantifiers are independent. p=0 is allowed in the first conjunct; its coordinate conclusions then quantify over an empty set, but all positive p are also required.

### SAP.P011c.T31

`NOT [for every Family F, for every real c1,c2,c3,c4, S(F,c1,c2,c3,c4) implies IP(F,O,v)]`.

Classically, there exist a Family and four real constants satisfying **all** the expanded scaling conditions, for which the n-scaled oracle error does not converge in probability to zero. Equivalently, there exists ε>0 for which `P_k(|n_k V1(G_k,X_k)−n_k Var(hatβ_k)|>ε)` does not tend to zero. This is an existential refutation, not failure for every family. It does not require Valid, homoskedasticity, or a maximizing graph.

### SAP.P011c.T32

`NOT [for every Family F, then every real c1,c2,c3,c4, S implies Valid(F) implies, for every graph-valued function A assigning a graph to each row k and raw outcome y, (for every k,y, A_k(y) maximizes B↦V1(B,X_k(y)) among graphs compatible with R_k,d_k) implies (Cons(F,V_A) and ((for every k, Homoskedastic(m_k)) implies Cons(F,V_A)))]`, where `V_A,k(y)=V1(A_k(y),X_k(y))`.

Thus a refutation must exhibit a scaled valid family and an **everywhere** maximizing selector A for which this conjunction fails. The second conjunct repeats exactly the same conservativeness conclusion under an additional antecedent; the conjunction is logically equivalent to its first conjunct. Consequently this theorem does **not** assert a counterexample with equal weighted-coordinate variances. No measurability of A is expressly assumed, and no uniform bound on caps d is assumed.

### SAP.P011c.T33

`NOT [for every Family F, then every real c1,c2,c3,c4, S implies Valid(F) implies, for every A, (A maximizes V1 for every k,y among compatible graphs) implies PCC(F,V_A)]`.

Classically, there is a scaled valid family and an everywhere maximizing selector for which there exists 0<α<1 with `liminf_k Cprint_k(V_A,α)<1−α`. Negative variance-estimate realizations are uncovered by definition. This is a refutation of a universal coverage assertion; neither homoskedasticity nor measurability of A is an explicit assumption.

### SAP.P011c.T34

For **every** Family F and then every real c1,c2,c3,c4, if S holds, then for **every** k,

`1 ≤ 1+(Σ_i deg_(G_k)(i))/n_k ≤ 1+c2`.

No graph validity, homoskedasticity, optimizer, correlation coefficient, estimator convergence, or variance comparison is required or concluded. S contains the degree bound used here as well as all of its other conditions.

### SAP.P011c.T35

`NOT [for every Family F, then every real c1,c2,c3,c4, S implies Valid(F) implies, for every natural p, then every coefficient j∈[p], then every sequence D_k of real n_k×p matrices and every fixed vector b∈ℝ^p, (every Gram determinant is nonzero) implies (MeanModel(m_k,D_k,b) for every k) implies (θ_ki=olsTheta(D_k)_(j,i) for every k,i) implies, for every A, (A maximizes V1 for every k,y among compatible graphs) implies (Cons(F,V_A) and PCC(F,V_A))]`.

This asserts existence of a counterexample to the **combined** conservativeness-and-coverage contract for a fixed OLS coefficient with integrable correct linear means and invertible designs. The single b and coefficient j do not vary between rows; D, laws, and weights may. It need not refute both conjuncts, and no homoskedasticity assumption is present. A counterexample necessarily chooses p>0, since j∈[p] must exist.

### SAP.P011c.T36

For **every** Family F, then every real c1,c2,c3,c4, if S holds and every row is Homoskedastic, then `Cons(F,V_G²)`, where `V_G²,k(y)=V2(G_k,X_k(y))`.

Expanded conclusion: for every ε>0, `P_k(n_k[Var(hatβ_k)−V2(G_k,X_k)]>ε)→0`. The graph used is the model's true G. No Valid assumption, optimizer, or bound on supplied caps occurs. No inconsistency witness, consistency assertion, coverage result, or auxiliary mean-square limit is concluded.

### SAP.P011c.T37

For **every** Family F, then every real c1,c2,c3,c4, if S holds, if every row is Homoskedastic, and if Valid(F), then for **every** selector A that maximizes `B↦V2(B,X_k(y))` among compatible graphs for **every** k,y, both

`Cons(F,(k,y)↦V2(A_k(y),X_k(y)))` and `Cons(F,(k,y)↦V2prime(d_k,X_k(y)))`.

Each Cons quantifies over every ε>0 and states the one-sided n-scaled underestimation limit above. The two Cons assertions have independent ε quantifiers. No uniform bound on supplied d, no measurability of A, and no coverage assertion is expressly included.

### SAP.P011c.T38

For **every** Family F, then every real c1,c2,c3,c4, if S holds, then both:

* for all sufficiently large k, `Var_(μ_k)(hatβ_k)>0`;
* for **every** real t, `P_k((hatβ_k−β_k)/sqrt(Var(hatβ_k))≤t)→Φ(t)`.

The threshold t is fixed before taking the limit. Standardization uses the true variance, not a graph-based estimate. Any zero-variance early rows use total real division, but eventual positivity is part of the conclusion. Valid, homoskedasticity, and a graph selector are not required.

### SAP.P011c.T39

For **every** Family F, then every real c1,c2,c3,c4, if S holds, then for **every** sequence of real statistics V_k on the raw row spaces, if **each** V_k is Borel measurable, both following implications hold:

1. If `IP(F,(k,y)↦n_k V_k(y),v)`, then for **every** real α, if 0<α<1, `C_k(V,α)→1−α`.
2. If `Cons(F,V)`, then `CC(F,V)`, that is, for every 0<α<1, `1−α≤liminf_k C_k(V,α)`.

The consistency/conservativeness antecedents are separate, not jointly required. Both conclusions use nonnegative clipping. Borel measurability is on the raw product σ-algebra, and is stronger than measurability only after completing μ_k. No integrability or sign assumption on V is imposed. Valid and homoskedasticity are not required.

### SAP.P011c.T40

For **every** Family F, then every real c1,c2,c3,c4, if S holds, if every row is Homoskedastic, and if Valid(F), then for **every** A that maximizes `B↦V2(B,X_k(y))` among compatible graphs for **every** k,y, both

`PCC(F,(k,y)↦V2(A_k(y),X_k(y)))` and `PCC(F,(k,y)↦V2prime(d_k,X_k(y)))`.

Each conclusion separately quantifies over every 0<α<1 and asserts at least 1−α limiting inferior coverage of the event with nonnegative estimate and the unmodified square root. The theorem does not separately conjoin a finite-sample nonnegativity assertion, although that follows directly from the definitions for positive row sizes. No cap bound or measurability of A is an explicit assumption.

### SAP.P011c.T41

This is a conjunction of two independent universal assertions.

First, for **every** natural n, every graph R on [n], and every natural h-vector, if **every** i satisfies the real inequality `2 deg_R(i)−1≤h_i`, then K(R,h) is symmetric and has nonnegative quadratic form for every real vector; furthermore, **if** n>0, then for **every** real vector δ, `Q(K(R,h),δ)/n≥0`. The capacity condition and the diagonal subtraction are real, not truncated natural arithmetic. The PSD assertion includes n=0; only the normalized inequality requires positive n. There is no requirement that R be a forest, that h≤n−1, or that h equal degrees of a larger graph.

Second, for **every** natural n, graph R, natural d-vector, arbitrary real function f on graphs, fixed real number c, and graph A,

`Maximizes(R,d,(B↦f(B)+c),A) ↔ Maximizes(R,d,f,A)`.

c is fixed across candidate graphs B. No feasibility assumption is required: each side includes compatibility of A and hence both are false for infeasible A. No matrix decomposition or data-dependent correction identification is concluded.

## Mathlib source tracing

The terminal notions were checked in the installed Mathlib sources, without reading proof/Solution/Comparator files:

* `MeasureTheory/MeasurableSpace/Constructions.lean`: product-coordinate measurable space and `measurable_pi_iff`.
* `MeasureTheory/MeasurableSpace/Defs.lean`: `Measurable` is preservation of measurable preimages.
* `MeasureTheory/Measure/MeasureSpaceDef.lean`, `MeasureTheory/Measure/Real.lean`: `μ.real(E)=(μ(E)).toReal`.
* `MeasureTheory/Integral/Bochner/Basic.lean`: real Bochner integral and `integral_undef` (zero without integrability).
* `MeasureTheory/Function/L1Space/Integrable.lean`, `MeasureTheory/Function/LpSeminorm/Defs.lean`: almost-everywhere strong measurability plus finite norm integral, and L² membership.
* `Probability/Independence/Basic.lean`, `Probability/Independence/Kernel/IndepFun.lean`, `Probability/Independence/Kernel/Indep.lean`: function independence via generated σ-algebras and product probabilities.
* `Probability/CDF.lean`, `Probability/Distributions/Gaussian/Real.lean`: cdf and Gaussian with variance parameter; variance one is a probability measure with the ordinary standard normal cdf.
* `Analysis/Real/Sqrt.lean`: square root via nonnegative truncation, zero on negative arguments.
* `Order/LiminfLimsup.lean`, `Order/Filter/Defs.lean`, `Order/Filter/AtTopBot/Defs.lean`: supremum of eventual lower bounds, filter convergence, and the tail filter.
* `LinearAlgebra/Matrix/Defs.lean`, `Data/Matrix/Mul.lean`, `Data/Matrix/Diagonal.lean`, `LinearAlgebra/Matrix/NonsingularInverse.lean`: matrix operations, identity/diagonal matrices, matrix-vector product, and determinant inverse.
