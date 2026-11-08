# Blind reading of SAP.P011b.T16

This file was written at step 1, before opening `claims.json`, `record.json`,
`earlier.json`, or `architect-report.md`. Sources inspected: the target docstring
and statement, `closure.json`, all the relevant source declarations in
`Defs/Part1.lean`, `Defs/Part2.lean`, `Defs/Part3.lean`, and `Defs/WholeW2.lean`,
and the generated proof declarations printed in `scratch/ClosurePrint.lean`.
The closure fingerprint is
`483b859337441acb0d003e765280fa336f3bec12faeff6c848ae4074ee06526a`.

## SAP.P011b.T16

### Objects and definitions, unfolded

All finite vectors and matrices are real valued. A graph on n vertices is a
Boolean function a : Fin n → Fin n → Bool together with proofs that a(i,j) =
a(j,i) and a(i,i) = false. Its real adjacency matrix A has entries 1 on edges
and 0 otherwise. Its degree at i is the finite sum of those Boolean indicators.
Write M(A) = I + A, where I is the **identity matrix**, not the all-ones matrix.
A graph B is compatible with recruitment graph R and natural-number caps d_i
exactly when every edge of R is an edge of B and deg_B(i) ≤ d_i for every i.
To maximize an objective means both compatibility and an objective value at
least that of every compatible graph; ties are permitted.

A model consists of a Borel measure μ on R^n with total mass one, deterministic
real weights θ_i, graphs G and R, and natural caps d_i. It imposes no dependency,
integrability, validity, or mean-model condition by itself. The structure's
constructor and projections do exactly this bookkeeping. For y ∈ R^n, define

* x_i(y) = θ_i y_i, x̄(y) = (Σ_i x_i(y))/n, and x̃_i = x_i − x̄;
* E_μ f = the real Bochner integral ∫ f dμ;
* β̂(y) = x̄(y), β = E_μ β̂, and Var_μ(f) = E_μ[(f − E_μ f)^2];
* δ_i = E_μ x_i − β;
* q_C(v) = Σ_i Σ_j C_ij v_i v_j;
* s²(v) = (Σ_i (v_i − (Σ_j v_j)/n)^2)/n;
* V₁(B,v) = [Σ_i (v_i − v̄)^2 + Σ_iΣ_j B_ij(v_i − v̄)(v_j − v̄)]/n²;
* V_res(B,r) = q_{I+B}(r)/n²;
* b_mean = q_{I+G}(δ)/n.

The dependency condition is full dependency-graph independence, not merely zero
covariance: for every pair of disjoint finite vertex sets S,T with no G-edge
between them, the random coordinate vectors (Y_i)_{i∈S} and (Y_j)_{j∈T} are
independent under μ, in Mathlib's `IndepFun` sense. Coordinate subtype indices
are only a way of presenting these finite vectors.

A family consists of n_k : N → N, proofs n_k > 0 and n_k → ∞, and a model at
each k. The measures can differ with k. Nestedness means that n_k is monotone
and, for every k, there exists an injection Fin n_k → Fin n_{k+1} preserving
both edges and nonedges of the true graph. It does not require a coupling of
the laws at different k. The condition called `Scaling F c1 c2 c3 c4` means,
in order: this nestedness; c1,c2,c3,c4 are strictly positive reals; the dependency
condition at every k; for every k, μ_k-almost surely |θ_ki Y_ki − β_k| ≤ c1
simultaneously for all i; every true degree is ≤ c2; n_k Var_μk(β̂_k) → c3;
and |θ_ki| < c4 for every k,i. Validity means that G_k is compatible with
R_k,d_k at every k.

For a statistic T_k and a deterministic real sequence a_k, convergence in
probability here means that for every real ε > 0,
μ_k({y : |T_k(y) − a_k| > ε}).toReal → 0. A variance statistic V_k is
conservative exactly when for every ε > 0,
μ_k({y : n_k[Var_μk(β̂_k) − V_k(y)] > ε}).toReal → 0.
Write t_k = n_k Var_μk(β̂_k) and o_k(y) = n_k V₁(G_k,x_k(y)).
Tightness of T_k means: for every ε > 0 there exist real B > 0 and integer k0
such that, for all k ≥ k0, μ_k({|T_k| > B}).toReal ≤ ε.

For deterministic design D ∈ R^{n×p}, write
H(D) = (DᵀD)⁻¹Dᵀ, b̂_D(y) = H(D)y, and Θ(D) = n H(D).
The `ols` and `olsTheta` definitions are exactly these formulas using Mathlib
matrix multiplication, transpose, inverse, and matrix-vector multiplication.
The mean-model predicate for b ∈ R^p says that every coordinate Y_i is
Bochner integrable and E_μ Y_i = Σ_l D_il b_l for every i.
The true weighted residual vector is e_i(y) = θ_i[y_i − (Db)_i].
The fitted weighted residual for an estimator g is r_i(y) =
θ_i[y_i − (Dg(y))_i]. The Euclidean norm used throughout is
||v||₂ = sqrt(Σ_i v_i²), even when the number of coordinates is p.

### Quantifiers and conclusions

The theorem has no external hypotheses. Its proposition is the conjunction
of the following eight independent assertions, in this order.

1. **Finite OLS identities.** For all natural n,p, if 0 < p and p ≤ n, then
   for every model, real n×p design D, real p-vector b, and index j ∈ Fin p,
   if det(DᵀD) ≠ 0, the mean-model condition holds, and θ_i = Θ(D)_ji for all i,
   then β̂(y) = b̂_D(y)_j for every real data vector y, β = b_j, and for every i
   E_μ x_i = Θ(D)_ji (Db)_i and δ_i = Θ(D)_ji (Db)_i − b_j.
   No asymptotic scaling assumption is used for these identities.

2. **Design-space shifts.** For all n,p with 0 < p ≤ n, every model, design D,
   and j, assuming det(DᵀD) ≠ 0 and θ_i = Θ(D)_ji, for every y ∈ R^n and
   c ∈ R^p: b̂_D(y+Dc) = b̂_D(y)+c; r(y+Dc) = r(y), where g = b̂_D;
   V_res(B,r(y+Dc)) = V_res(B,r(y)) for **every** graph B; and the raw centered
   weighted vector at y+Dc equals its value at y plus the vector with entries
   θ_i(Dc)_i − c_j. Invariance of each residual pair product follows from
   equality of the residual vectors. The raw pair-product change is obtained
   by expanding this explicit vector identity. There is no mean-model premise.

3. **Intercept shifts.** For all n,p with 0 < p ≤ n, every model, design D,
   indices j,j0, assuming det(DᵀD) ≠ 0, θ_i = Θ(D)_ji, D_i,j0 = 1 for every i,
   and j ≠ j0, for every y and real t: b̂_D(y+t1)_j = b̂_D(y)_j,
   r(y+t1) = r(y), and V_res(B,r(y+t1)) = V_res(B,r(y)) for every graph B.

4. **Raw oracle and maxima.** For every family and every real c1,c2,c3,c4,
   the scaling condition implies all the following:

   * (o_k − t_k) − b_mean,k → 0 in probability;
   * o_k − t_k → 0 in probability iff b_mean,k → 0 as a real sequence;
   * V₁(G_k,x_k) is conservative iff 0 ≤ liminf_k b_mean,k;
   * if validity holds, there exists a selection A_k(y) attaining a compatible
     V₁ maximum for **every** k,y, and nonnegative liminf bias implies
     conservativeness for **every** such maximizing selection;
   * if E_μk x_ki = β_k for every k,i, the raw oracle is consistent, and
     under validity every compatible raw maximum is conservative.

   A selection is any function sending k and the whole data vector to a graph;
   no measurability premise on the selection itself is introduced.
   A real-sequence liminf is Mathlib's supremum of its eventual lower bounds.

5. **Explicit nonnecessity example.** Fix the following family; it is a
   conjunction about concrete data, not an implication with an uninhabited
   premise. Let K=k+1 and n=4K. On each of K mutually independent blocks, draw
   U_0,U_1,U_2 uniformly and independently in {0,1,2,3}, and V uniformly in
   {0,…,47}, independently of all U's and of other blocks. The three leaves
   are L_j = 1[U_j < 1]. Set C = 1[V < 33+4(L_0+L_1+L_2)]. The block vector
   is (C,L_0,L_1,L_2). The law is the pushforward of the uniform PMF on the
   **entire product** (Fin K → ((Fin 3 → Fin 4) × Fin 48)), followed by
   `PMF.toMeasure`. Thus repeated blocks are independent draws, not copies
   of one draw. The true graph is K disjoint stars, with center first and three
   leaf neighbors; recruitment is empty, caps are 3 at centers and 1 at leaves,
   and θ_i=1. Block quotient and remainder are floor(i/4) and i mod 4.
   The fixed two-column design has rows (1,3) at centers and (1,−1) at leaves;
   b=(3/8,1/8) and j=0.

   The assertion is: scaling holds with (c1,c2,c3,c4)=(1,3,27/128,2), validity
   holds, and for every k the Gram determinant is nonzero, the mean model
   holds, θ_i = Θ(D)_0i, t_k = 27/128, b_mean,k = −3/128, the empty graph is
   compatible, and n V₁(empty,x(y)) = s²(x(y)) for every y. In addition,
   s²(x_k) → 15/64 in probability; maximizing selections exist; every raw
   maximizing selection is conservative; and liminf b_mean,k < 0.

   The shared `starLeaves`/`starBlock` definitions also have an `upper=true`
   branch: leaf success thresholds (3,1,2) out of 4, center threshold
   18+4 count out of 48. The example here always uses the false branch.
   `starModel` normally sets recruitment equal to the true stars;
   `unforcedModelW2` replaces only recruitment by the empty graph. The
   auxiliary `starFamily` has n=4(k+1) and supplies the growth proof.

6. **Explicit constant-shift example.** The fixed design is
   D=((1,−1),(1,1)), with two rows and two columns. The model is the Dirac law
   at y=(0,0), θ=(−1,1), empty true and recruitment graphs, and zero caps.
   The assertion is: det(DᵀD) ≠ 0; the mean model holds with b=0;
   θ_i = Θ(D)_1i; column 0 is all ones; the slope at y=0 equals the slope at
   y=1; their fitted weighted residual vectors agree; but their raw empty-graph
   V₁ values are respectively 0 and 1/2. There is no positive-variance or
   scaling premise on this finite algebraic witness.

7. **Residual asymptotics.** For every family and real scaling constants,
   assuming scaling, for every natural p, j ∈ Fin p, sequence of real n_k×p
   designs D_k, and deterministic sequence b_k ∈ R^p, assume, in order:
   0 < p; p ≤ n_k for every k; det(D_kᵀD_k) ≠ 0 for every k; the mean model
   for b_k at every k; θ_ki = Θ(D_k)_ji for every k,i; and design regularity.
   The last condition means that there **exist** reals Bx,By,λ with Bx,By ≥ 0
   and λ > 0 such that ||row_i D_k||₂ ≤ Bx for every k,i, μ_k-almost surely
   |Y_ki| ≤ By for every i and every k, and
   λ||z||₂² ≤ q_{(D_kᵀD_k)/n_k}(z) for every k and z ∈ R^p.
   Thus p and j are fixed outside the k quantifier, while b_k may vary.

   Put Δ_i(y)=θ_ki[D_k(b̂_Dk(y)−b_k)]_i and e_i(y)=θ_ki[y_i−(D_k b_k)_i].
   Then sqrt(n_k)||b̂_Dk−b_k||₂ is tight; at every k,y the fitted weighted
   residual equals e−Δ; and at every k,y the deterministic inequality

       |q_{I+G_k}(e−Δ) − q_{I+G_k}(e)|/n_k
         ≤ (1+c2)[2 (||e||₂/sqrt(n_k))(||Δ||₂/sqrt(n_k)) + ||Δ||₂²/n_k]

   holds. Both sides tend to zero in probability. Also
   n_k V_res(G_k,r_k) − t_k → 0 in probability. Finally, if validity holds,
   compatible residual maximizers exist for all k,y, and **every** such
   maximizing selection is conservative in the same scaled one-sided sense.
   The c2 in the bound controls the true graph's degree, not the candidate
   graphs' caps.

8. **Measurability of maximum values.** For every natural n (including zero),
   graphs R,G and natural caps d, assuming G is compatible, for every family
   of real functions f_B on R^n which are Borel measurable separately for each
   graph B, and every selection A(y) maximizing f_B(y) among compatible B
   at every y, the scalar function y ↦ f_{A(y)}(y) is Borel measurable.
   Because the finite nonempty feasible set has a well-defined maximum value,
   no measurability of A itself is necessary, including at ties.

### Closure coverage

The prose above expands every mathematical definition in the supplied closure:
the graph, model, family, dependency, scaling, convergence, conservativeness,
OLS, residual, selection, witness, regularity, and perturbation definitions.
The listed constructors/projections of `Model` and `Family` are ordinary
structure operations. Every line-zero generated declaration was also checked
with Lean: these provide Boolean graph symmetry/diagonal proofs, finite-index
bounds, positivity/growth of family sizes, probability-measure instances,
nonempty finite source spaces, nonzero natural numeral instances used for
vectors and rational denominators, or the ordinary outer-measure instance
for a measure. They introduce no substantive mathematical hypothesis or
axiomatic substitute for a conclusion. The target is a theorem stub; the
review does not use that stub as an independent verification of the examples.

### Junk-value and boundary audit

* **Real division by zero.** Mathlib real division is total and gives zero
  for a zero denominator. All averages, V₁, V_res, mean-bias, and normalized
  perturbation expressions in substantive finite OLS clauses have n ≥ p > 0;
  all family occurrences have n_k > 0 by the structure; both fixed examples
  have n ≥ 2. No conclusion exploits division by zero. Abstract maxima
  measurability permits n=0 but asserts only a legitimate finite maximum of
  supplied functions and introduces no normalized formula.
* **Matrix inverse.** Mathlib's square matrix inverse is zero at a singular
  real matrix. Every assertion using an OLS inverse assumes or explicitly
  asserts det(DᵀD) ≠ 0. The star and two-point witness designs have positive
  Gram determinants. There is no singular-inverse interpretation here.
* **Bochner integrals.** These are totalized (in particular they give zero
  outside their integrability domain). Finite OLS uses the explicit coordinate
  integrability in the mean model; finite linear combinations are therefore
  integrable. In scaling clauses each weighted outcome minus a deterministic
  finite β is bounded almost surely, so weighted outcomes, their finite sums,
  their squares, and all raw moments actually used are integrable. The
  residual clause additionally bounds raw outcomes. The star laws have finite
  support and the slope example is a Dirac law. General model definitions
  alone do not guarantee moments, but the theorem's applicable premises do.
* **Square root.** Every norm square root has a nonnegative finite sum of
  real squares as input. sqrt(n) in a denominator has positive natural n.
  The convention sqrt(t)=0 for t<0 cannot affect these assertions.
* **Real-valued liminf.** This is sSup of eventual lower bounds and could
  behave as a junk value for sequences diverging outside R. Here scaling
  implies |δ_ki| ≤ c1, and hence
  |b_mean,k| ≤ (1+c2)c1² using the degree bound. The sequence is uniformly
  bounded above and below, so its eventual lower bounds form a nonempty,
  bounded-above set. The fixed example has the constant sequence −3/128.
  Thus the liminf is the ordinary finite real liminf in every use.
* **Probability toReal.** `Measure.real E` is `(μ E).toReal`. Although ENNReal
  infinity is mapped to zero, μ is a probability measure, so μ E ≤ 1 for
  every set. Infinity cannot occur. Statistics are polynomial/continuous
  functions or finite maxima of Borel functions; the last conjunct deals
  explicitly with arbitrary maximizing selections. Outer-measure behavior
  on nonmeasurable events is not used to supply a statistical conclusion.
* **Finite uniform PMFs and index arithmetic.** The uniform source is a
  finite nonempty type. Product function spaces are nonempty even at zero
  blocks; the actual example uses K=k+1>0. Block quotient and remainder use
  a positive block width q (here 4); their proof arguments ensure they lie
  in the required finite index types. There is no default value for an
  out-of-bounds index. Star center thresholds lie within {0,…,48}, so their
  uniform-threshold interpretation is literal.
* **Empty indices and casts.** Fin 0 is empty, finite sums over it are zero,
  and the abstract measurability clause covers the harmless one-graph case.
  All OLS coefficient clauses require p>0 and j∈Fin p; all statistical
  sequences have positive n. Natural-to-real casts preserve positivity and
  exact arithmetic. There is no natural truncated subtraction in the
  dependency closure's substantive formulas. All displayed vector and
  quadratic subtractions are real, pointwise subtraction.
* No `Real.log`, real power outside its domain, `limsup`, standalone empty
  infimum, unbounded optimization supremum, conditional-law default, or
  partial-function default appears in this statement's closure. Finite
  maximization uses an explicit feasible graph and ordinary order comparison,
  not a supremum convention. Probability laws are on finite-dimensional real
  spaces, so the usual sigma-finiteness and standard Borel requirements hold.

At the end of the blind stage, these eight assertions appear substantive and
their assumptions appear jointly satisfiable. The scaling and OLS-residual
premises will be checked by an explicit independent-sign intercept family,
and the fixed witnesses will be checked separately, in the claim stage.
