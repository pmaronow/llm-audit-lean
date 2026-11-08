# Blind reading

Saved at step 1, before opening `claims.json` or `record.json`.

Sources read: all of `closure.json`; `Challenge/Part1.lean`; and the complete source of
`Defs/Part1.lean`, `Defs/Part2.lean`, `Defs/WholeW1.lean`, and `Defs/WholeW2.lean`.
These contain every source declaration in the five closures. Structure declarations
include their constructors and projections. `scratch/Blind.lean` additionally prints
both structures and every generated proof declaration listed in the closures; it
compiled successfully. The generated proofs supply only the outer-measure instance,
nonemptiness of Boolean vectors, numeral `AtLeastTwo` instances, and `NeZero 2`.
They add no statistical assumptions. The unrelated T41 proof in T34's closure is a
shared proof that the numeral 2 is at least two, not a dependency on T41's assertion.

## Fully expanded notation common to the five readings

All vector spaces below have the ordinary product Borel measurable structure.
Write `[n] = Fin n`, the finite type of natural numbers strictly below `n`.
A graph on `[n]` is a Boolean function `a : [n] → [n] → Bool` satisfying
`a(i,j)=a(j,i)` and `a(i,i)=false`. Write
`a_ij = if a(i,j) then (1:ℝ) else 0` and
`deg_a(i) = ∑_{j∈[n]} (if a(i,j) then (1:ℕ) else 0)`.
Thus graphs are simple and undirected, diagonal contributions are zero, and every
double sum below counts each undirected edge twice. A graph `a` is compatible with
`(r,d)` exactly when every true Boolean entry of `r` is true in `a` and
`deg_a(i) ≤ d(i)` for every vertex, where `d : [n] → ℕ`.

A model consists of an arbitrary Borel probability measure `μ` on `[n] → ℝ`,
fixed real weights `θ : [n] → ℝ`, two graphs `g,r`, and natural degree caps `d`.
The probability field explicitly asserts `IsProbabilityMeasure μ`. For an outcome
`y : [n] → ℝ`, put

* `x_i(y)=θ_i y_i`, `b̂(y)=(∑_i x_i(y))/(n:ℝ)`, and `b=∫ b̂(y) dμ(y)`;
* for any real function `f`, `E(f)=∫ f dμ` (Mathlib's real Bochner integral) and
  `Var(f)=∫(f(y)-∫f dμ)^2 dμ(y)`;
* `μ_i=∫x_i dμ` and `C_ij=∫(x_i-μ_i)(x_j-μ_j) dμ`;
* `x̄=(∑_i x_i)/(n:ℝ)`, `δ_i=x_i-x̄`, and
  `s²(x)=(∑_i δ_i²)/(n:ℝ)`;
* `Q(M,x)=∑_i∑_j M_ij x_i x_j`;
* `v₁(a,x)=[∑_i δ_i² + ∑_i∑_j a_ij δ_i δ_j]/(n:ℝ)²`;
* `v₂(a,x)=[s²(x)/(n:ℝ)] [1+(∑_i∑_j a_ij)/(n:ℝ)]`;
* `v₂′(d,x)=[s²(x)/(n:ℝ)] [1+(∑_i (min(d_i,n-1):ℕ):ℝ)/(n:ℝ)]`.

The dependency condition is the following full random-vector independence, not
merely zero covariances: for **every** pair of finite vertex sets `S,T`, if they are
disjoint and `g(i,j)=false` for all `i∈S,j∈T`, the functions
`y ↦ (y_i)_{i∈S}` and `y ↦ (y_j)_{j∈T}` are `ProbabilityTheory.IndepFun` under `μ`.
The coordinates of these vectors are indexed by the membership subtypes of `S,T`.
Homoskedasticity means `C_ii=C_jj` for all vertices; it concerns weighted outcomes,
and does not require equality of `μ_i`.

A family is **data**, not just a predicate: `n : ℕ → ℕ`, proofs that `n_k>0` for
every `k` and `n_k→∞` (`Filter.Tendsto ... atTop atTop`), and a model of size
`n_k` for every `k`. Each row has its own probability measure; there is no common
coupling requirement. Put `s_k=n_k Var_k(b̂_k)`. Write `P_k(E)=(μ_k(E)).toReal`,
which is `Measure.real` on arbitrary sets.

Both `WholeScaling` and `WholeW2Scaling` mean precisely the same conjunction:

1. `c₁,c₂,c₃,c₄` are strictly positive real constants;
2. each row satisfies the dependency condition just expanded;
3. for each `k`, for `μ_k`-almost every `y`, **all** coordinates satisfy
   `|θ_ki y_i-b_k| ≤ c₁` (centering at the scalar target, not the individual mean);
4. for every `k,i`, `(deg_{g_k}(i):ℝ) ≤ c₂`;
5. the real sequence `s_k` converges to `c₃`;
6. for every `k,i`, `|θ_ki| < c₄`.

These predicates require neither nesting of full graphs nor relations between
observed graphs. The separate `Nested` predicate asserts that `n` is monotone and
for each `k` there exists an injection `e:[n_k] ↪ [n_{k+1}]` such that
`g_k(i,j)=g_{k+1}(e(i),e(j))` for every pair. `Valid` asserts compatibility of
`g_k` with `(r_k,d_k)` in every row.

For row statistics `v_k(y)`, the conservativeness conclusion abbreviates exactly
`∀ ε:ℝ, ε>0 → P_k{y : n_k(Var_k(b̂_k)-v_k(y))>ε} → 0`.
Convergence in probability to real numbers `a_k` abbreviates
`∀ ε:ℝ, ε>0 → P_k{y : |T_k(y)-a_k|>ε} → 0`.
Every convergence here is `Filter.Tendsto` from natural-number `atTop` to the
ordinary real neighborhood filter. No liminf/limsup is hidden in these definitions.

## SAP.P011c.T34

Declaration: `Challenge/Part1.lean:42–50`, statement body
`Defs/WholeW1.lean:119–132`.

### Exact statement, hypotheses, and quantifiers

There **exists** a family `F` as defined above such that all of the following hold:

* `n_k=k+1` for every natural `k`;
* the observed graphs nest by the injections just defined;
* the six scaling conditions hold with `(c₁,c₂,c₃,c₄)=(1,1,1,2)`;
* all true row graphs are compatible with the known graphs and degree caps;
* for every row, its law is exactly the uniform distribution of the real vectors
  obtained from **all** Boolean vectors `u:[n_k]→Bool`, with
  `y_i=if u_i then 1 else -1`; every weight is 1; every entry of `g_k` is false;
  all weighted variances are equal; `b_k=0`; and `n_k Var_k(b̂_k)=1`;
* **for every** collection of coefficient vectors `q_k:[n_k]→ℝ` and **every**
  positive real `ε`, both
  `P_k{|n_k u_k(y)-s_k|<ε}→1` and `¬(P_k{|n_k u_k(y)-s_k|<ε}→0)` hold, where
  `u_k(y)=[s²(x(y))/n_k][1+(∑_i∑_j (g_k)_ij q_ki)/n_k]`.

This unfolds `printedAuxiliary`. The `q` quantifier is after the family exists,
so a single independent-sign family works for every coefficient array. The
strict inequality is `<ε` inside the event. On these empty graphs `u_k=s²/n_k`
irrespective of `q`. For supported outcomes, `s²=1-b̂_k²`, so the event is
`b̂_k²<ε`. This is a true convergence/negation-of-limit statement, not a claim
that this event ever has zero probability.

The docstring explicitly calls this a refutation of a printed P4 assertion,
without interpreting undefined correlations or repairing P2. It does not claim
that the auxiliary estimator is inconsistent: its statement actually asserts
scaled consistency of this auxiliary estimator in this example.

### Junk conventions

All divisions are real divisions, for which division by zero is zero. Family
positivity and `n_k=k+1` exclude zero denominators. Empty graphs are intentional;
the vertex types are nonempty. The uniform Boolean-vector PMF exists even for
`n=0` because the function type is inhabited, but the witness never uses that row.
The law really is independent signs (uniform over all vectors, then mapped), not
a repeated shared sign. All weights/outcomes in its support are bounded, so all
Bochner integrals are genuine integrals. `Measure.real` would send infinite mass
to zero, but the measure is a probability measure and every set has mass at most
one. Natural-to-real casts are exact; `k+1` is natural addition without overflow.
No truncated subtraction, sqrt, log, rpow, extrema of sets, or partial functions
enter this statement. Arbitrarily large real `q_i` multiply zero adjacency entries,
not an extended-real infinity. All automatic proof dependencies are benign.

## SAP.P011c.T35

Declaration: `Challenge/Part1.lean:52–61`, statement body
`Defs/WholeW2.lean:37–47`.

### Exact statement, hypotheses, and quantifiers

There **exist together** a family `F`, a matrix
`D_k : [n_k] × Fin 2 → ℝ` for each row, and a selector
`A_k : ([n_k]→ℝ) → Graph(n_k)` such that:

* the six rowwise scaling conditions hold with constants `(6,2,29/15,2)`;
* the observed graphs nest and the true graphs meet all known-edge/degree constraints;
* for every `k`, `det(D_kᵀ D_k)≠0`;
* for every `k,i`, the raw coordinate `y↦y_i` is Bochner integrable and
  `∫y_i dμ_k=(D_k · (0,1))_i`, i.e. the second column of `D_k`;
* for every `k,i`, `θ_ki` is entry `(0,i)` of
  `n_k • [(D_kᵀ D_k)⁻¹ D_kᵀ]` (ordinary scalar multiplication of the real matrix);
* for every row `k` and **every** outcome vector `y`, `A_k(y)` is compatible and
  for **every** compatible graph `B`,
  `v₁(B,x_k(y)) ≤ v₁(A_k(y),x_k(y))`;
* it is **not** the case that for every positive real `ε`,
  `P_k{y:n_k(Var_k(b̂_k)-v₁(A_k(y),x_k(y)))>ε}→0`.

Thus at least one positive error tolerance has a nonvanishing-underestimation
probability in the sense of failure to converge to zero. No particular rate or
liminf lower bound is stated. There is no explicit Wald interval or coverage
formula in this proposition. The docstring refers to failure of a combined
variance-and-coverage contract through its variance component, and disclaims
any claim about the vignette's realized numerical standard errors.

The sample-size and Gram hypotheses force each row to have at least two rows;
the first OLS coefficient estimates the first entry, zero, of `(0,1)`. The
weights make `b̂` that coefficient because the average cancels the displayed
factor `n_k`.

### Junk conventions

All sample-size denominators are nonzero. The matrix inverse is Mathlib's total
adjugate/determinant inverse, which can return the zero matrix for singular real
matrices; `det≠0` explicitly rules out that convention. Both `Fin 2` columns are
present, and the coordinate `0:Fin 2` is valid. The numeral proof declarations
do not add assumptions. `29/15` is real division with a nonzero denominator.
Raw coordinate integrability is explicit. Weighted coordinates are measurable
and bounded around the fixed finite real target by the scaling assumption,
which implies the finite moments used throughout; no failed Bochner integral is
used. Each optimized value is the maximum of finitely many continuous graph
objectives over a fixed nonempty feasible set (it contains the true graph).
Hence even an arbitrary selector gives the same measurable value, so selector
nonmeasurability cannot manufacture the failed probability limit. Probability
mass is finite, so `toReal ∞=0` is irrelevant. There is no natural subtraction,
log, sqrt, rpow, limsup/liminf, empty supremum/infimum, or partial-function default.

## SAP.P011c.T36

Declaration: `Challenge/Part1.lean:63–71`, statement body
`Defs/WholeW2.lean:57–65`.

### Exact statement, hypotheses, and quantifiers

This is a conjunction of two independent assertions:

1. **For every** family `F` and **every** four real constants, if all six scaling
   conditions hold, and if `C_kii=C_kjj` for every `k,i,j`, then **for every**
   positive real `ε`,
   `P_k{y:n_k(Var_k(b̂_k)-[s²(x_k(y))/n_k]
     [1+(∑_i∑_j(g_k)_ij)/n_k])>ε}→0`.
2. There **exists** a family with scaling constants `(2,1,1,2)`, nested observed
   graphs, and equal weighted variances in every row, for which it is **not**
   true that **for every** positive real `ε`,
   `P_k{y:|n_k [s²(x_k(y))/n_k]
     [1+(∑_i∑_j(g_k)_ij)/n_k]-n_k Var_k(b̂_k)|>ε}→0`.

The first conjunct is universal and contains no `Nested` or `Valid` hypothesis.
The second is an existence assertion of failure of **scaled** convergence in
probability. It does not assert failure of unscaled absolute consistency.
Neither conjunct assumes equality of individual weighted means. The oracle
uses the actual row dependency graph, not a maximizing selector.

### Junk conventions

Positivity of family sizes excludes every zero denominator and empty vertex
type. The a.e. bound on the measurable weighted coordinates gives all required
moments; targets are finite real numbers and the variance integral is genuine.
Every probability is in `[0,1]`, so the `ENNReal.toReal` infinity convention is
inactive. Both error definitions use strict `>ε`, ordinary real subtraction,
and ordinary absolute value. The existential part is a negation of real
convergence, not a `limsup` computed on an unbounded sequence. There is no sqrt,
log, rpow, truncated subtraction, partial inverse, set extremum, or partial-function
default in this closure.

## SAP.P011c.T37

Declaration: `Challenge/Part1.lean:73–79`, statement body
`Defs/WholeW2.lean:73–80`.

### Exact statement, hypotheses, and quantifiers

**For every** family `F` and four real constants, assume the six scaling
conditions, rowwise equal weighted variances, and compatibility of every true
graph with its known graph and degree caps. **For every** outcome-dependent
graph selector `A_k(y)`, assume that **for every** `k,y` it is compatible and
its `v₂` value is at least that of **every** compatible graph. Then both:

* **for every** `ε>0`,
  `P_k{y:n_k(Var_k(b̂_k)-[s²(x_k(y))/n_k]
    [1+(∑_i∑_j(A_k(y))_ij)/n_k])>ε}→0`;
* **for every** `ε>0`,
  `P_k{y:n_k(Var_k(b̂_k)-[s²(x_k(y))/n_k]
    [1+(∑_i(min(d_ki,n_k-1):ℕ):ℝ)/n_k])>ε}→0`.

The tolerances in the two conjuncts are independently universally quantified.
The selectors themselves have no measurability hypothesis. There is no nesting
condition or uniform bound on supplied degree caps, only on actual true-graph
degrees. There is no condition on equality of means. These are probability
limits of underestimation, not assertions that the variances or estimates
converge to a positive constant without scaling.

### Junk conventions

The displayed `n_k-1` is **natural truncated subtraction**. Since `n_k>0`, it
equals the ordinary nonnegative integer `n_k−1` and correctly bounds the largest
possible simple-graph degree; it never wraps negative or relies on `0−1=0`.
The sum casts these finite natural numbers exactly into the reals. All real
denominators are nonzero; no empty vertex type occurs. All moments are finite
by the measurable coordinate bound. Probability mass is finite, so conversion
of infinity to zero is excluded. The feasible set is nonempty since the true
graph is feasible, and it is finite since adjacency is a finite Boolean array.
No `sSup` or `sInf` implements maximization: it is explicit pairwise comparison.
Any maximizing selector has the same value as the finite maximum of the fixed
graph objectives, so this value is measurable even if the selector is not.
There is no sqrt, log, rpow, limsup/liminf, inverse, or partial-function default.

## SAP.P011c.T38

Declaration: `Challenge/Part1.lean:81–87`, statement body
`Defs/WholeW1.lean:44–49`.

### Exact statement, hypotheses, and quantifiers

**For every** family `F` and four real constants, if the six scaling conditions
hold, then the following conjunction holds:

* **eventually** in natural-number `k`, `Var_k(b̂_k)>0`;
* **for every** real threshold `t`,
  `P_k{y:(b̂_k(y)-b_k)/sqrt(Var_k(b̂_k)) ≤ t} → Φ(t)`,
  where `sqrt` is `Real.sqrt`, and `Φ(t)` is Mathlib's cdf at `t` of
  `ProbabilityTheory.gaussianReal 0 (1:ℝ≥0)`, i.e. the probability of `(-∞,t]`
  under the real normal measure of mean zero and variance one.

The event uses `≤t`, not `<t`; the threshold quantifier follows the eventual
positivity conjunct. The statement has no equality-of-means, homoskedasticity,
valid-constraint, nesting, or monotonicity assumption. Sizes may be any positive
natural sequence tending to infinity. The law of each row may differ without
any consistency or coupling between rows.

### Junk conventions

`Real.sqrt` is zero for nonpositive inputs, and real division by zero is zero.
Here variance is always nonnegative because its genuine integrand is a square,
and it is explicitly **eventually strictly positive**. A finite initial segment
can have zero variance and standardized variable zero by the division convention;
this cannot affect any claimed limit. Positive limiting `n_k Var_k(b̂_k)=c₃`
also explains the eventual positivity clause. The coordinate bound implies
integrability and all needed moments, so no zero-by-nonintegrability integral
can create it. Family sizes exclude the empty type and zero averaging denominator.
Every probability has finite mass. The Gaussian variance parameter is one,
so its own zero-variance Dirac convention is not used. There is no log, rpow,
natural subtraction, inverse, partial-function default, `sInf`/`sSup`, or
`liminf`/`limsup` in this closure; `Phi` is a genuine normal cdf.
