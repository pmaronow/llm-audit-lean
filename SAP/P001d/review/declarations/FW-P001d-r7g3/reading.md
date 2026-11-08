# Blind reading

This file was written before opening `claims.json`, `record.json`, `earlier.json`, or `architect-report.md`. Sources read: all five declarations and their docstrings in `SAP/P001d/Challenge/Part2.lean`; every unit declaration listed for them in `closure.json`; and the relevant Mathlib definitions. `scratch/BlindCheck.lean` compiled and printed all the generated auxiliary declarations in the closure. Those auxiliaries prove only continuity of real scalar multiplication, elementary numeral/index facts, and the scalar-tower instance for extended nonnegative reals. They introduce no mathematical assumptions.

Notation below: `Fin n` is the set of natural numbers strictly less than n; vectors are functions on such a set. A matrix is a function of a row index and a column index. Matrix multiplication and matrix-vector multiplication are finite sums. All real-space measurable structures are Borel structures. `Integrable f μ` means that f is almost everywhere strongly measurable and its absolute value has finite integral. All integrals below are Mathlib's real Bochner integrals; a set integral uses the restricted measure. Independence means the joint probability of each pair of measurable inverse-image events is the product of their marginal probabilities.

## SAP.P001d.T68

Sources: Challenge Part2:10–16; WholeW1:217–230; Part1:31–36.

In quantifier order: for every type Ω with a measurable structure, every measure μ on Ω equipped with the assertion μ(Ω)=1, and every pair of real-valued functions X and ε on Ω, assume:

1. X and ε are measurable;
2. X and ε are independent under μ;
3. ε is integrable and ∫ε dμ=0.

For every function g:ℝ→ℝ, assume g is Borel measurable and g∘X is integrable. Write Y(ω)=g(X(ω))+ε(ω). The conclusion is the conjunction of:

1. Y is integrable;
2. g is measurable, Y and g∘X are integrable, and, for every Borel set A⊆ℝ,
   ∫_{X⁻¹(A)}Y dμ = ∫_{X⁻¹(A)}g(X) dμ;
3. g∘X equals Eμ[Y | σ(X)] μ-almost everywhere, where σ(X) is the pullback of the Borel σ-algebra by X.

Item 2 is the full unfolding of `IsCEF`; the repeated integrability assertions really occur. It specifies a conditional-mean version by its integrals, rather than a unique conditional mean at each point x. The equality in item 3 is equality of sample-space functions almost everywhere. The docstring calls g a version, and identifies this almost-sure characterization.

Junk-value audit: the Bochner integral is zero for a nonintegrable function, and conditional expectation is the zero function if its conditioning structure is not a sub-σ-algebra, its trimmed measure is not σ-finite, or its input is not integrable. Here X's measurability gives the sub-σ-algebra condition, the probability measure is finite also on the sub-σ-algebra, and integrability of Y follows from the two assumed integrabilities and is explicitly concluded. Integrability on all restricted sets follows as well. Thus these defaults do not affect the assertion. No division, roots, logarithms, inverse matrices, infima, suprema, limsups, partial indexing, or truncated subtraction occur. An empty Ω cannot carry a probability measure, so its instance is excluded by the assumptions; ordinary probability spaces do satisfy them.

## SAP.P001d.T69

Sources: Challenge Part2:18–27; WholeW1:94–139; Part3:81; Part1:12–13,31–39; all nine generated auxiliary declarations in this closure were printed in `scratch/BlindCheck.lean`.

The statement is a conjunction of two separately universally quantified propositions.

First, for every measurable type Ω, probability measure μ on Ω, and real-valued functions X₁,X₂,Y on Ω, assume, in this order:

1. X₁ and X₂ are measurable;
2. Y is integrable;
3. X₁ and X₂ are independent;
4. the pushforwards μ∘X₁⁻¹ and μ∘X₂⁻¹ each equal the measure having Lebesgue density 1 on [0,1] and 0 elsewhere;
5. with m(u,v)=-u if v≤4/5 and m(u,v)=9u otherwise, m is measurable on ℝ², both Y and m(X₁,X₂) are integrable, and, for every Borel A⊆ℝ²,
   ∫_{(X₁,X₂)⁻¹(A)}Y dμ = ∫_{(X₁,X₂)⁻¹(A)}m(X₁,X₂) dμ.

Here a pushforward is the measure obtained by taking measurable inverse images; item 5 unfolds `IsCEF`. The law in item 4 unfolds `uniformLaw 0 1`: its density is `ENNReal.ofReal (if u∈[0,1] then (1-0)⁻¹ else 0)`.

Under these hypotheses all the following hold, in order:

1. For every real u,v, the function t↦m(t,v) has derivative -1 at u when v≤4/5, and derivative 9 otherwise. This is a `HasDerivAt` assertion and includes actual differentiability, including when v=4/5.
2. μ{X₂≤4/5}=4/5 and μ{4/5<X₂}=1/5.
3. ∫X₁ dμ=1/2 and ∫X₂ dμ=1/2.
4. D(ω)=(d/dt m(t,X₂(ω))) evaluated at t=X₁(ω) is integrable.
5. ∫D dμ=(-1)μ{X₂≤4/5}+9μ{4/5<X₂}.
6. ∫D dμ=1.
7. The derivative of t↦m(t,∫X₂ dμ), at t=∫X₁ dμ, equals -1.
8. The expectation in item 6 differs from the derivative in item 7.

Each probability above is defined as `(μ A).toReal`, not as a different counting convention.

Second, for every pair of natural numbers d,n, assume n>0; then for every sample x:Fin n→(Fin d→ℝ), every fitted function mhat:(Fin d→ℝ)→ℝ, and every coordinate k∈Fin d, assume that, for every i∈Fin n, the real function t↦mhat(xᵢ+t eₖ) is differentiable at 0. Here eₖ is 1 at k and 0 elsewhere. Define νₓ=(1/n)∑ᵢδ_{xᵢ}, where the scalar is the extended nonnegative real `ENNReal.ofReal (1/(n:ℝ))`, and define Pₖ(z) as the derivative at 0 of t↦mhat(z+t eₖ). Then:

1. νₓ is a probability measure;
2. Pₖ is integrable under νₓ;
3. ∫Pₖ dνₓ = (1/n)∑ᵢPₖ(xᵢ).

These definitions unfold `wholeEmpiricalLaw`, `wholePartial`, and `wholePluginAPD` completely. The second proposition is a deterministic identity for any fitted function; it does not assert sampling consistency or how a fitted function was obtained. The index k is a coordinate, independent of the observation index i.

Junk-value audit: `deriv` is zero where a function is not differentiable. The first proposition proves `HasDerivAt` everywhere it uses this derivative. The second assumes differentiability at all sample atoms, so the values contributing to the finite measure are genuine derivatives; arbitrary derivative defaults away from its support have no effect. The sample need not consist of distinct points: repeated Dirac masses are counted repeatedly as intended. Arbitrary functions on this finite support are almost everywhere measurable, and the finite real derivative values are integrable. Bochner integrals are totalized by zero off the integrable domain, but the CEF and derivative integrabilities are stated, and the uniform pushforward laws imply integrability of X₁,X₂. `ENNReal.toReal ∞=0` does not intervene because μ is a probability measure. `ENNReal.ofReal` clips negative reals to zero, but the empirical weight is strictly positive and the uniform density nonnegative. `uniformLaw a b` in general is a total density formula and is not a uniform probability law when b≤a, but only a=0,b=1 occurs here. n=0, where 1/n=0 and the empirical measure would be zero, is explicitly excluded. When d=0 there is no k, so that coordinate-indexed assertion has no instances; positive d has many instances. All casts from natural numbers are exact casts into ℝ. The constants 4/5, 1/5, and 1/2 are real divisions by nonzero numerals. No roots, logarithms, infima, suprema, limsups, or truncated subtraction occur.

## SAP.P001d.T70

Sources: Challenge Part2:29–36; WholeW2:61–79; Part4:14–30; Part3:12–16; generated index-nonemptiness proof printed in `scratch/BlindCheck.lean`.

For natural n>0, natural degree J, real-valued sample vectors x,y:Fin n→ℝ and coefficient vector b:Fin(J+1)→ℝ, put

U(b)=∑ᵢ(yᵢ-∑_{k=0}^J bₖ xᵢᵏ),
Vᵢₖ=xᵢᵏ,
R(b)=∑ᵢ(yᵢ-∑_{k=0}^J Vᵢₖbₖ)²,
G=VᵀV,
β=G⁻¹Vᵀy.

These are the full meanings of `wholeUnsquared`, `polynomialDesign`, `olsRSS`, and `olsCoef`. Gⱼₖ=∑ᵢxᵢʲxᵢᵏ and (Vᵀy)ⱼ=∑ᵢxᵢʲyᵢ. Matrix invertibility is expressed as `IsUnit G.det`, equivalent over ℝ to det G≠0.

The statement is a conjunction of two universally quantified assertions. In the first, quantify over n, assume n>0, then quantify over J,x,y and conclude:

1. For every real lower bound B, there exists b with U(b)<B.
2. There does not exist b such that, for every c, U(b)≤U(c).
3. For every b, R(b)=∑ᵢ(yᵢ-∑ₖbₖxᵢᵏ)².
4. If det G≠0, then, for every b, R(β)≤R(b), and R(b)=R(β) if and only if b=β.

In the second assertion, separately quantify over n, assume n>0, then quantify over J,x,y and conclude:

1. For every b,
   U(b)=∑ᵢyᵢ-n b₀-∑_{r=0}^{J-1}b_{r+1}∑ᵢxᵢ^{r+1}.
2. For every b, as real a tends to +∞, U evaluated at b with its coordinate 0 replaced by a tends to -∞. Explicitly, for every real B there is a real A such that a≥A implies U(b with intercept a)≤B.
3. If det G≠0 then J+1≤the cardinality of the finite set {xᵢ:i∈Fin n}.

The last assertion gives a necessary distinct-value count. It does not assert the converse. There is no quantified degree sequence, no asymptotic sample-size statement, and no sieve rate assumption. Since every finite J is quantified, these identities and implications can be specialized at the degree chosen by any sequence. The docstring's reference to sieve rates is at this specialization level.

Junk-value audit: Matrix inversion returns the zero matrix if the determinant is not a unit; every assertion using β is protected by det G≠0, so only the genuine inverse is used. Natural powers are total, including x⁰=1 at x=0, which supplies the intercept. J=0 is allowed; its sum over `Fin J` is the empty sum 0, while `Fin(J+1)` still has coordinate 0. n=0 is excluded, so decreasing the criterion by increasing an intercept genuinely uses a positive multiplier n. n and exponents are exact natural casts/indices, not truncated differences; J-1 in the prose display denotes the empty upper range when J=0, whereas the Lean range is simply `Fin J`. `Function.update` replaces a coordinate that is present, so there is no default missing-coordinate value. `atTop`/`atBot` here are ordinary real filters, not totalized real limsup/liminf values. There are no Bochner integrals, division by a sample size, logarithms, roots, real powers, infima or suprema.

## SAP.P001d.T71

Sources: Challenge Part2:38–40; Part4:32–47; Part3:12–13; generated index-nonemptiness proof printed in `scratch/BlindCheck.lean`.

Quantifier order: for every natural n,K, assume n>0; then for every real matrix X with n rows and K+1 columns and every response vector Y:Fin n→ℝ, define

R(b)=∑_{i=0}^{n-1}(Yᵢ-∑_{j=0}^K Xᵢⱼbⱼ)²,
P(b)=∑_{j=1}^K|bⱼ|,
L_λ(b)=R(b)/n+λP(b).

These unfold `olsRSS`, `slopePenalty`, and `lassoCriterion`. The conclusions are:

1. For every b∈ℝ^{K+1}, L₀(b)=R(b)/n.
2. For every b, [for every c, L₀(b)≤L₀(c)] if and only if [for every c, R(b)≤R(c)]. Thus the minimizer sets coincide, without an existence claim.
3. For every b,c, P(b)≥0, for every real a one has P(ab)=|a|P(b), and P(b+c)≤P(b)+P(c).
4. P(e₀)=0 for the vector e₀ whose coordinate 0 is 1 and every other coordinate is 0.
5. ∑_{j=0}^K |(e₀)ⱼ|=1.
6. For every real λ≥0, L_λ is convex on the whole coefficient space. Fully unfolded: the domain is convex and for b,c in the coefficient space and a,t≥0 with a+t=1, L_λ(ab+tc)≤aL_λ(b)+tL_λ(c).

Thus P satisfies the seminorm axioms and vanishes on a nonzero intercept vector. Nothing assumes that the matrix's column 0 is actually all ones, or that the Gram matrix is invertible. The assertions are algebraic and hold for arbitrary matrices. The docstring describes these properties and identifies the exempt coordinate as the intercept.

Junk-value audit: R/n uses real division, with n>0 preventing a zero denominator. All other operations are finite real sums, multiplication, square, absolute value, and componentwise scalar multiplication. K=0 is allowed; then the slope sum is empty and P is identically zero, while the coefficient/intercept space is still one-dimensional and e₀ exists and has full ℓ¹ norm 1. The generated proof guarantees this nonempty index, not an extra assumption. n=0 is excluded; natural casts are exact. No inversion, integrals, roots, logarithms, infima/suprema, limsups/liminfs, or partial functions occur.

## SAP.P001d.T72

Sources: Challenge Part2:42–45; Part4:49–60; generated numeral fact printed in `scratch/BlindCheck.lean`.

In order: for every natural K, fixed vectors x,b∈ℝ^{K+1}, and real s>0, write m=∑_{k=0}^Kxₖbₖ and

f_{m,s}(y)=exp(-(y-m)²/(2s²))/(s√(2π)).

This unfolds `normalDensity`; √ is the nonnegative real square root and exp the real exponential. The conclusion is the conjunction of:

1. For every real y, f_{m,s}(y)≥0.
2. f_{m,s} is Lebesgue integrable on ℝ.
3. y↦y f_{m,s}(y) is Lebesgue integrable.
4. ∫ℝ f_{m,s}(y)dy=1.
5. ∫ℝ y f_{m,s}(y)dy=m.
6. With the same total formula evaluated at scale 0, ∫ℝ f_{m,0}(y)dy=0.
7. This last integral is not 1.

There are no sample-space random variables, no conditional distribution, no model assumption, and no conditional expectation conclusion. x is arbitrary and need not have x₀=1. The docstring expressly restricts the item to normalization and the first moment at a fixed covariate, together with the zero-scale diagnostic, and omits the conditional-model-to-CEF implication.

Junk-value audit: real division uses 1/0=0. For s>0, 2s² and s√(2π) are positive since π>0, so the first five conclusions use ordinary well-defined Gaussian formulas. The real square root's default on negative input is irrelevant because its only input is 2π>0. At s=0 the exponent's division evaluates to 0, the exponential is 1, and division by the normalizing denominator 0 gives f_{m,0}(y)=0 for every y. Thus the final two assertions deliberately depend on totalized division and describe this zero function; they do not describe a degenerate Gaussian point mass. Its integral is a genuine integral of the zero function. The positive-scale integrabilities are explicitly concluded, so no nonintegrable-integral default is used. There are no logarithms, real powers, infima/suprema, limsups/liminfs, matrix inverses, truncated subtraction, or partial indexing. K=0 leaves a one-coordinate dot product, not an empty coefficient space.
