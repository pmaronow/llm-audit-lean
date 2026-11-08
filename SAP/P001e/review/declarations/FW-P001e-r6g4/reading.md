# Blind reading

This file was initially saved before opening `claims.json` or `record.json`. A later scratch check clarified the `Fin` numeral convention below; this technical clarification changed no mathematical reading or claim-stage decision. I read the four Challenge docstrings and statements, every source definition in their supplied closures, and all 66 distinct generated proof/constructor declarations in those closures. The latter were printed by Lean in `scratch/ClosurePrint.out`; they are numeral/finite-index typeclass witnesses, a standard-Borel instance for the real line, finite-measure/outer-measure instances, a scalar-tower instance, and the constructor of the explicitly described model structure. They add no mathematical assumptions. Line numbers below refer to the supplied sources, not the closure's approximate locations.

## SAP.P001e.T92

The statement is a closed conjunction with no universally quantified data or hypotheses. Index the six units by `Fin 6`, starting at zero. The real vectors are

* Y = (2,5,3,10,2,0), D = (1,0,1,1,1,0);
* X1 = (1,8,10,3,5,7), X2 = (7,2,3,1,2,0);
* b = (13563,6178,-759,-1778)/2437, indexed by `Fin 4`.

Let A be the real 6-by-4 matrix whose row i is (1,D_i,X1_i,X2_i). Define the fitted value at arbitrary real (x,z,d) to be

    q(x,z,d) = b_0 + b_1 d + b_2 x + b_3 z.

For any real six-vector v, define

    P(v) = (sum over D_i=1 of [Y_i-q(v_i,X2_i,0)]
            + sum over D_i≠1 of [q(v_i,X2_i,1)-Y_i])/6,
    F(v) = sum_i [q(v_i,X2_i,1)-q(v_i,X2_i,0)]/6.

The vector used in these two imputation calculations is v=(1,8,9,3,5,7), whereas the regression matrix uses X1 with third entry 10. The six conclusions, in order, are:

1. det(AᵀA) is a unit of the real field, equivalently is nonzero.
2. (AᵀA)⁻¹(AᵀY)=b, using matrix multiplication and matrix-vector multiplication over the real field.
3. P(v)=12103/4874.
4. F(v)=6178/2437.
5. 12103/4874−6178/2437=−253/4874 in the real field.
6. P(v)≠F(v).

The Challenge docstring calls this a refutation of the printed claim through disagreement of the two printed imputation estimates. The formal statement itself is the above collection of numerical facts, including certification of the regression coefficients from the original design.

Junk conventions: real division by zero is totalized to zero, but every actual denominator here is the positive integer 6, 2437, or 4874. Matrix inverse is the adjugate divided by the determinant and returns the zero matrix at a singular real matrix; conclusion 1 excludes that case for this fixed design. A numeral at type `Fin n` is reduced modulo n; its generated `NeZero` witness ensures a nonzero modulus, not a bound on an arbitrary numeral. Every literal subscript used here is already in range (0 through 5 or 0 through 3), so no lookup wraps and there is no partial/default lookup. Natural numeral casts have their ordinary real values. No truncated subtraction, logarithms, roots, powers with exceptional domains, integrals, extrema, or limit operators occur. All index types are explicitly nonempty.

## SAP.P001e.T93

The statement is the conjunction of four independent clauses. Its quantifiers do not identify the arbitrary population coefficients with a random finite-sample fit.

### Shared conditional-mean and independence predicates

For a measurable space Ω, a measure μ, a covariate map X:Ω→E, an outcome V:Ω→ℝ, and m:E→ℝ, the SAP conditional-mean predicate means precisely: m is measurable; V and m∘X are Bochner integrable for μ; and for every measurable A⊆E,

    integral over X⁻¹(A) of V dμ = integral over X⁻¹(A) of m(X) dμ.

Thus it specifies an integrable measurable version of the conditional mean through the defining integral identities, including when μ is a restricted, unnormalized finite measure.

The SAP conditional-independence predicate for maps U:Ω→F and V:Ω→G given measurable X says: for every measurable A⊆F and B⊆G, the conditional expectation of the indicator of {U∈A,V∈B} given the sigma-algebra pulled back by X equals, μ-almost everywhere, the product of the corresponding two conditional indicator expectations. The quantifier over sets is outside the almost-everywhere quantifier, as usual. Conditional expectations are Mathlib's conditional expectations relative to that pulled-back sigma-algebra.

### Clause 1: fitted contrast

For every natural K, all real a,b, all real coefficient vectors c and covariate vectors x indexed by `Fin K`, define

    q(a,b,c,x,d) = a + bd + sum_{k∈Fin K} x_k c_k.

The assertion is q(a,b,c,x,1)−q(a,b,c,x,0)=b, for every x, without fitting or probabilistic assumptions.

### Clause 2: finite sample

For every natural n,K, real vectors Y,D on `Fin n`, covariates X:`Fin n→Fin K→ℝ`, assume D_i∈{0,1} for every i, and that at least one unit belongs to each arm. Then for every real a,b and c:`Fin K→ℝ` that globally minimize

    RSS(a,b,c) = sum_i [Y_i-q(a,b,c,X_i,D_i)]²

over all real a',b',c', put

    g_i=a+sum_k X_ik c_k, e_i=Y_i−g_i−bD_i,
    C=[sum_{D_i=1} e_i−sum_{D_i=0} e_i]/n,
    Aall=sum_i [q(a,b,c,X_i,1)−q(a,b,c,X_i,0)]/n,
    Amiss=[sum_{D_i=1}(Y_i−g_i)+sum_{D_i=0}(g_i+b−Y_i)]/n.

For d∈ℝ, the completed column is W_d(i)=Y_i if D_i=d, and q(a,b,c,X_i,d) otherwise. The conclusion consists of all of:

* n>0, sum_i e_i=0, and sum_i e_iD_i=0;
* Aall=b;
* [sum_i q(a,b,c,X_i,1)]/n−[sum_i q(a,b,c,X_i,0)]/n=Aall;
* [sum_i W_1(i)]/n−[sum_i W_0(i)]/n=Amiss;
* Amiss=b+C, C=0, and Amiss=b.

No rank, uniqueness, stochastic sampling, or causal hypothesis occurs in this finite clause. Global least squares is defined directly by comparison of RSS values, not an inverse-matrix formula.

### Clause 3: population

For every measurable Ω, every probability measure μ on Ω, every natural K, maps X:Ω→ℝ^K and D,Y0,Y1:Ω→ℝ, assume in this order:

* X,D,Y0,Y1 are measurable; Y0,Y1 are integrable;
* D is in {0,1} μ-almost surely;
* p:ℝ^K→ℝ is a conditional-mean version of D given X in the above integral sense;
* there exists a real η>0 such that η<p(X)<1−η μ-almost surely;
* (Y0,Y1) and D are conditionally independent given X in the above indicator sense.

Then quantify over every real a,b and c∈ℝ^K for which q(a,b,c,x,d) is an exact conditional-mean version of Y=Y1D+Y0(1−D) given (D,X). In particular this last hypothesis explicitly requires Y and q(a,b,c,X,D) to be integrable. Put m_d(x)=q(a,b,c,x,d) and τ=Y1−Y0. The conclusions are:

1. m_0 and m_1 are conditional-mean versions of Y given X under μ restricted to {D=0} and {D=1}, respectively.
2. m_0 and m_1 are conditional-mean versions of Y0 and Y1 given X under μ.
3. x↦m_1(x)−m_0(x) is a conditional-mean version of τ given X, and so is the constant b.
4. The Mathlib conditional expectation of τ given the pulled-back X sigma-algebra equals b μ-almost everywhere.
5. For every measurable integrable conditional-mean version t:ℝ^K→ℝ of τ given X, for μ.map X-almost every x, simultaneously t(x)=m_1(x)−m_0(x), m_1(x)−m_0(x)=b, and t(x)=b.
6. The Bochner integral of τ for μ equals b.

The uniform lower and upper propensity bounds are substantive quantitative assumptions. The predicate does not impose separate moments on each coordinate of X.

### Clause 4: six-unit calculation

Use all fixed data A,Y,D,X1,X2,b and q from the T92 reading, with X1's third entry 10. Define V_{s,d}(i) to retain Y_i exactly when s=true and D_i=d, and otherwise use q(X1_i,X2_i,d). The closed assertions are:

* (D_2,X1_2,X2_2)=(1,10,3);
* V_{true,0}=(q(1,7,0),5,q(10,3,0),q(3,1,0),q(5,2,0),0);
* V_{true,1}=(2,q(8,2,1),3,10,2,q(7,0,1));
* V_{false,0} and V_{false,1} have respectively all six entries q(X1_i,X2_i,0) and q(X1_i,X2_i,1), in the displayed data order;
* det(AᵀA) is a real unit, (AᵀA)⁻¹AᵀY=b, and b=(13563,6178,−759,−1778)/2437;
* both P(X1) and F(X1) from the T92 reading equal 6178/2437;
* the difference of the two completed-column means equals 6178/2437, both when s=true and when s=false.

The docstring additionally explicitly describes the strong-ignorability, uniform-overlap, and exact-population-CEF assumptions and says usual measure-theoretic conditions are assumed. It makes no computational-cost or statistical-consistency assertion.

Junk conventions: sample division is in ℝ with denominator the natural number n cast to ℝ; both nonempty arms force n≥2. K=0 gives an empty covariate sum, the valid intercept-plus-treatment model. The fixed numerical inverse and denominators have the protection described for T92. Bochner integrals are zero by definition for a nonintegrable integrand, but the conditional-mean predicates explicitly require integrability and all further integrands are integrable under the stated assumptions and conclusions. Mathlib conditional expectation returns zero outside its integrability/sub-sigma-algebra/sigma-finiteness conditions; here indicator integrands are bounded measurable functions on a probability space, X is measurable, and the pulled-back restriction is finite. The direct τ conditional expectation has integrable τ. Version values on null sets remain arbitrary; all population identification is stated almost everywhere. No `toReal` of infinity, empty extrema, limit operators, exceptional real functions, truncated subtraction, or partial lookups occur.

## SAP.P001e.T94

This is a conjunction of three independently universally quantified statements. All expectations are Bochner integrals of real functions. The conditional-mean and conditional-independence predicates have exactly the expansions given in the T93 reading.

### Conditional-density and model definitions

A conditional-density version for measurable-space-valued Z and real Y under a finite measure μ is a real function f(z,y) such that (z,y)↦f(z,y) is measurable, f(z,y)≥0 for every z,y, and for μ.map Z-almost every z the Mathlib conditional distribution of Y given Z=z is the measure whose density with respect to real Lebesgue measure is ENNReal.ofReal(f(z,y)). Thus for measurable B⊆ℝ its mass is the lower integral of that nonnegative density over B. The real outcome space has the standard Borel structure. The equality is between measures, not just their means; it implies density normalization at almost every conditioning value.

For natural K and maps X:Ω→ℝ^K, D,Y0,Y1:Ω→ℝ, p:ℝ^K→ℝ, the binary potential model consists of exactly: measurability of all four random variables; integrability of Y0,Y1; D∈{0,1} almost surely; p a conditional-mean version of D given X; some ε>0 with ε<p(X)<1−ε almost surely; and conditional independence of (Y0,Y1) and D given X. The measure is required to be a probability measure by every caller here.

For natural τ, g:ℝ→ℝ→ℝ^K→ℝ^τ→ℝ and a parameter θ∈ℝ^τ, put

    m(d,x,θ)=integral over y∈ℝ of y g(y,d,x,θ) dy.

A correct model means: f((d,x),y)=g(y,d,x,θ) is the above conditional-density version of Y=Y1D+Y0(1−D) given (D,X); for each d∈{0,1}, y↦y g(y,d,X(ω),θ) is Lebesgue integrable for μ-almost every ω; and ω↦m(d,X(ω),θ) is μ-integrable. These requirements concern the true parameter only.

### Clause 1: population formulas

For every measurable Ω, probability measure μ, natural K,τ, maps X,D,Y0,Y1,p satisfying the binary potential model, and every g,θ satisfying the correct-model conditions, for every real d∈{0,1}, all of the following hold. Let Y_d denote Y0 if d=0 and Y1 otherwise.

1. x↦m(d,x,θ) is a conditional-mean version of Y_d given X.
2. integral Y_d dμ = integral m(d,X,θ) dμ.
3. The latter integral equals the integral of m(d,x,θ) with respect to μ.map X.
4. For every measurable, everywhere nonnegative fX:ℝ^K→ℝ such that μ.map X is Lebesgue measure with density ENNReal.ofReal(fX), integral Y_d dμ equals the Lebesgue integral in x of m(d,x,θ) fX(x), that is, the printed iterated integral with y integrated inside x.

The optional density for X is an antecedent only of the last display. No density of X is required by the preceding conclusions.

### Clause 2: identification

Quantify first over any two measurable spaces Ω,Ω' in the specified universe, probability measures μ,ν, natural K,τ,τ', and two sets of maps X,D,Y0,Y1,p and X',D',Y0',Y1',p' satisfying the binary potential model under their respective measures. Then quantify over arbitrary (possibly different) families g,g', parameters θ,θ', and correct-model witnesses. Assume the two pushforward laws of ((D,X),Y1D+Y0(1−D)) and ((D',X'),Y1'D'+Y0'(1−D')) are equal. Conclude integral Y0 dμ=integral Y0' dν and integral Y1 dμ=integral Y1' dν. No coupling, common parameter family, or equality of unobservable laws is assumed.

### Clause 3: fitted formulas

For all natural n,K,τ with n>0, every real family g of the above arity, real sample vectors Y,D on `Fin n`, covariate sample X:`Fin n→ℝ^K`, parameter set Θ⊆ℝ^τ, and θhat∈ℝ^τ, suppose θhat∈Θ and the likelihood product at θhat dominates the product at every t∈Θ:

    product_i g(Y_i,D_i,X_i,t) ≤ product_i g(Y_i,D_i,X_i,θhat).

Suppose also each displayed y g(y,d,X_i,θhat) is Lebesgue integrable for every unit and d∈{0,1}. Define

    Mhat_d = sum_i m(d,X_i,θhat)/n,
    H_X = (n as an extended nonnegative real)⁻¹ times sum_i δ_{X_i}.

Then for every d∈{0,1}, Mhat_d equals both the explicit mean of the displayed y-integrals and integral m(d,x,θhat) dH_X. For every fixed x at which the inner y-integral is integrable, sum_{i∈Fin n} m(d,x,θhat)/n=m(d,x,θhat). Finally Mhat_1−Mhat_0 equals sum_i [m(1,X_i,θhat)−m(0,X_i,θhat)]/n. No outcome-density, nonnegativity, binary-sample-treatment, or sampling-law assumption is imposed in this algebraic estimator clause; it holds for arbitrary real g satisfying the displayed assumptions.

The docstring describes the conditional and marginal identification, the sample-indexed corrected estimator, and collapse of the printed average with a free covariate argument. It says overlap is almost sure; the expanded model additionally makes its bound uniform.

Junk conventions: Bochner integral is zero for nonintegrable functions. The inner model mean is therefore total even at exceptional x, but the population formula explicitly assumes inner integrability at μ.map X-almost every x and outer integrability; no exceptional value is identified pointwise. The fitted calculations require integrability at every sampled x and separately at any fixed x used in the free-covariate identity. `condDistrib` is a chosen regular conditional kernel, unconstrained by the observable law on null conditioning values; all density assertions are version assertions almost everywhere. It is used with measurable random variables, finite probability measures, and real outcomes, so its fallback for an invalid law is not exploited. `ENNReal.ofReal` would truncate negative real density values to zero, but everywhere nonnegativity of the true conditional and optional covariate densities excludes this. The empirical factor uses ENNReal inverse, for which 0⁻¹=∞; n>0 excludes that case and makes H_X an actual empirical probability law. All real divisions by n have n>0. K=0 or τ=0 are allowed; their function spaces are singleton zero-dimensional Euclidean spaces, not empty sample domains. No `toReal`, logs, square roots, real powers, extrema, limit operators, truncated subtraction, or partial function defaults occur. The conditional-expectation protection for the independence predicate is as in T93.

## SAP.P001e.T95

This is a closed conjunction with no free data or hypotheses. All units have indices 0 through 5. Use Y,D from T92, and scores

    s=(33/100,14/100,73/100,35/100,78/100,70/100).

The treated/respondent candidate set is R={0,2,3,4}; the control/nonrespondent set is N={1,5}. For i,j∈Fin 6 and a finite candidate set C, the unique-nearest predicate means j∈C and for every k∈C with k≠j, |s_j−s_i|<|s_k−s_i|. These are strict distance comparisons in ℝ.

The first conjunct lists all eight control-to-treatment distances:

    to unit 1 from units 0,3,2,4: 19/100,21/100,59/100,64/100;
    to unit 5 from units 0,2,3,4: 37/100, 3/100,35/100, 8/100.

The second conjunct says unit 1 has unique nearest treated donor 0 and unit 5 has unique nearest treated donor 2; unit 3 is no farther from unit 1 than any treated candidate other than 0; and its distance exceeds unit 0's by 2/100. The third says the unique nearest control donors for units 0,2,3,4 are respectively 1,5,1,5. All six selected opposite-arm donors are explicitly encoded by

    j=(1,0,5,1,5,2).

The completed control outcome is C_i=Y_i if D_i=0, otherwise Y_{j_i}; the completed treatment outcome is T_i=Y_i if D_i=1, otherwise Y_{j_i}. The remaining conclusions are

    C=(5,5,0,5,0,0), T=(2,2,3,10,2,3),
    sum_i T_i/6=22/6, sum_i C_i/6=15/6,
    sum_i (T_i−C_i)/6=7/6.

Thus the statement verifies the fixed scores, donor choices, completed columns, and arithmetic of this example. It asserts no general consistency or identification theorem for matching and does not assert that the displayed scores were fitted by a particular algorithm.

Junk conventions: all denominators are the positive integers 6 or 100; real division by zero is not reached. Distances use ordinary absolute value. The candidate sets are both nonempty, each selected donor lies in the relevant set, and nearest-neighbor claims are defined by membership plus strict comparisons, not an infimum or a choice from a possibly empty set. Numerals at type `Fin 6` are reduced modulo 6, but every displayed donor numeral is in the range 0 through 5, so none wraps; no out-of-range/default lookup occurs. There are no integrals, exceptional transcendental functions, truncated subtractions, infinities, extrema, or limit operators.
