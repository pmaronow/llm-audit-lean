# Blind reading of the challenge

This file was written from `SAP/P001d/Defs*.lean`, `SAP/P001d/Defs/*.lean`, the Challenge files, and Mathlib sources, before reading either `claims.json` or `record.json`. The descriptions below concern theorem types, independently of their docstrings or proofs.

## Definitions and conventions followed to Mathlib

All finite indices start at zero: `Fin n` is `{0,...,n-1}`. All unspecified real integrals are Lebesgue integrals. An integral over a set uses the restricted measure. All displayed sums over `Fin n` include every index, with multiplicity when observations coincide. Arithmetic in the formulas below is real arithmetic unless indicated otherwise.

* `prob μ A = (μ A).toReal`. Measures take values in the extended nonnegative reals; `toReal` sends infinity to zero. On a probability space this is the usual real probability, including the measure's value on arbitrary sets (the theorem types do not separately require measurability of each event).
* `CP μ Z c` means: for every real ε>0, `μ{ω : ε ≤ dist(Z_n(ω),c)}` tends to zero as the natural index n tends to infinity. For real variables this is the absolute difference. Limits use `Filter.Tendsto`, `atTop` and the ordinary neighborhood filter.
* `cdf μ X x = prob μ {ω : X(ω) ≤ x}`. `CD μ Z ν` means: for every real x at which the real function `t ↦ prob ν (-∞,t]` is continuous, `cdf μ Z_n x` tends to `prob ν (-∞,x]`. No further condition is part of `CD` itself.
* `IID μ X` means all `X_i` are measurable, their generated sigma algebras are jointly independent (finite intersections of events have product probability), and every `X_i` has the same pushforward measure as `X_0`. Mathlib's `IdentDistrib` also requires both variables to be almost everywhere measurable. `IndepFun` means independence of the two generated sigma algebras.
* `IsCEF μ X Y m` means that m is globally measurable, Y and `m∘X` are integrable, and, for every measurable subset A of X's codomain, `∫_{X⁻¹(A)}Y dμ = ∫_{X⁻¹(A)}m(X) dμ`. Measurability of X is not included in this definition; relevant theorem hypotheses supply it. This is an event-integral description of a conditional-mean version, not pointwise conditioning on each value of X.
* Mathlib's real Bochner integral is zero when its integrand is not integrable. `Integrable` includes almost everywhere strong measurability and finite integral of the norm. `MemLp Z 2 μ` means almost everywhere strong measurability and finite second absolute moment. `AEMeasurable` allows equality almost everywhere to a measurable representative.
* `variance Z μ` is the extended integral of `|Z-EZ|²`, converted with `toReal`; infinite variance is therefore represented by zero. `covariance U V μ = ∫(U-EU)(V-EV)dμ`. In the square-integrable regimes used here these are ordinary variance and covariance.
* `gaussianReal a v`, where v is a nonnegative real, is the normal law with mean a and **variance** v. It is a Dirac measure at a if v=0, and otherwise the measure with its normal density. All Gaussian limits in these types have strictly positive variance.
* `uniformLaw a b` is Lebesgue measure with density `(b-a)⁻¹` on the closed interval `[a,b]`, zero elsewhere, converted by `ENNReal.ofReal`. For a<b it is the usual uniform probability law. The definition is total even for other endpoints, but the statements use only a<b.
* For data `x : Fin n → ℝ`, write `M(x)=n⁻¹∑_i x_i`. Let A_n be the set of all maps `a : Fin n → Fin n`. `bootMean T x = n^{-n}∑_{a∈A_n}T(x∘a)` and `bootVar T x = n^{-n}∑_{a∈A_n}(T(x∘a)-bootMean T x)²`. Thus the bootstrap law draws n indices independently and uniformly, including repetitions. For n>0 the denominator is its actual cardinality n^n. The definitions also exist at n=0 by Lean's empty-sum and zero-power conventions.
* `firstSample X n ω` is `(X_0(ω),...,X_{n-1}(ω))`. `bootstrapTestMean T x f` is `n^{-n}∑_{a∈A_n} f(√n(T(x∘a)-T(x)))`. `BootstrapWeakCP μ X sizes T ν` quantifies first over every continuous real f and then assumes the existence of a real bound C with `|f(t)|≤C` for all t. For each such f, the displayed bootstrap average, evaluated on the first `sizes(k)` observations, converges in μ-probability to `∫f dν`. It is a test-function condition; it asserts neither almost sure convergence nor a uniform quantifier over f inside the probability limit.
* Write `D_{K,h,x}(u) = n⁻¹∑_i K((u-x_i)/h)/h` for `kernelDensity`, and `F_{K,h,x}(u)=∫_{(-∞,u]}D_{K,h,x}(t)dt` for `kernelCDF`. Division is totalized, but the general statements require n>0 and h>0.
* `signedKernel(t)` is 1 on `|t|≤1`, -1/2 on `1<|t|≤2`, and 0 elsewhere. `rectangleKernel(t)` is 1/2 on `|t|≤1`, and 0 elsewhere.
* `sampleMedian x` sorts the full list of n observations in nondecreasing order and takes the zero-based element at natural index `n/2`, using default 0 if missing. It is the middle observation at positive odd n and the upper middle observation at positive even n; it is 0 for n=0.
* Let H denote `heavyBootstrapLaw`: one half times U[-1,1], one quarter times the law of `2^(1/U²)` for U uniform on [0,1], and one quarter times the law of its negative. The exponent is a real exponent. The value at U=0 uses real division by zero, but that endpoint has zero mass.
* Put `a(x)=n⁻¹ #{i:x_i≤0}`. `regularHeavyStatistic x` is `a(x)-1/2` when `a(x)∈[1/4,3/4]`, and otherwise `sampleMedian x`. For an arbitrary real function G, `regularHeavyFunctional G` is `G(0)-1/2` on the same interval condition, and otherwise the real `sInf {x:1/2≤G(x)}`. This infimum is totalized; no CDF property is required in its definition.
* `Filter.limsup u atTop` is the real infimum of the eventual upper bounds of u. For a bounded real sequence this is the usual limsup. The only explicit limsup below is of probabilities in [0,1].
* Matrices have real entries; `mulVec` and matrix multiplication are the usual finite sums. The matrix inverse is Mathlib's nonsingular inverse, which becomes zero for a nonunit determinant. Over ℝ, `IsUnit A.det` means `det A≠0`, and then this inverse is the ordinary inverse. `olsCoef X Y=(XᵀX)⁻¹XᵀY`; `olsRSS X Y b=∑_i(Y_i-(Xb)_i)²`.
* `robustCov X e=(XᵀX)⁻¹[Xᵀdiag(e_i²)X](XᵀX)⁻¹`; `classicalCov X s2=s2(XᵀX)⁻¹`; `coefficientSE V k=√(V_{kk})`. Real square root is zero on negative inputs. `populationGram μ X` has entries `E[X_jX_k]`; `populationMeat μ X ε` has entries `E[ε²X_jX_k]`.
* Mathlib `deriv f x` is the derivative when it exists and zero otherwise. `ConvexOn ℝ univ f` means the domain is convex and `f(ab+(1-a)c)≤af(b)+(1-a)f(c)` for all coefficient vectors b,c and a∈[0,1].

Relevant Mathlib definitions were inspected in `Probability/Independence/Basic.lean`, `Probability/IdentDistrib.lean`, `Probability/Moments/{Variance,Covariance}.lean`, `Probability/Distributions/{Gaussian/Real,Uniform}.lean`, `MeasureTheory/Function/{LpSeminorm/Defs,L1Space/Integrable}.lean`, `MeasureTheory/Measure/{Map,WithDensity}.lean`, `MeasureTheory/Integral/Bochner/Basic.lean`, `Order/LiminfLimsup.lean`, `LinearAlgebra/Matrix/NonsingularInverse.lean`, and `Analysis/{Calculus/Deriv/Basic,Convex/Function}.lean`.

## SAP.P001d.T58

There are no hypotheses or external parameters. The specified signed kernel is even, integrable, and has integral 1. Moreover, for every real a, its density estimate with the one-observation data vector constantly a and bandwidth 1 equals `signedKernel(u-a)` at every real u, and its integrated estimate at a-1 equals -1/2. The quantifier on a precedes the conjunction of the density identity (for all u) and the integral value.

## SAP.P001d.T59

For every natural n>0, every deterministic real data vector x of length n, and every real function K: if K≥0 Lebesgue almost everywhere, `∫K=1`, and `K(t)=K(-t)` for every t, then for every h>0, `D_{K,h,x}≥0` almost everywhere, `∫D_{K,h,x}=1`, and `F_{K,h,x}` is nondecreasing and continuous on all ℝ, tends to 0 at -∞, and tends to 1 at +∞. Integrability of K is not an explicit hypothesis; the nonzero Bochner integral entails it. No randomness, distinctness, or boundedness of the observations is assumed.

## SAP.P001d.T60

For every n>0, every real length-n data vector x, and every h>0, both following assertions hold. First, for every Lebesgue-integrable real K and every real u,

`F_{K,h,x}(u) = n⁻¹∑_i ∫_{(-∞,(u-x_i)/h]}K(t)dt`.

Second, for every real u such that `x_i≠u-h` for every i,

`D_{rectangleKernel,h,x}(u) = [(n⁻¹∑_i 1{x_i≤u+h})-(n⁻¹∑_i 1{x_i≤u-h})]/(2h)`.

No nonnegativity, normalization or symmetry assumption on K is used in the first assertion. The endpoint exclusion applies only to the second assertion and only to the boundary u-h.

## SAP.P001d.T61

For every type Ω with a sigma algebra, every probability measure μ on it, and every sequence X of real random variables: if `IID μ X` and `μ.map X_0=H`, then the following conjunction holds.

1. Along sizes n=2k+1, `√n sampleMedian(firstSample X n)` converges in distribution to N(0,4), and its centered bootstrap law satisfies `BootstrapWeakCP` with the same limit. For every natural n, if n is odd and n≥5 then `P(5<n bootVar sampleMedian(firstSample X n))≥3/16`. Also `n bootVar sampleMedian(firstSample X n)` along n=2k+1 does not converge in probability to 4.
2. For every arbitrary function G:ℝ→ℝ with `|G(u)-cdf H id u|<1/4` for every real u, `regularHeavyFunctional G-regularHeavyFunctional(cdf H id)=G(0)-cdf H id 0`. Along n=2k+1, `√n regularHeavyStatistic(firstSample X n)` converges in distribution to N(0,1/4). For every odd n≥5, `P(5<n bootVar regularHeavyStatistic(firstSample X n))≥3/16`. Along n=2k+1 this scaled bootstrap variance does not converge in probability to 1/4.

There is no bootstrap weak-convergence assertion for `regularHeavyStatistic` in the second branch, no identification of that statistic with `regularHeavyFunctional` on empirical CDFs in the conclusion, and no full-size marginal limit. The theorem is universally quantified over Ω, not an assertion that every Ω supports the required IID sequence.

## SAP.P001d.T62

For every measurable Ω and probability μ, the following four assertions hold, in this order.

1. For every measurable real sequence X, every statistic family T with each map `T_n:ℝ^n→ℝ` measurable (including n=0), and every real φ>0: if `BootstrapWeakCP μ X (n↦n+1) T N(0,φ²)`, define for n≥0 the centered bootstrap variable `Z*=√(n+1)(T(x∘a)-T(x))`, conditional finite average `E*`, and x=the first n+1 observations. Then

   `(for every ε>0, lim_{K∈ℕ→∞} limsup_{n→∞} P(ε < E*[Z*² 1{K<|Z*|}])=0)`

   is equivalent to `(n+1)bootVar T(x)→φ²` in probability. In addition, if the latter variance convergence holds, then `√(n+1)√(bootVar T(x))→φ` in probability. The natural cutoff K is inside the outer limit, after ε; the n-limsup applies to probabilities, not to an unbounded second moment. IID is not assumed in this assertion.
2. For every n>0 and every real x of length n,

   `n bootVar finiteSampleMean x = n⁻¹∑_i x_i²-M(x)²`.
3. For every IID real sequence X with `X_0∈L²(μ)` and `variance X_0 μ>0`, `(n+1)bootVar finiteSampleMean(firstSample X (n+1))` converges in probability to `variance X_0 μ`; its standard-error counterpart `√(n+1)√bootVar` converges to `√(variance X_0 μ)`.
4. For every IID real sequence X, then every real m, real function f and δ>0: suppose the law of X_0 restricted to `(m-δ,m+δ)` equals Lebesgue measure on that interval weighted by `ofReal f`; f≥0 there; f is almost everywhere measurable for that restricted Lebesgue measure; f is continuous at m and f(m)>0; `F(m)=1/2`, `F(u)<1/2` for every u<m and `F(u)>1/2` for every u>m. Then for every real η>0 such that `E|X_0|^η<∞` (integrability is explicit), `(n+1)bootVar sampleMedian(firstSample X (n+1))→1/(4f(m)²)` in probability and `√(n+1)√bootVar→1/(2f(m))` in probability. This includes even sample sizes, using the upper middle order statistic as defined above.

## SAP.P001d.T63

Define the average of cluster i, of fixed natural size m, as `A_i=m⁻¹∑_{j<m}X_{ij}`; the first-l cluster mean as `C_l=(lm)⁻¹∑_{i<l}∑_{j<m}X_{ij}`; and the first-l sample mean of a real sequence as `l⁻¹∑_{i<l}A_i`.

For every measurable Ω, probability μ, natural m>0, and IID sequence of measurable real cluster vectors `X_i:Ω→ℝ^m` such that every coordinate of X_0 lies in L²(μ), all following hold: the A_i are IID; for every l>0, `C_l=sampleMean A l` as functions on Ω and `E C_l=E A_0`; `E A_0=m⁻¹∑_j E X_{0j}`; for every l>0,

`Var(C_l)=Var(A_0)/l = [∑_{j<m}∑_{k<m}Cov(X_{0j},X_{0k})]/(lm²)`;

and `C_{n+1}→E A_0` in probability. Coordinates within one cluster need not be independent or identically distributed.

## SAP.P001d.T64

For every measurable Ω, there is a conjunction of two assertions.

1. For every probability μ, natural m>0, IID sequence of m-vectors X with each coordinate of X_0 in L², natural l>0, and real s,ρ: assume s>0, ρ∈[0,1], `Cov(X_{0j},X_{0j})=s` for every j, and `Cov(X_{0j},X_{0k})=ρs` for every distinct j,k. Then

   `Var(C_l)=s/(lm)·(1+ρ(m-1))`,

   and, if ρ=0, this variance is `s/(lm)`; if ρ=1, it is `s/l`.
2. For all naturals l,m with l>0 and m>0 and every deterministic array `x:Fin l→Fin m→ℝ`, let R be the product over i<l of the discrete uniform probability on `Fin l`. R is a probability measure on all maps `a:Fin l→Fin l`; the coordinate draws `a↦a_i` are jointly independent; for every i,j, `P_R(a_i=j)=1/l`; for every whole draw a, `P_R(b=a)=(1/l)^l`; the number of position pairs `(i,j)` is lm; and for every a,i,j, `blockResample x a i j=x(a_i,j)`. The latter resampling function is defined by this identity. No covariance or consistency assertion about the resampled estimator occurs here.

## SAP.P001d.T65

For all naturals n,K with n>0, every real n-by-(K+1) design X and response vector Y: assume `det(XᵀX)≠0` and `X_{i0}=1` for every i. With `β=(XᵀX)⁻¹XᵀY` and `e=Y-Xβ`, for every coefficient vector b, `RSS(β)≤RSS(b)` and `RSS(b)=RSS(β)↔b=β`. Also `Xᵀe=0`, `n⁻¹∑_i e_i=0`, and for every coefficient index k both `n⁻¹∑_i e_iX_{ik}=0` and `n⁻¹∑_i e_iX_{ik}-(n⁻¹∑_i e_i)(n⁻¹∑_i X_{ik})=0`. K may be zero; the design always has at least the intercept column.

## SAP.P001d.T66

For all naturals n,K with n>0, every real n-by-(K+1) matrix X with `det(XᵀX)≠0`, every arbitrary residual vector e, every real s2≥0, and every coefficient index k: if the selected robust and classical covariance diagonals are both nonnegative, then

`coefficientSE(robustCov X e,k)=√(robustCov X e)_{kk}`

and the corresponding equality holds for `classicalCov X s2`. Each equality is the definition of `coefficientSE`. There is no assertion that e is an OLS residual, that s2 is an estimated variance, that these matrices estimate any population covariance, or that their selected diagonals follow from the other hypotheses.

## SAP.P001d.T67

For every measurable Ω, probability μ, natural K, and measurable `X:Ω→ℝ^K`, then every real random variable ε∈L²(μ) with `IsCEF μ X ε 0`, then every real σ2≥0: assume `IsCEF μ X ((ε-0)²) (constant σ2)`; every `X_jX_k` is integrable; every `ε²X_jX_k` is integrable; and the population Gram matrix Q has nonzero determinant. Then `IsCEF μ X (ε²) (constant σ2)`, the population meat M equals σ2Q, and `Q⁻¹MQ⁻¹=σ2Q⁻¹`. K is allowed to be zero. The conditional-square premise differs from the first conclusion only by subtracting zero.

## SAP.P001d.T68

For every measurable Ω, probability μ, real random variables X,W that are both measurable and independent, if W is integrable and EW=0, then for every globally measurable `g:ℝ→ℝ` such that g∘X is integrable, `IsCEF μ X (g(X)+W) g`. Thus the conclusion includes integrability of signal plus noise, integrability of the signal, measurability of g, and the conditional event-integral identities.

## SAP.P001d.T69

Put `m(x,y)=-x` if y≤4/5 and `m(x,y)=9x` otherwise. For every measurable Ω, probability μ, and real variables X1,X2,Y: assume X1,X2 are measurable and independent, each has law U[0,1], Y is integrable, and `IsCEF μ (X1,X2) Y m`. Then for all real x,y the derivative in the first coordinate is -1 if y≤4/5 and 9 otherwise; EX1=EX2=1/2; `E[∂₁m(X1,X2)]=1`; `∂₁m(EX1,EX2)=-1`; and these last two quantities differ. No derivative of Y, no sample estimator, and no independence involving Y is asserted.

## SAP.P001d.T70

For every natural n>0, every natural degree J, and every pair of real length-n data vectors x,y, define the polynomial design `P_{ik}=x_i^k` for k=0,...,J. The following hold: for every real B there is a coefficient vector b for which `∑_i(y_i-∑_k b_kx_i^k)<B`; there is no b whose value of this unsquared criterion is ≤ the value at every coefficient vector c; for every b, `olsRSS P y b=∑_i(y_i-∑_k b_kx_i^k)²`; and, if `det(PᵀP)≠0`, for every b the inverse-Gram coefficient minimizes this squared criterion, with equality exactly at that coefficient. The noninvertible case is included in the first three assertions.

## SAP.P001d.T71

For coefficients `b:Fin(K+1)→ℝ`, let `p(b)=∑_{k=1}^K|b_k|`, omitting coordinate 0. Let `L_λ(b)=RSS(b)/n+λp(b)`.

For all naturals n,K with n>0, all real n-by-(K+1) designs X and responses Y: for every b, `L_0(b)=RSS(b)/n`; for every b, b minimizes L_0 globally if and only if it minimizes RSS globally; for every b,c, p(b)≥0, for every real a `p(ab)=|a|p(b)`, and `p(b+c)≤p(b)+p(c)`; for the unit intercept vector e0, p(e0)=0 and its full coordinate absolute-value sum is 1; and for every real λ≥0, L_λ is convex on all coefficient vectors. No invertibility or literal intercept-column condition is imposed on X. For K=0 the penalty is the empty sum, identically zero.

## SAP.P001d.T72

Define `q_{a,s}(y)=exp(-(y-a)²/(2s²))/(s√(2π))`. For every natural K, coefficient and covariate vectors x,b of length K+1, and every real s>0, with `a=∑_k x_kb_k`, q is pointwise nonnegative and Lebesgue integrable; `y↦yq(y)` is Lebesgue integrable; `∫q=1`; and `∫yq(y)dy=a`. In addition, for the same a the totalized formula with s=0 has integral 0 and that integral differs from 1. This is a density-and-moment assertion at a fixed x, without random covariates or a conditional law premise.

## SAP.P001d.T73

There are no hypotheses. On four equally weighted indices let `X=(0,0,1,1)`, `Y=(1,3,0,6)` and `e_i=Y_i-(2+X_i)`. `finiteMean` is the average over the four indices, `finiteProb` is the fraction satisfying a predicate, `finiteCov` is the average centered product, and `finiteCond Y X x` divides the weighted sum of Y over `{X=x}` by the mass of that event (zero division is totalized outside the specified cases). The assertion is the conjunction:

`P(X=0)=P(X=1)=1/2`; `E[Y|X=0]=2`; `E[Y|X=1]=3`; `Ee=0`; `Cov(X,e)=0`; `P(X=0 and |e|=1)=1/2`; `P(X=0)P(|e|=1)=1/4`; and `1/2≠1/4`.

Both specified conditioning events have positive mass. No general conditional-expectation object or general independence predicate is used in this theorem.

## SAP.P001d.T74

For every pair of types Ω,E with sigma algebras and every probability μ on Ω, the following two assertions hold; the conjunction also includes the entire unconditional `T73Statement` just read.

1. For every measurable X:Ω→E, Y∈L²(μ), and function m:E→ℝ: if `IsCEF μ X Y m` and m∘X∈L²(μ), let e=Y-m(X). Then `IsCEF μ X e 0`; Ee=0; for every globally measurable g:E→ℝ with g∘X∈L²(μ), `Cov(g(X),e)=0`; and for every v:E→ℝ such that `IsCEF μ X (e²) v`, also `IsCEF μ X ((e-0)²) v` and `Var(e)=E[v(X)]`. The last CEF identity is just subtraction of zero. The existence of v is a premise to that subassertion, not a conclusion.
2. For every measurable X:Ω→E and measurable Y:Ω→ℝ, then every globally measurable m:E→ℝ and real s>0: if the joint law of (X,Y) is the image of `(law X)⊗N(0,s²)` under `(x,z)↦(x,m(x)+z)`, then `law(Y-m(X))=N(0,s²)` and X is independent of Y-m(X). No conditional law at every individual covariate value is asserted. No moment condition on m is imposed in this second assertion.

## SAP.P001d.T75

For every natural K, real covariate and coefficient vectors x,b of length K+1, and every real function h:ℝ→ℝ satisfying `0≤h(t)≤1` for every real t, define `binaryChoiceMean x b h=0·(1-h(∑x_kb_k))+1·h(∑x_kb_k)`. Then this expression equals `h(∑x_kb_k)` and belongs to [0,1]. There is no probability measure or random variable in the theorem type. It computes the first moment of the supplied two weights, whose nonnegativity and unit sum follow arithmetically from the premise.

## SAP.P001d.T76

Define `ℓ(b,s)=-n log s-(n/2)log(2π)-RSS(b)/(2s²)`. For all naturals n,K with n>0, all real n-by-(K+1) designs X and responses Y, both assertions hold. First, for every bstar and every s>0, `(for every b, ℓ(b,s)≤ℓ(bstar,s))` if and only if `(for every b, RSS(bstar)≤RSS(b))`. Second, for every bstar and s,t>0, `(for every b, ℓ(b,s)≤ℓ(bstar,s))` if and only if `(for every b, ℓ(b,t)≤ℓ(bstar,t))`. Thus the optimizer sets at fixed positive scales agree. This asserts neither an explicit optimizer nor uniqueness, existence of a joint optimizer in (b,s), a likelihood-density product identity, nor a statistical sampling model.
