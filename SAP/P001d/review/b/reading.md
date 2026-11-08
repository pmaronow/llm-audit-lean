# Blind reading of the Challenge

Saved before opening `claims.json` or `record.json`. This reading uses the Lean statements, all four Defs parts, and the Mathlib definitions they use. Challenge docstrings are commentary, not additional hypotheses. All assertions below are universally quantified unless an existential quantifier is explicitly written. All real integrals without a named measure are Lebesgue integrals.

## Shared definitions and conventions

* `prob μ A = (μ A).toReal`. Mathlib measures take values in the extended nonnegative reals; `toReal` sends infinity to zero. Every probability-space theorem here explicitly assumes `IsProbabilityMeasure μ`, meaning μ(Ω)=1, so this exceptional convention is unavailable in those theorems. A set need not be measurable to be evaluated by a measure, but the random-variable events used here are measurable under the supplied assumptions.
* `CP μ Z c` means: for every real ε>0, the real sequence μ{ω: dist(Z_n(ω),c)≥ε} tends to zero as n→∞. For real-valued Z this is convergence in probability to c, with absolute distance.
* `cdf μ X x = μ{X≤x}` (as a real number). `CD μ Z ν` means: for every real x at which t↦ν((−∞,t]) is continuous, μ{Z_n≤x} tends to ν((−∞,x]). These are CDF convergence statements, not a separately assumed Mathlib weak-convergence predicate.
* `IID μ X` means every X_i is measurable, the whole countable family is mutually independent, and, for every i, X_i and X_0 have the same pushforward measure. Mathlib `IdentDistrib` additionally includes a.e. measurability; this is already supplied by measurability here. Independence means the usual product equation for finite collections of inverse images of measurable sets, not merely pairwise independence.
* `IsCEF μ X Y m` means: m is measurable on its entire codomain E; Y and m∘X are integrable; and, for every measurable A⊆E, ∫_{X∈A}Y dμ=∫_{X∈A}m(X) dμ. The predicate itself does not require X measurable, but its uses in these statements supply that property. It specifies an integrable conditional-mean version by event integrals, rather than pointwise conditioning on null events.
* Mathlib `Integrable` includes a.e. strong measurability and finite integral of the norm. `MemLp Z 2 μ` means a.e. strong measurability and finite second absolute moment. Mathlib's Bochner integral is defined to be zero for a nonintegrable function. `variance Z μ` is the extended integral of |Z−∫Z|², converted to a real using `toReal`; it is zero when that extended variance is infinite. `covariance U V μ=∫(U−∫U)(V−∫V)dμ`, also using the totalized integral. The L² hypotheses in the moment assertions make these ordinary finite variances and covariances.
* `uniformLaw a b` has Lebesgue density 1_{[a,b]}(b−a)⁻¹, with the real density converted by `ENNReal.ofReal` (negative values are truncated to zero). In the occurrences here a<b, so this is the ordinary uniform probability law. The definition is not a uniform probability law at a=b.
* For x=(x_0,…,x_{n−1}), write S_n(X,ω)=(X_0(ω),…,X_{n−1}(ω)). `finiteSampleMean x = n⁻¹∑_i x_i`. For a statistic T on n-tuples, let the bootstrap index a range over **all** nⁿ functions {0,…,n−1}→{0,…,n−1}, each with weight n⁻ⁿ, and set x_a=(x_{a(i)})_i. Then `bootMean T x=E_*T(x_a)` and `bootVar T x=E_*[(T(x_a)−E_*T(x_a))²]`. This is the exact finite conditional bootstrap variance, centered at the bootstrap mean. `bootstrapTestMean T x f=E_*f(√n(T(x_a)−T(x)))`, centered instead at the observed statistic.
* `BootstrapWeakCP μ X sizes T ν` means: for each continuous f:ℝ→ℝ for which there exists a real C with |f(t)|≤C for every t, the conditional bootstrap average E_*f(√sizes(k)(T(S_sizes(k),a)−T(S_sizes(k)))) converges in μ-probability to ∫f dν as k→∞. The test function is chosen before the probability limit. All used sample sizes are positive.
* `kernelDensity K h x u = (nh)⁻¹∑_i K((u−x_i)/h)`, interpreted by real-field totalized division. `kernelCDF K h x u=∫_{−∞}^u kernelDensity K h x v dv`, using a restricted Lebesgue integral. Positivity of n and h is explicit wherever the general formulas are used.
* The signed kernel is K(t)=1 for |t|≤1, −1/2 for 1<|t|≤2, and 0 otherwise. The rectangular kernel is R(t)=1/2 for |t|≤1 and 0 otherwise.
* Write H for `heavyBootstrapLaw`: the mixture (1/2)Unif[−1,1]+(1/4)Law(2^(1/U²))+(1/4)Law(−2^(1/U²)), with U uniform on [0,1]. The outer power is real exponentiation, 2^r=exp(r log 2). At U=0 Lean defines 1/U²=0, making the two mapped values ±1; this affects a null event only. For U>0 the positive tail is ≥2 and unbounded. This definition uses actual pushforward measures.
* `sampleMedian x` sorts the n entries increasingly and takes the zero-based entry floor(n/2), with fallback 0 if the list is too short. Thus it is the middle order statistic for positive odd n, and the **upper** middle order statistic for positive even n. Its empty-sample value is 0.
* Put a(x)=n⁻¹#{i:x_i≤0}. `regularHeavyStatistic x=a(x)−1/2` if 1/4≤a(x)≤3/4, and `sampleMedian x` otherwise. `regularHeavyFunctional G=G(0)−1/2` if 1/4≤G(0)≤3/4, and inf{x: G(x)≥1/2} otherwise. This latter infimum is Mathlib's real `sInf`, a totalized infimum on arbitrary real sets; only the first branch is used by the local identity below.
* `gaussianReal m v` is the real Gaussian probability measure of mean m and **variance** v (v is nonnegative). At v=0 it is the Dirac measure at m. Thus `gaussianReal 0 4` has standard deviation 2, whereas `gaussianReal 0 (1/4)` has standard deviation 1/2.
* Finite vectors and matrices are indexed from zero. Matrix multiplication and `mulVec` are ordinary sums. `IsUnit A.det` over ℝ means det A≠0. Mathlib matrix inverse is the usual inverse in this case and is the zero matrix otherwise. This distinction is guarded wherever its inverse properties are claimed. `Real.sqrt` is the nonnegative square root, defined to be zero on negative arguments. `deriv` is the usual scalar derivative where it exists, and is zero otherwise.

The Mathlib source definitions checked include `Probability/Independence/Basic.lean` (and its kernel definition), `Probability/IdentDistrib.lean`, `Probability/Moments/{Variance,Covariance}.lean`, `Probability/Distributions/Gaussian/Real.lean`, `Probability/Distributions/Uniform.lean`, `MeasureTheory/Function/LpSeminorm/Defs.lean`, `MeasureTheory/Integral/Bochner/Basic.lean`, `MeasureTheory/Measure/{Map,Restrict,WithDensity}.lean`, `MeasureTheory/Constructions/Pi.lean`, `Order/LiminfLimsup.lean`, `LinearAlgebra/Matrix/NonsingularInverse.lean`, and `Analysis/Calculus/Deriv/Basic.lean`. Other algebraic and finite-list operations have their usual meanings described above.

## SAP.P001d.T58

No parameters or hypotheses. The specified signed K is even, Lebesgue integrable, and has integral 1. For every real observation a, (i) for every real x the one-observation kernel density with bandwidth 1 equals K(x−a), and (ii) its integrated estimate at a−1 equals −1/2. No monotonicity conclusion, probability claim, or other counterexample is present.

## SAP.P001d.T59

For every natural n>0, every deterministic x∈ℝⁿ, and every K:ℝ→ℝ, assume K≥0 Lebesgue-a.e., ∫K=1, and K(t)=K(−t) for every t. Then for every real h>0: the kernel density is nonnegative Lebesgue-a.e.; its integral is 1; its integrated estimate is nondecreasing and continuous on ℝ; and that estimate tends to 0 at −∞ and 1 at +∞. K integrability is not a separate hypothesis, but follows from its real Bochner integral being nonzero. No pointwise nonnegativity of K or of the estimator is asserted.

## SAP.P001d.T60

For every n>0, x∈ℝⁿ, and h>0, two assertions hold. First, for every Lebesgue-integrable K:ℝ→ℝ and every real u,

    kernelCDF(K,h,x,u) = (1/n) Σ_i ∫_{−∞}^{(u−x_i)/h} K(t) dt.

Second, for every real u such that x_i≠u−h for all i,

    kernelDensity(R,h,x,u) = [F_x(u+h)−F_x(u−h)]/(2h),

where F_x(v)=n⁻¹#{i:x_i≤v}. There is no exclusion of observations at u+h. K need not be nonnegative, even, or normalized for the first formula.

## SAP.P001d.T61

For every measurable space Ω, every probability measure μ on Ω, and every IID real sequence X with Law(X_0)=H, all the following hold.

1. Along sizes n=2k+1, √n times the sample median converges in the CDF sense to N(0,4).
2. Along those sizes the conditional weak bootstrap convergence in probability for the median holds with limit N(0,4).
3. For every natural n, if n is odd and n≥5, then μ{n bootVar(median,S_n)>5}≥3/16.
4. Along n=2k+1, n bootVar(median,S_n) does not converge in probability to 4.
5. For every function G:ℝ→ℝ, if |G(t)−F_H(t)|<1/4 for **every** real t, then regularHeavyFunctional(G)−regularHeavyFunctional(F_H)=G(0)−F_H(0). No measurability, monotonicity, or CDF requirement on G is imposed; this premise is a pointwise strict bound everywhere, not an explicit supremum norm bound.
6. Along n=2k+1, √n times regularHeavyStatistic(S_n) converges in the CDF sense to N(0,1/4).
7. For every odd natural n≥5, μ{n bootVar(regularHeavyStatistic,S_n)>5}≥3/16.
8. Along n=2k+1, n bootVar(regularHeavyStatistic,S_n) does not converge in probability to 1/4.

There is no weak-bootstrap conclusion for the regular statistic, no assertion identifying its finite-sample value with the functional of an empirical CDF, and no full-sequence even-size limit in this theorem. Its functional assertion is syntactically inside the implications about μ and X, but involves only the fixed H and G.

## SAP.P001d.T62

For every measurable Ω and every probability measure μ, the following four assertions hold.

1. For every sequence X of measurable real functions, every family T of statistics on finite real samples with T measurable for **every** natural sample size, and every real φ>0, assume conditional weak bootstrap convergence in probability along n+1 to N(0,φ²). Define

       Q_{n,K}(ω) = E_*[ Z*² 1_{|Z*|>K} ],
       Z* = √(n+1)[T(S_{n+1},a)−T(S_{n+1})].

   Then [for every ε>0, lim_{K→∞, K∈ℕ} limsup_{n→∞} μ{Q_{n,K}>ε}=0] is equivalent to [(n+1)bootVar(T,S_{n+1})→φ² in probability]. Also the latter variance consistency implies √(n+1)√bootVar(T,S_{n+1})→φ in probability. No IID assumption is made in this assertion. The `limsup` is of real probabilities in [0,1], so its real infimum definition has bounded input.
2. For every natural n>0 and every x∈ℝⁿ,

       n bootVar(finiteSampleMean,x) = (Σ_i x_i²)/n − (finiteSampleMean x)².

3. For every IID real sequence X with X_0∈L²(μ) and Var(X_0)>0, (n+1)bootVar(mean,S_{n+1}) converges in probability to Var(X_0), and its square-root version √(n+1)√bootVar converges in probability to √Var(X_0).
4. For every IID real sequence X, every real m, f:ℝ→ℝ, δ>0 satisfying: the law of X_0 restricted to (m−δ,m+δ) equals Lebesgue measure restricted there with density `ofReal(f)`; f is nonnegative at every point of that interval and a.e. measurable for its restricted Lebesgue measure; f is continuous at m and f(m)>0; F(m)=1/2, F(t)<1/2 for all t<m, and F(t)>1/2 for all t>m; and, after these choices, for every η>0 with ∫|X_0|^η dμ<∞, one has (n+1)bootVar(median,S_{n+1})→1/(4f(m)²) in probability and √(n+1)√bootVar→1/(2f(m)) in probability. The fractional moment is a separate hypothesis. The median convention here includes the upper median at even sample sizes.

## SAP.P001d.T63

For every measurable Ω, every probability μ, every natural cluster size m>0, and every IID sequence X of measurable ℝᵐ-valued clusters with each coordinate of X_0 in L², define C_i=m⁻¹Σ_j X_{ij} and M_l=(lm)⁻¹Σ_{i<l,j<m}X_{ij}. Then:

* C_i are IID.
* For every l>0, M_l equals, as a function on Ω, the ordinary l-observation sample mean of C; and E M_l=E C_0.
* E C_0=m⁻¹Σ_j E X_{0j}.
* For every l>0, Var(M_l)=Var(C_0)/l=(lm²)⁻¹Σ_{j,k}Cov(X_{0j},X_{0k}).
* M_{n+1}→E C_0 in probability as n→∞.

No independence among the coordinates inside a cluster is required.

## SAP.P001d.T64

For every measurable Ω, a conjunction of two assertions:

1. For every probability μ, m>0, and IID ℝᵐ-valued sequence X with L² coordinates in the first cluster; for every l>0 and every real s,ρ with s>0 and 0≤ρ≤1; if Cov(X_{0j},X_{0j})=s for every j and Cov(X_{0j},X_{0k})=ρs for every distinct j,k, then

       Var(M_l) = s/(lm) [1+ρ(m−1)],

   and ρ=0 implies Var(M_l)=s/(lm), while ρ=1 implies Var(M_l)=s/l. The parameter s is a variance, not a standard deviation. The expression m−1 here is real subtraction.
2. For every pair of naturals l,m>0 and every fixed X∈ℝ^{l×m}, equip all maps a:Fin l→Fin l with the product of l uniform laws on Fin l. This law is a probability measure; the coordinates a_i are mutually independent; for every i,j the probability a_i=j is 1/l; for every complete map a its singleton has probability (1/l)^l; Fin l×Fin m has cardinality lm; and for every a,i,j the defined block resample equals X_{a_i,j}. Thus each of l independent uniform selections copies an intact cluster with all m coordinates.

The second assertion does not depend on μ or any randomness in X.

## SAP.P001d.T65

For every n>0, natural K, real n×(K+1) design X and response y∈ℝⁿ, assume XᵀX invertible and X_{i0}=1 for every i. Let β=(XᵀX)⁻¹Xᵀy and e=y−Xβ; write RSS(b)=Σ_i(y_i−(Xb)_i)². Then for **every** b, RSS(β)≤RSS(b) and RSS(b)=RSS(β) iff b=β. Also Xᵀe=0, Σ_i e_i/n=0, Σ_i e_iX_{ik}/n=0 for every k, and Σ_i e_iX_{ik}/n−(Σ_i e_i/n)(Σ_i X_{ik}/n)=0 for every k. These last expressions use the empirical normalization 1/n. Singular designs are not covered, including for the residual identities.

## SAP.P001d.T66

For every n>0, K, and n×(K+1) real design X with invertible G=XᵀX; for every supplied vector e and real s²≥0; for every coefficient index k with V^R_{kk}≥0 and V^C_{kk}≥0, one has

    coefficientSE(V^R,k)=√V^R_{kk},
    coefficientSE(V^C,k)=√V^C_{kk},

where V^R=G⁻¹[Xᵀ diag(e_i²) X]G⁻¹ and V^C=s²G⁻¹. Here s² denotes the input variable named `s2`, not its square. The function coefficientSE(V,k) is **defined** as √V_{kk}, so the conclusions are definitional equalities. e is not assumed to be an OLS residual and s2 is not defined as a residual variance estimate. No equality with another covariance-estimator expression is asserted. The index k has printed one-based number k.val+1.

## SAP.P001d.T67

For every measurable Ω, every probability μ, every natural K (including zero), measurable X:Ω→ℝᴷ, and ε∈L²(μ) with IsCEF(X,ε,0); for every σ²≥0, assume IsCEF(X,(ε−0)²,constant σ²); assume X_jX_k and ε²X_jX_k are integrable for every j,k; and assume A=(E X_jX_k)_{jk} invertible. Then IsCEF(X,ε²,constant σ²), B=σ²A for B=(E ε²X_jX_k)_{jk}, and A⁻¹BA⁻¹=σ²A⁻¹. The first conclusion is the supplied conditional-square hypothesis after simplification of ε−0. The nontrivial conclusions factor the moments and simplify the population sandwich. No asymptotic sample-covariance assertion appears.

## SAP.P001d.T68

For every measurable Ω, probability μ, and measurable real X,W, assume X and W independent, W integrable, and E W=0. For every globally measurable g:ℝ→ℝ with g∘X integrable, IsCEF(X,g(X)+W,g) holds: g is a global measurable conditional-mean version of the additive model. W need not have a second moment and g need not be continuous.

## SAP.P001d.T69

For every measurable Ω, probability μ, and real random variables X₁,X₂,Y, assume X₁ and X₂ measurable and independent, each with law Unif[0,1], Y integrable, and IsCEF((X₁,X₂),Y,a) where a(x,y)=−x if y≤4/5 and 9x otherwise. Then for all real x,y, ∂₁a(x,y)=−1 if y≤4/5 and 9 otherwise; E X₁=E X₂=1/2; E[∂₁a(X₁,X₂)]=1; ∂₁a(E X₁,E X₂)=−1; and these two quantities are unequal. The derivative is only with respect to the first argument, where each branch is linear. Nothing is claimed about differentiability in the second argument or about an estimator from a sample. The conclusions are universal over admissible Y, not tied to one noise construction.

## SAP.P001d.T70

For every n>0, natural degree J, and real samples x,y∈ℝⁿ, put P_{ik}=x_i^k for k=0,…,J. Then:

* For every real B there exists b∈ℝ^{J+1} such that Σ_i(y_i−Σ_k b_kx_i^k)<B.
* There does not exist b such that this unsquared sum at b is ≤ its value at every c.
* For every b, olsRSS(P,y,b)=Σ_i(y_i−Σ_k b_kx_i^k)².
* If PᵀP is invertible, then for every b the coefficient β=(PᵀP)⁻¹Pᵀy satisfies RSS(β)≤RSS(b), with equality iff b=β.

The invertibility assumption applies only to the last assertion. There is no assertion about a necessary count of distinct x values.

## SAP.P001d.T71

For every n>0, K, design X∈ℝ^{n×(K+1)} and y∈ℝⁿ, define p(b)=Σ_{k=1}^K|b_k| and L_λ(b)=RSS(b)/n+λp(b). Then: for every b, L_0(b)=RSS(b)/n; for every b, b minimizes L_0 over all coefficients iff it minimizes RSS over all coefficients; for every b,c, p(b)≥0, p(ab)=|a|p(b) for every real a, and p(b+c)≤p(b)+p(c); p(e_0)=0, whereas Σ_{j=0}^K|(e_0)_j|=1; and for every λ≥0, L_λ is convex on all of ℝ^{K+1}. There is no Gram-invertibility requirement or minimizer-existence assertion. K=0 is permitted, giving the zero slope penalty on the one-dimensional intercept space.

## SAP.P001d.T72

For every natural K, x,b∈ℝ^{K+1}, and real s>0, set m=Σ_kx_kb_k and d(m,s,y)=exp(−(y−m)²/(2s²))/(s√(2π)). Then d(m,s,y)≥0 for every real y; d(m,s,·) and y↦yd(m,s,y) are Lebesgue integrable; ∫d=1 and ∫yd=m. Also, evaluating the **same real expression** at zero scale gives ∫d(m,0,y)dy=0≠1. Lean's division by zero makes d(m,0,y)=0 for every y. The statement expressly contrasts this zero function with a positive-scale density; it does not call it a probability density or assert that it is the zero-variance Gaussian measure.

## SAP.P001d.T73

There are no parameters or hypotheses. Give each i∈{0,1,2,3} weight 1/4; let X=(0,0,1,1), Y=(1,3,0,6), and e=Y−(2+X)=(−1,1,−3,3). `finiteMean`, `finiteProb`, and `finiteCov` are exactly the finite weighted mean, event weight, and centered covariance. `finiteCond(Y,X,x)` is Σ_{X_i=x}Y_i/4 divided by the event weight (totalized at zero, but only used here at positive masses). The assertions are:

    P(X=0)=P(X=1)=1/2;
    E[Y|X=0]=2, E[Y|X=1]=3;
    E e=0, Cov(X,e)=0;
    P(X=0 and |e|=1)=1/2;
    P(X=0)P(|e|=1)=1/4;
    1/2≠1/4.

The final three equalities exhibit failure of the independence product equation. No further conditional variances or orthogonality identities are asserted.

## SAP.P001d.T74

For every pair of measurable spaces Ω,E and every probability μ on Ω, two universal assertions and the fixed T73 assertion hold.

1. For every measurable X:Ω→E, every Y∈L²(μ), and every m:E→ℝ satisfying IsCEF(X,Y,m) and m(X)∈L²(μ), put e=Y−m(X). Then IsCEF(X,e,0); E e=0; for every globally measurable g:E→ℝ with g(X)∈L², Cov(g(X),e)=0; and for every v:E→ℝ satisfying IsCEF(X,e²,v), one has IsCEF(X,(e−0)²,v) and Var(e)=E v(X). In the last assertion v is supplied, not constructed. Its first conclusion is the supplied identity after subtracting zero. m and v measurability/integrability are included in IsCEF. No assertion of independence between X and e is made in this branch.
2. For every measurable X:Ω→E and measurable Y:Ω→ℝ, every globally measurable m:E→ℝ, and every s>0, suppose the joint law of (X,Y) is the pushforward of Law(X)⊗N(0,s²) under (x,z)↦(x,m(x)+z). Then Law(Y−m(X))=N(0,s²) and X is independent of Y−m(X). The premise explicitly specifies the translated-product joint law. There is no first/second-moment assumption on m(X), and none is needed for this conclusion. No pointwise conditional-law assertion at every x appears.
3. All finite-model conclusions listed under T73 hold. This finite model is fixed independently of Ω,E and μ.

## SAP.P001d.T75

For every natural K, x,b∈ℝ^{K+1}, and h:ℝ→ℝ, assume 0≤h(t)≤1 for every real t. Then `binaryChoiceMean x b h`, defined as 0·(1−h(Σx_kb_k))+1·h(Σx_kb_k), equals h(Σx_kb_k) and belongs to [0,1]. Thus the weighted mean of the two values 0 and 1 is the probability assigned to 1. No probability measure, measurable conditional kernel, or random-variable model is constructed by this statement; the weights at the fixed x are nonnegative and sum to one by the hypothesis.

## SAP.P001d.T76

For every n>0, K, design X∈ℝ^{n×(K+1)}, and y∈ℝⁿ, define

    ℓ(b,s)=−n log(s)−(n/2)log(2π)−RSS(b)/(2s²).

For every candidate b* and every s>0, [for all b, ℓ(b,s)≤ℓ(b*,s)] iff [for all b, RSS(b*)≤RSS(b)]. Also, for every b* and every s,t>0, [b* maximizes ℓ(·,s)] iff [b* maximizes ℓ(·,t)]. These assertions hold even for singular designs. No optimizer existence, uniqueness, explicit inverse coefficient formula, or optimization over s is asserted. Logarithms are used only at positive s in the claims about likelihood.
