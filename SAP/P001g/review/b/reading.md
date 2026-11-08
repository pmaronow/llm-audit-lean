# Blind reading

This file was written after reading all supplied `Defs` and `Challenge` Lean files and the Mathlib definitions identified below, and before opening `claims.json` or `record.json`. The Challenge docstrings were visible; their descriptions are not used as substitutes for the theorem types. There are 13 theorem stubs, each asserting its corresponding `T...Statement` definition. All universal quantifiers below precede the conclusion unless explicitly nested otherwise. A conjunction of separately quantified statements allows different probability spaces in its different conjuncts. Lean universe parameters only control the sizes of the quantified types.

## Shared definitions, including their Mathlib meaning

* A probability space means an arbitrary type with a sigma algebra and a measure of total mass one. Real spaces have their Borel sigma algebras. `prob μ A` is `(μ A).toReal`; on a probability space this is ordinary real probability, including for outer-measured sets. On an infinite-measure set `toReal` would instead return zero. All outer probability calculations here use probability measures.
* `mean μ Z` is the real Bochner integral of Z. Mathlib returns zero if Z is not integrable. `Integrable` includes almost-everywhere strong measurability and finite integral of the absolute value. `MemLp Z 2 μ` means almost-everywhere strong measurability and a finite second moment. `var μ Z` is the real conversion of the extended integral of |Z−E Z|²; an infinite extended variance converts to zero. Moment assumptions in the sample-mean statements avoid that convention.
* `cdf μ Z x` is P(Z≤x). `CP μ Z c` means: for every real ε>0, P(dist(Z_n,c)≥ε) tends to zero as n tends to infinity. Measurability of Z is not part of this predicate. Finite real vectors use the usual finite-product topology (the Mathlib product sup metric). `CD μ Z ν` means convergence of P(Z_n≤x) to ν((−∞,x]) at every continuity point x of the latter CDF. It also does not itself impose measurability. `gaussianReal a v` is the real Gaussian with mean a and variance v; v is a nonnegative real, and v=0 gives the point mass at a.
* `IID μ X` explicitly requires every coordinate X_i to be measurable, joint independence of all finite subfamilies, and equality of each pushforward law with the law of X_0. Mathlib independence is independence of the sigma algebras pulled back from the codomains; `IdentDistrib` includes almost-everywhere measurability and equality of pushforward measures.
* `sampleMean X n` is n⁻¹∑_{i=0}^{n−1}X_i. At n=0 it is zero, using real division by zero. `firstSample X n ω` is the vector (X_0(ω),…,X_{n−1}(ω)) indexed by `Fin n`. `empirical X n ω` is n⁻¹∑_{i<n}δ_{X_i(ω)} as an extended-nonnegative scalar multiple of measures. At n=0 the sum is the zero measure, so the empirical measure is zero; at n>0 it is a probability measure.
* `HasPDF ν f` says f is Lebesgue-almost-everywhere measurable, nonnegative at every real argument, Lebesgue integrable, and ν has density f relative to Lebesgue measure. Normalization follows when ν is a probability measure. `withDensity` uses the nonnegative Lebesgue integral over measurable sets; `ENNReal.ofReal` truncates negative inputs, but the relevant models explicitly impose nonnegativity. All maps used as random variables in law hypotheses are measurable by surrounding assumptions, so Mathlib's arbitrary fallback for nonmeasurable pushforwards is irrelevant.
* `IsCEF μ X Y m` says m is measurable, Y and m(X) are μ-integrable, and, for every measurable A in the codomain of X, ∫_{X∈A}Y dμ=∫_{X∈A}m(X)dμ. Thus it is an integral characterization of a specified conditional mean, without requiring a regular conditional law. For a restricted measure it uses that unnormalized restricted measure, which yields the same conditional-mean identities inside the treatment arm. Measurability of X must come from the surrounding statement.
* `CI μ X hX Y Z` says, for every measurable set A in the codomain of Y and every measurable set B in the codomain of Z, E[1_{Y∈A,Z∈B}|σ(X)]=E[1_{Y∈A}|σ(X)]E[1_{Z∈B}|σ(X)] μ-almost surely. The almost-sure set can depend on A,B. Mathlib conditional expectation is zero if the conditioning sigma algebra is not a sub-sigma algebra, its trimmed measure is not sigma finite, or the integrand is not integrable. Here X is measurable, μ is finite, and the indicators are measurable and bounded, so these fallbacks do not apply.
* The observed outcome is Y=Y_1 D+Y_0(1−D). A censored outcome is Y*=YR−99(1−R). A completed outcome at endpoint c is Y*R+c(1−R). These have the intended treatment/missingness meaning where D or R is binary. `conditionalMeanAt μ X Z x` is ∫_{X=x}Z dμ/P(X=x), with a zero-denominator fallback if the event is null; T130 requires positive probabilities for both R arms.
* For a kernel K and real bandwidth h, `kernelDensity K h s x` is (1/n)∑_{i<n}K((x−s_i)/h)/h. The rectangle kernel is 1/2 for |t|≤1 and zero otherwise. T127 assumes h_n>0. `standardizedMean μ X n` is (sampleMean_n−E sampleMean_n)/sqrt(Var sampleMean_n). `VarianceConsistent μ vhat v` means n vhat_n→v in probability.
* A conditional model g(y,x,t), covariate probability ν_X and reference measure κ produce the joint measure with density g(y,x,t) relative to ν_X⊗κ. `conditionalKL κ f g x t` is ∫f(y,x)log(f(y,x)/g(y,x,t))dκ(y). The expected log likelihood M(t) is E log g(Y,X,t); the sample log likelihood is its sample average. `sampleLikelihood` is the actual product ∏_{i<n}g(Y_i,X_i,t). Mathlib has log 0=0 and division by zero=0; support and integrability premises must therefore be checked separately.
* `disjointMixture p a b` is the mass vector (p(1−a),pa,(1−p)(1−b),(1−p)b) on four points.
* The OLS coefficient is (AᵀA)⁻¹Aᵀd, and residual sum of squares is ∑(d_i−(Aβ)_i)². Mathlib's square-matrix inverse is the ordinary inverse if the determinant is nonzero and the zero matrix otherwise. The placebo restricted design has columns (1,X), the full design (1,X,W). With K original and L additional regressors, `placeboFStatistic` is ((RSS_restricted−RSS_full)/L)/(RSS_full/(n−(K+L+1))). The subtraction in this denominator is real subtraction, not truncated natural subtraction. `fReference k v` is the pushforward of k+v independent standard normals under (∑_{i<k}Z_i²/k)/(∑_{k≤i<k+v}Z_i²/v). It is the ordinary F(k,v) law for positive k,v.

Mathlib source checks: `Probability/Moments/Variance.lean:54–64`, `Probability/Independence/Basic.lean:105–147`, `Probability/Independence/Kernel/IndepFun.lean:47–58`, `Probability/IdentDistrib.lean:71–77`, `Probability/Distributions/Gaussian/Real.lean:222–234`, `MeasureTheory/Function/ConditionalExpectation/Basic.lean:93–110`, `MeasureTheory/Function/L1Space/Integrable.lean:59–61`, `MeasureTheory/Function/LpSeminorm/Defs.lean:148–164`, `MeasureTheory/Integral/Bochner/Basic.lean:158–162`, `MeasureTheory/Measure/Map.lean:93–107`, `MeasureTheory/Measure/Restrict.lean:43–51`, `MeasureTheory/Measure/WithDensity.lean:39`, `Analysis/Normed/Lp/lpSpace.lean:78–82,371,452`, `LinearAlgebra/Matrix/NonsingularInverse.lean:166–176`, and `Analysis/SpecialFunctions/Log/Basic.lean:44,103`. Line ranges here identify source evidence, not extra premises.

## SAP.P001g.T115

For every probability space, measurable integrable real potential outcomes Y_0,Y_1 and measurable real D, assume D(ω)∈{0,1} at every point and both treatment-arm probabilities are positive. Define Y=Y_1D+Y_0(1−D), and A_d(Z)=E[Z1_{D=d}]/P(D=d). Then the following conjunction holds:

1. If the pair (Y_0,Y_1) is independent of D, E(Y_1−Y_0)=A_1(Y)−A_0(Y).
2. Without that independence premise, A_1(Y)−A_0(Y)=A_1(Y_1−Y_0)+A_1(Y_0)−A_0(Y_0).

There is no sample estimator in the conclusion. Independence is an antecedent only for the first conjunct.

## SAP.P001g.T116

This is a conjunction of three separately quantified components.

First, on every probability space and every countable covariate measurable space E with measurable singleton sets, quantify measurable X:Ω→E; measurable integrable real Y_0,Y_1; measurable pointwise binary D; a function p:E→R with `IsCEF μ X D p`; a real ε>0 such that ε<p(X(ω))<1−ε at every ω; conditional independence (Y_0,Y_1) independent of D given X in the indicator sense above; and functions m_0,m_1:E→R which are CEFs of the observed Y under μ restricted to D=0 and D=1 respectively. Require also integrability of m_0(X),m_1(X) under the full μ. Then

E(Y_1−Y_0)=∑'_x m_1(x)P(X=x)−∑'_x m_0(x)P(X=x).

The sums are Mathlib real infinite sums, whose default is zero when nonsummable; the stated countability and integrability are intended to make them absolutely summable. E is not assumed finite or nonempty independently of X and the probability space.

Second, quantify exactly the same data and assumptions except E is an arbitrary measurable space, without countability or singleton assumptions. Then x↦m_1(x)−m_0(x) is a CEF of Y_1−Y_0 given X, and

E(Y_1−Y_0)=E[m_1(X)−m_0(X)].

Third, on an independently quantified probability space and arbitrary covariate measurable space E, take measurable X,Y_0,Y_1,D with D pointwise binary, p a CEF of D given X, ε>0 and the same pointwise uniform overlap, and the same conditional independence. This component has no integrability assumption on Y_0 or Y_1 and no m_d. Then (i) D and X are conditionally independent given p(X); (ii) (Y_0,Y_1) and D are conditionally independent given p(X); (iii) id is a CEF of D given p(X); and (iv) there exists δ>0 with δ<p(X)<1−δ μ-almost surely. The overlap assumption here remains pointwise and uniform, even though its conclusion is almost sure.

## SAP.P001g.T117

For every probability space, natural dimension K (including zero), measurable finite real vector X, measurable integrable real Y_0,Y_1, and measurable real D, assume D is binary almost surely and both D-arm probabilities are positive. Next quantify p:R^K→R, assume p is a CEF of D given X, there exists ε>0 such that ε<p(X)<1−ε almost surely, and (Y_0,Y_1) is conditionally independent of D given X. Define Y=Y_1D+Y_0(1−D). Then:

1. E(Y_1−Y_0)=E[Y D/p(X)−Y(1−D)/(1−p(X))].
2. For every triple of measurable real functions m_0,m_1,q on R^K, with both m_d(X) integrable, if either (a) m_0 and m_1 are CEFs of Y given X in the respective treatment arms and q has almost-sure uniform overlap η<q(X)<1−η for some η>0, or (b) q(X)=p(X) almost surely, then

E(Y_1−Y_0)=E[m_1(X)+D(Y−m_1(X))/q(X)−m_0(X)−(1−D)(Y−m_0(X))/(1−q(X))].

The second alternative does not require correct outcome regressions; the first does not require q=p. In both alternatives the separately stated measurability and integrability premises remain. Neither q positivity at every point nor binary D at every point is required.

## SAP.P001g.T118

This is the conjunction of the negations of two universal statements, not a direct asymptotic-normality theorem.

For the first, define a real CDF F to mean a function R→[0,1] which is nondecreasing, right continuous (via limits from [x,∞) at every x), and has limits 0 at −∞ and 1 at +∞. For bounded functions h let ||h||_∞=sup_x|h(x)|. `uniformNorm` is expressed as a real supremum; every h and h_n to which it is applied in the derivative test is bounded.

`CDFHadamard T F` means there exists a map L from all real functions on R to R, additive and real homogeneous on all such functions, and a constant C≥0 with |Lh|≤C||h||_∞ for every bounded h. Furthermore, for every bounded h, every positive real sequence t_n→0, and every sequence of bounded functions h_n with ||h_n−h||_∞→0 such that F+t_nh_n is a real CDF for every n,

[T(F+t_nh_n)−T(F)]/t_n→Lh.

The first negated statement would assert: for every probability space, every real IID sequence X, every functional T:(R→R)→R with this derivative property at F(x)=P(X_0≤x), there exists φ>0 such that sqrt(n)[T(F_n)−T(F)] converges in distribution to N(0,φ²), where F_n is the empirical CDF. T118 asserts that this universal statement is false. It does not explicitly display the counterexample and does not negate a version allowing zero limiting variance.

For the second, `KolmogorovSpace` is the normed space of all bounded pointwise real functions on R (`lp ... ∞`), with the actual sup norm, not an almost-everywhere quotient. A bounded f is embedded as itself; the definition embeds an unbounded f as zero. `finiteSecondCDF F` means that F is the CDF of some probability ν on R with ∫x²dν<∞. The mean functional on this domain is ∫x dν for one chosen representing probability; outside the domain it is defined as zero. CDF uniqueness makes the choice immaterial on the domain.

For a normed real space, `HadamardAt D H T F L` says: for every direction h∈H, every sequence t_n>0 tending to zero, and every sequence h_n→h with F+t_n h_n∈D at every n, the difference quotient tends to Lh. L must be a continuous real linear functional on the ambient space. The second negated statement would say: for every probability ν with finite second moment, there exists such L for the mean functional at its embedded CDF, with D all finite-second-moment CDFs and H the entire bounded-function space. T118 asserts this universal statement is false. It does not claim failure at every ν.

## SAP.P001g.T120

This negates a universal consistency assertion. The negated assertion quantifies, in order:

* An arbitrary probability space; natural dimensions K,τ; sequences of covariates X_i∈R^K and outcomes Y_i∈R whose pairs are IID; a sigma-finite-in-the-`SFinite`-sense reference measure κ on R (countable sum of finite measures, not necessarily sigma finite); a probability ν_X on R^K; functions f(y,x),g(y,x,t); and a joint-law equality saying (X_0,Y_0) has density f(y,x) relative to ν_X⊗κ.
* A parameter set Θ⊆R^τ; pointwise nonnegativity, measurability, and ∫ f(y,x)dκ(y)=1 at every x; parameterwise joint measurability, pointwise nonnegativity, and ∫g(y,x,t)dκ(y)=1 for every t∈Θ and every x.
* A fixed x with ν_X({x})>0; t*∈Θ; support domination g(y,x,t)>0 wherever f(y,x)>0 for κ-almost every y, separately for each t∈Θ; κ-integrability of f(y,x)log(f(y,x)/g(y,x,t)) for each t∈Θ; and unique conditional-KL minimization at x: for every t∈Θ, KL_x(t*)≤KL_x(t), with equality forcing t=t*.
* An estimator sequence t_hat_n(ω)∈Θ for all n,ω, maximizing the actual sample product ∏_{i<n}g(Y_i(ω),X_i(ω),t) over all t∈Θ for all n,ω. No estimator measurability, compactness, or uniform limit is required.

The assertion would conclude t_hat_n→t* in probability. T120 says that this complete universal assertion is false; its fixed-x support positivity is part of the assertion being refuted.

## SAP.P001g.T121

This negates the following assertion. For every probability space, every IID sequence X_i taking values in a four-point set, every b_0∈[1/4,3/4], and the law

P(X_0=j)=(2/3,1/3,0,0)_j=disjointMixture(1,1/3,b_0)_j,

take any family of maps t_hat_n from all n-observation samples into triples (p,a,b), with p,a∈[0,1] and b∈[1/4,3/4] on every possible sample. Require that for every n and every sample s, t_hat_n(s) globally maximizes ∏_{i<n}disjointMixture(p,a,b)_{s_i} over that parameter box. The assertion would conclude that the triple t_hat_n(X_0,…,X_{n−1}) converges in probability to (1,1/3,b_0). T121 asserts that this is false. The universal estimator property ranges even over samples with zero probability under the specified true law. No efficiency property is separately mentioned; a failure of consistency is the only asserted negative result.

## SAP.P001g.T124

There exist a probability μ on the infinite product of the 12-point set and a real sequence critical_n with all of the following properties. For j∈{0,…,11}, let x_j be −1,0,1 according as floor(j/4) is 0,1,2; let z_j be −1 when j mod 4<2 and +1 otherwise; let d_j=1 when j is odd and 0 otherwise; let w_j=x_j²+z_j/2. The sequence (x_{ω_i},w_{ω_i},d_{ω_i}), with x,w each represented as a one-coordinate vector, is IID. At observation zero, w and d are conditionally independent given x in the indicator/conditional-expectation sense. All d values are pointwise binary.

For an n-sample s, define normalized cell frequencies q_j=n⁻¹#{i:s_i=j}. For a cell-indexed design R_j, the weighted Gram matrix is ∑_j q_j R_jR_jᵀ, cross vector ∑_j q_j R_j d_j, coefficient its inverse times the cross vector, and residual risk ∑_j q_j(d_j−R_jᵀβ)². `placeboGood s` requires n>3, nonzero Gram determinants for both restricted R=(1,x) and full R=(1,x,w), and strictly positive full residual risk. Almost surely, the first n observations satisfy this condition for every sufficiently large n.

For every n>3 the reference F(1,n−3) law assigns probability 1/2 to (−∞,critical_n]. The natural subtraction n−3 is used here only when n>3, so the denominator degrees of freedom are positive. Finally

P(placeboGood(first n observations) and F_statistic(first n observations)>critical_n)→1.

F_statistic is the ordinary unweighted nested OLS F statistic from the shared definition, with K=L=1. Every rejection in this event has nonsingular Gram matrices, positive residual sum of squares and positive residual degrees of freedom. The statement supplies an existential counterexample at nominal level 1/2; it gives no explicit distribution on the cells and makes no assertion for arbitrary nominal levels.

## SAP.P001g.T125

For every probability space and real IID sequence with finite second moment at index zero, its sample mean converges in probability to E X_0. There is no strictly positive-variance requirement and no n>0 premise, since this is an asymptotic assertion.

## SAP.P001g.T126

Three separately universally quantified statements are conjoined. In each, take a probability space and real IID sequence with a finite second moment and strictly positive variance σ²=Var X_0.

1. sqrt(n)(sampleMean_n−E X_0) converges in distribution to N(0,σ²).
2. (sampleMean_n−E sampleMean_n)/sqrt(Var sampleMean_n) converges in distribution to N(0,1).
3. For every natural n>0, sqrt(Var sampleMean_n)=sqrt(σ²)/sqrt(n); at every ω the standardized mean equals sqrt(n)(sampleMean_n−E X_0)/sqrt(σ²); and the standardized mean has expectation zero, variance one and standard deviation one.

The finite identities are asserted only at positive sample sizes. The asymptotic parts include a harmless zero value at n=0 from the totalized standardization formula.

## SAP.P001g.T127

For every probability space and real IID sequence X, every real function f which is a PDF of the pushforward law of X_0 and is continuous on all of R, and every real bandwidth sequence h with h_n>0 at every n, h_n→0, and n h_n→+∞, the following holds for every fixed real x:

(1/n)∑_{i<n}[1_{|x−X_i|≤h_n}/(2h_n)]→f(x) in probability.

There is no uniform-in-x convergence conclusion and no moment assumption on X. The n=0 formula is zero; only the limit is asserted.

## SAP.P001g.T128

For every probability space, real estimator sequences t_hat_n and v_hat_n each measurable at every n, with v_hat_n(ω)≥0 at every n,ω, and real θ,φ,α,z satisfying φ>0, 0<α<1 and Φ(z)=1−α/2, assume sqrt(n)(t_hat_n−θ) converges in distribution to N(0,φ²), and n v_hat_n→φ² in probability. Then there exists a real c≥1−α such that

P(θ∈(t_hat_n−z sqrt(v_hat_n),t_hat_n+z sqrt(v_hat_n)))→c.

The endpoints form an open interval. The conclusion includes existence of a coverage limit and a lower bound, not an assertion that c=1−α. Positivity of z follows from the Gaussian quantile and α premises rather than being an explicit premise.

## SAP.P001g.T129

Two independent universal assertions are conjoined.

For product-MLE consistency, quantify a probability space, natural K,τ, sequences of covariates X_i∈R^K and outcomes Y_i with IID pairs; a covariate probability ν_X; an SFinite reference κ; a conditional density family g; a compact parameter set Θ⊆R^τ and θ∈Θ. Require, separately for every t∈Θ: joint (x,y) measurability of g, pointwise nonnegativity, and normalization ∫g(y,x,t)dκ(y)=1 at every x. The true joint law equals ν_X⊗κ weighted by g at θ. Require integrability of log g(Y_0,X_0,t) and its almost-sure positive observed density for every t∈Θ. These are parameterwise, not simultaneous-in-t, almost-sure statements. M(t)=E log g(Y_0,X_0,t) is continuous on Θ, attains its maximum at θ, and equality M(t)=M(θ) for t∈Θ forces t=θ.

Next quantify an estimator t_hat_n measurable at every n, belonging to Θ at every n,ω and globally maximizing the actual product likelihood over Θ at every n,ω. Next quantify a real sequence Δ_n(ω) which, at every n,ω and every t∈Θ, bounds |sampleLogLikelihood_n(ω,t)−M(t)| from above, and require Δ_n→0 in probability. There is no separate measurability requirement on Δ and its sign is forced by the bound because Θ contains θ. Conclude t_hat_n→θ in probability. No separate log/product identity, uniqueness of the empirical maximizer, or derivation of the envelope is a conclusion.

For the expected-log maximum assertion, independently quantify a probability space, K,τ, measurable X∈R^K and Y∈R, covariate probability ν_X, SFinite reference κ, conditional family g, parameter set Θ and θ∈Θ. Require the same parameterwise measurability, pointwise nonnegativity and normalization, and the same true-law equality. For every t∈Θ assume g(y,x,θ)>0 implies g(y,x,t)>0 for ν_X⊗κ-almost every (x,y), and assume log g(Y,X,t) is integrable. No compactness, IID sequence, parameter continuity, uniqueness or envelope is required here. Then, for every t∈Θ,

M(t)≤M(θ), and M(t)=M(θ) if and only if g(Y,X,t)=g(Y,X,θ) almost surely under the true μ.

The equality condition concerns observed joint true-law values, not pointwise equality of densities everywhere.

## SAP.P001g.T130

For every probability space, real sequences Y_i,R_i measurable at every index, real endpoints a≤b, assume Y_i∈[a,b] almost surely at every i, R_i∈{0,1} almost surely at every i, and P(R_0=0)>0 and P(R_0=1)>0. Assume only that the observable pairs (Y_iR_i−99(1−R_i),R_i) are IID; the latent pairs (Y_i,R_i) need not be IID. Write Y*_i for the censored value and define L_i=Y*_iR_i+a(1−R_i), U_i=Y*_iR_i+b(1−R_i). Define

l=E[Y*_0|R_0=1]P(R_0=1)+aP(R_0=0),
u=E[Y*_0|R_0=1]P(R_0=1)+bP(R_0=0),

where the conditional expectation at R_0=1 is the explicit event-integral ratio with its positive denominator. Then E L_0=l and E U_0=u; for every n>0, E sampleMean(L,n)=l and E sampleMean(U,n)=u; and sampleMean(L,n)→l and sampleMean(U,n)→u in probability. There is no explicit conclusion l≤E Y_0≤u, no assertion that every value in [l,u] is attainable, and no assertion of unbiasedness at n=0.
