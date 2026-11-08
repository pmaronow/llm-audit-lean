# Blind reading of the Challenge

This reading was saved before opening `claims.json` or `record.json`. It interprets the declarations in `SAP/P001g/Challenge/Part1.lean` through all seven Defs files. The Challenge docstrings are annotations; the propositions below are what the theorem types actually assert. No Solution or Comparator was consulted.

## Common definitions and Mathlib conventions

* Unless stated otherwise, every probability-space quantifier means: for every type Ω, every σ-algebra on Ω, and every measure μ on it satisfying μ(Ω)=1. Objects and hypotheses following this quantifier are universally quantified in their displayed order. Separate conjuncts with their own Ω quantifiers are independent universal assertions. Universe parameters only allow different sizes of types.
* `prob μ A` is `(μ A).toReal`. For the probability measures used here this is ordinary probability. A Lean measure can be applied to an arbitrary set, but all events used below are measurable in the concrete examples discussed. `mean μ Z` is the real Bochner integral ∫Z dμ. Mathlib assigns zero to a nonintegrable Bochner integral. `var μ Z` is the extended integral ∫|Z−∫Z dμ|² dμ followed by `toReal`; an infinite extended variance is thereby assigned zero. Under finite-second-moment hypotheses it is the usual variance.
* `cdf μ Z(x)=Pμ(Z≤x)`. `CD μ Z ν` means: for every real x at which t↦ν((−∞,t]).toReal is continuous, Pμ(Z_n≤x) tends to ν((−∞,x]).toReal as n→∞. `CP μ Z c` means: for every real ε>0, Pμ(ε≤dist(Z_n,c)) tends to zero. For real variables dist is absolute difference; for the finite real parameter vectors it is the supremum distance.
* `IID μ Z` means, in order: each Z_i is measurable; the whole sequence is mutually independent (`iIndepFun`, independence on every finite set of indices); and every Z_i has the same law as Z_0 (`IdentDistrib`, including a.e. measurability and equality of pushforward measures). `IndepFun` is independence of the generated σ-algebras. `MemLp Z 2 μ` means a.e. strong measurability and a finite integral of |Z|². The references are Mathlib's `Probability/Independence/Basic.lean`, `Probability/IdentDistrib.lean`, and `MeasureTheory/Function/LpSeminorm/Defs.lean`.
* For n∈ℕ, the sample mean is bar Z_n=(1/n)∑_{i=0}^{n−1}Z_i; `firstSample Z n ω` is the vector (Z_i(ω))_{i∈Fin n}. The empirical measure is (n:ℝ≥0∞)⁻¹ times the sum of these n Dirac measures. Real division by zero is zero; the sample mean and empirical measure at n=0 are zero. All asymptotic assertions concern n→∞, and explicit finite-sample assertions below require n>0.
* `IsCEF μ X Y m` means exactly: m is measurable; Y is μ-integrable; m∘X is μ-integrable; and for every measurable set A in the codomain of X, ∫_{X∈A}Y dμ=∫_{X∈A}m(X) dμ. This also applies with the unnormalized restricted measures μ|{D=d}. It is a version of the conditional expectation when X is measurable.
* `CI μ X hX U V` means: for every measurable A in the codomain of U and B in that of V, E[1_{U∈A,V∈B}|σ(X)]=E[1_{U∈A}|σ(X)]E[1_{V∈B}|σ(X)] μ-a.s. Here σ(X) is the comap σ-algebra. Mathlib conditional expectation is zero if the σ-algebra inclusion, σ-finiteness of the restricted σ-algebra, or integrability fails (`MeasureTheory/Function/ConditionalExpectation/Basic.lean:102`). Here X is measurable, μ is finite, and the integrands are bounded indicators, so these fallback cases do not apply.
* `observedOutcome(y0,y1,d)=y1 d+y0(1−d)`; `censored(y,r)=yr−99(1−r)`; `missingEndpoint(y*,r,c)=y*r+c(1−r)`. `conditionalMeanAt μ X Y x` is ∫_{X=x}Y dμ/Pμ(X=x), with zero division convention if the denominator is zero. Positive-denominator hypotheses below prevent that convention where this function is used.
* `HasPDF ν f` means f is Lebesgue-a.e. measurable, f(x)≥0 for every x, f is Lebesgue-integrable, and ν is Lebesgue measure weighted by `ENNReal.ofReal(f)`. `gaussianReal m v` is the normal law of mean m and **variance** v≥0; for v=0 it is δ_m (`Probability/Distributions/Gaussian/Real.lean:222`).
* `uniformNorm(h)=sup_{x∈ℝ}|h(x)|`, represented by the real conditional supremum. An unbounded real set has Mathlib's default conditional-supremum value, so boundedness matters. `KolmogorovSpace=ℓ∞(ℝ,ℝ)` is the space of all bounded real functions on ℝ with the ordinary supremum norm, not an a.e. quotient. This follows from `Memℓp` at p=∞ and `lp.norm_eq_ciSup` in `Analysis/Normed/Lp/lpSpace.lean`. `kolmogorovEmbed(f)` is f as an element of that space if f is bounded and is the zero function otherwise. CDFs are bounded.
* `IsRealCDF F` means 0≤F≤1 everywhere, F is nondecreasing, F is right-continuous (limits from [x,∞) at each x), and its limits at −∞ and +∞ are 0 and 1.
* `CDFHadamard T F` means there exists a real-valued functional L on **all** functions ℝ→ℝ such that (i) L is additive on all functions, (ii) L is real-homogeneous on all functions, (iii) there exists C≥0 with |Lh|≤C‖h‖∞ for every bounded h, and (iv) for every bounded h, every sequence of positive real t_n, and every sequence of bounded functions h_n, if t_n→0, ‖h_n−h‖∞→0, and every F+t_n h_n is a real CDF, then [T(F+t_n h_n)−T(F)]/t_n→Lh. No separate assumption that T is measurable appears.
* `finiteSecondCDF F` means there exists a probability measure ν on ℝ with ∫x²dν<∞ whose CDF is pointwise F. `cdfMeanFunctional(F)` is the mean of a classically chosen such ν when one exists, and zero otherwise. The representing probability measure is unique because its CDF determines its law. `HadamardAt D H T F L` means: for every h∈H, positive sequence t_n, and vector sequence h_n, if t_n→0, h_n→h in norm, and F+t_n h_n∈D for all n, then [T(F+t_n h_n)−T(F)]/t_n→Lh. L is explicitly a continuous real linear map.
* For K,τ∈ℕ, a conditional model has covariate vectors x∈ℝ^K and parameter vectors t∈ℝ^τ. Zero dimensions are permitted. `conditionalModelLaw νX κ g t` is the measure on ℝ^K×ℝ with density g(y,x,t), converted by `ofReal`, relative to νX⊗κ. `conditionalKL κ f g x t=∫ f(y,x)log(f(y,x)/g(y,x,t))dκ(y)`. `expectedLogLikelihood μ X Y g t=Eμ log g(Y,X,t)`. The sample log likelihood is the **average** of the n observed logs, while `sampleLikelihood` is their actual n-factor product (the empty product is 1). Mathlib's real log is zero at zero. Positivity, integrability, and domination assumptions are therefore relevant, rather than implicit in the definitions.
* For real design matrices, `olsCoef(X,Y)=(XᵀX)⁻¹XᵀY`, and `olsRSS(X,Y,b)=∑(Y_i−(Xb)_i)²`. Mathlib's square-matrix inverse is the usual inverse if nonsingular and the zero matrix otherwise (`LinearAlgebra/Matrix/NonsingularInverse.lean:169`). With K base covariates X and L added covariates W, `placeboFStatistic` uses a restricted design [1,X], full design [1,X,W], their OLS residual sums rr,rf, and F=((rr−rf)/L)/(rf/(n−(K+L+1))). Here subtraction in that denominator is real subtraction. `fReference(k,v)` is the law of [(sum of k independent squared N(0,1)'s)/k]/[(sum of a disjoint v such squares)/v], using a product Gaussian space indexed by Fin(k+v). For k,v>0 this is the usual F(k,v) law.

## SAP.P001g.T115

For every probability space, measurable real Y0,Y1,D, integrable Y0 and Y1, pointwise binary D∈{0,1}, and positive probabilities of both D=0 and D=1, set Y=Y1D+Y0(1−D) and arm(Z,d)=E[Z1_{D=d}]/P(D=d). The conclusion is the conjunction:

1. If (Y0,Y1) is independent of D, then E(Y1−Y0)=arm(Y,1)−arm(Y,0).
2. Without this independence assumption, arm(Y,1)−arm(Y,0)=arm(Y1−Y0,1)+arm(Y0,1)−arm(Y0,0).

The independence implication governs only the first conjunct. No sample estimator is quantified.

## SAP.P001g.T116

This is the conjunction of three independent universal assertions, in the following order.

1. **Discrete covariates.** For every probability space, countable measurable space E with measurable singletons, measurable X:Ω→E, measurable real Y0,Y1,D, integrable Y0,Y1, pointwise binary D, function p:E→ℝ satisfying `IsCEF μ X D p`, ε>0 with ε<p(X(ω))<1−ε at every ω, conditional independence (Y0,Y1) ⟂ D | X, and functions m0,m1:E→ℝ satisfying `IsCEF (μ|D=d) X Y md` for d=0,1 and also integrable md(X) under μ, conclude E(Y1−Y0)=∑'_x m1(x)P(X=x)−∑'_x m0(x)P(X=x). Both sums are Lean `tsum`; integrability here makes them the usual absolutely convergent sums. Y is the observed outcome above.
2. **General conditional identification.** The same universally quantified data and hypotheses as in part 1, except E is an arbitrary measurable space without countability or measurable-singleton assumptions, imply `IsCEF μ X (Y1−Y0) (m1−m0)` and E(Y1−Y0)=E[m1(X)−m0(X)].
3. **Propensity score.** For every probability space, arbitrary measurable space E, measurable X and measurable Y0,Y1,D, pointwise binary D, p satisfying `IsCEF μ X D p`, ε>0 with ε<p(X)<1−ε pointwise, and (Y0,Y1) ⟂ D | X, conclude simultaneously: D ⟂ X | p(X); (Y0,Y1) ⟂ D | p(X); `IsCEF μ (p∘X) D id`; and there exists δ>0 such that δ<p(X)<1−δ μ-a.s. This third part assumes neither integrability of potential outcomes nor existence of m0,m1.

There is no pointwise conditional identity at null covariate values: the identities use versions of conditional expectations and a.s. independence.

## SAP.P001g.T117

Quantifier order: for every probability space, K∈ℕ, measurable X:Ω→ℝ^K and real Y0,Y1,D, assume measurable Y0,Y1,D, integrable Y0,Y1, a.s. binary D, and positive probabilities of both arms; then for every p:ℝ^K→ℝ satisfying `IsCEF μ X D p`, an a.s. uniform overlap bound ε<p(X)<1−ε for some ε>0, and (Y0,Y1) ⟂ D | X, set Y=Y1D+Y0(1−D). Conclude:

1. E(Y1−Y0)=E[YD/p(X)−Y(1−D)/(1−p(X))].
2. For every m0,m1,q:ℝ^K→ℝ, assume **all three are measurable** and m0(X),m1(X) are **separately μ-integrable**. If either (a) each md is the arm-specific CEF of Y and there is η>0 with η<q(X)<1−η μ-a.s., or (b) q(X)=p(X) μ-a.s., then
   E(Y1−Y0)=E[m1(X)+D(Y−m1(X))/q(X)−m0(X)−(1−D)(Y−m0(X))/(1−q(X))].

The separate integrability requirements precede the disjunction and apply to both branches. The nuisance overlap requirement in branch (a) is unnecessary in branch (b), where it follows from equality with p. The expectations on the right are ordinary integrable scores under these assumptions.

## SAP.P001g.T118

This theorem is a conjunction of **negations**.

1. It is not the case that, for every probability space, every iid measurable real sequence X, every functional T:(ℝ→ℝ)→ℝ, and `CDFHadamard T F` with F the law-CDF of X0, there exists a real φ>0 for which sqrt(n)[T(F_n)−T(F)] converges in distribution to N(0,φ²). Here F_n is the CDF of the empirical probability measure for n>0. No moment assumption on X is in this universal assertion. Its negation says that some such space, sequence, and differentiable functional do not have **any positive-variance** normal limit of that form.
2. It is not the case that, for every probability measure ν on ℝ with a finite second moment, there exists a continuous real linear L:ℓ∞(ℝ)→ℝ such that the mean functional is Hadamard differentiable at the embedded CDF of ν, with domain all finite-second-moment CDFs and tangent set **all** of ℓ∞(ℝ). The derivative is tested along positive t_n and domain-feasible perturbations as defined above. Thus some finite-second-moment law has no such derivative.

This theorem does not assert a positive general plug-in limit result or identify particular counterexamples in its type.

## SAP.P001g.T120

The theorem negates the following universal implication (hence asserts the existence of a failure of it). Quantifier order inside the negation:

* Every probability space; K,τ∈ℕ; sequences X_i:Ω→ℝ^K and Y_i:Ω→ℝ whose pairs are iid.
* Every S-finite measure κ on ℝ, probability measure νX on ℝ^K, true density f(y,x) and model density g(y,x,t), with the law of (X0,Y0) equal to (νX⊗κ) weighted by f; every parameter set Θ⊆ℝ^τ.
* Hypotheses: f≥0 everywhere; ∫f(y,x)dκ=1 for every x; joint measurability of f; for every t∈Θ, joint measurability of g(·,·,t), its pointwise nonnegativity, and ∫g(y,x,t)dκ=1 for every x.
* Every fixed x with νX({x})>0, every tstar∈Θ, with: for every t∈Θ, κ-a.e. y satisfies f(y,x)>0⇒g(y,x,t)>0; the conditional KL integrand f(y,x)log(f(y,x)/g(y,x,t)) is κ-integrable; and, for every t∈Θ, KL(x,tstar)≤KL(x,t) with equality only if t=tstar.
* Every estimator sequence that_n:Ω→ℝ^τ taking values in Θ at **every** n,ω, and maximizing the actual product ∏_{i<n}g(Y_i(ω),X_i(ω),t) over all t∈Θ at **every** n,ω.
* The negated conclusion is that_n→tstar in probability.

No estimator measurability, compactness of Θ, expected-log uniform convergence, or agreement of fixed-x and unconditional KL optima is an assumption. The covariate x explicitly has positive probability. The KL support and integrability safeguards are only imposed at that x.

## SAP.P001g.T121

For p,a,b∈ℝ let q(p,a,b)=(p(1−a),pa,(1−p)(1−b),(1−p)b), a mass function on four outcomes for p,a∈[0,1] and b∈[1/4,3/4]. The theorem negates the following universal assertion:

For every probability space, every iid sequence X_i:Ω→Fin 4, b0∈[1/4,3/4] with law(X0)=q(1,1/3,b0)=(2/3,1/3,0,0), and every family of estimators that_n:(Fin n→Fin 4)→ℝ³, if for **all** n and sample vectors s their coordinates lie in [0,1]×[0,1]×[1/4,3/4], and for **all** n,s,p∈[0,1],a∈[0,1],b∈[1/4,3/4] the product likelihood at (p,a,b) is at most its value at that_n(s), then that_n(X0,…,X_{n−1}) converges in probability to (1,1/3,b0).

Thus it asserts a failure of universal full-vector MLE consistency at a boundary mixing weight with an inactive second component. Every estimator is a function of the finite sample, and likelihood maximization is required even for sample vectors of true probability zero. There is no efficiency or asymptotic-variance clause in the proposition being negated.

## SAP.P001g.T124

On twelve cells j=0,…,11 define x_j=−1,0,1 according as floor(j/4)=0,1,2; z_j=−1 if j mod 4<2 and +1 otherwise; d_j=1 if j is odd and 0 if it is even; w_j=x_j²+z_j/2. Write r_j=(1,x_j) and f_j=(1,x_j,w_j).

For a length-n cell sample s define q_j=n⁻¹#{i:s_i=j}. For either design R define G_R(q)=∑_j q_j R_jR_jᵀ, c_R(q)=∑_j q_j R_j d_j, b_R(q)=G_R(q)⁻¹c_R(q), and risk_R(q)=∑_j q_j(d_j−R_jᵀb_R(q))². `placeboGood(s)` means n>3, det G_r(q)≠0, det G_f(q)≠0, and risk_f(q)>0. `placeboF(s)` is the ordinary F statistic from regressing the sample d's on [1,x] versus [1,x,w], with one added regressor and n−3 residual degrees of freedom.

There exist a measure μ on the sequence space ℕ→Fin 12 and a real sequence critical_n such that, in order:

1. μ is a probability measure.
2. The sequence of triples ((x_{ω_i}),(w_{ω_i}),d_{ω_i}) is iid, with x and w viewed as one-dimensional vectors.
3. The time-zero X map is measurable (an existentially quantified proof hX), and W0 ⟂ D0 | X0 in the indicator conditional-expectation sense above.
4. For all i and all ω, d_{ω_i}∈{0,1}.
5. μ-a.s., for all sufficiently large n, the sample (ω0,…,ω_{n−1}) is good.
6. For every n>3, the actual F(1,n−3) reference CDF at critical_n equals 1/2. The natural subtraction n−3 is positive under this guard.
7. Pμ(sample good AND placeboF(sample)>critical_n) tends to 1.

The statement chooses the data law existentially; it does not specify cell probabilities. Its rejections cannot be produced by the zero-inverse or zero-denominator fallback conventions, because the event includes all the stated guards.

## SAP.P001g.T125

For every probability space and iid measurable real sequence X with E|X0|²<∞, the sample mean converges in probability to E X0. There is no positive-variance hypothesis; constants are included.

## SAP.P001g.T126

Three independently universally quantified assertions are conjoined. In each, take a probability space and iid measurable real X with E|X0|²<∞ and v=Var(X0)>0.

1. sqrt(n)(bar X_n−E X0) converges in distribution to N(0,v).
2. Set Z_n=(bar X_n−E bar X_n)/sqrt(Var(bar X_n)). Then Z_n converges in distribution to N(0,1).
3. For every n∈ℕ with n>0, sqrt(Var(bar X_n))=sqrt(v)/sqrt(n); **for every ω**,
   Z_n(ω)=sqrt(n)(bar X_n(ω)−E X0)/sqrt(v);
   E Z_n=0; Var(Z_n)=1; and sqrt(Var(Z_n))=1.

The finite identity in part 3 is pointwise, whereas the moment expressions integrate over μ. All standardization denominators in that part are positive.

## SAP.P001g.T127

For every probability space, iid measurable real sequence X, real function f that is a PDF of law(X0) in the full `HasPDF` sense, hypothesis that f is continuous on **all of ℝ**, and bandwidth sequence h_n>0 at **every** n, if h_n→0 and nh_n→+∞, then for every x∈ℝ the estimator

fhat_n(x)=(1/n)∑_{i<n}K((x−X_i)/h_n)/h_n,

with K(t)=1/2 for |t|≤1 and 0 otherwise, converges in probability to f(x). The order is ∀data,∀bandwidth satisfying the limits,∀x. This is pointwise consistency, not uniform convergence over x. There is no bounded-density or moment assumption.

## SAP.P001g.T128

For every probability space, real estimator sequences that_n and vhat_n measurable for every n, assume vhat_n(ω)≥0 for **all** n,ω. For every real θ,φ,α,z with φ>0, 0<α<1, and Φ(z)=1−α/2, assume sqrt(n)(that_n−θ) converges in distribution to N(0,φ²), and n vhat_n converges in probability to φ² (`VarianceConsistent`). Then there exists a real c with c≥1−α such that

Pμ(θ∈(that_n−z sqrt(vhat_n),that_n+z sqrt(vhat_n)))→c.

The interval is open. The quantile z is any real satisfying the exact standard-normal CDF equation. The conclusion only asserts existence of a coverage limit at least nominal, not equality with 1−α. Neither sampling nor iid assumptions are imposed beyond the two stated asymptotic premises.

## SAP.P001g.T129

This is the conjunction of the following **independent** assertions.

1. **Product-MLE consistency.** Quantify, in order: a probability space; K,τ∈ℕ; sequences (X_i,Y_i) with values in ℝ^K×ℝ that are iid; a probability νX and S-finite κ; model g and parameter set Θ; compactness of Θ; θ∈Θ; joint measurability, pointwise nonnegativity, and κ-integral one in y for every x and every t∈Θ; equality of law(X0,Y0) with `conditionalModelLaw νX κ g θ`; integrability of log g(Y0,X0,t) for every t∈Θ; strict positivity g(Y0,X0,t)>0 μ-a.s. **for each t separately**; continuity on Θ of M(t)=E log g(Y0,X0,t); and, for every t∈Θ, M(t)≤M(θ), with equality implying t=θ. Next quantify an estimator that_n, assume each is measurable, its values belong to Θ at every n,ω, and for every n,ω,t∈Θ its actual product likelihood dominates the likelihood at t. Finally quantify a real-valued Δ_n(ω) with |sample-average log g(t)−M(t)|≤Δ_n(ω) for **every** n,ω,t∈Θ, and assume Δ_n→0 in probability. Conclude that_n→θ in probability. No measurability or nonnegativity of Δ is separately postulated; nonnegativity follows since θ∈Θ and it bounds an absolute value. The positivity premise is not explicitly a simultaneous positivity premise across all parameters.
2. **Expected-log maximum.** Quantify a fresh probability space; K,τ∈ℕ; measurable X:Ω→ℝ^K and Y:Ω→ℝ; probability νX and S-finite κ; model g; set Θ and θ∈Θ. Assume joint measurability, pointwise nonnegativity and κ-normalization of g for every t∈Θ and every x; law(X,Y) equals the true model with θ; for each t∈Θ, (νX⊗κ)-a.e. (x,y) satisfies g(y,x,θ)>0⇒g(y,x,t)>0; and log g(Y,X,t) is μ-integrable for every t∈Θ. Conclude, for every t∈Θ, M(t)≤M(θ), and M(t)=M(θ) **if and only if** g(Y,X,t)=g(Y,X,θ) μ-a.s.

Part 2 assumes no compactness, identifiability, sampling, estimator, or uniform-convergence envelope. There is no separate product/log identity or uniqueness-of-sample-maximizer conclusion in either part.

## SAP.P001g.T130

For every probability space and real sequences Y_i,R_i, assume each Y_i and R_i is measurable. Quantify real a,b with a≤b; for every i assume Y_i∈[a,b] μ-a.s. and R_i∈{0,1} μ-a.s.; assume P(R0=0)>0 and P(R0=1)>0; and assume the **observable pairs** (Y_i*,R_i) are iid, where Y_i*=Y_iR_i−99(1−R_i). Latent pairs (Y_i,R_i) are not assumed iid.

Set L_i=Y_i*R_i+a(1−R_i), U_i=Y_i*R_i+b(1−R_i),
ℓ=E[Y0*|R0=1]P(R0=1)+aP(R0=0),
u=E[Y0*|R0=1]P(R0=1)+bP(R0=0),
where the displayed conditional mean is its positive-atom integral/probability ratio. Conclude simultaneously E L0=ℓ, E U0=u; for every n>0, E bar L_n=ℓ and E bar U_n=u; bar L_n→ℓ in probability; and bar U_n→u in probability. The theorem type does not additionally assert sharpness of the endpoints or the inequality ℓ≤E Y0≤u.
