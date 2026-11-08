# Blind source and closure reading

This file is the stage-1 reading, saved before decoding `claims.json`, `record.json`, or `binding.json`. All 43 files in `INPUT-INVENTORY.json` matched their SHA-256 hashes. The three sealed JSON files were processed as opaque bytes for that check. I read the complete sources of both Challenge parts, all six Defs parts, WholeW1, WholeW2, the two import aggregators, and every entry in `closure.json`. The closure's generated `_proof_*` entries are elaboration support for the displayed finite indices, numeric nonnegativity/probability witnesses, and notation/typeclass arguments; their originating source expressions have been read. Their compiled proof terms were not printed: the local machine has no Lean executable and the authorized SSH attempt was blocked. I have not used the accepted certificate as evidence of semantic fidelity.

## Notation and complete common unfolding

These conventions apply in each section below; using E, Var, Cov, C, A, P, R, a*, or b* is an abbreviation for the formulas here, not an opaque SAP predicate. All random variables in this unit are real valued except the indicated finite vectors and empirical processes. A quantified probability measure means a Mathlib `Measure` with `IsProbabilityMeasure`; consequently its total mass is one. `MemLp Z 2 μ` means a.e. strong measurability and finite L2 seminorm. In this setting it supplies square integrability and integrability. An explicit `Measurable` hypothesis additionally selects an everywhere measurable representative. `=ᵐ[μ]` means equality outside a μ-null set. `μ.map Z` is the pushforward law, and `gaussianReal m v` uses **variance** v in the nonnegative reals, not standard deviation v.

* `probability μ A` is `(μ A).toReal`; write Pμ(A). `expectation μ Z` is the Bochner integral `∫ Z dμ`; write EμZ. Under the finite moments in use, Varμ(Z) is Eμ[(Z−EμZ)²], and Covμ(Z,W) is Eμ[(Z−EμZ)(W−EμW)]. `evariance` is the nonnegative extended variance, retaining ∞. `meanSquaredError μ Z c` is Eμ[(Z−c)²].
* `cdfAt μ Z x` is Pμ{Z≤x}. Write FZ(x) for it. `convergesInProbability μ Z c` means, in quantifier order, for every real ε>0, Pμ{dist(Zn,c)≥ε} tends to zero as n→∞. Its limit c is deterministic. For real variables dist is absolute difference; for CDFSpace it is the sup-norm distance.
* `convergesInDistribution μ Z ν` means: for every real x at which t↦Pν((−∞,t]) is continuous, Pμ{Zn≤x}→Pν((−∞,x]). This unit uses ν a probability law, including degenerate Gaussian/Dirac laws.
* `isIID μ X` is the conjunction: every Xi is measurable, the whole indexed family is mutually independent (`iIndepFun`), and every Xi has identical distribution to X0 (`IdentDistrib`, including its a.e. measurability). It is not just pairwise independence.
* `sampleAverage X n ω`, denoted A_n(X), is n⁻¹∑_{i=0}^{n−1}Xi(ω). `pluginVariance X n`, denoted P_n(X), is A_n(X²)−A_n(X)². `empiricalLaw X n ω` is `(n:ENNReal)⁻¹ • ∑_{i<n} dirac(Xi(ω))`.
* `correlationCoefficient μ X Y` is C=Covμ(X,Y)/(sqrt(VarμX) sqrt(VarμY)). `affineRisk μ X Y a b`, denoted R(a,b), is Eμ[(Y−a−bX)²]. `regressionSlope` is b*=Covμ(X,Y)/VarμX, and `regressionIntercept` is a*=EμY−b*EμX.
* `isConditionalMean μ X Y m` means m is measurable on the value space of X, Y and m∘X are integrable, and for **every measurable set B in that value space**, ∫_{X⁻¹B}Y dμ=∫_{X⁻¹B}m(X) dμ. For real X, m is Borel measurable. This is the event-integral specification of a version of the conditional mean, not pointwise conditioning on an event of probability zero.
* For w,x,y:Fin n→R, `finiteMean` is ∑i wi xi; `finiteProbability w Q` is ∑i(if Q(i) then wi else 0); `finiteVariance` is ∑i wi(xi−∑j wj xj)²; `finiteCovariance` is ∑i wi(xi−∑j wj xj)(yi−∑j wj yj); and `finiteCorrelation` divides that covariance by the two square roots of those variances. These definitions do not themselves enforce PMF conditions. `nullWeights`=(1/2,1/2,0), `signWeights`=(1/2,1/2), `equalWeights N` assigns 1/N to each of N indices. In their actual uses these are probability weights with N>0.
* `fairCoinLoss(c)`=((0−c)²+(1−c)²)/2. `normalPDF(m,s,y)`=exp(−(y−m)²/(2s²))/(s sqrt(2π)). `bivariatePDF(mx,my,sx,sy,r)(x,y)`=exp(−[((x−mx)/sx)²+((y−my)/sy)²−2r(x−mx)(y−my)/(sx sy)]/[2(1−r²)])/[2π sx sy sqrt(1−r²)]. `isJointDensity ν f` asserts a.e. measurability with respect to two-dimensional Lebesgue measure, nonnegativity **at every point**, Lebesgue integrability, and ν=volume.withDensity(ofReal∘f). It does not by itself normalize f; the statements separately assert that ν is a probability measure.
* `intervalUniform(a,b)` is Lebesgue measure with density ofReal(1_[a,b](x)/(b−a)). The only interval used in a target statement is [0,1].
* `covarianceEntries μ X j k` is Covμ(Xj,Xk). `affinePredictor b x`=b0+∑_{k:Fin K} b_{k+1}xk. `coordinatePartial f x k` is `deriv(t↦f(update x k (xk+t))) 0`, the ordinary one-variable derivative value. `affineResidual X Y b`=Y−b0−∑k b_{k+1}Xk. `finiteAffineLosses` means that **for every coefficient vector c** its squared residual is integrable. `minimizesAffineLoss ... b` means that **for every coefficient vector c**, E(residual_b²)≤E(residual_c²); it contains no residual identities, uniqueness, or nonsingularity assumption.
* `varianceConsistent μ V v` is nVn→v in probability. `standardErrorConsistent μ V v` is sqrt(n)sqrt(Vn)→sqrt(v) in probability. `unbiasedSampleVariance`, S_n, is [n/(n−1)]P_n (subtraction after casting n to R). `wholeMeanVarianceEstimate`, V_n, is S_n/n.
* `powerTailMass(k)`=7(1/8)^(k+1). `endpointLaw` is geometricMeasure with success parameter 1/2, so its atom k has mass (1/2)^(k+1). `endpointSequence n k`=1_{k=n}. `powerTailLaw` is geometricMeasure with success parameter 7/8, atom k of mass 7/8^(k+1); `powerTailValue(k)`=2^k; `powerTailProduct` is the countable product of these geometric laws; `powerTailSample i ω`=2^(ωi).
* `hadamardDerivative D H T F L` uses a continuous R-linear map L and asserts: for every h∈H, then every sequence tn in R and hn in the normed space, if all tn>0, tn→0, hn→h, and F+tn hn∈D for every n, then [T(F+tn hn)−T(F)]/tn→Lh. `supNorm h` is the real supremum of {|h(x)|:x∈R}. `isCDF F` requires values in [0,1], monotonicity, right continuity at every real x, and limits 0 at −∞ and 1 at +∞. `cdfHadamard T F` asserts existence of an R-linear function L on all real functions, bounded by C supNorm(h) for bounded h with some C≥0; for each bounded h and bounded hn converging uniformly to h and positive tn→0 with F+tn hn a CDF, the same difference quotient converges to Lh.
* `CDFSpace` is `lp (fun _:R => R) ∞`, the Banach space of bounded real functions on R with its supremum norm. `embedCDF f` is f in this space if f is bounded (`Memℓp f ∞`), otherwise zero. `cdfSet` is the subset satisfying the preceding CDF axioms. `empiricalCDF X n ω` embeds the CDF of the empirical measure. `cdfTangent F` consists of bounded h uniformly continuous for the pseudodistance |F(x)−F(y)|, with h(x)=0 wherever F(x)=0 or F(x)=1.
* `isCDFBridge F ν` asserts ν((cdfTangent F)^c)=0 and, **for each finite r, each x:Fin r→R and a:Fin r→R**, v=∑jk aj[min(F(xj),F(xk))−F(xj)F(xk)]ak≥0 and the law under ν of ∑j aj h(xj) equals gaussianReal(0,max(v,0)). Probability and tightness are separate assertions in T57. This specifies the centered Gaussian finite-dimensional bridge laws and its supported function class.
* `upperExpectation μ Z` is the real infimum of expectations of measurable integrable g with Z(ω)≤g(ω) **for every ω**. `outerWeakConvergence μ Zn ν` requires for **every bounded continuous f:E→R** both upper expectations of f(Zn) and lower expectations −upperExpectation(−f(Zn)) to converge to ∫f dν. Process measurability is not required by this definition. The scalar plug-ins are separately required measurable.
* `quadraticFunctional G`=(G(0)−1/2)². `cdfFunctionalValue T f`, for T:cdfSet→R, is T(f) when f is a CDF and zero otherwise. `cdfHadamardOn T F H ell` is the sequential definition above for **every h in the real submodule H**, with continuous linear derivative ell defined on H; approximating hn need not belong to H, but F+tn hn must belong to cdfSet. Its difference quotient uses cdfFunctionalValue. H is not required closed.

## SAP.P001c.T39

Source: Challenge/Part1:7–18; Defs/Part4:13–31; WholeW2:57–102; the density, moments, and correlation definitions above. Quantification over Ω in the whole statement is universal (at its universe level), not a choice of a special probability space.

The first conjunct, for every Ω, has two parts. (1) For every probability μ on Ω, n∈N, measurable mutually independent Xi (i:Fin n), real vectors mi,ai, nonnegative variance parameters vi which are all strictly positive, with law(Xi)=N(mi,vi), and with at least one ai≠0, **for every real b**, law(∑i aiXi+b)=N(∑i aimi+b,∑i ai²vi), and ∑i ai²vi>0. (2) For every real mx,my,sx,sy,r with sx,sy>0 and −1<r<1, define f as the bivariate formula above and ν=f dxdy. Then ν is a probability, has precisely that density, both coordinate maps are L2, their means are mx,my, their standard deviations sx,sy, and C=r. If r=0, they are independent and **at every (x,y)** f(x,y)=normalPDF(mx,sx,x)normalPDF(my,sy,y).

The second whole conjunct: for every probability μ and measurable X with law N(m,s²), with m∈R and s>0, X is L2, EX=m, sqrt(Var X)=s. The third (`wholeBivariateTransport`) quantifies every Ω, probability μ, measurable X,Y, then mx,my,sx,sy,r as above, then equality of the joint pushforward to f dxdy. It concludes L2 of X,Y, their marginal laws N(mx,sx²), N(my,sy²), the displayed means, standard deviations, correlation r, and independence when r=0. Finally, a **fixed** law on R² with density [f_(r=3/5)+f_(r=−3/5)]/2 is a probability with this joint density, both coordinate marginal laws N(0,1), both coordinates L2, correlation zero, and nonindependent coordinates.

Junk audit: positive sx,sy and |r|<1 keep every density division and square root in its intended domain; positivity of the finite combination variance excludes a degenerate normal in that clause. n=0 has no nonzero coefficient and is excluded by the existential premise. Gaussian parameters are NNReal variances. The mixture uses only valid nonsingular parameters. All moment and correlation uses have finite positive marginal variances. `ofReal` does not discard any negative density under these parameters. No log, real power, truncated subtraction, infimum, partial-function default, or nonintegrable expectation is used substantively.

## SAP.P001c.T40

Source: Challenge/Part1:20–27; Defs/Part4:33–46 and the loss/moment definitions above. For each Ω with a measurable space, the theorem conjoins a universal probability statement and fixed arithmetic facts. For every probability μ and X∈L2, **for every c∈R**, E(X−c)²=Var X+(EX−c)²; E(X−EX)²≤E(X−c)², with equality iff c=EX. For every c, fairCoinLoss(c)=c²−c+1/2≥1/4, equality iff c=1/2, and twice that loss equals (0−c)²+(1−c)². The loss at −2,2,1/2 is respectively 13/2,5/2,1/4. The fair two-outcome variable (0,1) has mean 1/2, variance 1/4, and its finite weighted squared error equals fairCoinLoss(c). For every c, twice the loss is 2c²−2c+1, with values 13,1/2,5 at −2,1/2,2. The docstring explicitly omits the derivative computation and identification of the actual drawn curve.

Junk audit: all arithmetic denominators are 2 or 4. L2 on a probability space ensures every general loss and variance is finite. The finite PMF is normalized and positive. No derivative default arises because the derivative calculation is absent.

## SAP.P001c.T41

Source: Challenge/Part1:29–35; Defs/Part4:48–66. This is a closed finite statement with no random-variable or measure hypotheses. On the three indices with weights (1/2,1/2,0), put X=(0,1,0), Y+=(0,1,1), Y−=(1,0,0). All three means are 1/2, variances 1/4 (also explicitly strictly positive). Cov(X,Y+)=1/4, Cov(X,Y−)=−1/4; the corresponding correlations are 1 and −1. The weighted probability of Y+=X is one, as is that of Y−=1−X. Nevertheless there do not exist reals a,b with Y+(i)=a+bX(i) **for every i**, nor a,b with Y−(i)=a−bX(i) **for every i**. These nonexistence assertions quantify all real b, so they also exclude b>0. At i=0 and i=2, X is the same and each Y differs. The docstring presents this as a pointwise-affine counterexample.

Junk audit: the zero-mass third outcome is intentional and remains part of the pointwise universal quantifier. It is not an empty type or a division-by-zero argument. Both correlations divide by sqrt(1/4)²>0. Direct sums are legitimate probabilities for the displayed weights; no integrals or infinity conversions occur.

## SAP.P001c.T42

Source: Challenge/Part1:37–41; Defs/Part4:68–73. For every Ω with its measurable space, probability μ, and real X,Y, first assume X,Y∈L2 and Var X,Var Y>0. Then C∈[−1,1]; C=1 iff **there exist a,b∈R with b>0** such that Y=a+bX μ-a.s.; C=−1 iff **there exist a,b∈R with b>0** such that Y=a−bX μ-a.s. The conclusions concern versions up to null sets, not pointwise equality.

Junk audit: all denominators and square-root products are strictly positive. L2 supplies moment existence, including the covariance product. A.e. measurability is sufficient for these assertions, and no empty or unbounded supremum is involved.

## SAP.P001c.T43

Source: Challenge/Part1:43–54; WholeW2:104–176. For every Ω, probability μ and **measurable** X,Y∈L2, the following all hold, before any positive-variance condition is imposed.

First R:R²→R is C∞. For **all a,b**, its a-partial is certified by `HasDerivAt` to be −2E(Y−a−bX), and its b-partial to be −2E[(Y−a−bX)X]. Both second pure partials are certified derivatives, 2 and 2EX²; both mixed orders are certified derivatives, 2EX. The determinant expression 2(2EX²)−(2EX)² equals 4Var X. Second, a Borel conditional-mean function m:R→R exists and m(X) is L2; **every** event-integral conditional-mean version is L2.

If Var X>0, the pair of normal equations E(Y−a−bX)=E[(Y−a−bX)X]=0 holds iff a=a*,b=b*, for every a,b. R(a*,b*)≤R(a,b), with equality iff those same coefficient equalities hold. The Hessian determinant is positive. With residual e=Y−(a*+b*X), Ee=E(Xe)=Cov(X,e)=0. **For every conditional-mean version m**, a*+b*X minimizes E[(m(X)−a−bX)²] over a,b. If **any** affine x↦a+bx is a conditional-mean version, then m(X)=a*+b*X μ-a.s. for every version m.

If Var X=0, X=EX μ-a.s. For **every g,h:R→R with g(X),h(X) measurable**, g(EX)=EY implies E[(Y−g(X))²]=Var Y and that this loss is at most E[(Y−h(X))²]. For all a,b, R(a,b)=Var Y iff a+bEX=EY. For each such a,b the residual Y−a−bX has zero mean, zero product expectation with X, and zero covariance with X. This describes all affine minimizers because an affine constant EY attains Var Y.

Junk audit: the b*,a* divisions are used only in the Var X>0 branch; the zero-variance branch does not assert their formula is a unique coefficient pair. When Var X=0, arbitrary finite-valued h(X) is μ-a.s. the constant h(EX); its integrability and squared-loss integrability follow, so this clause cannot exploit the Bochner zero convention. Nonmeasurable compositions are expressly excluded. Derivative values appear with actual `HasDerivAt` certificates, including both mixed orders, preventing use of `deriv`'s zero default. Conditional laws are for real values; the event-integral definition and probability/L2 hypotheses support existence and uniqueness up to null sets.

## SAP.P001c.T44

Source: Challenge/Part1:56–64; Defs/Part4:105–113. A fixed fair two-outcome X=(−1,1) has variance one. For Y=X, two candidate affine predictors p=X and q=1+X=(0,2) have Cov(X,p)=Cov(X,q)=1. The weighted loss E(Y−q)² is one, p≠q as functions on Fin 2, and E(Y−p)²=0. The statement contains these explicit calculations; it does not separately quantify a general uniqueness assertion or prove Cov(X,a+bX)=b Var X. The docstring calls the printed claim false and discloses retaining only counterexample (a), omitting (b) and that general formula.

Junk audit: all quantities are finite sums with weights (1/2,1/2); the index type is nonempty, and the distinctness is present on positive-mass outcomes. No undefined covariance, default integral, or zero denominator supports this example.

## SAP.P001c.T45

Source: Challenge/Part1:66–69; Defs/Part4:115–126. For every Ω, probability μ and X,Y∈L2, assume Var X>0. **For every real a,b**, Cov(X,a+bX)=Cov(X,Y) iff b=b*. The conjunction of that covariance equation and E(a+bX)=EY holds iff b=b* and a=a*. Also **for every a,b**, R(a*,b*)≤R(a,b), with equality iff a=a*,b=b*. Thus the covariance equation alone quantifies an unrestricted intercept; adding the mean equation determines it.

Junk audit: positive Var X justifies division for b*. All affine candidates have finite loss and covariance under L2; no default derivative or a.e.-versus-pointwise ambiguity enters coefficient equality.

## SAP.P001c.T46

Source: Challenge/Part1:71–79; Defs/Part4:128–140; WholeW2:186–210. Four universally quantified parts are conjoined.

(1) For every Ω, probability μ and measurable independent X,W with law(X)=Uniform[0,1], law(W)=N(0,1), let Y=10X²+W. Then X,Y∈L2; x↦10x² is a conditional-mean version of Y given X. EX=1/2, EX²=1/3, EX³=1/4, Var X=1/12, EY=10/3, Cov(X,Y)=5/6, b*=10, a*=−5/3. For **every a,b**, R(−5/3,10)≤R(a,b), with equality iff a=−5/3 and b=10.

(2) For every Ω, probability μ and measurable X,Y∈L2 with Var X>0, the a*,b* formulas give the global risk minimum, with equality precisely at that coefficient pair, for all a,b. (3) For every Ω, probability μ and measurable independent X,Y with Y integrable, the constant function EY is a conditional-mean version of Y given X; no moment assumption on X is imposed. (4) For the independent uniform/normal setting of part (1), x↦x² is a conditional mean of X² given X and zero is a conditional mean of W given X. Mathlib conditional expectations onto the comap sigma-algebra of X satisfy E[Y|X]=10 E[X²|X]+E[W|X] a.s. and E[Y|X]=10X² a.s. Further Cov(X,Y)=10[EX³−EX EX²], b*=10[(1/4)−(1/2)(1/3)]/[(1/3)−(1/2)²], and a*=(10/3)−10/2.

Junk audit: Uniform[0,1] uses a positive interval length; Gaussian variance is one. Bounded X and normal W supply all moments used, including the squares in the losses. The conditional-expectation sigma-algebra is below the original sigma-algebra because X is measurable; its finite measure is sigma-finite, and the conditional integrands are integrable. Thus the conditional-expectation default for invalid data is not at issue. The regressor variance is 1/12 in the example and assumed positive in the general minimization clause.

## SAP.P001c.T47

Source: Challenge/Part1:81–92; WholeW2:215–267. Three universal statements are conjoined. First, for every probability μ and measurable real X,Y, independence of X,Y is equivalent to: **for every Borel g,h:R→R**, g(X),h(Y) are independent. Second, for every such independent pair:

* if Y is integrable, the constant EY is a conditional-mean version of Y given X;
* if Y∈L2, the constant Var Y is a conditional-mean version of (Y−EY)² given X;
* if X,Y are integrable, XY is integrable, E(XY)=EX EY and Cov(X,Y)=0;
* if X,Y∈L2, Var(X+Y)=Var X+Var Y, C=0 when **both** variances are positive, and the affine constant EY minimizes R. If Var X>0, b*=0,a*=EY, and R(a,b)=R(EY,0) iff a=EY,b=0 for every a,b;
* for **every Borel g,h**, the transformed variables are independent. If h(Y) is integrable their conditional mean given g(X) is the constant E[h(Y)]. If both transformed variables are L2, the preceding best-affine and positive-variance uniqueness statements apply to them.

Third, for every probability μ and measurable X,Y∈L2 with Var X>0, independence is not assumed: a*,b* uniquely minimize R over all a,b. Thus the transformed conditional mean is explicitly E[h(Y)|g(X)]=E[h(Y)], with the same orientation as the outcome h(Y).

Junk audit: product integrability is concluded under independence and individual integrability, rather than silently assumed from L1 alone. Second moments are required only for clauses using variances or loss; positivity is required for the correlation denominator and for coefficient uniqueness. Zero-variance independent regressors still have the (possibly nonunique) constant best predictor. All transformed functions are Borel. The constant conditional-mean definition adds no probability-zero conditioning convention.

## SAP.P001c.T48

Source: Challenge/Part1:94–99; Defs/Part5:32–39. For every Ω, probability μ, natural K, and vector X:Ω→(Fin K→R), assume **for every coordinate k** Xk∈L2. The matrix Σjk is Cov(Xj,Xk) for all j,k, Σ is symmetric, Σkk=Var Xk for every k, and Var(∑k Xk)=∑j∑k Cov(Xj,Xk). The first entry identity unfolds the matrix definition; the remaining identities are assertions about those genuine covariances.

Junk audit: K=0 is allowed, giving an empty matrix and both sums/variance zero, while all positive K remain quantified. All sums are finite; coordinate L2 ensures finite cross moments. No positive-definiteness or invertibility is silently added, and no division or supremum occurs.

## SAP.P001c.T49

Source: Challenge/Part2:8–14; Defs/Part5:41–47; WholeW1:16–50. The deterministic part quantifies **every K∈N, coefficient vector b∈R^(K+1), then x∈R^K**. The affine predictor at zero is b0; for **each k:Fin K**, increasing xk by one increases it by b_(k+1). The scalar function of the kth coordinate has derivative b_(k+1) at xk, and coordinatePartial as unfolded above equals that slope.

The stochastic part quantifies every Ω, probability μ, K, vector X and outcome Y; assume each Xk and Y measurable, and **every candidate coefficient vector has integrable squared residual**. Then **for every b** which globally minimizes the squared-residual expectation, E e_b=0 and, **for every k**, E(Xk e_b)=0 and Cov(Xk,e_b)=0. It does not assume a residual identity or an invertible covariance matrix in its premises and does not assert uniqueness or construct a minimizer.

Junk audit: K=0 retains an intercept and its zero-mean residual conclusion; coordinate claims then have an empty index. K>0 remains covered. By using the zero coefficient vector and vectors selecting one coordinate, finiteAffineLosses implies L2 of Y and all Xk, so the cross products and covariances are legitimate. All derivative values have `HasDerivAt` evidence. Minimization is an ordinary comparison of finite Bochner integrals, not comparisons of junk zeros.

## SAP.P001c.T50

Source: Challenge/Part2:16–20; Defs/Part5:49–70. The first conjunct quantifies **N∈N with N>0, then every x:Fin N→R**. At each t the weighted mass of {xi=t} is its number of occurrences divided by N; mean is ∑i xi/N, variance ∑i(xi−∑j xj/N)²/N. The fixed population (3,4,3,10) has value set {3,4,10}, respective masses 1/2,1/4,1/4, mean 5 and variance 17/2. The general probability part quantifies every μ on the given Ω and Z∈L2 and asserts Var Z=EZ²−(EZ)² and EZ²+(EZ)²−Var Z=2(EZ)². Finally, **for every infinite deterministic real sequence x and every n>0**, its first-n empirical law (constructed on Unit) is a probability, has mean ∑_{i<n}xi/n, and variance ∑_{i<n}xi²/n−(∑_{i<n}xi/n)².

Junk audit: N>0 and n>0 exclude empty populations and zero reciprocal weights. Every empirical law is a finite supported probability with all moments finite. The erroneous plus-sign expression is compared algebraically to 2(EZ)², not declared a variance. The n=0 empirical-law convention is unused here. No undefined real infinite sum occurs.

## SAP.P001c.T51

Source: Challenge/Part2:22–27; WholeW1:52–78. First, **for every Ω, probability μ, sequence of measurable real Zn and c∈R**, convergence in probability to c is equivalent to: for every ε>0, P(|Zn−c|<ε)→1. It is also equivalent to: **for every p∈[0,1), then every ε>0, there exists N∈N, then for every n≥N**, p≤P(|Zn−c|<ε). N may depend on p and ε, and is not required uniform in them.

The fixed endpoint witness is the measurable sequence Zn(k)=1_{k=n} on the geometric probability law P{k}=2^(−(k+1)). It converges in probability to zero. For **every n**, P(|Zn|<1/2)=1−(1/2)^(n+1)<1. There is **no N** such that for every n≥N that probability is at least one. The witness is about the endpoint of an eventual bound, not failure of the probability limit to be one.

Junk audit: all probabilities are of measurable events under probability measures, so toReal is finite. The geometric parameter 1/2 is valid. Real powers here are natural powers with exponent n+1, never a problematic rpow domain. N and n are ordinary natural indices without truncated subtraction.

## SAP.P001c.T52

Source: Challenge/Part2:29–32; Defs/Part5:79–85. For every probability μ on the given Ω, (1) for every measurable X:Ω→R and every Borel D⊆R, E[1_D(X)]=P(X∈D); (2) for every real IID sequence Xi, **for each fixed x∈R**, A_n(1_{Xi≤x})→P(X0≤x) in probability. The statement does not assert uniform-in-x empirical CDF convergence.

Junk audit: indicators are measurable, bounded, and integrable, regardless of moments of Xi. The sample average is defined as zero for n=0 by division by zero; changing this first term cannot affect a limit at infinity. The μ probabilities are finite, and no unmeasurable threshold event or infinite toReal is involved.

## SAP.P001c.T53

Source: Challenge/Part2:34–42; Defs/Part5:87–95; WholeW1:80–125. First, the explicit masses pk=7/8^(k+1) are nonnegative and summable, sum to one, the weighted first and second powers of 2^k are summable and sum to 7/6 and 7/4, the **ENNReal** sum of weighted fourth powers is ∞, and 7/4−(7/6)²=7/18>0. Next the fixed countable product law on N^N is a probability, and its coordinate transforms Xi=2^(ωi) are IID. For **each i** and **each k**, P(Xi=2^k)=pk; Xi∈L2; E|Xi|=EXi=7/6; Xi² is integrable with expectation 7/4; Var Xi=7/18; its extended fourth moment is ∞; Xi² is not L2 and evariance(Xi²)=∞.

A separate universal theorem quantifies every Ω, probability μ and IID real Xi with X0∈L2 and Var X0>0. It concludes the finite-variance WLLN A_n(X)→EX0, E P_n=[(n−1)/n]Var X0 for every n>0, and P_n→Var X0 in probability. For the fixed heavy-tail product sequence, the same expectation identity is repeated with 7/18; P_n→7/18, A_n(X)→7/6 and A_n(X²)→7/4 in probability. The docstring identifies the counterexample as a failure of a finite-variance inference for the squares while retaining sample-variance consistency.

Junk audit: the divergent fourth moment and squared-variable variance use extended integrals/evariance, so ∞ is never silently converted to the real zero. The real infinite sums are explicitly summable. Every ordinary expectation asserted is integrable by the accompanying L2/integrability facts. The product uses genuinely independent draws. Bias denominators occur only at n>0; n−1 is real subtraction. The n=0 zero sample convention has no asymptotic effect.

## SAP.P001c.T54

Source: Challenge/Part2:44–51; WholeW1:127–153. Three statements are conjoined. (1) For every probability space and IID integrable real Zi, A_n(Z)→EZ0 in probability. (2) For every probability space, measurable sequences Sn,Tn with respective **constant** probability limits a,b, and **every continuous g:R²→R**, g(Sn,Tn)→g(a,b) in probability. No independence is assumed between these sequences. (3) For every probability space and IID Xi with X0∈L2 and Var X0>0, A_n(X)→EX0, A_n(X²)→EX0², EX0²−(EX0)²=Var X0, E P_n=[(n−1)/n]Var X0 for all n>0, and P_n→Var X0 in probability. No fourth moment appears in these premises.

Junk audit: the WLLN uses L1, and the squares are L1 from X0∈L2. The squares need not have a finite real variance; none is taken in this statement. General g has no expectation requirement because only its probability limit is asserted. Sample-size denominators and n=0 terms are as in T53. The a,b limits in the continuous-mapping clause are deterministic.

## SAP.P001c.T55

Source: Challenge/Part2:53–61; Defs/Part5:103–114; WholeW2:14–55. The first universally quantified block covers every probability μ, measurable real sequences thetaHat_n,Vhat_n, scalar θ, with Vhat_n(ω)≥0 **for every n,ω**, and every probability limit law ν on R with id∈L2(ν), assuming sqrt(n)(thetaHat_n−θ) converges in distribution to ν. Put v=Varν(id). It concludes the equivalences: nVhat_n→v iff nVhat_n−v→0 in probability; sqrt(n)sqrt(Vhat_n)→sqrt(v) iff its centered difference→0; and these variance and standard-error consistencies are equivalent.

The second block covers every probability space and IID Xi with X0∈L2 and v=Var X0>0, defining S_n=n/(n−1)P_n and V_n=S_n/n. It asserts measurability and pointwise nonnegativity of V_n **at every n**, then for n≥2 and every sample point the centered-squares formula S_n=∑_{i<n}(Xi−A_n X)²/(n−1) and V_n=P_n/(n−1). For every n≥2, ES_n=v and EV_n=Var(A_n X). For every n>0, n Var(A_n X)=v. The root-n centered mean converges in distribution to N(0,v). Also nV_n→v and sqrt(n)sqrt(V_n)→sqrt(v) in probability. For every n>0 and every point, nV_n−n Var(A_n X)=nV_n−v. Both of these centered variance sequences converge in probability to zero, as does the centered standard-error sequence sqrt(n)sqrt(V_n)−sqrt(v).

Junk audit: at n=0, A_0=P_0=S_0=V_0=0 under Lean real division; at n=1, P_1=0 and S_1=V_1=0 by 1/0=0. No finite-sample unbiasedness claim is made at these n; limits ignore them. n−1 is real subtraction, not truncated natural subtraction. v≥0 and Vhat,V≥0 ensure square roots in their actual domain. The general equivalences allow v=0 but still require Vhat≥0. Positive v is imposed for the IID normal limit. L2 ensures every exact variance identity uses finite quantities.

## SAP.P001c.T56

Source: Challenge/Part2:63–74; Defs/Part6:13–30, and the differentiability/CDF definitions above. For every Ω, probability μ and IID real Xi with X0 law (δ0+δ1)/2, let F(x)=P(X0≤x). The constant functional T(G)=7 has the normed-space Hadamard derivative zero at embedCDF(F), domain cdfSet, tangentially to the whole CDFSpace, and also satisfies the raw-function cdfHadamard predicate. For every n,ω, sqrt(n)(7−7)=0. For every strictly positive NNReal v, the identically zero sequence does **not** converge in distribution to N(0,v).

For Q(G)=(G(0)−1/2)², cdfHadamard Q F holds and Q(F)=0. For every n>0,
E[(sqrt(n) Q(F_emp,n))²]=(3n−2)/(16n²).
The sequence sqrt(n)Q(F_emp,n) converges in probability to zero. The theorem is conditional on any IID Bernoulli realization; it does not existentially construct one. It does not export the value of Q's derivative, the binomial distribution, or the limit of the displayed scalar second-moment formula. The docstring expressly lists these and other omissions.

Junk audit: probability and bounded Bernoulli laws make F and every positive-size empirical CDF bounded true CDFs; embedCDF's zero fallback cannot replace them. Supremum norms in cdfHadamard are only applied to bounded functions and differences of bounded directions, on nonempty R, so their suprema are finite. Positive tn prevents quotient-by-zero in the derivative predicates. These predicates quantify feasible paths; zero directions provide actual paths at a CDF, so the domain is not empty. The default value of deriv is not used in this target. At n=0 empiricalLaw is the zero measure (∞ times zero measure), whose CDF is zero, not a probability CDF; that initial term has no effect on the probability limit, and the moment formula requires n>0. For n>0 the displayed expectation is finite. The negative normal-convergence clause assumes v>0.

## SAP.P001c.T57

Source: Challenge/Part2:76–86; WholeW1:155–208; Defs/Part3:40–72. Universally quantify Ω with measurable space, a Borel measurable-space structure on CDFSpace, probability μ and an IID real sequence Xi. No moment hypothesis on Xi appears. Then **there exists one law ν on CDFSpace** which is a probability, whose singleton family is tight, satisfies the bridge definition for F=P(X0≤·), and is the outer weak limit of sqrt(n)(F_emp,n−embedCDF(F)). This ν is selected **before** the following arbitrary functional and tangent data.

For **every real submodule H⊆CDFSpace, continuous linear ell:H→R and function T:cdfSet→R**, assume ν(H^c)=0, cdfHadamardOn T F H ell, and, for every n>0, the scalar T of the empirical CDF (using cdfFunctionalValue) is measurable. Then **there exists a continuous linear L:CDFSpace→R** extending ell on H, with L∈L2(ν), EνL=0 and v=Varν(L)≥0. The pushforward ν.map L is N(0,v.toNNReal), and the scalar sqrt(n)[T(F_emp,n)−T(F)] converges in distribution to ν.map L. If v=0 that law is δ0. If v>0 there exists phi>0 with phi²=v and the scalar sequence converges in distribution to N(0,phi²). **For every other continuous linear extension L' of ell**, ν.map L'=ν.map L. H need not be closed and ell need not initially be defined on the whole Banach space.

Junk audit: CDFSpace is the bounded-function space, so its norms are genuine finite suprema. embedCDF is evaluated only on true bounded CDFs, except the harmless n=0 empirical zero function. cdfFunctionalValue's zero extension is used only outside cdfSet; F and all n>0 plug-ins lie in cdfSet, and its n=0 use does not affect a limit. The positive tn condition prevents zero difference quotients. With bounded continuous f on a probability space, upperExpectation has measurable integrable constant majorants, and all majorant expectations have a finite lower bound by a constant; neither the empty-infimum convention nor an unbounded-below real infimum is used. This handles possibly nonmeasurable empirical processes through outer/lower expectations. ν is a genuine probability, so its toReal probabilities are finite. v is a finite nonnegative variance by L2; toNNReal does not truncate a negative quantity, and the zero-variance Gaussian is intentionally Dirac. The bridge's max(v,0) does not alter its covariance parameters because nonnegativity is separately asserted. For H not closed, continuous linear extension is an asserted conclusion and its law is independent of the extension by ν(H^c)=0. No existence, Gaussianity, moment, or outer-convergence conclusion is packed into cdfHadamardOn's premises.

## Scope of checks at this stage

All source statements and all their SAP dependencies have been unfolded above, including the nested statement predicates that the whole statements actually use. Unused legacy statement predicates were also read in full, but are not substituted for the actual target types. I have not compiled scratch Lean. The read-only SSH preflight failed with `Operation not permitted` before any remote source read or remote write. Nonvacuity will therefore be argued with explicit mathematical probability spaces and witnesses at the claim stage, as permitted by the brief. No paper search, delegation, prior review, integration narrative, or external message has been used.
