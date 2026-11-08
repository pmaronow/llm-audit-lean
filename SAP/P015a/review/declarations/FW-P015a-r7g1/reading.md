# Blind statement reading

This file was written before opening `claims.json` or `record.json`. The sources read were `closure.json`, the five Challenge declarations and their docstrings, all source declarations in their closures, and the Mathlib definitions needed to interpret the analytic and probability notation. The 34 generated proof declarations in the union of the closures were all printed by `scratch/ClosurePrint.lean`; their complete output is in `scratch/closure-print.log`. They supply only numeral `AtLeastTwo`/`NeZero` instances and real/complex continuity instances. They add no mathematical assumptions.

Throughout the finite models, indices 0,1,2,3 mean elements of `Fin 4`. All outcome, probability, treatment, covariate and matrix entries are real. A finite sum below is a Mathlib `Finset.univ` sum. To make the unfolding unambiguous, write

* `E_p Z = sum_a p_a Z_a` and `P_p(E) = sum_a (if E(a) then p_a else 0)`.
* `E_p[Z|X=x] = (sum_a p_a (if X_a=x then Z_a else 0))/P_p(X=x)`.
* `P_p(D=d|X=x) = P_p(X=x and D=d)/P_p(X=x)`.
* `w_a = (D_a-E_p[D|X=X_a])^2` and `q_a=p_a w_a/(sum_b p_b w_b)`.
* `Var_p Z = sum_a p_a (Z_a-sum_b p_b Z_b)^2`.

These are actual finite sums and quotients, rather than unspecified conditional-expectation versions. A probability vector means every entry is nonnegative and the sum of the entries is 1. For a finite-atom variable U of any codomain, the package's conditional independence is exactly the identity

`P_p(X=x,U=u,D=d) P_p(X=x) = P_p(X=x,U=u) P_p(X=x,D=d)`

for every x,u,d. In these finite models this is the ordinary conditional independence condition. All finite probability spaces can carry their full sigma algebra, so measurability and finite moments are available.

## SAP.P015a.T1

Location: `SAP/P015a/Challenge/Part1.lean:9-18`; mathematical statement at `Defs/Part3.lean:13-24` and `Defs/Part2.lean:14-67`.

This is an unconditional conjunction about explicit data, not a conditional theorem about arbitrary populations. Put `e0=1/1000000`, `X=(0,0,1,1)`, `D=(0,1,0,1)`, and

`p(e)=((1-e)/2,e/2,1/4,1/4)`.

The potential outcome is `Y_a(d)=2X_a+(1+X_a)d` for each atom a and every real treatment d. Its observed outcome is `Y_a(D_a)`. Define

`Z_a(e)=D_a Y_a(D_a)/(e+(1/2-e)X_a) -(1-D_a)Y_a(D_a)/(1-e-(1/2-e)X_a)`.

Every occurrence of a mean, event mass, conditional mean, conditional probability, residual weight and effective law is the finite-sum expression given above. With p=p(e0), the first conjunction asserts all of the following:

1. p is a probability vector. For every atom a and real d, `Y_a(d)=Y_a(0)+(1+X_a)d`. The pair `(Y_a(0),1+X_a)` and D satisfy the displayed conditional-independence identity for every x,u,d.
2. For each real x in the two-element finset `{0,1}`, `E_p[D|X=x]=e0+(1/2-e0)x`, and the two conditional probabilities of D=0 and D=1 are strictly positive.
3. `E_p[w|X=0]=999999/1000000000000`; `E_p[w|X=1]=1/4`; `P_p(X=0)=1/2`; and `P_q(X=0)=999999/250000999999 < 1/250000`.
4. `Z(e0)=(0,1000000,-4,8)`. The unweighted target `E_p(1+X)` and `E_p Z(e0)` both equal 3/2. The second moment is 500020 and the variance is 2000071/4. The effective target `E_q(1+X)=500000999999/250000999999`, and this number is different from 3/2.

Next, for every real e, after hypotheses `0<e` and `e<1/2`, the theorem asserts that p(e) is a probability vector, the same potential-outcome affine identity and conditional independence hold, and for each x in `{0,1}` the conditional treatment mean is `e+(1/2-e)x` and both binary treatment probabilities are positive. For this e-dependent law,

`P_q(X=0)=e(1-e)/(e(1-e)+1/4)`, and `0<P_q(X=0)<4e`.

This universally quantified family does not assert estimator moments or consistency uniformly in e; those appear only at e0.

Another conjunction fixes p=p(e0) and the `4 by 3` real matrix `W_a=(1,D_a,X_a)`. Put `G_jk=sum_a p_a W_aj W_ak` and `b_j=sum_a p_a W_aj Y_a(D_a)`. It asserts `det G != 0` and `(G^{-1} b)_1=500000999999/250000999999`. The inverse and matrix-vector multiplication are Mathlib matrix operations; thus this is the actual coefficient of D in population least squares with an intercept and X, with nonsingularity explicitly certified.

For each natural n with `1<=n`, the sample space is the finite type of functions `a:Fin n -> Fin 4`, with mass `p_n(a)=product_{i:Fin n} p(e0)_{a(i)}` and statistic `Zbar_n(a)=(sum_i Z(e0)_{a(i)})/(n:real)`. The statement asserts that p_n is a probability vector,

`E_{p_n} Zbar_n=3/2`, `Var_{p_n} Zbar_n=2000071/(4n)`,

and, for every real delta after the hypothesis `0<delta`,

`P_{p_n}(delta<=|Zbar_n-3/2|)<=2000071/(4n delta^2)`.

Finally, for every fixed real delta>0, this deviation probability tends to zero as n tends to infinity through the naturals. Here `Tendsto ... atTop (nhds 0)` has its ordinary real epsilon-neighborhood meaning. This is consistency in probability for the fixed population e0.

The additional `T1Statement` conjunction explicitly restates conditional probabilities `(e0,1-e0)` at x=0 and `(1/2,1/2)` at x=1, `E_p[w|X=0]=e0(1-e0)`, the above effective-mass ratio, and `E_p w>0`.

Junk conventions: real division by zero is zero. The conditional means and probabilities would therefore be zero on a zero-mass profile, and the effective law would be all zero if its normalizer vanished. Neither occurs: both profile masses are 1/2, all four atom masses are positive for the e values used, and the residual second moment is positive. Both IPW denominators are positive on all atoms at e0. Mathlib matrix inverse would be zero for a singular real matrix; `det G!=0` excludes that. At n=0 the sample space has one empty function, its product mass is 1, its numerator sum is zero, and its empirical mean is `0/0=0`. All finite-n moment/bound clauses assume n>=1; the consistency sequence includes the n=0 value but a finite initial term cannot affect its limit. Natural-to-real casts are exact, and n>=1 excludes zero denominators in those bounds. There is no truncated natural subtraction, nonintegrable integral, log, sqrt, real power, `toReal`, partial-function default, limsup/liminf or conditional `sSup`/`sInf` in this closure.

Docstring reading: the tiny but positive effective profile mass does not imply a failure of strict binary endpoint positivity; it distinguishes the fixed e0 estimator facts from the family of arbitrarily small masses.

## SAP.P015a.T2

Location: `SAP/P015a/Challenge/Part1.lean:20-28`; statement at `Defs/Part3.lean:26-29`, `Defs/Part2.lean:69-101`.

This too is an unconditional conjunction about a fixed finite population. Set p=(1/4,1/4,1/4,1/4), X=(0,0,1,1), and D=(0,1,0,2). Its conditional treatment means at every atom are `1/2+X_a/2`. Its individual squared residuals are `(1/4,1/4,1,1)`, each strictly positive, with mean 5/8. Dividing `p_a w_a` by this mean gives `q=(1/10,1/10,2/5,2/5)`, whose X-profile masses are 1/5 and 4/5. The theorem also states explicitly that p is a probability vector and that the conditional squared-residual means given X=0 and X=1 are respectively 1/4 and 1.

Define potential-outcome world A by `Y^A_a(d)=d` and world B by

`Y^B_a(d)=3 if X_a=1 and d=1; otherwise Y^B_a(d)=d`.

For each world, the triple `(Y_a(0),Y_a(1),Y_a(2))` and D satisfy the finite conditional-independence identity in the introduction, for every real profile x, every triple u, and every real d. At every atom both observed outcomes are exactly D_a, so their observed triples `(X_a,D_a,Y_a(D_a))` agree pointwise. The contrast at endpoints 0 and 1 is `(Y_a(1)-Y_a(0))/(1-0)`, hence it is identically 1 in A and equals `1+2X_a` in B. The respective p-means are 1 and 2, and the respective q-means are 1 and 13/5.

The conditional probability of D=1 at X=1 is zero under both p and q. For every real d, the conjunction that D=d has positive conditional probability at both X=0 and X=1 holds if and only if d=0, separately under p and q. Thus the only common support point is 0, and there is no common distinct pair.

The final clause quantifies, in order, over any type Omega (in the declaration's universe), a measurable-space instance on Omega, any measure P with an `IsProbabilityMeasure` instance, any infinite sequence `draw:Nat -> Omega -> Fin 4`, a proof of uniform independent sampling, and any sequence of statistics `T_n:(Fin n -> (real times real times real)) -> real`. Uniform independent sampling unfolds to: each draw_i is measurable; the family is Mathlib `iIndepFun draw P` (every finite subfamily has joint law the product of its marginal laws); and `P{omega:draw_i omega=a}=ENNReal.ofReal(1/4)` for every i,a.

Let `S_n^A(omega)=T_n(i -> (X,D,Y^A(D))_{draw_i(omega)})`, and similarly for B. The theorem asserts both

`not (S_n^A -> 1 in P-measure and S_n^B -> 2 in P-measure)`,

`not (S_n^A -> 1 in P-measure and S_n^B -> 13/5 in P-measure)`.

`TendstoInMeasure` means, for each positive extended-real epsilon, the P-mass of the set where the extended distance to the constant limit is at least epsilon tends to zero along n->infinity. The two sample sequences coincide pointwise, which makes this a genuine statement about indistinguishable observed data.

Junk conventions: both profile masses are 1/2 under p, and are 1/5 and 4/5 under q, so no conditional denominator is zero. The effective-law denominator is 5/8. The contrast divisor is 1, so the generic `effectContrast` zero value for coincident endpoints is irrelevant. The uniform masses passed to `ENNReal.ofReal` are positive, so its clipping of negative values is irrelevant. No `ENNReal.toReal` is used. Although T is not explicitly assumed Borel on its full real-vector domain, its composition here factors through a finite sample of `Fin 4` atoms; consequently these random statistics are measurable whenever the draws are measurable. At n=0 the input is the unique empty tuple and T_0 may take any real value, which has no asymptotic effect. The statement includes probability and genuine independence hypotheses; standard infinite products give nonempty examples of these hypotheses. There are no integrability, matrix-inverse, logarithm, square-root, rpow, truncated-subtraction, sInf/sSup or limsup defaults in this closure.

Docstring reading: the example defeats fixed-distinct-endpoint positivity for multivalued treatment, while keeping positive within-profile treatment variance. It does not assert that positive within-profile variance fails.

## SAP.P015a.T3

Location: `SAP/P015a/Challenge/Part1.lean:30-37`; statement at `Defs/Part3.lean:31-34`, `Defs/Part2.lean:103-122`.

The population has four equally likely atoms, with X=(0,0,1,1) and D=(0,1,0,1). The statement is unconditional and explicitly asserts that the masses form a probability vector. For each x in `{0,1}` and each d in `{0,1}`, `P(D=d|X=x)=1/2`. For each x in `{0,1}`, `E[(D-E[D|X])^2|X=x]=1/4`.

The ordered four-draw sample is `a=(0,0,2,3)`, with independent product probability `(1/4)^4=1/256>0`. Its controls matrix, sampled treatment, and full design are respectively

`V=[[1,0],[1,0],[1,1],[1,1]]`,

`d=(0,0,0,1)`,

`W=[[1,0,0],[1,0,0],[1,0,1],[1,1,1]]`.

Every sample row's second control equals the population X at the sampled atom, and every sample treatment equals the population D there. The controls cross-product is `V^T V=[[4,2],[2,2]]`; `V^T d=(1,1)`; `[[4,2],[2,2]](0,1/2)=(1,1)`; and `det(V^T V)!=0`. The fitted residuals `d_i-sum_j V_ij omega_j` at `omega=(0,1/2)` equal `(0,0,-1/2,1/2)`, with squared residuals `(0,0,1/4,1/4)`. The package least-squares vector is the matrix formula `(V^T V)^{-1}(V^T d)`, and the theorem states that this vector equals `(0,1/2)` and that plugging it into the residual formula gives those same residuals and squared residuals. The full-regression cross-product is `W^T W=[[4,1,2],[1,1,1],[2,1,2]]` and has determinant 2.

Quantifiers over population x,d are finite-membership implications, and the sample-to-population row identities are for every `i:Fin 4`. There is no general estimator or outcome Y being quantified: this is an explicit positive-probability design example.

Junk conventions: conditional denominators equal 1/2. The matrix inverse is a total Mathlib operation, with value zero on singular real matrices, but the controls Gram determinant is 4 and explicitly nonzero. The full Gram determinant is 2. The sample product law is an actual independent product; drawing atom 0 twice in this particular ordered outcome does not make the random draws dependent. The four sample and three/two column index types are nonempty; there is no empty-design loophole. All sums, powers and divisions here have finite ordinary values, with only fixed nonzero denominators. There are no Bochner integrals, `toReal`, logs, sqrt, rpow, sInf/sSup, limsup/liminf, truncated subtraction or partial-function defaults in this closure.

Docstring reading: exactly zero fitted sample-profile weights do not entail zero population conditional variance or failed population positivity. The statement does not challenge the corresponding exact-zero assertion for population profile weights.

## SAP.P015a.T13

Location: `SAP/P015a/Challenge/Part1.lean:39-41`; statement at `Defs/Part3.lean:163-173`.

For every real p, after hypotheses `0<p` and `p<1`, put `c=log(p/(1-p))` and `f(a)=1/(1+exp(-a))` (Mathlib `Real.sigmoid`). All of the following form one conjunction under those hypotheses:

* For every real a, f has derivative `exp(a)/(1+exp(a))^2` at a (`HasDerivAt`).
* `f(c)=p`; its total Mathlib derivative at c is both `exp(c)/(1+exp(c))^2` and `p(1-p)`.
* For every real a, the first Taylor polynomial, defined as `f(c)+deriv(f,c)(a-c)`, equals both `p+p(1-p)(a-c)` and `(p-p(1-p)c)+p(1-p)a`.
* `log((1/2)/(1-1/2))=0`; the expression `exp(logOdds(1/2))/(1+logOdds(1/2))^2` equals 1; and the actual derivative of f at that center is 1/4.

Thus it explicitly distinguishes a denominator `1+c` from the correct `1+exp(c)` at p=1/2. It does not claim that the erroneous expression is a valid derivative at other p.

Junk conventions: `Real.log` is total (`log 0=0`, and on a negative real it agrees with log of its absolute value), but p/(1-p)>0 under the hypotheses. All real sigmoid denominators are strictly positive. Mathlib `deriv` defaults to zero when the function is not differentiable; the universal `HasDerivAt` assertion excludes that here. The erroneous denominator can vanish at c=-1 in general, but the only occurrence asserted for that expression is at c=0, where its square equals 1. No empty index types, integrals, extended-real conversions, sqrt/rpow, truncated subtraction, sInf/sSup or sequence-bound conventions occur.

Docstring reading: corrected inverse-logit derivative and affine Taylor polynomial, with a concrete discrepancy from the printed fraction at p=1/2.

## SAP.P015a.T12

Location: `SAP/P015a/Challenge/Part1.lean:43-52`; statement and dependencies at `Defs/WholeW1.lean:13-77`, together with `Defs/Part1.lean:106-113,128-130,203`.

Set `f(a)=1/(1+exp(-a))`, `c(p)=log(p/(1-p))`, `F(z)=1/(1+exp(-z))` for complex z, and `R(c)=sqrt(c^2+pi^2)` for real c. For a natural N define the real Taylor polynomial

`T_N(c,a)=sum_{k=0}^N ((iteratedDerivWithin k f univ c)/(k!:real)) (a-c)^k`.

This is Mathlib's `taylorWithinEval` on `Set.univ`, hence all derivatives are ordinary real derivatives. The full statement is a conjunction of four assertions, with no hypotheses surrounding the conjunction as a whole:

1. For every real p after `0<p<1`, for every real a the degree-one polynomial is `p+p(1-p)(a-c(p))`. The error is `O((a-c(p))^2)` as a approaches c(p). In Mathlib's norm definition this means there is a real constant C such that throughout some neighborhood of c(p), `|f(a)-(p+p(1-p)(a-c(p)))|<=C |(a-c(p))^2|`.
2. For every real p after `0<p<1`, there exists a formal complex multilinear series s, with `HasFPowerSeriesAt F s (c(p):complex)`, whose radius is `ENNReal.ofReal(R(c(p)))`. Here `HasFPowerSeriesAt` means there is a positive extended-real ball radius t, at most `s.radius`, such that for every complex h with norm below t the series `sum_n s_n(h,...,h)` has sum `F(c(p)+h)`. Its formal convergence radius is Mathlib's supremum of nonnegative radii r for which `norm(s_n) r^n` is bounded in n by some real C. In one complex dimension this is the usual power-series radius.
3. Universally quantify real p,r,rho in that order, then assume `0<p`, `p<1`, `0<=r`, `r<rho`, `rho<R(c(p))`. Set c=c(p) and

   `M=sSup { norm(F(z)) : z:complex, dist(z,c)=rho }`.

   The theorem asserts that the set in this supremum is nonempty and bounded above, and that there exists a z on that sphere with `M=norm(F(z))`. For every natural N, the real error image `{|f(a)-T_N(c,a)|:a:real, |a-c|<=r}` is nonempty and bounded above, and its real supremum is at most

   `M (r/rho)^(N+1)/(1-r/rho)`.

   The sequence of these upper bounds tends to zero as N tends to infinity. In particular the supremum controls the whole closed interval, not just individually selected points. The attained maximum, boundedness and nonemptiness are conclusions, not extra antecedents.
4. There is a fully specified grouped binary-data witness. Its two-row design is `V=[[1,0],[1,1]]`; each row has 100 Bernoulli observations with successes k=(1,99). The log likelihood at real coefficient vector t in `Fin 2 -> real` is

   `ell(t)=sum_{i:Fin 2} [k_i log(f(sum_j V_ij t_j))+(100-k_i)log(1-f(sum_j V_ij t_j))]`.

   Put `L=log 99` and `theta=(-L,2L)`. The Gram matrix of the 200 individual rows is `100*(V^T V)` and its determinant is 10000. For every real coefficient vector t, `ell(t)<=ell(theta)`; for every such t, equality implies `t=theta`. Thus theta is a unique finite global maximizer. The overall success fraction `(1+99)/200` is 1/2 and its log odds is zero. The two fitted linear predictors are `V theta=(-L,L)`. Moreover `pi<L`, and for each of the two row indices their absolute distances from the expansion center zero are greater than `R(0)`. Finally, for every natural degree N, both `|f(L)-T_N(0,L)|` and `|f(-L)-T_N(0,-L)|` are at least 49/100.

The latter assertion is stronger than just having predictors outside the convergence disk: it supplies a degree-independent nonzero lower bound on their actual probability approximation errors. It does not state approximation accuracy for coefficients or residual weights.

Junk conventions: `Real.log` is evaluated on positive p/(1-p) and 99. The real square root is total with zero assigned to nonpositive arguments, but `c^2+pi^2>0`; R is finite and strictly positive. `ENNReal.ofReal` clips negatives to zero but is applied to this positive finite R. Complex inverse assigns zero to zero, so F has assigned value zero at its usual poles `(2k+1)pi*i`; the circles used satisfy rho<R and avoid all poles, and an analytic germ at a real center is unaffected by arbitrary pole values. Formal-series radius is an extended-real supremum, not a real empty-supremum convention; the statement explicitly makes it the finite positive number R.

Real `sSup` is total and has non-mathematical defaults on empty or unbounded sets, but the circle and error image sets are explicitly asserted nonempty and bounded above. The circle supremum is also attained. The real interval is nonempty even at r=0; the complex sphere has rho>0 from `0<=r<rho`. Also `rho>0`, `0<=r/rho<1`, and `1-r/rho>0`, so the Cauchy bound has no zero denominator or negative-ratio problem. Exponents N+1 are natural; r=0 gives `0^(positive)=0`, not `0^0`. Factorials are positive and all natural-to-real casts are exact. Total derivatives could default to zero at nonsmooth functions, but f is analytic at every real center, and the complex germ is certified as a conclusion. Logistic fitted probabilities lie strictly between 0 and 1 at every finite t, so every likelihood logarithm is in its genuine domain. The count subtraction `100-k_i` is real, not truncated natural subtraction, and gives positive counts (99 and 1). The matrices and both index types are nonempty. No nonintegrable Bochner integral, mean, `toReal` of infinity, rpow, partial-function default, limsup/liminf or empty-design convention affects this statement.

Docstring reading: a local quadratic first-order approximation, exact finite complex radius, uniform shrinking real-interval error bound, and a full-rank logistic data set whose actual ML predictors defeat all Taylor degrees at the specified center. No coefficient or weight approximation guarantee is made.
