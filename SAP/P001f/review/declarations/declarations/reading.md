# Blind declaration reading

This file was written after reading only the declaration brief, the two input inventories (hash verification only for their entries), declarations/closure.json, and the supplied declaration/definition source files. Neither claims.json, record.json nor binding.json has been opened. All 37 entries in each inventory matched their hashes. This is a mathematical reading, not a fidelity decision. Source line numbers below are the physical numbered source lines; closure locations can identify the beginning of a docstring instead.

## Common notions, fully expanded to Mathlib notions

All scalar arithmetic is real unless explicitly natural. A probability measure has total mass one, so its event masses are finite and `ENNReal.toReal` is their ordinary real probability. A real Bochner integral in Lean is totalized to zero when the required integrability fails. Each use below must therefore be checked against the indicated integrability premises. `MemLp f 2 μ` means almost everywhere strong measurability and finite second norm; on a probability space it ensures integrability and finite second moment. `variance f μ` is Mathlib's real variance; the moment hypotheses below exclude nonintegrable conventions. Square roots are real square roots (zero on negative arguments); genuine variances here are nonnegative.

`ConditionalMean μ X Y m` is the conjunction: m is measurable, Y is integrable, m(X) is integrable, and for every measurable covariate set A, the integral of Y over X⁻¹(A) equals that of m(X) over X⁻¹(A). When X is measurable this expresses an integrable version of E[Y|X]. It does not select values at covariate points of zero law. With a restricted measure, both integrability and the identities are with respect to that unnormalized restriction.

`ConditionallyIndependent μ X hX Y Z` says, for every measurable value set A for Y and B for Z, E[1{Y∈A,Z∈B}|σ(X)] equals E[1{Y∈A}|σ(X)]E[1{Z∈B}|σ(X)] almost surely. The conditional expectations are Mathlib conditional expectations on the comap sigma algebra of X. Here X is measurable and all underlying measures are finite, including restrictions when used, so bounded indicators are integrable and conditional-expectation junk is excluded. The condition has an event-dependent null set, as usual.

`IndependentCopies μ X` says all X_i are measurable, the whole natural-indexed family is independent (`iIndepFun`), and every X_i has the same distribution as X_0 (`IdentDistrib`, including its measurability conditions). Finite-family independence/distribution hypotheses below use those same Mathlib notions. `RealDensity ν f` means f is almost everywhere measurable for volume, f≥0 everywhere, f is integrable for volume, and ν equals volume weighted by `ENNReal.ofReal ∘ f`. Thus it is an actual Lebesgue density, not a formal density name; normalization follows when ν is a probability law.

`sampleAverage X n ω = (Σ_{i=0}^{n-1} X_i(ω))/n`. `wholeFiniteAverage X ω = (Σ_{i∈Fin n} X_i(ω))/n`. They evaluate to zero at n=0 by empty sum and real zero-division, but their theorem uses require n>0.

`eventMean μ D Y d = (∫_{D=d}Y dμ)/P(D=d)`. Real division by zero is zero; the declarations using this as a conditional mean require a positive event probability. `censoredOutcome(y,r)=yr-99(1-r)`: for binary r it is y at response and -99 otherwise. `realizedOutcome(y0,y1,d)=y1 d+y0(1-d)`. Binary d makes this the observed arm outcome. The -99 censor is an encoding, not an outcome bound.

`finiteMean(w,Y)=Σ_i w_iY_i`; `finiteProbability(w,A)=Σ_{i:A(i)}w_i`; `finiteEventMean(w,Y,X,x)=(Σ_{i:X_i=x}w_iY_i)/finiteProbability(w,X=x)`. These are probability notions only with nonnegative normalized w. `FiniteConditionalIndependence(w,Y,Z,X)` means, for all x,y,z with positive cell probability, P(X=x,Y=y,Z=z)P(X=x)=P(X=x,Y=y)P(X=x,Z=z). In the finite cases used here singleton tests suffice. Classical decidability instances make finite indicators well-defined; they add no probabilistic hypotheses. Generated `._proof_*` closure constants belong to the displayed array indices, type coercions and decidability/side-condition elaboration; the corresponding source expressions were read in their enclosing definitions.

## SAP.P001f.T100

Source: Challenge/Part1.lean:36–41; Defs/Part3.lean:85–98; ConditionalMean, ConditionallyIndependent and eventMean in Part1.

For every measurable space Ω, covariate measurable space E, probability μ, measurable X:Ω→E, real measurable Y0,Y1,D, assume the effect Δ=Y1−Y0 is integrable (the separate potentials need not be), D∈{0,1} almost surely, and 0<P(D=1)<1. For every measurable integrable version p of E[D|X], assume the pair (Y0,Y1) is conditionally independent of D given X. Define P=P(D=1), W=E[p(X)Δ], A=E[Δ|D=1], with the last quantity the event integral divided by P. Then E[p(X)]=P>0, W=E[DΔ]=P A, A=W/E[p(X)], and W=A iff P=1 or A=0. P=1 is impossible under the earlier strict upper bound, so that disjunct is an algebraic characterization whose only admissible branch here is A=0. The ordering is universal data, hypotheses, universal p, its conditional-mean and independence hypotheses, then identities.

Junk audit: P and E[p(X)] are positive finite denominators. Δ is integrable, D is binary almost surely, and p(X) is a conditional mean of D, hence is between zero and one almost surely: the weighted effect integrals are genuine. No pointwise restrictions on null-set versions of D or p are imposed. No empty index, log, derivative or supremum is involved.

## SAP.P001f.T101

Source: Challenge/Part1.lean:43–44; Defs/WholeW1.lean:78–92.

For every type Ω and U,A,B⊆Ω with A⊆U and B⊆U, A\B={s:s∈A and s∉B}=A∩(U\B). Also A\B=A∪(U\B) iff A∪B=U and A∩B=∅; the same identity holds iff A=U\B; and the covering/disjointness condition is itself equivalent to A=U\B. Additionally, over the naturals, {1,2}\{2}={1}, {1,2}∩({1,2,3}\{2})={1}, and {1,2}∪({1,2,3}\{2})={1,2,3}. These are set differences, not numeric subtractions. An empty Ω or U is allowed and gives legitimate set identities. No analytic junk conventions.

## SAP.P001f.T102

Source: Challenge/Part1.lean:46–59; Defs/Part3.lean:104–113; Part2.lean:31–37,82–100; ConditionalMean, RealDensity, sampleAverage in Part1.

First conjunct negates this universal identification assertion: for every probability space Ω and finite dimension K, measurable X:Ω→ℝ^K and Y:Ω→ℝ with every coordinate of X integrable and Y integrable, for every marginal density f of X and joint density q of (X,Y), assume range(X)={x:f(x)>0}. For every two conditional-mean versions m0,m1:ℝ^K→ℝ that are globally Fréchet differentiable, and for every coordinate k∈Fin K, their coordinate derivatives at xbar=(E[X_j])_j coincide. A coordinate derivative is `deriv (t ↦ m(update x k (x_k+t))) 0`. Thus the negation asserts existence of admissible data and two such versions with unequal derivatives at the mean; it is not a claim that a chosen differentiable function lacks its own derivative. No requirement places xbar inside the density's positive set. Range saturation is literal pointwise saturation, not almost sure inclusion or closure of support.

Second conjunct: for every type Ω, K, sequence X_i:Ω→ℝ^K, fitted functions mhat_n(ω):ℝ^K→ℝ and n>0, for every ω and coordinate k, if the displayed coordinate path at the coordinatewise sample mean is differentiable at 0, then `samplePDA` equals that same coordinate derivative. Expanded, both sides are exactly `deriv (t ↦ mhat_n(ω)(update samplemean k (samplemean_k+t))) 0`. The equality is definitional even without the two domain premises; it proves no estimator performance property.

Junk audit: derivative defaults outside differentiability do not explain the negation, since both versions are globally differentiable. The plug-in equality would remain reflexive even with default derivatives, but its premise excludes that case. n>0 prevents zero-division for sample means. Coordinate expectations are integrable. Probability densities exclude infinite or signed density artifacts. K=0 has no k and cannot witness the first negation. Covariate density versions away from their law can matter to range saturation; globally differentiable CEF extensions can still differ in gaps of the support. The docstring explicitly describes a mean in such a gap, not an interior support modification.

## SAP.P001f.T103

Source: Challenge/Part1.lean:61–67; Defs/Part3.lean:115–118; Part2.lean:102–118.

It is not the case that for every n>0 and every strictly positive real sample y:Fin n→ℝ there is a valid seven-parameter θ whose sample likelihood dominates every valid θ'. Valid means θ0,θ1≥0, θ0+θ1≤1, normal scale θ3>0, lognormal scale θ5>0 and exponential rate θ6>0; locations θ2,θ4 are arbitrary real. For real y, the density is θ0 φ(θ2,θ3,y)+θ1 l(θ4,θ5,y)+(1−θ0−θ1)e(θ6,y), where φ(m,s,y)=exp(−(y−m)^2/(2s²))/(s sqrt(2π)), l(m,s,y)=φ(m,s,log y)/y if y>0 and zero otherwise, and e(r,y)=r exp(−ry) if y≥0 and zero otherwise. Sample likelihood is the finite product of those densities. The negation needs only one positive-size, all-positive sample without a maximum; it does not assert nonexistence for all samples or a failure of consistency/efficiency.

Junk audit: valid scales and rate exclude zero or negative Gaussian denominators, sqrt(2π)>0, all sample values are positive so log and division by y are in their ordinary domains. Empty product is excluded by n>0. Mixture weights may vanish, legitimately. No argmax, sup or logarithm of likelihood is defined. The maximum quantifiers are `¬∀ sample ∃ θ ∀ valid θ'`, not a statement about a supplied candidate.

## SAP.P001f.T104

Source: Challenge/Part1.lean:69–76; Defs/Part3.lean:120; Part2.lean:120–128.

Negates the following universal equivalence: for all nonnegative summable t,c:ℕ→ℝ with positive sums T,C and T+C=1, {k:t_k>0}={k:c_k>0} iff there exists ε>0 such that for every k with t_k+c_k>0, ε<t_k/(t_k+c_k)<1−ε. The t and c are treated/control joint masses, not separately normalized conditional laws. Thus it asserts at least one countable-mass probability law, with positive arm probabilities, for which equality of positive-mass supports fails to be equivalent to uniform two-sided positivity. It does not separately state which implication fails, regional examples, or any other overlap assertion.

Junk audit: `tsum` defaults on nonsummable series are guarded by both Summable hypotheses, and joint masses sum to one. The ratio is tested only where its denominator is positive; zero-mass cells do not enter the inequalities. Infinite countably many cells are permitted, and the uniform ε is chosen before all cells. This order is stronger than cellwise strict positivity. There is no supremum/infimum convention or nonmeasurable witness.

## SAP.P001f.T106

Source: Challenge/Part1.lean:78–82; Defs/Part4.lean:14–26.

For every probability μ on any measurable Ω, (i) for all integrable real X,Y and real a,b,c, E[aX+bY+c]=aE[X]+bE[Y]+c; and (ii) for every X with finite second moment and all real a,c, Var X=E[X²]−E[X]², Var(X+c)=Var X, Var(aX)=a²Var X, sqrt Var(X+c)=sqrt Var X, and sqrt Var(aX)=|a|sqrt Var X. If Var X>0 then for every ε>0, P(ε sqrt Var X≤|X−E[X]|)≤1/ε². The probability is represented by `.toReal`. There are no independence assumptions.

Junk audit: integrability or second-moment assumptions justify every integral and variance. Nonnegative variance keeps square roots in their ordinary domain. Strictly positive variance and ε exclude zero standardization/threshold denominators. μ is finite so no ∞ conversion. a=0 is permitted and yields a legitimate degenerate affine transform. No n or empty index type enters.

## SAP.P001f.T107

Source: Challenge/Part1.lean:84–85; Defs/WholeW1.lean:94–120; ConditionalMean in Part1.

For every probability μ, measurable X:Ω→E and measurable integrable Y:Ω→ℝ, and every conditional-mean version m of Y given X, E[Y]=E[m(X)]. If Y has finite second moment, m(X) does too, and for every conditional-mean version v of (Y−m(X))² given X, Var Y=E[v(X)]+Var(m(X)). Independently of a second-moment assumption on Y, for every such v, and every measurable g:E→ℝ with integrable (Y−g(X))², the squared difference (m(X)−g(X))² is integrable; E[(Y−g(X))²]=E[v(X)]+E[(m(X)−g(X))²]; the second term is nonnegative; E[(Y−m(X))²] and E[v(X)] are at most E[(Y−g(X))²]; and E[v(X)]=E[(Y−m(X))²]. The v quantifier and its ConditionalMean premise precede the g quantifier. Existence of a version v is not asserted within this theorem; its conditional-mean premise already includes integrability of the squared CEF residual and of v(X).

Junk audit: ordinary integrable expectations throughout. Variance branch is guarded by MemLp Y 2. Prediction branch has finite squared residuals rather than merely assigning a totalized infinite risk a value. One must distinguish the premise that v is a conditional mean from existence of v; standard conditional-expectation theory supplies versions in the intended regular setting. No pointwise CEF uniqueness or equality of arbitrary versions away from the law is asserted. No division or finite-index convention.

## SAP.P001f.T108

Source: Challenge/Part1.lean:87–88; Defs/WholeW1.lean:122–144.

For every probability μ, every natural n>0, finite family X:Fin n→Ω→ℝ and chosen j∈Fin n, if each X_i is measurable, the family is jointly independent, all X_i have the same distribution as X_j, and X_j is integrable, then Xbar=(Σ_i X_i)/n is integrable and E[Xbar]=E[X_j]. If X_j has finite second moment, Xbar does too and Var(Xbar)=Var(X_j)/n. Under additionally Var(X_j)>0, every ε>0 satisfies P(ε≤|Xbar−E[X_j]|)≤Var(X_j)/(ε²n). These are finite families on their original probability space; extension to an infinite iid family is not required.

Junk audit: n>0 ensures both Fin n nonempty and all n denominators nonzero. The selected j exists in the actual domain. Moment hypotheses exclude integral and variance defaults. ε>0 ensures ε²n>0. Finite μ excludes ∞ toReal. Constants are legitimate iid variables (Chebyshev positive-variance branch then inactive), and nonconstant iid families are also possible.

## SAP.P001f.T109

Source: Challenge/Part1.lean:90–95; Defs/Part4.lean:45–70; ConditionalMean and RealDensity in Part1.

First conjunct: for all a≤b, continuous f on [a,b] and ε>0, a real polynomial p exists with |f(x)−p(x)|<ε for every x∈[a,b]. Second conjunct: for every probability μ and measurable real X with X∈[a,b] almost surely and square-integrable real Y, assume either (i) the law of X has a real Lebesgue density whose positive set is exactly [a,b], or (ii) range X is countable and for every real x, P(X=x)>0 iff x∈[a,b]. For every conditional-mean version m of Y given X continuous on [a,b], there exists a sequence p_J of real polynomials of degree at most J minimizing E[(Y−p_J(X))²] among all degree≤J polynomials, for every J. Moreover every such minimizing sequence has: for each ε>0 there exists J such that for every J'≥J, E[(m(X)−p_{J'}(X))²]<ε. Existence of a minimizing sequence precedes the universal assertion about every minimizing sequence. The claimed limit concerns integrated CEF approximation, not a uniform guarantee about the fitted polynomials.

Junk audit: `natDegree` of zero is zero in Lean; degree≤J includes the zero polynomial at every J and matches the vector space of degree≤J. Compact X and continuous m make all polynomial/CEF compositions essentially bounded; square-integrable Y makes prediction risks genuine finite integrals. The density branch has total mass one; an empty or singleton interval cannot supply such a Lebesgue density. The point-mass branch on a nondegenerate full real interval would require uncountably many atoms and is impossible; a singleton is an available nonempty PMF instance. This domain is stringent and should be compared carefully with the intended full-interval support notion. The theorem does not explicitly require a≤b in this second branch, but its probability support hypothesis forces a nonempty interval. No limsup, sInf or sSup is used; convergence is explicit ε/eventual quantification.

## SAP.P001f.T110

Source: Challenge/Part1.lean:97–101; Defs/Part4.lean:72–83.

For every n>0 and Bool-valued sample Y:Fin n→Bool, let k be the number of true observations and a=k/n in ℝ. Then a∈[0,1], a is also the sum of the 0/1 indicators divided by n, and for every t∈[0,1], (1−t)^(n−k)t^k≤(1−a)^(n−k)a^k, with equality iff t=a. Separately, every t∈[0,1] satisfies (1−t)t²≤(1−2/3)(2/3)², with equality iff t=2/3. This is maximization of the sample likelihood, not of a binomial probability with any parameter-dependent coefficient.

Junk audit: n−k is natural truncated subtraction, but k is the cardinality of a subset of Fin n so k≤n; it equals the true failure count. The sample-size denominator is nonzero. Natural powers use 0^0=1; this is precisely the empty-product convention needed for all-failure/all-success samples and makes endpoint likelihoods meaningful. Parameter domain includes both endpoints. No logarithms are taken, so log 0 does not intervene. Empty sample excluded.

## SAP.P001f.T111

Source: Challenge/Part1.lean:103–104; Defs/WholeW1.lean:146–208; Part5.lean:14–19; Part1 definitions.

The statement is the conjunction of the following assertions.

1. For every probability μ and measurable integrable Y and measurable R binary almost surely with P(R=0)>0 and P(R=1)>0, if Y and R are independent, then E[Y]=E[Y*|R=1], where Y*=YR−99(1−R) and the respondent mean is the positive-event ratio.
2. For every probability μ, finite dimension K, measurable X:Ω→ℝ^K and measurable integrable Y and measurable R, assume binary R almost surely and both response values have positive probability. For every conditional response mean p and respondent regression m, assume p(X)>ε almost surely for some ε>0, Y and R conditionally independent given X, and m is a conditional mean of Y* given X under μ restricted to R=1. Then m(X) is integrable under the full μ, m is also a conditional mean of Y given X under μ, and E[Y]=E[m(X)]. If range X is countable, the sums over the subtype S={x:P(X=x)>0} of m(x)P(X=x) and |m(x)|P(X=x) are summable and E[Y]=Σ_{x∈S}m(x)P(X=x). This uses positive-mass support, not zero-mass conditional values.
3. For every n>0, real sample y,r with binary r and Σr>0, the respondent estimator on the censored y is its displayed sum Σy*r/Σr. This conjunct unfolds its definition.
4. For every n>0, K and real-vector covariate sample X, binary response r, and a respondent in every observed covariate profile, the empirical response plug-in is the sum over `univ.image X` of the cell respondent mean times its sample frequency. Expanded cell size is Σ_i1{X_i=x}, treated/response count is Σ_{i:X_i=x}r_i, and treated/response sum is Σ_{i:X_i=x}Y*_i r_i. This equality also unfolds its definition, using exactly observed profiles instead of a finite ambient vector space.
5. For Y*=[1,−99,1,0,1,−99], r=[1,0,1,1,1,0] and X=[0,0,0,0,1,1] in Fin 2, the respondent estimate is 3/4 and the response plug-in is (2/3)(4/6)+1(2/6)=7/9.

Junk audit: event ratios have positive finite denominators; sample ratios require n>0 and positive response counts on all included cells. Summation over positive probability support avoids conditional values at zero mass; the explicit Summable conclusions exclude tsum defaults. Population m(X) integrability is derived, not a separate premise. ConditionalMean for respondents still imposes integrability under the respondent restriction, and bounded inverse response under uniform overlap controls its transfer. -99 values are always removed by a binary response multiplier or by restriction to respondents. K=0 is a legitimate constant-covariate vector. The empirical definitional identities do not prove stochastic consistency; no such quantifiers occur.

## SAP.P001f.T112

Source: Challenge/Part1.lean:106–110; Defs/Part5.lean:57–68; ConditionalMean and ConditionallyIndependent in Part1.

For every probability μ, finite K, measurable vector X and real measurable Y,R with R binary almost surely and both response probabilities positive, for every conditional mean p of R given X, assume Y and R are conditionally independent given X. For every ε>0 satisfying p(X)>ε almost surely, conclude: conditional on p(X), R and X are independent; conditional on p(X), Y and R are independent; id is a conditional-mean version of R given p(X); and there exists η>0 with p(X)>η almost surely. No integrability assumption is placed on Y, because only its measurable events enter conditional independence. ConditionalMean for R includes its integrability, already implied by binary response on a probability space. The first independence order is R,X, the second Y,R.

Junk audit: no inverse score or outcome expectation occurs. Conditional expectations are bounded indicator expectations on a finite probability space with measurable conditioning functions, so their usual conditions hold. Score values are versions, with lower bound only almost surely; null-set values need not lie in [0,1]. K=0 is allowed without producing an empty observation type. No zero divisions, infinite mass conversions, derivative or extremum conventions.

## SAP.P001f.T113

Source: Challenge/Part1.lean:112–120; Defs/WholeW2.lean:15–43; ConditionalMean, ConditionallyIndependent and censoredOutcome in Part1.

For every probability μ, finite K, measurable vector X, and real measurable Y,R, assume Y integrable, R binary almost surely and both response probabilities positive. For every conditional response mean p, assume p(X)>ε almost surely for some ε>0 and Y conditionally independent of R given X. For every measurable nuisance pair m,q:ℝ^K→ℝ, assume the complete score S=m(X)+R(Y*−m(X))/q(X) is integrable. If either (a) m is the respondent conditional mean under μ restricted to R=1 and for some η>0, η<q(X)<1−η almost surely, or (b) q(X)=p(X) almost surely, then E[Y]=E[S]. There is no separate full-population integrability premise for m(X). The OR is inside the universal m,q quantifiers; this is two alternatives for the same displayed score, not an existentially chosen nuisance pair.

Junk audit: in branch (a), q is bounded away from zero on the law; in branch (b), q equals a true uniformly positive response probability almost surely. Null-set zero values may still use Lean's zero inverse but cannot alter an integrable expectation. Y and S have expressly finite expectations; component integrability cannot simply be presumed when m is unrestricted in branch (b), so the proof must justify manipulations of the complete score. Y* equals Y on respondents and is multiplied by R in the correction; −99 disappears. The upper candidate bound is present only in the regression-correct branch; true p need not be bounded away from one. No empty sum or default conditional-event ratio.

## SAP.P001f.T114

Source: Challenge/Part1.lean:122–131; Defs/WholeW2.lean:45–84; SharpATEBounds in Part5.lean:88–105; Part1 definitions.

First, for every probability μ, measurable real potential outcomes Y0,Y1 and treatment D, and real a,b, assume both potential outcomes lie in [a,b] almost surely, D binary almost surely and both treatment arms have positive probability. Write Y=Y1D+Y0(1−D), P1=P(D=1), P0=P(D=0), m1=E[Y|D=1], m0=E[Y|D=0]. Set L=m1P1+aP0−(m0P0+bP1), U=m1P1+bP0−(m0P0+aP1). Then E[Y1−Y0]∈[L,U], U−L=b−a, and for every c∈[L,U] there exist measurable bounded potentials Z0,Z1 on the same Ω, with the same observable joint law of (realized outcome,D), whose mean effect is c. Thus sharpness permits choosing the missing outcomes while retaining the observed law; it does not assume ignorability.

Second, for every real y0,y1,d,a,b with y0,y1∈[a,b] and binary d, let y=y1d+y0(1−d), I1(y,d,z)=yd+z(1−d), I0(y,d,z)=y(1−d)+zd. If d=1 then for every real z, I1=y1 and I0=z; if d=0 then I1=z and I0=y0. Also y1∈[I1(a),I1(b)], y0∈[I0(a),I0(b)], I1(a)−I0(b)=yd+a(1−d)−y(1−d)−bd, and I1(b)−I0(a)=yd+b(1−d)−y(1−d)−ad. Those last expressions are the definitions of lowerATE and upperATE.

Finally, for y=[1,1,1,0,1,0], d=[1,0,1,1,1,0], endpoints a=0,b=1, the averages of I1(1), I0(0), I1(0), I0(1) are respectively 5/6,1/6,3/6,5/6; the lowerATE and upperATE averages are −2/6 and 4/6; and the differences of the corresponding endpoint means reproduce these ATE endpoints.

Junk audit: bounded potentials on a probability space ensure all displayed expectations are genuine, including observed Y and constructed bounded Z. Both event denominators are strictly positive finite probabilities. Bounds imply a≤b in every satisfiable probability instance; no empty [a,b] can make the premises hold almost surely on a probability space. a=b is allowed; then the sharp interval has width zero and c is its sole value, with no statement-level division by b−a. The witness quantifier follows each c, rather than using one pair to realize all c. Fixed Fin 6 sums have no empty-sample convention. No `sInf`, `sSup`, unbounded limsup, Real.rpow or other partial-domain convention appears in any of the 18 statements.

## SAP.P001f.T96

Source: Challenge/Part1.lean:11–16; Defs/Part3.lean:14–40; Part2.lean:13–23.

There are no free data hypotheses: this is a conjunction about three fixed cells with covariates x=[−1,0,1], sizes N=[6,6,6], treated counts r=[3,1,5], treated outcome sums sT=[12,3,20], control outcome sums sC=[9,10,3]. Set q(a,b,x)=exp(a+bx)/(1+exp(a+bx)) and l(a,b)=Σ_j[r_j log q(a,b,x_j)+(N_j−r_j)log(1−q(a,b,x_j))]. For all real a,b, l(a,b)≤l(0,log 2), with equality iff a=0,b=log 2. In all three cells 0<r_j<N_j, fitted q are [1/3,1/2,2/3], individual-style grouped IPW (Σ_j[sT_j/q_j−sC_j/(1−q_j)])/18=59/36, and post-stratification (Σ_jN_j[sT_j/r_j−sC_j/(N_j−r_j)])/18=1, with 59/36≠1. It additionally gives observed fractions [1/2,1/6,5/6], score residuals [1,−2,1] whose intercept and slope sums are zero, explicit repeated arithmetic with arm means [4,3,4] and [3,2,3], and nonzero gap 23/36.

Junk audit: exp>0 implies 0<q<1 for all real parameters, so log arguments and reciprocal denominators are legitimate. log 2 has positive argument. Fixed counts ensure all cell denominators are positive; all subtractions are real. Every index is Fin 3, all sums are nonempty, and the 18 divisor is nonzero. Unique maximum is global over ℝ², not merely stationary score arithmetic. The fixed data can be realized by six units per cell with the indicated arm counts and constant within-arm outcomes.

## SAP.P001f.T97

Source: Challenge/Part1.lean:18–19; Defs/WholeW1.lean:16–76; poststratifiedAverage and example data in Part1.

For every n>0, finite decidable cell type E, X:Fin n→E, binary real D:Fin n→ℝ and q:E→(0,1), assume X is surjective and each cell has both a positive treated count and a positive control count. For cell x write N_x=Σ_i1{X_i=x}, T_x=Σ_{X_i=x}D_i, C_x=N_x−T_x, S1_x(Y)=Σ_{X_i=x}Y_iD_i, S0_x(Y)=Σ_{X_i=x}Y_i(1−D_i). For every individual real outcome vector Y, the individual IPW I(Y)=(Σ_i[Y_iD_i/q(X_i)−Y_i(1−D_i)/(1−q(X_i))])/n equals (Σ_x[S1_x/q_x−S0_x/(1−q_x)])/n. The plug-in P(Y), defined as the poststratified treated mean minus the poststratified control mean, equals (Σ_xN_x[S1_x/T_x−S0_x/C_x])/n. If every q_x=T_x/N_x then for every Y, I(Y)=P(Y). Moreover [for every individual Y, I(Y)=P(Y)] iff [for every x, q_x=T_x/N_x]. It does not say equality for one outcome vector forces saturation. Finally, with X=[1,0,0,1,1,1], D=[1,0,1,1,1,0], Y=[1,1,1,0,1,0], the plug-in equals (1−1)(2/6)+(2/3−0)(4/6)=4/9.

Junk audit: q and 1−q are positive. Both arm-count premises ensure N_x>0 and both empirical conditional denominators positive. Counts and subtraction are real, avoiding truncated natural subtraction. n>0 and surjectivity make E nonempty in any admissible instance; there is no empty-cell junk hidden by summing over a larger ambient type. Finite indicator instances are classical. Example cells each contain both arms. All sums use actual individuals, so outcome-sum arbitrariness is not an independent assumed cell model.

## SAP.P001f.T98

Source: Challenge/Part1.lean:21–28; Defs/Part3.lean:50–65; ConditionalMean, IndependentCopies and sampleAverage in Part1.

For every probability μ, measurable covariate space E and infinite iid measurable sequence of pairs (X_i,D_i), for every p:E→ℝ that is a conditional-mean version of D_0 given X_0, assume D_i(ω)∈{0,1} for every i and every ω, and there exists ε>0 such that ε<p(X_i(ω))<1−ε for every i,ω. Then D_0/p(X_0) and (1−D_0)/(1−p(X_0)) both have conditional mean the constant one given X_0, and their ordinary means are one. For every n>0 the first-n averages of the corresponding arm weights also have expectation one. Finally E[1/p(X_0)]>1 and E[1/(1−p(X_0))]>1. The reciprocal means use all units, without arm indicator numerators. It asserts no outcome-estimator formula, denominator limit, or efficiency comparison.

Junk audit: the uniform pointwise ε bounds ensure every reciprocal exists and is bounded, and force ε<1/2 in a nonempty probability space. Binarity is pointwise for all observations, stronger than almost sure binarity. IndependentCopies includes measurability and joint independence of the infinite family, with a common pair law. Positivity of n prevents the zero-size average convention. All integrals and conditional means are of bounded measurable functions. The index sequence ℕ is never empty; probability Ω cannot be empty. Correctness of p for other indices is transported by their common law, not separately assumed.

## SAP.P001f.T99

Source: Challenge/Part1.lean:30–34; Defs/Part3.lean:67–83; finite-law definitions and attWeights in Part1.

Fixed law on Fin 2 has w=[3/4,1/4], with nonnegative weights summing to one, treatment D=[0,1], covariate X=0, potentials Y0=0,Y1=1. Treatment masses are 3/4 and 1/4. The potential pair is conditionally independent of D given X in the exact finite cell-product sense defined above. The conditional treatment mean at X=0 is 1/4. Two explicit numeric positivity chains hold: 1/8<1/4<1−1/8 and 1/4<3/8<1. The unnormalized weighted mean E[(1/4)(1−0)]=1/4, the treated event mean of the effect is one, these are unequal, and dividing the former by E[1/4]=1/4 restores one. This is a concrete probability-law counterexample, with its normalization correction, rather than a universal ATT theorem.

Junk audit: all conditional-event denominators are positive (covariate mass one, treatment mass 1/4) and weights are an actual probability distribution. Two-point conditional independence is well-defined; the potential pair is constant. All real ratios are rational and ordinary; neither zero division nor nonintegrable means can explain the inequality. All quantifiers within independence range over arbitrary singleton values but the support is finite. No asymptotic or version-extension issue.
