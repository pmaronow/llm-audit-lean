# Blind reading of the Challenge

This file was written and saved after reading only `SAP/P029b/Defs*.lean`,
`SAP/P029b/Defs/*.lean`, `SAP/P029b/Challenge*.lean`,
`SAP/P029b/Challenge/*.lean`, and the relevant Mathlib definitions. Neither
`claims.json` nor `record.json` had been opened. The descriptions below read
the propositions themselves; the Challenge docstrings are not additional hypotheses.

## Shared objects and conventions

A potential unit is a tuple `(X,D0,D1,Y0,Y1)` with covariate in an arbitrary
type, two Boolean potential receipt indicators, and two real potential
outcomes. Write `tau=Y1-Y0`, `C={D0=false,D1=true}` for compliers, and
`F={D0=true,D1=false}` for defiers. Receipt at Boolean assignment `z` is
`D(z)=D1` if `z=true`, and `D0` otherwise; the observed outcome is `Y1` if
receipt is true, and `Y0` otherwise. Thus exclusion is built into the outcome
definition. Write `b(z)` for the real number 1 or 0 corresponding to a Boolean.

For a finite type `L`, `ValidLaw p` means that every real mass `p(i)` is
nonnegative and their sum is 1. `fE(p,v)=sum_i p(i)v(i)`;
`fP(p,A)=sum_{i:A(i)}p(i)`; and `fCE(p,v,A)=fE(p,1_A v)/fP(p,A)`.
`FIndep(p,V,W)` means, for every pair of values `(v,w)`,
`fP(V=v,W=w)=fP(V=v)fP(W=w)`. In a valid finite law this is ordinary
independence, including when a codomain is infinite. `randomized(p,e)` assigns
mass `p(i)e` to `(i,true)` and `p(i)(1-e)` to `(i,false)`.

For a measure `mu`, `mP(mu,A)=(mu A).toReal`; `mCE(mu,v,A)` is the Bochner
set integral of `v` on `A`, divided by `mP(mu,A)`. In all the measure-theoretic
theorems the measure is a probability measure. Write `P`, `E`, and `E[.|A]`
for these quantities when their ordinary probability interpretation applies.
`scoreAt(x)=P(C,X=x)/P(X=x)` and `complierAt(x)=E[tau|C,X=x]`.
`latentAt(x)` is exactly `E[tau|X=x]=E[tau|C,X=x]`.
`typicalAt(x)` is the conjunction, for `j=0,1`, of
`E[Yj|D(Z)=true,X=x]=E[Yj|D(Z)=false,X=x]`.
The finite versions use the corresponding finite sums; finite latent
ignorability is required at every profile with positive mass.

`IVAssumptions(mu,U,Z)` bundles, in this order: measurability of `X,D0,D1,Y0,Y1,Z`;
integrability of `Y0,Y1`; independence of `Z` and the entire tuple
`(X,D0,D1,Y0,Y1)`; `0<P(Z=true)<1`; `mu(F)=0`; and a nonzero receipt first
stage `E[D(Z)|Z=true]-E[D(Z)|Z=false]`. `FIV` instead bundles a valid finite
law, the same strict assignment probabilities, finite independence of that
tuple and `Z`, zero defier mass, and the same nonzero finite first stage.

For a weight `w`, `mArm(w,V,z)=E[wV|Z=z]/E[w|Z=z]`. The population weighted
Wald ratio `W(w)` is the difference of the two weighted outcome arm means
divided by the difference of the two weighted receipt arm means. `fWald`
is precisely its finite analogue. For a sample indexed by `Fin N`,
`sampleArm(w,V,z)=sum_{Z_i=z}w_i V_i / sum_{Z_i=z}w_i`, and `sampleWald`
uses the same ratio of arm differences. `sampleCross(Z,V)` is
`sum_i (b(Z_i)-sum_j b(Z_j)/N)(V_i-sum_j V_j/N)`.
`SampleDefined(w,D,Z)` requires both weighted arm mass sums and the weighted
receipt first stage to be nonzero. `RatiosEventuallyDefined` means that for
almost every infinite draw sequence there is a (sequence-dependent) sample
index after which `SampleDefined` holds for every subsequent sample.

`covariateSigma U` is the pullback of the measurable structure on the
covariate type under `X`. `ScoreVersions(mu,U,c,m)` requires that the two
real functions `c,m` on the covariate type are measurable and that, almost
everywhere, `c(X)=E[1_C|sigma(X)]` and
`c(X)m(X)=E[1_C tau|sigma(X)]`, with Mathlib conditional expectations.
`A1Versions(mu,U,m)` requires `m(X)=E[tau|sigma(X)]` almost everywhere.
There is no division by `c` in `ScoreVersions`; on covariate regions where
`c=0` it need not determine `m`.

For measurable spaces `Omega,X`, `ICSWConditions(mu,U,Z,c,m,s)` means all of:

1. For every natural index `i`, `IVAssumptions(mu,U_i,Z_i)`.
2. The whole tuples `((X_i,D0_i,D1_i,Y0_i,Y1_i),Z_i)` are mutually
   independent over all natural indices and identically distributed with
   the index-zero tuple. Mathlib's `iIndepFun` means factorization for every
   finite family of measurable events. `IdentDistrib` includes almost
   everywhere measurability of both maps and equality of their pushforwards.
3. For every `i`, `ScoreVersions(mu,U_i,c,m)`.
4. There exists a single real `epsilon>0` such that, for every `i`,
   `epsilon<c(X_i)<=1` almost everywhere.
5. Every estimate `s(n,i):Omega -> R` is measurable.
6. For every `n`, almost everywhere all estimates with `0<=i<=n` lie in `(0,1]`.
7. `max_{0<=i<=n}|s(n,i)-c(X_i)|` tends to zero in measure as `n` tends to infinity.

`icswSequence(n)` is the sample Wald ratio on the first `n+1` units with
weights `1/s(n,i)`. `winsorizedSequence(n)` replaces each weight by
`1/max(s(n,i),cutoff(n))`. Convergence in measure is Mathlib's requirement
that for every positive extended-real error threshold, the measure of the
event where the extended distance to the target is at least that threshold
tends to zero. On probability spaces and real variables this is convergence
in probability. All limits use `atTop` on natural numbers and the usual
topology on real numbers (or extended nonnegative reals for event measures).

For sample size `N=n+1`, `Type7Quantile(s,lambda,c)` means there exists a
permutation `pi` of `Fin(n+1)` that orders `s` nondecreasingly and an index
`j` in that type such that `j<=n*lambda<j+1` and
`c=(1-r)s(pi(j))+r s(pi(min(j+1,n)))`, where `r=n*lambda-j`.
The order-index inequalities are real inequalities. At `n=0` the sole
sample value is returned; at level 1 the last value is returned.
`belowCount(s,c)` counts the **strict** inequalities `s_i<c`.
`weightChange(s,c)=1/s-1/max(s,c)`.

Mathlib's real division is total, with `a/0=0`. Its Bochner integral is
zero for nonintegrable functions; its conditional expectation is zero if
the sigma algebra is not a subalgebra, the trimmed measure is not sigma
finite, or the input is not integrable. Probability, measurability, and
integrability hypotheses in the applications must justify the ordinary
interpretation. Real logarithm has `log(0)=0` and `log(-x)=log(x)`;
positive likelihoods below avoid those extensions. `ENNReal.ofReal` clips
negative inputs to zero; `toReal(infinity)=0`. `Measure.map` is ordinary
pushforward for measurable maps, as used here. `withDensity(f)` integrates
the extended nonnegative density against its base measure. Measure support
consists of the points all of whose open neighborhoods have positive measure;
under the stated second-countable Borel assumptions its complement is null.

## SAP.P029b.T14

The binomial law on pairs `(k1,k0)` is the product of
`choose(n1,k1)p1^k1(1-p1)^(n1-k1)` and its control-arm counterpart. Here
`0<=ki<=ni` by the `Fin(ni+1)` types, so the natural subtraction in the
exponent is ordinary nonnegative subtraction. Set
`R=max(k1/n1-k0/n0,0)` and `d=p1-p0`. The theorem is the conjunction of four
independently universally quantified statements:

1. For every positive natural `n1,n0`, then every real `p1,p0` with
   `0<=p0<=p1<=1`, `E[R]-d=E[max(k0/n0-k1/n1,0)]>=0`;
   if additionally `p0>0` and `p1<1`, that bias is strictly positive;
   for every real `delta>0`,
   `P(delta<|R-d|)<=(p1(1-p1)/n1+p0(1-p0)/n0)/delta^2`.
2. For every such `n1,n0,p1,p0`, then every allowed pair of counts,
   `|R-d|<=|(k1/n1-k0/n0)-d|`.
3. For every pair of sequences of positive natural arm sizes both tending
   to infinity, then every `0<=p0<=p1<=1`, then every `delta>0`, the above
   error-event probability tends to zero.
4. For every positive `n1,n0`, then every `p1` in `[0,1]`, with `p0=0`,
   the control count is zero with probability 1, `R=k1/n1` on that event,
   and `E[R]=p1`.

No optimization or identification of `R` as a maximum-likelihood estimate is stated.

## SAP.P029b.T15

This is a conjunction of concrete statements about a six-point law and
constant arrays, with no outer assumptions. The latent types have masses
`1/2,1/4,1/4`: respectively complier, always-taker, never-taker. Assignment
is an independent fair Boolean; covariate is the sole value of `Unit`;
`Y0=0,Y1=1` for every type. The theorem asserts `FIV`, finite latent
ignorability, score `1/2>1/4`, average effect 1, and `fWald` with constant
weight 2 equal to 1. It asserts convergence to zero of the constant sequence
`|1/2-score|`, and nonconvergence to zero of the constant sequence `1/2`.
For every natural `n`, then every level in `[0,1]`, the constant array of
length `n+1` with value `1/2` has a type-7 quantile `1/2`, and every real
type-7 quantile is `1/2`. For every `n` its count strictly below `1/2` is
zero; finally `1/(1/2)=2`.

## SAP.P029b.T16

The following five clauses are conjoined:

1. For every natural `n`, array `s:Fin(n+1)->R`, and real `lambda,c,b`,
   if `0<lambda<1`, `c` is a type-7 quantile at that level, and
   `b<=s_i` for every `i`, then
   `belowCount(s,c)<=1+n*lambda`,
   `belowCount(s,c)/(n+1)<=lambda+1/(n+1)`, and `b<=c`.
2. For every triangular array `s`, real sequence `c`, and real `alpha>0`,
   if for **every** natural `n`, `c_n` is a type-7 quantile at level
   `(n+1)^(-alpha)`, then the fraction strictly below `c_n` tends to zero.
3. For every `n`, arrays `s,V`, and real `lambda,c,b,K`, assume in order
   `0<lambda<1`, the quantile condition, `b>0`,
   `b<=s_i<=1` for all `i`, `K>=0`, and `|V_i|<=K` for all `i`.
   Then for every `i`, `0<=weightChange(s_i,c)<=b^(-1)1_{s_i<c}`, and
   `|sum_i weightChange(s_i,c)V_i/(n+1)| <= (K/b)(lambda+1/(n+1))`.
4. For every `n`, real level in `[0,1]`, and real `c`, a type-7 quantile
   of the half-valued constant array must equal `1/2`. Separately the
   constant sequence `1/2` does not tend to zero. This clause does not
   assert quantile existence.
5. For arbitrary measurable `Omega` and **finite** measurable `X` with
   measurable singletons, probability measure `mu`, sequences `U,Z`,
   measurable versions `c,m`, estimates `s`, and cutoff sequence, assume
   `ICSWConditions`; then choose `alpha>0`; assume a positive uniform
   lower bound for `scoreAt(U_0,x)` on every positive-mass profile, with
   upper bound 1; assume all cutoffs are measurable and, for every `n`,
   almost everywhere are the type-7 quantile of the `n+1` estimates at
   `(n+1)^(-alpha)`; finally assume `RatiosEventuallyDefined` for both
   original and Winsorized weights. Then their difference tends to zero
   in probability, and each sequence tends in probability to
   `sum_x P(X_0=x) E[tau_0|C_0,X_0=x]`. If latent ignorability holds at
   every positive-mass profile of unit zero, this target equals `E[tau_0]`.

## SAP.P029b.T17

Write `B(p,d)=p^(b(d))(1-p)^(1-b(d))` and
`r(a,b,z)=a(1-b)b(z)+ab`. Three clauses:

1. For every real `pi` and Booleans `z,d`, if `0<pi<1`,
   `B(r(pi,0,z),d)=B(pi*b(z),d)`.
2. For every finite observation type `I`, arbitrary parameter type `Theta`,
   probability family `pi:Theta->I->R`, and Boolean data `Z,D`, assume
   `0<pi(theta,i)<1` for **all** parameters and observations and assume
   `Z_i=false` implies `D_i=false`. Then, for every parameter, the product
   of `B(pi(theta,i)b(Z_i),D_i)` over all observations equals the product
   of `B(pi(theta,i),D_i)` over treated observations. For every parameter
   `theta`, being a global maximizer of the first product (comparison
   with every `t:Theta`) is equivalent to being a global maximizer of
   the treated product. There is no nonemptiness assumption on `Theta`
   and no existence of maximizers asserted; the identities also cover
   an empty observation type using the empty product 1.
3. The additive expressions at `pi=3/4` are `7/4` for `d=true` and `5/4`
   for `d=false`, whereas the Bernoulli factors are `3/4` and `1/4`.

## SAP.P029b.T18

Five clauses:

1. For arbitrary measurable `Omega,X` with measurable singletons in `X`,
   probability `mu`, `U,Z`, assume measurability of `X,D0,D1,Z`, zero
   defier measure, independence of `Z` and `(X,D0,D1)`, and
   `0<P(Z=true)<1`. Next choose a profile `x` with `P(X=x)>0` and
   `E[D1|X=x]>0`. Put `a=E[D1|X=x]` and
   `b=P(D0=true,D1=true,X=x)/P(D1=true,X=x)`. Then
   `ab=E[D0|X=x]`, `a(1-b)=scoreAt(x)`, and for every Boolean `z`,
   `E[D(Z)|X=x,Z=z]=scoreAt(x)b(z)+E[D0|X=x]=r(a,b,z)`.
   No outcome conditions or overall relevance hypothesis are needed.
2. For every covariate type and potential unit that is not a defier,
   complier and `D0=true` are disjoint, and
   `(complier or D0=true)` is equivalent to `D1=true`.
3. For every `a,b` in `(0,1)` and Boolean `z`, `r(a,b,z)` is in `(0,1)`
   and equals `a` at true assignment, `ab` at false assignment.
4. For every real `p>0` and real `v`, `(pv)/p=v`.
5. A specific uniform four-point law on two independent Booleans has
   `U(i)=((),false,i.first,0,1)`, so `P(D(Z)=true)=1/4`,
   `scoreAt(())=1/2`, `(1/2)b(false)=0`, and `(1/2)b(true)=1/2`.
   This is one concrete misconditioning example, not a quantified family.

## SAP.P029b.T19

For every real index pair `(iAC,iA)`, then every Boolean `z`, define
`AC=1_{iAC>0}`, `A=1_{iA>0}AC`, `C=AC-A`, and `D(z)=Cb(z)+A`.
The theorem asserts that `AC,A,C,D(z)` all belong to `{0,1}`, `A<=AC`,
`AC`'s always and complier parts satisfy `A*C=0`,
`D(true)-D(false)=C>=0`, and the following exact equivalences hold:
`D(false)=1 iff A=1`; `(D(false)=0 and D(true)=1) iff C=1`;
`(D(false)=0 and D(true)=0) iff AC=0`.
Separately there is no real `D` satisfying `D=D*1+1`; both 0 and 1
satisfy `D=D*1+0`; and for all real `D,A`, `D=D*0+A iff D=A`.
Finally for every real `Y0,tau,D`,
`Y0+tau*D=Y0+D*((Y0+tau)-Y0)`.

The baseline index definitions are `2+a+b*x1+c*x2+d*x3+error` and
`-2+e+f*x1+g*x2+h*x3+error`; the nonlinear ones are
`2+a+(1+b*x1)(1+c*x2)+d*x3^3/3+error` and its `-2,e,f,g,h` analogue.
They are not mentioned in `T19Statement`. No distributions of indices,
errors, covariates, or assignments are stated by this theorem.

## SAP.P029b.T20

First it negates a universal implication over all small measurable types
`Omega,X` (with measurable singletons in `X`), all probability measures,
potential-unit maps, and assignments: under `IVAssumptions`, for every
profile with positive covariate mass and positive score, `typicalAt(x)`
would imply `latentAt(x)`. Thus it asserts the existence of a genuine
counterexample to that implication, without specifying its data in the
statement.

Second it asserts concrete finite identities for the six-point law with
the same type masses and randomization as T15, but now always-takers have
`Y0=1,Y1=2`, and compliers and never-takers have `Y0=0,Y1=1`.
This law satisfies `FIV` and finite latent ignorability, while its received
and unreceived conditional means are respectively `1/2,0` for `Y0` and
`3/2,1` for `Y1`. This is a separate witness in the other direction.

## SAP.P029b.T21

Three clauses:

1. For arbitrary measurable `Omega,X` with measurable covariate singletons,
   probability `mu`, `U,Z` satisfying `IVAssumptions`, functions `c,m`
   satisfying `ScoreVersions`, a real `epsilon>0` such that
   `epsilon<c(X)<=1` almost everywhere, and a real `tau` with
   `U(omega).tau=tau` for **every** `omega`, the conclusion is:
   for every positive-mass profile with positive score,
   both `E[effect|X=x]` and `E[effect|C,X=x]` equal `tau`;
   `A1Versions` holds; and `W(1)=W(1/c(X))=tau`.
2. The following universal implication is false. For all small measurable
   `Omega`, finite measurable `X` with measurable singletons, probability
   `mu`, and `U,Z`, `IVAssumptions` plus positive score at every
   positive-mass profile plus **marginal** independence of the real effect
   and the Boolean complier indicator imply the conjunction of latent
   ignorability at every positive-mass profile, `W(1)=E[effect]`, and
   `W(1/scoreAt(X))=E[effect]`.
3. A separate universal implication with the same types and positivity is
   false when the independence antecedent is replaced by, for every
   positive-mass profile `x`, independence of effect and the pair
   `(D0,D1)` under the normalized restriction
   `P(X=x)^(-1) mu|{X=x}`. The consequent is the **same conjunction**.

Neither negation says that every individual conjunct fails, nor do they
by themselves assert failure of each of the three conclusions under each
independence condition. The second independence condition actually
implies the conditional mean identity in the first conjunct; the negation
can instead be witnessed by the unweighted Wald identity.

## SAP.P029b.T23

Let `q(x,z)` be four real cell probabilities, with `x,z` Boolean, whose
parameter space is **all** arrays satisfying, for every `x`,
`0<q(x,false)<q(x,true)<1`. There are 16 observations `(x,z,j)`,
`j=0,1,2,3`. Their binary responses have success counts 1 in either control
cell, 2 in the treated `x=false` cell, and 3 in the treated `x=true` cell.
An observation likelihood is `B(q(x,z),D)` and its weight is 9 for a
success and 1 for a failure. Write
`Qinside(q)=-sum_observations log(B(q,D)*weight)` and
`Qweighted(q)=-sum_observations weight*log(B(q,D))`.

The theorem asserts there exists a parameter `q` equal to the cell array
`q(x,false)=1/4`, `q(false,true)=1/2`, `q(true,true)=3/4`, such that
for **every** parameter `t`, `Qinside(q)<=Qinside(t)`, and it is false
that `Qweighted(q)<=Qweighted(t)` for every `t`.
This is an exact global optimization counterexample with strictly positive
likelihoods and weights. There are no numerical solver or bootstrap claims.

## SAP.P029b.T25

Three clauses:

1. For arbitrary measurable `Omega,X`, probability `mu`, and `U,Z`
   satisfying `IVAssumptions`, the receipt ITT equals `P(C)`, the outcome
   ITT equals `E[1_C tau]`, that last expectation equals
   `P(C)E[tau|C]`, and `E[tau|C]` equals both `W(1)` and the explicit
   outcome-ITT/receipt-ITT ratio. Relevance and monotonicity ensure that
   `P(C)` is positive; the statement does not add it as a hypothesis.
2. For every natural `N`, real sample outcomes `Y`, and Boolean `D,Z`,
   assume `0<sum_i b(Z_i)<N` and a nonzero unweighted receipt first stage.
   Then `sampleWald(1,Y,D,Z)=sampleCross(Z,Y)/sampleCross(Z,b(D))`.
3. Pure numerical equalities give `(0/2+1/2)/(1/2+1/2)=1/2`,
   the complier-weighted mean with half each sex, compliance `3/4,1/10`,
   and effects `0,1` equal to `2/17`, its inclusion in
   `[115/1000,125/1000)`, and restoration of `1/2` by inverse-compliance
   weighting. No stochastic specification of this numerical example is asserted.

## SAP.P029b.T26

Two clauses:

1. For arbitrary measurable `Omega,X`, probability `mu`, `U,Z` with
   `IVAssumptions`, `c,m` with `ScoreVersions`, real `epsilon>0` with
   `epsilon<c(X)<=1` almost everywhere, the following identities hold:
   `P(C)E[tau|C]=E[c(X)m(X)]`; `P(C)=E[c(X)]`;
   the weighted outcome ITT at `w=1/c(X)` is `E[m(X)]/E[1/c(X)]`;
   the weighted receipt ITT is `1/E[1/c(X)]`;
   `W(1/c(X))=E[m(X)]`; and if additionally `A1Versions` holds,
   that Wald ratio equals `E[tau]`.
2. For arbitrary measurable `Omega`, measurable topological `X` with
   second-countable topology and its Borel sigma algebra, probability
   `mu`, sequences `U,Z`, versions `c,m`, estimates `s`, assume
   `ICSWConditions`. Next choose a measurable `a:X->R` such that for
   every `i`, `a(X_i)=E[tau_i|sigma(X_i)]` almost everywhere. Assume
   `m(x)=a(x)` at **every point** of the support of the law of `X_0`;
   assume there exists `epsilon>0` such that
   `epsilon<c(x)<=1` at **every point** of that support; and assume
   `RatiosEventuallyDefined` for inverse estimated-score weights.
   Then `icswSequence` tends in probability to `E[tau_0]`.

## SAP.P029b.T27

Three clauses:

1. For arbitrary measurable `Omega,X`, probability `mu`, `U,Z` satisfying
   `IVAssumptions`, `c,m` satisfying `ScoreVersions`, and positive
   complier mass `pC`, define `nuC` as the pushforward under `X` of
   `pC^(-1)mu|C`. Then
   `nuC=(law of X).withDensity(ofReal(c(x)/pC))` and
   `E[tau|C]=integral m(x) d nuC`. No positive lower bound on score is
   assumed in this clause.
2. For arbitrary measurable `Omega`, second-countable Borel `X`,
   probability `mu`, `U,Z,c,m,s` satisfying `ICSWConditions`, assume
   there exists `epsilon>0` such that `epsilon<c(x)<=1` at every point
   of the support of the law of `X_0`, then assume
   `RatiosEventuallyDefined` for inverse estimated-score weights.
   The ICSW sample sequence tends in probability to `E[m(X_0)]`.
   No `A1Versions` or latent ignorability is assumed.
3. For every natural sample size `N`, real `Y`, Boolean `D,Z`, and real
   `p>0`, if both `SampleDefined(1/p,D,Z)` and
   `SampleDefined(1,D,Z)` hold, the sample Wald ratio with constant
   weight `1/p` equals the unweighted sample Wald ratio.

## Mathlib source checks

The reductions above were checked against
`MeasureTheory/Function/ConvergenceInMeasure.lean:57`,
`MeasureTheory/Function/ConditionalExpectation/Basic.lean:102`,
`Probability/Independence/Basic.lean:136,144` and its kernel definitions,
`Probability/IdentDistrib.lean:71`,
`MeasureTheory/Integral/Bochner/Basic.lean:158,204`,
`MeasureTheory/Measure/Support.lean:59`,
`MeasureTheory/Measure/Map.lean` (`map`),
`MeasureTheory/Measure/WithDensity.lean:39`, and
`Analysis/SpecialFunctions/Log/Basic.lean` (`log_zero`, `log_neg_eq_log`).
All paths in this paragraph are relative to the supplied Mathlib source root.
