# Blind reading

Written before opening `claims.json`, `record.json`, `earlier.json`, or
`architect-report.md`. Sources: the five declarations in Challenge/Part1,
every declaration listed for them in closure.json, and the relevant Mathlib
definitions. ClosureChecks.lean also prints every generated auxiliary declaration
in the closures. These auxiliaries prove index bounds, nonemptiness of a finite
range, or the numeral `AtLeastTwo` instances used for rational literals; they add
no statistical assumptions.

In the mathematics below, a Boolean is 0 or 1 when used numerically. Limits of
real sequences are ordinary limits as the natural index tends to infinity.
Convergence in probability means that, for every positive extended-real distance
threshold, the measure of the set where the distance is at least that threshold
tends to zero. All probability measures are Mathlib measures of total mass one.
Integrals are Mathlib Bochner integrals. These conventions are expanded further
where they matter.

## SAP.P029b.T14

The theorem is the conjunction defined by T14WholeStatement (WholeW1:66), including
T14Statement (Part3:20). It asserts all of the following independently.

1. For every four natural numbers n1,n0,k1,k0 with n1>0, n0>0,
   k1<=n1, k0<=n0, let r1=k1/n1, r0=k0/n0 (natural numbers cast into R).
   On the triangle 0<=v0<=v1<=1 maximize
   L(v1,v0)=v1^k1 (1-v1)^(n1-k1) v0^k0 (1-v0)^(n0-k0).
   The specified fit is (r1,r0) if r0<=r1 and otherwise
   ((k1+k0)/(n1+n0),(k1+k0)/(n1+n0)). It belongs to the triangle;
   for every v in the triangle L(v)<=L(fit), with equality iff v=fit.
   Its coordinate difference is max(r1-r0,0).
   This fully unfolds BinomialKernelW1, SaturatedLikelihoodW1,
   ReceiptTriangleW1, SaturatedFitW1, MLConclusionW1, and positiveScore.
2. For every real p,q, if 0<q<p<1, then p and q/p belong to (0,1).
   Writing R(a,b,z)=a(1-b)1{z=true}+ab (nestedReceipt),
   R(p,q/p,false)=q, R(p,q/p,true)=p, and p(1-q/p)=p-q.
3. For every positive natural n1,n0 and reals 0<=p0<=p1<=1, give the pair
   (k1,k0) in {0,...,n1} x {0,...,n0} mass
   B(k1,k0)=choose(n1,k1)p1^k1(1-p1)^(n1-k1)
   choose(n0,k0)p0^k0(1-p0)^(n0-k0).
   Thus the two arm counts have independent binomial distributions.
   Put S(k)=max(k1/n1-k0/n0,0), d=p1-p0. Then
   sum_k B(k)S(k)-d = sum_k B(k)max(k0/n0-k1/n1,0) >=0.
   If additionally p0>0 and p1<1 the bias is strictly positive.
   For every real delta>0,
   sum_{|S-d|>delta} B <= [p1(1-p1)/n1+p0(1-p0)/n0]/delta^2.
   For every count pair, |S-d|<=|k1/n1-k0/n0-d|.
   Here fE is precisely the finite weighted sum and fP the sum of masses
   on the indicated predicate; binomialMass and binomialArmLaw are the
   displayed masses, and armRateScore is S.
4. For every pair of sequences n1(n),n0(n) of positive natural numbers,
   both tending to infinity, every fixed 0<=p0<=p1<=1, and every delta>0,
   the just-described binomial probability of |S-d|>delta tends to zero.
5. For every positive natural n1,n0 and p1 in [0,1], at p0=0 the
   probability k0=0 is one. For every count pair with k0=0, S=k1/n1;
   and the mean of S is p1.
6. For every positive n1,n0 and 0<=p0<=p1<=1, the probability of the
   event k1=0 and k0=n0 is (1-p1)^n1 p0^n0. This is strictly positive
   if p0>0 and p1<1.
7. JointStratumConsistencyW1: for every finite type G (possibly empty),
   every measurable space Omega, probability measure mu, arm sizes
   n1,n0:G->N->N positive at every g,n and tending to infinity for each g,
   and probabilities with 0<=p0(g)<=p1(g)<=1, consider measurable count
   pairs K(g,n):Omega->{0,...,n1(g,n)}x{0,...,n0(g,n)}.
   Assume for every g,n,k that the real mass mu{K(g,n)=k} is the product
   binomial mass B above. Then for every delta>0,
   mu{exists g, |S_g,n-(p1(g)-p0(g))|>delta} tends to zero.
   No independence across g or n is assumed; each pair's marginal law
   already specifies independence between its two arm counts.
8. For every positive natural n and p in [0,1],
   sum_{k=0}^n choose(n,k)p^k(1-p)^(n-k) k/n=p.
   This last one-arm assertion has no control-arm-size hypothesis.

The docstring describes these as a saturated ordered-binomial MLE, nested
interior parameters, bias, extreme-event probability, bounds, finite-stratum
consistency, and one-sided unbiasedness, with usual measure conditions.

Junk conventions: natural powers use 0^0=1, which is intentional and necessary
for the boundary binomial likelihood and probabilities. Natural subtraction in
n-k truncates at zero, but every relevant k<=n, including the Fin indices.
All rates, the pooled rate, q/p, and delta^-2 have positive denominators under
the respective hypotheses. Natural casts are exact; there is no integer rounding.
The definitions could evaluate zero-denominator rates outside these hypotheses,
but the theorem does not use those evaluations. Empty G makes just its joint
assertion trivial; the result also quantifies over every nonempty finite G.
The count types and binomial summations are nonempty. mP(mu,A)=(mu A).toReal;
infinity would map to zero, but mu is a probability measure here. All sums are
finite, so there is no integral-of-nonintegrable-function convention in this
theorem. There are no logarithms, square roots, real powers, extrema of empty
sets, limsups, or partial-function defaults.

## SAP.P029b.T15

T15WholeStatement (WholeW1:102), including T15Statement (Part3:52), is a
conjunction about fixed finite data followed by universally quantified vectors.
It has no antecedent that could exclude its proposed counterexample.

The data have six atoms (i,z) in {0,1,2} x Bool. The mass is t(i)/2 where
t(0)=1/2 and t(1)=t(2)=1/4 (typeMass, randomized, sixMass).
At each atom X is the unique element of Unit. Potential treatment is
(d0,d1)=(false,true) at i=0, (true,true) at i=1, (false,false) at i=2.
Every atom has y0=0,y1=1. This is constantUnit lifted across z by liftUnit.
The observed assignment is z. PotentialUnit contains X, Boolean d0,d1 and
real y0,y1; its treatment at assignment z is dz and its observed outcome is
y1 when dz=true and y0 otherwise. Its tau is y1-y0; its complier event is
d0=false,d1=true and its defier event d0=true,d1=false.

For finite masses p, fE(p,v)=sum p_i v_i, fP(p,A)=sum_{i in A}p_i,
and fCE(p,v,A)=sum_{i in A}p_i v_i / sum_{i in A}p_i.
The asserted FIV expands into: nonnegative masses summing to one; assignment
probability strictly between 0 and 1; independence of the tuple
(X,d0,d1,y0,y1) and Z, meaning every joint singleton probability factors;
zero defier probability; and a nonzero difference of mean observed receipt
between Z=true and Z=false. The observed-outcome definition also encodes
exclusion through receipt and consistency with the potentials.

The following further assertions hold for this fixed law:

* For every x with positive X probability, E[tau|X=x]=E[tau|complier,X=x]
  (fLatentIgnorability). The score fScore(x)=P(complier,X=x)/P(X=x) is
  exactly 1/2 at the unique profile and exceeds 1/4. Each atom's tau=1,
  the mean tau=1, and the population weighted Wald ratio with weights 2 is 1.
  That ratio (fWald) is the difference of weighted conditional outcome means
  divided by the difference of weighted conditional receipt means, where a
  weighted conditional mean is fCE(p,wv,{Z=z})/fCE(p,w,{Z=z}).
* Receipt-arm means are E[D|Z=true]=3/4, E[D|Z=false]=1/4.
* The constant estimate 1/2 has absolute score error tending to zero, while
  the constant sequence 1/2 does not tend to zero.
* For every n:N and every real level in [0,1], the vector of n+1 copies of
  1/2 has type-7 quantile 1/2, and every such quantile c is 1/2.
  Type7Quantile means there exists a permutation pi sorting the vector
  monotonically and an index j in {0,...,n} with
  j<=n*level<j+1, such that c=(1-gamma)s(pi(j))+gamma s(pi(min(j+1,n))),
  gamma=n*level-j. The finite-index minimum is nextOrderIndex.
* For every n and every level in (0,1], the same vector has inverse empirical
  quantile 1/2, uniquely. EmpiricalCDFW1(s,t) is the number of entries <=t
  divided by n+1. InverseEmpiricalQuantileW1(s,level,c) says the set
  A={t:level<=CDF(s,t)} is nonempty and bounded below and c=inf A.
* For every real alpha>0 and every n, both quantile predicates hold at
  level (n+1)^(-alpha), and |1/2-0|=1/2.
* For every n, the number of entries strictly below 1/2 (belowCount) is zero.
  The inverse score is 2. For every n, every outcome vector Y and Boolean
  vectors D,Z of length n+1, at every index max(1/2,1/2)=1/2 and its inverse
  is 2, and the Wald ratio after replacing scores by max(score,cutoff)
  equals the ratio using constant weights 2. Here sampleArm(w,Y,Z,z) is
  sum_i w_i 1{Z_i=z}Y_i / sum_i w_i 1{Z_i=z}; sampleWald is the
  difference of those outcome-arm means divided by the analogous receipt
  difference.

The docstring calls this a constant-score counterexample with the five IV
assumptions and Assumptions 1--3 and with a nonvanishing cutoff and unchanged
weights.

Junk conventions: every population conditioning event used at the actual unique
profile or in the two arms has positive mass; all population weighted-mean and
first-stage denominators in this fixed witness are nonzero. The fCE definition
would return zero on null events, but none is used to establish these numerical
facts; fLatentIgnorability is guarded by positive profile probability. The sample
Wald identity is quantified even over empty assignment arms and zero first stages:
division by zero is zero in R, so it is an identity of extended-to-all-input real
expressions in those cases. It does not assert those particular samples give a
defined statistical ratio. Length n+1 is always positive. The type-7 endpoint
level=1 uses j=n and the clamped next index n; its interpolation coefficient is
zero. The generalized inverse requires a nonempty bounded-below set, excluding
the arbitrary real sInf value on an empty or unbounded-below set. Real rpow has
strictly positive base n+1, so its nonpositive-base conventions are irrelevant.
All natural casts are exact and count subtraction is absent. No Bochner
integrals, toReal, logs, square roots, limsups, or partial defaults occur.

## SAP.P029b.T16

This theorem uses T16WholeStatement (WholeW1:163), NOT the older T16Statement
in Part3. It is a conjunction of six assertions with separate quantifiers.

1. For every n:N, real vector s of length n+1, real level,c,b, if
   0<level<1, c is its type-7 quantile as defined in the T15 section, and
   b<=s_i at every index, then the number M=#{i:s_i<c} obeys
   M<=floor_N(1+n*level), floor_N(1+n*level)<=1+n*level,
   M/(n+1)<=level+1/(n+1), and b<=c.
2. For every such s and 0<level<=1 an inverse empirical-CDF quantile exists.
   For every real c,b, if c is such a quantile and b is a lower bound on s,
   then M<=floor_N(1+n*level), M/(n+1)<=level+1/(n+1), and b<=c.
   The CDF and inverse predicates are the count/n+1 and nonempty,
   bounded-below infimum predicates expanded in T15.
3. For every triangular array s(n):Fin(n+1)->R, every cutoff sequence c(n)
   and real alpha>0, if for every n either quantile convention makes c(n)
   a quantile at level (n+1)^(-alpha), then M_n/(n+1) tends to zero.
   The choice between the two conventions may depend on n.
4. For every n, vectors s,V, and real level,c,b,K, assume 0<level<1,
   c is a type-7 quantile, b>0, b<=s_i<=1 for all i, K>=0, |V_i|<=K.
   Then at every i, the inverse-weight change
   Delta_i=1/s_i-1/max(s_i,c) (weightChange) lies between 0 and
   (1/b)1{s_i<c}. Also |sum_i Delta_i V_i/(n+1)|
   <=(K/b)(level+1/(n+1)). This is a bound on an unnormalized arithmetic
   average of weighted values.
5. For every n and level in [0,1], type-7 quantiles of the half-score vector
   exist and are uniquely 1/2; for every alpha>0 they exist at all the power
   levels above; and the constant sequence 1/2 does not tend to zero.
6. For every measurable Omega, finite covariate type X with measurable space
   and measurable singletons, probability measure mu, sequence
   U_i:Omega->PotentialUnit X, sequence Z_i:Omega->Bool,
   score array s(n,i):Omega->R and cutoff(n):Omega->R, assume the
   following FiniteSampleConditionsW1:
   - For every i the five coordinates X_i,d0_i,d1_i,y0_i,y1_i and Z_i are
     measurable, y0_i,y1_i are integrable, and Z_i is independent of the
     tuple (X_i,d0_i,d1_i,y0_i,y1_i). The probability of Z_i=true lies
     strictly in (0,1), defiers have measure zero, and the mean observed
     receipt difference between assignment arms is nonzero (IVAssumptions).
   - The joint tuples ((X_i,d0_i,d1_i,y0_i,y1_i),Z_i) (jointVariables)
     are independent across i and each has the same distribution as at i=0.
   - Each s(n,i) is measurable. For every n, almost surely every score at
     indices 0,...,n is in (0,1].
   - There exists a single real epsilon>0 such that at every profile x
     having positive mass for X_0, epsilon<c(x)<=1, where
     c(x)=mu{complier_0,X_0=x}.toReal/mu{X_0=x}.toReal (scoreAt).
   - max_{0<=i<=n}|s(n,i)-c(X_i)| converges in probability to zero.
     This maximum is uniformScoreError: the maximum of the absolute errors
     over the explicitly nonempty finite range 0,...,n.
   For every real alpha>0, if every cutoff(n) is measurable and, for every n,
   almost surely cutoff(n) is a type-7 quantile of the observed scores at
   level (n+1)^(-alpha), then WinsorizationLimitsW1 asserts:
   - Winsorized ICSW minus ordinary ICSW converges in probability to zero;
   - each of the two ratios converges in probability to
     L=sum_{x:X} mu{X_0=x}.toReal * m(x), where
     m(x)=integral_{complier_0,X_0=x}(y1_0-y0_0)dmu /
          mu{complier_0,X_0=x}.toReal (complierAt);
   - if for every positive-mass profile x,
     integral_{X_0=x}tau_0 / P(X_0=x) =
     integral_{complier_0,X_0=x}tau_0 / P(complier_0,X_0=x)
     (latentAt), then L=integral tau_0 dmu.
   Ordinary ICSW (icswSequence) is sampleWald on the first n+1 units with
   observed D_i=d_{Z_i,i}, Y_i=y_{D_i,i}, weights 1/s(n,i).
   winsorizedSequence uses weights 1/max(s(n,i),cutoff(n)). The arm means
   and final ratio are exactly those expanded in T15. No hypothesis of
   eventual definedness of these ratios occurs.

The docstring describes these count, fraction, lower-bound, nonvanishing-cutoff,
inverse-weight, weighted-value and finite-profile iid limit statements, and
explicitly discloses real division on undefined samples.

Junk conventions: floor_N is the natural-number floor (would be zero on negative
inputs), but its input here is positive. Vectors have length n+1 and the maximum
used for uniform error has a proved nonempty range. Type-7 clamps its last index;
the generalized inverse excludes empty and unbounded-below sets. The power base
n+1 is strictly positive; no log/sqrt or nonpositive-base rpow behavior is used.
All arithmetic n+1 denominators and the bound parameter b are positive. In the
sample-limit assertion the scores, their reciprocals and quantile cutoffs are
positive almost surely at every n. Nevertheless an assignment arm can be empty
or a sample first stage can be zero: all sample divisions then use real 0^-1=0.
These are permitted by design. Their asymptotic rarity is part of what a valid
statistical reading of the limit needs, rather than an input assumption.
All relevant measures are finite, so ENNReal.toReal never converts infinity to
zero. Conditional profile ratios return zero at zero-mass profiles; the score
overlap and latent-ignorability assumptions are guarded by positive mass, and
zero-mass profiles have zero coefficient in L. Positive-mass profiles have
positive complier mass. Integrability of the potential outcomes makes restricted
integrals of tau defined. The Bochner zero value for nonintegrable functions
therefore does not enter these population means. Finite X can formally be empty,
but then a map U from a probability space into PotentialUnit X cannot meet the
hypotheses. No supremum of an unbounded or empty set, limsup, integer cast, or
partial-function default is used.

## SAP.P029b.T17

T17WholeStatement (WholeW1:208) includes T17Statement (Part3:109). It asserts:

1. For every real pi in (0,1) and Boolean z,d, the Bernoulli factor at
   nestedReceipt(pi,0,z) equals the factor at pi*1{z=true}.
   The nested expression is pi(1-0)1{z=true}+pi*0. bernoulliFactor(p,d)
   is p^(1 if d else 0) * (1-p)^(0 if d else 1).
2. For every finite observation type I, arbitrary parameter type Theta,
   pi:Theta->I->R and Boolean data Z,D:I->Bool, assume for every theta,i
   that 0<pi(theta,i)<1 and for every i that Z_i=false implies D_i=false.
   For every theta the product of Bernoulli factors with probability
   pi(theta,i)1{Z_i=true} over all i equals the product with probability
   pi(theta,i) over only indices with Z_i=true.
   For every theta, the assertion that its full product is at least that of
   every t:Theta is equivalent to the corresponding assertion for the
   treated-only product. There is no claim that a maximizer exists.
3. At pi=3/4 the additive expression pi^1+(1-pi)^0 is 7/4 and
   pi^0+(1-pi)^1 is 5/4; the actual Bernoulli factors are 3/4 for d=true
   and 1/4 for d=false.
4. For every real pi in (0,1), every Boolean z,d,
   (pi*1{z=true})^(1 if d else 0) +
   (1-pi*1{z=true})^(0 if d else 1)
   equals pi*1{z=true}+1 if d=true and 2-pi*1{z=true} otherwise,
   and this additive expression is at least 1.

The docstring calls this the corrected one-sided Bernoulli likelihood reduction
and shows the two formulas for the printed additive factor. No sampling or
independence assumption is needed for these deterministic likelihood identities.

Junk conventions: natural exponent zero gives 0^0=1, in particular making a
control observation (Z,D)=(false,false) have Bernoulli factor 1. This is the
intended boundary convention. The incorrect additive factor deliberately uses
the same convention. If I is empty both products are 1 and every theta is a
maximizer; for nonempty I the universal identities remain substantive. If Theta
is empty the parameter-quantified assertions are vacuous, but all inhabited
parameter types are covered too. There are no divisions, integrals, infinite
measures, logarithms, roots, real powers, extrema, limits, or partial defaults.

## SAP.P029b.T18

T18WholeStatement (WholeW1:254) is the conjunction of the following assertions.

1. For every measurable Omega and covariate X with measurable singletons,
   probability measure mu, U:Omega->PotentialUnit X and Z:Omega->Bool,
   assume ReceiptConditionsW1: X,d0,d1,Z are measurable, defiers have
   measure zero, Z is independent of (X,d0,d1), and 0<P(Z=true)<1.
   Almost surely, the complier event and {d0=true} are disjoint, and their
   union is {d1=true}. For every x with P(X=x)>0, put
   a=E[1{d1=true}|X=x], a0=E[1{d0=true}|X=x],
   c=P(complier,X=x)/P(X=x), and e=P(Z=true). Then
   a=a0+c; for every Boolean z, E[D|X=x,Z=z]=c*1{z=true}+a0;
   E[D|X=x]=a0+e*c; and if P(d0=true)=0 then a0=0.
   These are ReceiptProfileConclusionW1. Every event mean mCE(mu,v,A)
   is integral_A v dmu / (mu A).toReal, and mP is (mu A).toReal.
   Further, if a>0, let b=P(d0=true,d1=true,X=x)/P(d1=true,X=x)
   (alwaysAmongAC). Then ab=a0, a(1-b)=c, and for every z,
   E[D|X=x,Z=z]=a(1-b)1{z=true}+ab (nestedReceipt).
   Finally, under the additional conditions P(d0=true)=0, c=1/2 and e=1/2,
   E[D|X=x]=1/4, whereas for every Boolean z the right side
   c*1{z=true}+a0 is 1/2 when z=true and 0 otherwise.
   This last assertion is universal over laws satisfying those conditions;
   it does not itself construct such a law.
2. For every real a,b in (0,1) and every Boolean z,
   nestedReceipt(a,b,z) is in (0,1) and equals a if z=true, ab otherwise.
3. For every real p,m with p>0, (p*m)/p=m.
4. For every measurable Omega and X (no finite-type or singleton assumption
   here), probability measure mu, U,Z and real functions c,m:X->R, assume:
   - IVAssumptions: coordinate and assignment measurability, integrable y0,y1,
     Z independent of (X,d0,d1,y0,y1), assignment probability in (0,1),
     no defiers almost surely, and a nonzero mean receipt first stage;
   - ScoreVersions: c,m are measurable,
     c(X)=E[1{complier}|sigma(X)] almost surely and
     c(X)m(X)=E[1{complier}tau|sigma(X)] almost surely.
     covariateSigma is the pullback of the measurable sets of X along U.x.
     condExp is Mathlib's conditional expectation with respect to that sigma
     algebra and mu, with equality only up to mu-null sets;
   - c(X)>0 almost surely; 1/c(X) is integrable; for each Boolean z,
     (1/c(X))*outcome(z) is integrable; and J=integral 1/c(X) dmu is nonzero.
   Write nu for the distribution of X, i.e. Measure.map(U.x,mu).
   Then m is nu-integrable. The difference of weighted observed-outcome
   arm means equals (1/J)*integral_X [(c(x)m(x))/c(x)] dnu, and this
   equals (1/J)*integral_X m(x) dnu.
   mArm(mu,Z,w,v,z) means E[wv|Z=z]/E[w|Z=z]; here w=1/c(X)
   and v=outcome(Z), with outcome(z)=y1 if dz=true, otherwise y0.
   Thus this component is a weighted ITT outcome difference, not a Wald
   ratio or a final ATE assertion. No latent-ignorability assumption is
   present in this component.
5. For every natural n, scores s and outcomes Y:Fin n->R and Boolean
   D,Z:Fin n->Bool, assume every s_i is in (0,1] and SampleDefined:
   for each Boolean z, sum_i (1/s_i)1{Z_i=z} is nonzero and the
   corresponding weighted receipt-arm difference is nonzero.
   Then SingleHatEstimatorW1 equals sampleWald with weights 1/s_i.
   The single-hat display is the ratio of the two differences of arm means
   using sums with factors 1/s_i, Z_i or (1-Z_i), and Y_i or D_i.
   sampleWald uses the same sums written with Boolean ifs. All four means
   use the identical inverse score. SampleDefined and the arm-mean and
   Wald definitions are expanded here; there is no different fitted score
   hidden in the display.

The docstring describes the receipt formulas, positive-AC nested representation,
interior range, a universal half-compliance misconditioning discrepancy,
the integral correction and cancellation, and a corrected single-hat sample
identity. It expressly assumes usual measurability/integrability and does not
assume a uniform positive lower bound on compliance for the integral assertion.

Junk conventions: mu is a probability measure, so toReal of infinity never
occurs. Point-profile claims are explicitly guarded by P(X=x)>0; independence
and assignment positivity make their arm intersections positive. The nested
parameter b is used only under a>0, making its AC-event denominator positive.
At other inputs the same definitions would use division-by-zero=0, but these
claims do not rely on that extension. In the integral assertion c is positive
almost surely, allowing cancellation nu-almost everywhere; values at exceptional
profiles may use zero reciprocals without affecting integrals. Reciprocal and
weighted-outcome integrability are explicit. Bochner integrals would be zero on
nonintegrable functions, but the asserted and supplied integrability rules this
out for the quantities being interpreted. Conditional expectation would be zero
if its conditioning sigma algebra were not a subalgebra, the measure were not
sigma finite on it, or its input were nonintegrable. Coordinate measurability,
the probability measure and integrable potentials prevent these failure cases
for the indicators and indicator*tau in ScoreVersions. Measure.map has a default
on nonmeasurable maps, prevented by coordinate measurability. The sample claim
requires nonzero arm and first-stage denominators, and so has no undefined
ratios. n=0 is formally permitted but cannot meet SampleDefined. There are no
logs, roots, real powers, truncated subtractions, infima, limsups, or defaults of
partial functions in this theorem.
