# Blind reading (saved before opening claims.json or record.json)

This reading uses only the Challenge declarations, their complete closure in
closure.json, the corresponding Defs sources, and Mathlib conventions. All
line-zero compiler-generated closure declarations were also inspected with
scratch/BlindClosure.lean. They provide numeric-literal instances, finite-index
nonzero instances, the nonemptiness proof for balanced assignments, a sum/product
pattern matcher, an outer-measure instance, and a scalar-tower instance; none adds
a mathematical hypothesis.

## SAP.P029b.T19

The statement is the following conjunction, with no external hypotheses.

1. There exists a probability measure Lambda on the Borel real line, whose CDF
   at every real t is 1/(1+exp(-t/3)), such that, for every natural k and then
   every Boolean w, the simulation law described below has all the listed
   properties. The same Lambda works for every k and w.
2. The integral of the identity under the real Gaussian with mean 0 and variance
   9 is 0, and the square root of its variance is 3. Mathlib variance here is
   the real conversion of the extended integral of squared deviation from the
   Bochner mean.
3. All the threshold/type, implicit-equation, and outcome identities below hold.
4. The four real functions defining the two indices, untreated outcome, and
   treatment effect are measurable, for every k, w, and unit i in Fin(2*k).
5. For every k, w, sample point, and unit, the treatment and outcome identities
   below hold pointwise, including sample points outside the law's support.

The coordinate index set is Fin(8) disjoint union (Fin(2*k) times Fin(6)). A
sample point consists of a real value at each coordinate and a finite subset S
of Fin(2*k). The law is a finite product of the following coordinate laws,
times an independent law of S:

- The eight first coordinates are independent normalized Lebesgue laws on
  (-2,2), shared across units.
- For each unit, coordinates 0,1,2 are independent normalized Lebesgue laws on
  (-1,1); coordinates 3,4 are independent Gaussian(0,9) if w=false and independent
  Lambda draws if w=true; coordinate 5 is Gaussian(0,1).
- S is the uniform PMF on the k-element subsets of Fin(2*k), converted to a
  measure. In particular it has cardinality k almost surely; each such subset
  has mass 1/choose(2*k,k), and other subsets have mass zero. Every unit has
  membership probability 1/2. All real coordinates are mutually independent,
  each has exactly its specified pushforward law, and S is independent of the
  entire real array. The full product is asserted to be a probability measure.

Assignment z_i is the Boolean deciding membership in S. Write the shared
coefficients as a,b,c,d,e,f,g,h and the unit coordinates as x1,x2,x3,u,v,eta.
For w=false the indices are

    I_AC = 2+a+b*x1+c*x2+d*x3+u,
    I_A  = -2+e+f*x1+g*x2+h*x3+v.

For w=true they are

    I_AC = 2+a+(1+b*x1)*(1+c*x2)+d*x3^3/3+u,
    I_A  = -2+e+(1+f*x1)*(1+g*x2)+h*x3^3/3+v.

For arbitrary real indices s,t (not just these random indices), put

    AC=1_{s>0}, A=1_{t>0}*AC, C=AC-A,
    D(z)=C*(if z then 1 else 0)+A.

For every s,t and Boolean z, the statement asserts AC,A,C,D(z) are each 0 or 1;
A<=AC; A*C=0; D(true)-D(false)=C; C>=0; D(false)=1 iff A=1;
(D(false)=0 and D(true)=1) iff C=1; and both D values are zero iff AC=0.
It also asserts both D values are one iff A=1, and C=1 implies D(true)=1.

Separately, there is no real D with D=D*1+1; both 0 and 1 solve D=D*1+0;
and for every real D,A, D=D*0+A iff D=A. These are numerical tests of an
implicit equation, not a universal characterization of all its solutions.
For all real Y0,tau,D, Y0+tau*D=Y0+D*((Y0+tau)-Y0).

The random recipe defines Y0=5*AC+eta and
tau=5*(1+x1+x2+x3+(if w then x1*x2 else 0)). Pointwise, d=C*bit(z_i)+A
equals D(z_i), and Y0+tau*d=Y0+d*((Y0+tau)-Y0).

Junk-value audit: normalized restriction of Lebesgue measure is used only on
intervals of radii 1 and 2, which have strictly positive finite measure. The
uniform PMF has a proved nonempty support, including k=0, where its support is
the singleton empty subset. choose(2*k,k) is positive, so its extended-real
inverse has no zero/infinity anomaly. At k=0 assertions over unit indices are
empty, but the coefficient array, law and assignment still exist; assertions
also cover positive k. Natural multiplications are exact and do not overflow;
Fin literals use valid nonzero index types. C=AC-A is subtraction in the reals,
not truncated subtraction. Every divisor is the nonzero number 3, or the
strictly positive 1+exp(-t/3), or a positive measure/cardinality. The Gaussian
mean and variance are finite; the Bochner integral's nonintegrable-to-zero and
ENNReal.toReal(infinity)=0 conventions cannot apply to these Gaussians. The
square root has a nonnegative variance argument (actually 9). Threshold zero
is deliberately assigned value 0. There is no rpow, infimum, supremum,
limsup/liminf, defaulted partial function, or sample mean over an empty set.

## SAP.P029b.T20

The statement is a conjunction of a negated universal implication and a
separate completely specified finite example.

Common definitions, fully expanded: a potential unit consists of a covariate
x in X, two Boolean potential receipts d0,d1, and two real potential outcomes
y0,y1. Its effect is y1-y0. A complier has d0=false,d1=true; a defier has
d0=true,d1=false. Receipt under assignment z is d1 when z=true and d0 otherwise.
For a measure mu, write P(B)=(mu(B)).toReal and
E[V|B]=(integral over B of V with respect to mu)/P(B). A profile score is
P(complier and x=x0)/P(x=x0). These are event-conditioned ratios, not a
regular conditional distribution at arbitrary non-atomic profiles.

The first conjunct negates this universal statement: for every pair of
small types Omega,X with measurable spaces, with measurable singletons in X,
every probability measure mu on Omega, every function U from Omega to potential
units in X and Boolean assignment function Z, if all the following IV conditions
hold, then for every x0, positive P(x=x0), positive profile score, and the two
typical equalities imply the latent equality:

- x,d0,d1,y0,y1,Z are measurable; y0 and y1 are integrable;
- Z is independent, in Mathlib's random-variable independence sense, of the
  joint tuple (x,d0,d1,y0,y1);
- 0<P(Z=true)<1;
- the defier event has measure zero;
- E[bit(receipt(Z))|Z=true]-E[bit(receipt(Z))|Z=false] is nonzero.

The typical equalities say, separately for j=0 and j=1,

    E[yj | receipt(Z)=true, x=x0]
      = E[yj | receipt(Z)=false, x=x0].

The latent equality is

    E[y1-y0 | x=x0] = E[y1-y0 | complier, x=x0].

Thus the first conjunct asserts existence of some valid IV probability model
and positive-mass, positive-score profile satisfying both typical equalities
and violating the latent equality. It does not specify its witness in the
statement.

The second conjunct fixes the six atoms (i,z) in Fin(3) times Bool, with
probabilities p_i/2, where p_0=1/2 and p_1=p_2=1/4. All have covariate ().
Their potential-unit table, repeated at both z values, is:

| i | d0 | d1 | y0 | y1 | tau |
|---|---|---|---|---|---|
| 0 | false | true | 0 | 1 | 1 |
| 1 | true | true | 1 | 2 | 1 |
| 2 | false | false | 0 | 1 | 1 |

Finite probability is a sum of nonnegative atom masses totaling 1; expectation
is sum p_i*v_i; event probability is sum of masses in the event; conditional
expectation divides the restricted expectation by event probability. Finite
independence means the joint mass of every pair of values equals the product
of marginal masses. The asserted finite IV conditions are valid law,
0<P(Z=true)<1, independence of the joint potential-unit tuple from Z, no
defiers, and nonzero difference of receipt-arm means. For every positive-mass
covariate value, the finite latent equality is asserted. The received and
nonreceived groups' y0 means are respectively 1/2 and 0, and their y1 means
are respectively 3/2 and 1. No universal converse implication is asserted.

Junk-value audit: real division by zero yields zero in fCE, mCE and scoreAt.
The first conjunct explicitly requires positive profile mass and score; under
randomization and positive assignment probabilities these also give positive
received/nonreceived group masses at that profile. Its outcomes are integrable
and the probability measure is finite, so neither nonintegrable Bochner zeros
nor toReal(infinity) can matter. The displayed finite law has both receipt
groups of probability 1/2, and complier probability 1/2. Finite latent
ignorability is tested only at positive profile mass. Empty underlying types
cannot support the asserted probability laws, and the concrete index type has
six atoms. No log, sqrt, rpow, truncated subtraction, infimum/supremum,
limsup/liminf or partial-function defaults occur.

## SAP.P029b.T21

This is three conjuncts: a universal constant-effect result, the negation of
one universal marginal-independence result, and the negation of one universal
profile-conditional independence result. Potential units, event probabilities,
event conditional means, scores, and IV conditions mean exactly the expanded
definitions given in the T20 section. Outcome under assignment z is y1 if
receipt(z)=true and y0 otherwise.

The first conjunct quantifies, in order, arbitrary types Omega,X with measurable
spaces and measurable singletons of X; a probability measure mu; U,Z; a proof
of the IV conditions; functions c,m:X->R; their version conditions; a real
epsilon>0; the almost sure bound epsilon<c(x)<=1; a real tau; and the
pointwise condition y1(omega)-y0(omega)=tau for every omega.

The version conditions require c,m measurable and, almost surely,

    c(x)=E[1_complier | sigma(x)],
    c(x)*m(x)=E[1_complier*(y1-y0) | sigma(x)],

where sigma(x) is the pullback of X's measurable space by the covariate
function, and these are Mathlib conditional expectations. The conclusion is:

- For every x0, if its event has positive probability and its ratio-defined
  score is positive, then E[y1-y0|x=x0]=tau and
  E[y1-y0|complier,x=x0]=tau.
- Almost surely m(x)=E[y1-y0|sigma(x)].
- The unweighted population Wald ratio and the ratio with weights 1/c(x)
  both equal tau.

Here for any w,V and Boolean z the weighted arm mean is

    A(w,V,z)=E[w*V|Z=z]/E[w|Z=z],

and the population Wald ratio is

    (A(w,outcome(Z),true)-A(w,outcome(Z),false)) /
    (A(w,bit(receipt(Z)),true)-A(w,bit(receipt(Z)),false)).

The second conjunct negates the following statement: for every pair of small
types Omega,X, with X finite and with the measurable structures above, every
probability mu,U,Z satisfying IV, if every positive-mass profile has positive
ratio-defined score, and effect y1-y0 is independent of the Boolean indicator
of being a complier, then all three of the following hold together:

1. Every positive-mass profile satisfies the latent equality.
2. The unweighted Wald ratio equals the integral of y1-y0.
3. The 1/score(x)-weighted Wald ratio equals that same integral.

It asserts existence of failure of at least one of these three conclusions,
not necessarily failure of each, and its independence variable distinguishes
compliers from their complement, rather than all three compliance types.

The third conjunct negates the analogous statement, replacing the marginal
independence condition by the following: at every positive-mass profile x0,
effect is independent of the pair (d0,d1) under the normalized restricted
measure P(x=x0)^(-1) times mu restricted to {x=x0}. The same three conclusions
remain conjoined. Consequently this negation alone does not assert that
conditional independence fails to imply the latent equality; failure of the
unweighted Wald/ATE equality suffices. Neither negated universal supplies its
witness in the statement. There are no sample convergence assertions.

Junk-value audit: all measures in use are probability measures or normalized
restrictions to positive-mass measurable events. ENNReal.ofReal is applied to
the inverse of strictly positive finite event probability. Thus it truncates
no negative numbers, and toReal never sees infinity. IV measurability makes
sigma(x) a sub-sigma-algebra; its trimmed probability measure is sigma-finite.
The indicated variables are integrable. The zero defaults of conditional
expectation outside these conditions therefore do not supply the conclusion.
Profile means are asserted only when both relevant profile masses are positive.
In the first conjunct inverse weights are bounded by the positive epsilon
condition; the IV first stage, and its weighted version under these conditions,
are nonzero. In the negated statements X is finite and all positive-mass
profiles have positive scores, so a positive minimum exists on the support;
the means and Wald denominators are meaningful. Zero-mass profiles have score
zero by real division-by-zero, but have zero law mass and are excluded from
pointwise assertions. No log, sqrt, rpow, truncated subtraction, extrema,
limsup/liminf or partial defaults occur. A probability law rules out an empty
sample space or empty covariate type for its U function.

## SAP.P029b.T22

For every array t:Fin(2500)->R, the empirical RMSE with benchmark array constantly
5 equals sqrt((sum over r in Fin(2500) of (t(r)-5)^2)/2500).
The only SAP definition is empiricalRMSE for arbitrary natural R and arrays
t,b:Fin(R)->R: sqrt((sum (t(r)-b(r))^2)/(R cast to R)). The theorem is the
specialization of this definition to R=2500 and b=5, so it follows by
definitional equality. There are no hypotheses on t, no sampling law or
estimator, no assertion that any actual effect equals 5, and no empirical
performance bound or numerical result.

Junk-value audit: the general definition gives zero when R=0 (empty sum and
real division by zero), but this theorem uses the fixed positive R=2500.
Every square is nonnegative, so the sqrt argument is nonnegative; Real.sqrt's
value 0 on negative arguments is irrelevant. The Fin index is nonempty, its
natural-to-real cast is exact, and there are no integrals, infinity conversions,
logs, rpow, truncated subtraction, extrema, limsup/liminf or defaults.

## SAP.P029b.T23

The parameter type consists of functions q:Bool times Bool->R satisfying, for
each Boolean profile x, 0<q(x,false)<q(x,true)<1. The observation type is
Bool times (Bool times Fin(4)): profile x, assignment z, replicate index j.
Let s(x,z) be 1 for z=false, 2 for (x=false,z=true), and 3 for
(x=true,z=true). Receipt D(x,z,j) is true exactly when j<s(x,z).
Thus each of the four cells has four observations, with success counts
1,2,1,3 in the order (false,false),(false,true),(true,false),(true,true).

The likelihood contribution is

    L_q(i)=q(x,z)^(if D then 1 else 0)
             *(1-q(x,z))^(if D then 0 else 1),

so it is q(x,z) for successes and 1-q(x,z) for failures. The observation
weight is 9 for a success and 1 for a failure. Define real-valued objectives

    Q_pkg(q)=-sum_i log(L_q(i)*w_i),
    Q_weighted(q)=-sum_i w_i*log(L_q(i)).

A minimizer means a global minimizer over the entire strict-interior ordered
parameter type: Q(q)<=Q(t) for every t in that type.

The statement asserts that there exists q in this parameter type such that
its underlying function is q(false,false)=q(true,false)=1/4,
q(false,true)=1/2, q(true,true)=3/4; that q globally minimizes Q_pkg; and that q
does not globally minimize Q_weighted. In particular the non-minimizer claim
requires some admissible strict-interior ordered competitor with a smaller
weighted objective. The statement is not about numerical optimization,
standard errors, bootstrap behavior, covariate-specific score estimation,
or the final treatment-effect estimator.

Junk-value audit: every likelihood factor is strictly positive because all
parameters lie strictly between 0 and 1; all weights are positive. Thus both
logs use the ordinary positive-real logarithm. Mathlib's extensions log(0)=0
and log(negative)=log(abs(negative)) cannot contribute. The exponents are
natural 0 or 1, with no 0^0 at admissible parameters; no subtraction is
truncated. The observation type has 16 elements and is nonempty. The
existential parameter's strict inequalities hold for its four displayed
values; the type's openness does not itself prove existence of a minimizer,
which is explicitly asserted here. There is no division by a variable, no
Bochner integral, sqrt, rpow, infinity conversion, extrema operator,
limsup/liminf, or partial-function default.
