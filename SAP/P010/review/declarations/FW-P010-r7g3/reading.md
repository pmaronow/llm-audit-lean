# Blind reading (saved before opening claims.json or record.json)

Read the five Challenge docstrings and statements, all source definitions in their
closure.json entries, and every listed line-zero auxiliary declaration. The latter
were inspected by compiling scratch/PrintClosure.lean: they supply numeral
AtLeastTwo/NeZero instances and the ENNReal scalar-tower instance, not additional
mathematical assumptions. No canonical claim or architect record was consulted.

Throughout this reading, an event mean means exactly the restricted real Bochner
integral divided by the real value of the event's extended nonnegative measure:
M_mu(f,E) = (integral_E f dmu)/(mu(E)).toReal. A conditional law means exactly
C_mu(f,E) = (mu(E))^(-1) times the pushforward of mu restricted to E by f. These
are the Mathlib operations, including their totalized behavior when their usual
probability interpretation is unavailable. Equality almost everywhere is equality
outside a set of measure zero.

## SAP.P010.T11

Source: Challenge/Part1.lean:54-58; Defs/Part4.lean:64-82;
Defs/Part2.lean:13-29. The docstring describes a counterexample to an
exact-distribution-matching interpretation of weighting guidance, coding
replication membership as one, with an attained logistic fit.

There are no external hypotheses or existentially quantified inputs. Define
two real probability mass vectors on {0,1} by O=(3/4,1/4) and R=(1/4,3/4).
For each cell x, p_x = ((1/2)R_x)/((1/2)R_x+(1-1/2)O_x).
For any real p, its odds are p/(1-p) and reciprocal odds are (1-p)/p.
For real vectors f,w on a finite set, the normalized weighted mass at x is
f_x w_x divided by the sum of f_u w_u over that set. Define
s(t)=exp(t)/(1+exp(t)). The conjunction asserted is:

1. s(log(1/3))=1/4 and s(log(1/3)+log(9))=3/4.
2. For every real q0 and then every real q1, if 0<q0<1 and 0<q1<1, the
   log likelihood L=log(q0)+3log(1-q0)+3log(q1)+log(1-q1) is at most
   L*=log(1/4)+3log(3/4)+3log(3/4)+log(1/4), and L=L* if and only if
   q0=1/4 and q1=3/4. This is the likelihood for cell counts (R,O)=(1,3)
   and (3,1). The displayed intercept and slope attain its maximum.
3. For every x in {0,1}, O_x>0, R_x>0 and 0<p_x<1; p_0=1/4 and p_1=3/4.
4. The two odds are 1/3 and 3. The unnormalized replication weighted masses
   are 1/12 and 9/4, and their sum is 7/3.
5. The normalized printed-odds mass at cell 1 is 27/28 and differs from O_1.
6. For every cell, normalizing R times reciprocal odds gives O exactly.

Junk conventions: real division uses 1/0=0, so general propensity, odds,
reciprocal odds, and normalization definitions could give totalized values.
Here the mixture denominator is 1/2, both p and 1-p are positive, printed
normalization mass is 7/3, and reciprocal normalization mass is 1. No zero
denominator occurs. Real.log is totalized (log(0)=0 and negative inputs use
the real logarithm of their absolute value), but all displayed inputs and
all likelihood inputs under the hypotheses are strictly positive. exp is
positive, so the sigmoid denominator is positive for every real input.
The sums have exactly two terms, and Fin numerals denote the intended cells;
no empty index, truncated subtraction, partial lookup, limit, or square root
is involved. Numerals in the vectors and fractions have real type.

## SAP.P010.T12

Source: Challenge/Part1.lean:60-72; Defs/WholeW1.lean:14-77;
Defs/Part2.lean:13-17,31-33. The docstring describes true-propensity Bayes
identities, transport by original-membership odds, constant cancellation,
printed-odds square-ratio weighting, and an infinite-mass alternative.

Quantifiers, in order: every type Omega (in the declaration's universe),
measurable-space structure on Omega, measure nu on it, real pi, and two
real functions R,O on Omega. Hypotheses, in order, are 0<pi, pi<1,
R>0 nu-almost everywhere, O>0 nu-almost everywhere, Bochner integrability
of R and O, integral R dnu=1, and integral O dnu=1.

At a point x put p(x)=pi R(x)/(pi R(x)+(1-pi)O(x)),
w(x)=p(x)/(1-p(x)), and v(x)=(1-p(x))/p(x).
Let Z=integral^+ ofReal(R(x)^2/O(x)) dnu and
W=integral^+ ofReal(R(x)w(x)) dnu, both in [0,infinity].
Here ofReal(t)=max(t,0) represented as an extended nonnegative real.
For any weight g, N(g)(x)=R(x)g(x)/(integral Rg dnu).
All the following conclusions are conjoined, in order:

1. Almost everywhere, 0<p<1, w=pi/(1-pi) times R/O, and
   O/R=pi/(1-pi) times v.
2. Almost everywhere, (1-p)/(1-(1-p))=v (odds after reversing membership).
3. Rv is integrable; its integral is (1-pi)/pi; and N(v)=O almost everywhere.
4. For every real c>0, N(c v)=O almost everywhere.
5. W=ofReal(pi/(1-pi)) Z, as an extended-real equality.
6. If Z<infinity, R^2/O is integrable; Z>0 and Z.toReal>0;
   0<W<infinity; Rw is integrable; its integral is
   pi/(1-pi) times Z.toReal and is positive;
   N(w)(x)=(R(x)^2/O(x))/Z.toReal almost everywhere; and
   [N(w)=O almost everywhere] if and only if [R=O almost everywhere].
7. If Z=infinity, W=infinity; for every finite nonnegative real c
   (Lean type NNReal), the measure whose density with respect to nu is
   c times ofReal(Rw) is not a probability measure. This includes c=0.

There is no assumption of fitted propensities, of a particular logistic
model, or of a finite covariate set. There is no explicit sigma-finiteness
or standard-Borel assumption in this theorem; its conclusions are integral
and algebraic identities.

Junk conventions: all real divisions are totalized, but pi, 1-pi, the
mixture denominator, R, O, p, and 1-p are positive almost everywhere under
the hypotheses. Null-set exceptional values do not affect the integrals
or almost-everywhere conclusions. A nonintegrable real Bochner integral
is defined as zero, hence the general N is not always a normalization;
here reciprocal-weight integrability and a positive normalization constant
are conclusions, and printed N occurs only in the Z<infinity branch,
where its integrability and positive integral are also conclusions.
ENNReal.toReal(infinity)=0, but Z.toReal is used only under Z<infinity.
In the infinite branch the mass is kept extended, and c=0 yields zero
measure by 0*infinity=0, correctly still not a probability measure.
ofReal discards negative inputs, which can occur here only on a null set.
The empty type or zero measure cannot satisfy the integral-one hypotheses.
No finite-index sum, log, root, nonintegral power, partial function,
supremum, infimum, or limit occurs in this closure.

## SAP.P010.T13

Source: Challenge/Part1.lean:74-76; Defs/Part6.lean:162-178;
Defs/Part3.lean:11-46; Defs/Part5.lean:13-42,61-65,102-103,122-123,138-140.
The docstring calls the printed upper-bound assertion false using a normal
example. No external hypotheses or variable inputs are quantified.

The state space is (Fin 2 -> R) x (Fin 2 -> Bool) x Fin 2 x (Fin 0 -> R),
with its product measurable structure. A state contains potential outcomes
Y_0,Y_1, potential passing indicators S_0,S_1, assigned arm Z, and the
unique empty covariate vector. Observed response is Y_Z; observed passing
is S_Z=true. Let A={S_0=S_1=true}, P={S_Z=true}, E_a={Z=a},
B_a={S_a=true}, and H_a={S_b=true for every b different from a}.

Let G be Mathlib's real Gaussian measure with mean zero and variance one,
and U=(1/2)delta_0+(1/2)delta_1 on Fin 2. For s in {false,true}, push
G product U forward under (y,z) -> ((y,y),(s,s),z,empty vector), obtaining
mu_s. The specific measure mu is (4/5)mu_true+(1/5)mu_false.
This is exactly a standard normal outcome shared by both potential arms,
an independent common Bernoulli(4/5) check, and an independent fair arm.

For a measure on this state space define r_a=mu(P intersect E_a)/mu(E_a)
with both masses converted to real before dividing;
F_a=(mu(P intersect E_a))^(-1) times the pushforward of mu restricted to
P intersect E_a by Y_Z. Let t_a=(sum over b different from a of (1-r_b))/r_a,
and t'_a=(sum over b different from a of mu(S_b=false).toReal)/mu(B_a).toReal.
For a real measure F define the extended left quantile
Q_F(u)=inf {x in EReal : u <= F({y in R : y <= x}).toReal}.
The observable upper endpoint is
M_mu(Y_Z,(P intersect E_a) intersect {Y_Z >= Q_Fa(t_a)}).

The conjunction asserts:

1. mu is a probability measure. For each a, (Y_a,S_a) is independent of Z
   (Mathlib IndepFun), mu(E_a)>0, and r_a>0. Independence here is per arm,
   not an asserted joint-vector independence. Also mu(A)=4/5.
2. The law of Y_Z has zero mass at every real singleton, and every nonempty
   real open interval has positive probability under Y_Z.
3. For every a in Fin 2, r_a=4/5 and F_a=G.
4. t'_0=t_0=1/4.
5. M_mu(Y_0,A)=0 and M_mu(Y_0,H_0 intersect B_0)=0.
6. Put q=(Q_G(3/4)).toReal. Then M_mu(Y_0,{Y_0<=q})
   = -phi(q)/(3/4), this mean is strictly negative, and it is false that
   M_mu(Y_0,A)<=M_mu(Y_0,{Y_0<=q}). Here
   phi(q)=exp(-q^2/2)/sqrt(2*pi) is the standard Gaussian density.
7. The observable upper endpoint for arm 0 is
   phi((Q_G(1/4)).toReal)/(3/4), and is strictly positive.

Junk conventions: event means, pass rates, conditional laws, and ratios
are totalized as above. In this example arm masses are 1/2, passer-arm
masses 2/5, potential-passing and all-passing masses 4/5, and the lower
and upper Gaussian tail probabilities used are 3/4, so every relevant
denominator is positive and finite. All outcome integrals used are finite
Gaussian first moments. ENNReal inverses at 0 or infinity and .toReal at
infinity are therefore harmless here. EReal infimum of an empty set is
top and of a set unbounded below is bottom; EReal.toReal sends either
infinity to zero. Q_G(1/4) and Q_G(3/4) are finite, so this conversion
does not substitute zero for an infinite quantile. The Gaussian variance
parameter is NNReal 1, so neither a degenerate Gaussian nor an invalid
square root is being used. Covariate indexing is intentionally empty,
but arm indexing has two elements; all sums, casts, and Fin numerals
have their ordinary meanings. Real subtractions are not truncated.
There are no rpow, limsup/liminf, or partial lookup operations. Listed
auxiliary declarations from other source definitions merely reuse proofs
needed to elaborate these concrete numerals.

## SAP.P010.T14

Source: Challenge/Part1.lean:78-80; Defs/Part6.lean:180-198;
Defs/Part3.lean:11-17,22,26,28-33; Defs/Part5.lean:13-15,23-24,28,61-71.
The docstring describes upper-tail maximization, monotonicity in the
discarded share, and a corrected potential upper bound.

Quantifiers, in order: arbitrary natural K,d; a measure mu on
(Fin K -> R) x (Fin K -> Bool) x Fin K x (Fin d -> R); a proof that it is
a probability measure; a chosen a in Fin K; positive mass of
A={all potential indicators S_b=true}; absence of atoms in
F=(mu(B_a))^(-1) times (mu restricted to B_a) pushed forward by Y_a,
where B_a={S_a=true}; and integrability of Y_a under mu restricted to B_a.
There is no random-assignment hypothesis in this statement.
Let H_a={all S_b=true for b different from a} and
t=(sum over b different from a of mu(S_b=false).toReal)/mu(B_a).toReal.
Let Q_F(u)=inf {x in EReal : u<=F({y in R:y<=x}).toReal}, and
U_F(u)=(integral over {y:Q_F(u)<=y} of y dF) /
F({y:Q_F(u)<=y}).toReal.

The following four assertions are conjoined:

1. For every real p with 0<=p<1:
   (a) For every measure gamma on R x Bool, if gamma is a probability
   measure, its first-coordinate pushforward is F, and
   gamma({(y,s):s=false}).toReal=p, then
   (integral_{s=true} y dgamma)/gamma({s=true}).toReal <= U_F(p).
   (b) Define gamma as F pushed forward under
   y -> (y, the Boolean truth value of Q_F(p)<=y). Then gamma satisfies
   those three conditions, and its mean given s=true equals U_F(p).
   This includes randomized selection via arbitrary gamma in (a).
2. For every real p and then real q, if 0<=p<=q<1, U_F(p)<=U_F(q).
3. mu((complement H_a) intersect B_a).toReal/mu(B_a).toReal <= t.
4. If t<1, M_mu(Y_a,A)<=U_F(t).

Junk conventions: a in Fin K forces K>0; d=0 is harmless. A subset B_a
has positive mass, so F really is a probability law with integrable
identity function. Every conditioning denominator is positive and finite:
the selected gamma mass is 1-p, and the atomless F upper-tail mass is
1-p. The t denominator is positive, and t>=0. In assertion 4, t<1
therefore places t in the valid probability range. At p=0 the extended
quantile is bottom, since every CDF value is at least zero; the selected
event is the whole line and the denominator is 1. This is intentional
and does not pass through EReal.toReal. At 0<p<1 the quantile is finite;
atomlessness ensures the threshold includes no positive tie mass.
General empty-set/unbounded infimum conventions of EReal are therefore
safe, as are totalized division and Bochner integration. The finite sum
is empty when K=1, giving t=0 and H_a=the whole state space; all claims
still have their ordinary meanings. No Nat subtraction, improper real
log/root/power, partial function, or limsup/liminf is used.

## SAP.P010.T15

Source: Challenge/Part1.lean:82-84; Defs/Part6.lean:200-211;
Defs/Part3.lean:11-46; Defs/Part5.lean:13-24,28,40-42,61-71.
The docstring describes equality of potential and observed passer laws
and trimming shares, and a corrected observable upper bound for ratio<1.

Quantifiers, in order: natural K,d; a measure mu on
(Fin K -> R) x (Fin K -> Bool) x Fin K x (Fin d -> R); a proof of the
population assumptions; an arm a in Fin K; positive mass of
A={all S_b=true}; zero mass at every singleton for the pushforward law
of observed response Y_Z; integrability of Y_Z on P intersect E_a,
where P={S_Z=true} and E_a={Z=a}.
The population assumptions are precisely: mu is a probability measure,
for every b the pair (Y_b,S_b) is independent of Z, every mu(E_b)>0,
and every r_b=mu(P intersect E_b).toReal/mu(E_b).toReal is positive.

Write B_b={S_b=true}, H_a={all S_b=true for b different from a},
C=(mu(B_a))^(-1) times the pushforward of mu restricted to B_a by Y_a,
F=(mu(P intersect E_a))^(-1) times the pushforward of mu restricted to
P intersect E_a by Y_Z,
t'=(sum_{b different from a} mu(S_b=false).toReal)/mu(B_a).toReal,
t=(sum_{b different from a}(1-r_b))/r_a,
Q_G(u)=inf {x in EReal : u<=G({y in R:y<=x}).toReal}, and
U_G(u)=(integral_{y>=Q_G(u)} y dG)/G({y>=Q_G(u)}).toReal.
Let e=M_mu(Y_Z,(P intersect E_a) intersect {Y_Z>=Q_F(t)}).

The conclusion is C=F as measures; for every b, mu(B_b).toReal=r_b;
t'=t; and, if t<1, the following three assertions hold jointly:
U_C(t)=e, M_mu(Y_a,A)=M_mu(Y_a,H_a intersect B_a), and M_mu(Y_a,A)<=e.
There is no assertion here about the t>=1 branch.

Junk conventions: a forces K>0, but d may be zero. All event masses
converted to real are finite, and arm and passer-arm masses are positive.
Independence and positive observed passing give mu(B_b)>0. In particular
C and F are genuine probability measures and both t ratios have positive
denominators. The assumed restricted integrability transfers to the
potential passer law by independence and observed/potential agreement
in the assigned arm; it then restricts to the positive-mass event A.
Atomlessness of the overall observed-response law implies atomlessness
of its positive-mass restricted passer law. Thus, when 0<=t<1, the tail
mass is 1-t>0, and all the displayed means are ordinary finite means.
At t=0 the extended quantile is bottom and the tail is the whole line,
without an EReal.toReal conversion. For interior t it is finite. General
division-by-zero, ENNReal.toReal(infinity), inverse-at-zero, nonintegrable
Bochner-integral, and EReal empty-infimum conventions do not determine
these conclusions. K=1 gives empty sums equal to zero and is consistent
with the formulas. All subtraction is real, all index casts are exact,
and there are no logarithms, roots, rpow, limits, or default partial values.

## Local Mathlib convention addendum

After the initial blind reading was saved, validation against the local Mathlib
source identified one more totalization to record. Measure.map (Map.lean:98-110)
uses an arbitrary Dirac measure for a non-almost-everywhere-measurable map with
nonzero input measure, and zero for zero input measure. Its internal map-linear
operation instead uses zero for a nonmeasurable function. Every coordinate,
finite-vector construction, Gaussian population map, and quantile-threshold map
used in T13--T15 is measurable, so these defaults do not affect any of the five
readings. ConditionalLaw additionally has extended inverse conventions
0^(-1)=infinity and infinity^(-1)=0; at a measurable zero-mass conditioning event
its restricted measure is zero and the resulting conditional law is zero.
All conditioning events used by the conclusions above have positive finite mass.
This addendum changes no statement interpretation or claim-stage conclusion.
