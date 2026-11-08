# Blind reading

This file records step 1 before opening `claims.json` or `record.json`.
All entries of `closure.json` were read in the Lean sources, including the
structure-generated declarations; the generated `_proof_*` declarations were
also inspected with `#print` in `scratch/BlindPrint.lean`. They provide ordinary
measure/probability instances, numeral denominator proofs and the proof that
1/2 belongs to [0,1], and do not add statistical hypotheses.

## SAP.P047.T1

### Objects, definitions, quantifiers and conclusions

A unit is `(x,a,(y0,y1))` in the product measurable space
`U = R × Bool × (R × R)` (real factors carry their Borel sigma algebras).
`covariate` is x, `potential false` is y0, `potential true` is y1,
and `arm b` is the real indicator of a=b. The observed outcome is
`1_{a=true} y1 + 1_{a=false} y0`, so consistency is built into observation.
The conditioning sigma algebra is the pullback of the real Borel sigma
algebra along x, i.e. sigma(X).

A `CausalLaw` L contains a probability measure P on U, a Borel measurable
real function e, and the following hypothesis (`Ignorable`): for every
b in Bool and every Borel real function f, **if** f(Yb) is P-integrable,
then, P-almost surely,

`E_P[1_{A=b} f(Yb) | X] = p_b(X) E_P[f(Yb) | X]`,

where p_true(x)=e(x) and p_false(x)=1-e(x). Taking f=1 calibrates e
as P(A=true | X); taking bounded tests expresses armwise conditional
independence of the corresponding potential outcome and treatment.
The constructor `CausalLaw.mk` requires exactly these five fields;
`measure`, `probability`, `propensity` are their projections.

For every natural n, the sample distribution P^N is Mathlib's countable
product `Measure.infinitePi (fun _ : Nat => P)`. Its coordinates are iid.
Only coordinates 0,...,n-1 enter either estimator. Put

* `Z = 1_{A=true} Yobs/e(X) - 1_{A=false} Yobs/(1-e(X))` (`score`);
* `tau = integral (Y1-Y0) dP` (`ate`);
* `T_n = (sum_{i=0}^{n-1} Z_i)/(n : R)` (`estimator`);
* `h_n = (B/eps) sqrt(2 log(2/alpha)/(n : R))` (`halfWidth`);
* `I_n = [T_n-h_n,T_n+h_n]` (`confidenceInterval`, a closed real interval);
* `width_n = (T_n+h_n)-(T_n-h_n)` (`intervalWidth`).

The statement is a conjunction of two universally quantified assertions.
In the first, **for every** L, real B and eps, **if** `BoundedOverlap` holds,
meaning

`B>0`, `eps>0`, `eps<=1/2`, `|Yb|<=B` P-a.s. for each b,
and `eps<=e(X)<=1-eps` P-a.s.,

then all of the following hold:

1. `E_P[Z | X] = E_P[Y1-Y0 | X]` P-a.s.
2. `integral Z dP = tau`.
3. `|Z| <= B/eps` P-a.s.
4. **For every** natural n with n>=1: `integral T_n dP^N = tau`;
   **for every** real t>=0,
   `P^N(t <= |T_n-tau|) <= 2 exp(-n t^2 eps^2/(2 B^2))`;
   and **for every** real alpha with 0<alpha<1,
   `P^N(tau in I_n)>=1-alpha`, `h_n>=0`,
   **for every** sequence s of units,
   `width_n(s)=2h_n=(2B/eps)sqrt(2 log(2/alpha))/sqrt(n)`, and
   `sqrt(n) (2h_n)=(2B/eps)sqrt(2 log(2/alpha))`.

The second assertion independently quantifies **every** L and real eps.
Its hypothesis (`TreatedMeanModel`) is eps>0, `0<=Y1<=1` P-a.s., and
`e(X)>=eps` P-a.s. L still has all CausalLaw fields, including armwise
ignorability for **both** potential outcomes; the control outcome is not
bounded and no positive lower bound on 1-e is imposed.
Put `Z1=1_{A=true}Yobs/e(X)`, `mu1=integral Y1 dP`,
`T1_n=(sum_{i<n} Z1_i)/n`, and
`h1_n=(1/eps)sqrt(log(2/alpha)/(2n))`.
The conclusions are `Z1 in [0,1/eps]` P-a.s., and **for every** n>=1:

* `integral T1_n dP^N=mu1`;
* **for every** t>=0,
  `P^N(t<=|T1_n-mu1|)<=2 exp(-2n eps^2 t^2)`;
* **for every** alpha in (0,1),
  `P^N(mu1 in [T1_n-h1_n,T1_n+h1_n])>=1-alpha`.

This branch does not explicitly assert conditional or unconditional means
of the individual contribution Z1, or a one-mean width identity.
The theorem docstring advertises these finite-sample conclusions and the
one-mean component under weaker one-arm conditions.

### Totalization and junk-value audit

Real division is total and 1/0=0. Scores can consequently have artificial
values at e=0 or e=1, but the first branch excludes these P-a.s.; the
treated branch excludes e=0 P-a.s. The possible control denominator e=1
does not occur in Z1. Sample sequences with exceptional coordinates still
exist, but have probability zero. The everywhere width identities are
algebraic in the center and remain meaningful on such sequences.

An empty sum at n=0 is zero and the estimators and half widths use total
division by zero there; all finite-sample conclusions require n>=1.
All n in denominators and square roots are casts to R, not integer
division or truncated natural subtraction. All subtractions here are real.
`Real.log 0=0`, and the real logarithm is defined on negative arguments
using absolute value; `Real.sqrt` is zero for nonpositive inputs.
Here alpha in (0,1) gives 2/alpha>2, log(2/alpha)>0, and n>=1 makes the
displayed square-root radicands positive. B and eps denominators are
strictly positive. No real-power (`rpow`) convention is used.

Bochner integrals are zero for nonintegrable/non-a.e.-strongly-measurable
functions. Here bounded potential outcomes, positivity of the relevant
denominators, and coordinate measurability imply the required
integrability. In the one-mean branch the unbounded Y0 need not be
integrable: multiplication by its inactive treatment indicator is
algebraically zero where it could otherwise contaminate Z1.
Conditional expectation is zero when the conditioning sigma algebra is
not a sub-sigma-algebra, its trimmed measure is not sigma-finite, or its
argument is not integrable. None applies: sigma(X) is a sub-sigma-algebra,
P is finite, the tests in Ignorable explicitly require integrability,
indicators are bounded, and the displayed first-branch arguments are bounded.
`Measure.real A = (P A).toReal`, with infinity sent to zero, is harmless
because every measure used for probabilities is a probability measure.
There is no supremum, infimum, limsup, liminf, partial-function default or
empty quantified base type in this statement.

## SAP.P047.T2

### Objects, definitions, quantifiers and conclusions

Here again U consists of real x, Boolean a and real potential outcomes
y0,y1, with the product Borel sigma algebra. X=x, Yb=yb, the real arm
indicator is 1_{A=b}, and Yobs=1_{A=true}Y1+1_{A=false}Y0.
A CausalLaw L consists of a probability P, a Borel real e, and, for each
Boolean b and every Borel f for which f(Yb) is integrable,
`E[1_{A=b}f(Yb)|sigma(X)] = p_b(X) E[f(Yb)|sigma(X)]` P-a.s., with
p_true=e and p_false=1-e. The conditioning sigma algebra is the pullback
of the Borel sigma algebra by X. The generated constructor and projections
have their literal structure meanings. `BoundedOverlap L B eps` means
B>0, eps>0, eps<=1/2, both |Yb|<=B a.s., and eps<=e(X)<=1-eps a.s.

The definitions used in this statement are
`Z=1_{A=true}Yobs/e(X)-1_{A=false}Yobs/(1-e(X))`,
`tau=integral(Y1-Y0)dP`, iid sample law P^N, and
`T_n=(sum_{i<n}Z_i)/(n:R)`.
Define the real number (`knownRootRisk`)

`r_{B,eps}(K) = sup ({0} union
 { P^N(K < sqrt(n)|T_n-tau|) :
       L is a CausalLaw with BoundedOverlap L B eps, n>=1 })`.

For **every** real B>0 and **every** real eps>0 with eps<=1/2,
the theorem asserts **both**:

1. `r_{B,eps}(K) -> 0` as the real K tends to +infinity. The supremum
   is simultaneously over every admissible population and every positive
   sample size, with the same B and eps.
2. **For every** admissible L, all three assertions hold:
   * **For every** natural n>=1 and **every** real K>=0,
     `P^N(K <= sqrt(n)|T_n-tau|) <= 2 exp(-K^2 eps^2/(2 B^2))`.
   * `Var_P(Z) <= B^2/eps^2`.
   * The random variables `sqrt(n)(T_n-tau)` under P^N converge in
     distribution as natural n tends to infinity to the identity random
     variable on R under `gaussianReal 0 (Var_P(Z)).toNNReal`.

Variance is the real value of the nonnegative extended integral
`integral ||Z-integral Z dP||^2 dP`. The Gaussian with variance v>0 is
Lebesgue measure with the usual centered normal density, and for v=0 it
is the Dirac probability at zero. Mathlib convergence in distribution
requires a.e. measurability and weak convergence of pushforward probability
measures. Equivalently here, expectations of bounded continuous real test
functions converge to their expectations under that Gaussian.
The normal limit is for each fixed L; it does not assert a uniform normal
approximation over laws. The docstring describes this distinction.

### Totalization and junk-value audit

Division by e(X) and 1-e(X) is total, but BoundedOverlap makes both
denominators positive almost surely; their exceptional values do not
affect the asserted probabilities or integrals. All finite-n inequalities
use n>=1. In the convergence sequence n=0 is allowed: the empty sum and
division by zero give T_0=0, and sqrt(0)=0, so its normalized value is zero;
this single initial term cannot affect convergence at infinity.

All n casts are to R; no natural-number truncated subtraction is used.
The square root is the ordinary nonnegative root on these nonnegative
casts. The exponential has no restricted domain. No logarithm or rpow
appears. Bochner integral and conditional-expectation zero defaults are
avoided for the same explicit reasons as above: bounded outcomes and score,
measurable coordinates and e, legitimate sigma(X), finite measures, and
integrable test functions. Variance uses `ENNReal.toReal`, which would send
an infinite second moment to zero, but bounded Z guarantees a finite second
moment. `Real.toNNReal` would replace a negative number by zero; the variance
is nonnegative. Zero variance is handled deliberately by a genuine Dirac
Gaussian, not a malformed density.

All event probabilities are in [0,1], so their `toReal` conversions are
finite. The supremum defining r has an inserted zero, making it nonempty,
and is bounded above by one; it is the ordinary supremum and cannot use
Mathlib's default value for an empty or unbounded real set. If the model
were empty, it would deliberately be zero. Admissibility/nonemptiness needs
an independent check; it is not supplied by the definition. There is no
limsup/liminf or partial-function default in T2. U, R and Nat are nonempty.

## SAP.P047.T3

### Objects, definitions, quantifiers and conclusions

U is again R × Bool × (R × R), with X=x, treatment A=a, Y0=y0,
Y1=y1 and observed outcome 1_{A=true}Y1+1_{A=false}Y0. A CausalLaw
has probability P, Borel e, and armwise conditional factorization for
every integrable Borel test f(Yb), conditional on the pullback sigma(X),
as written in the T1 section. All structure constructors and projections
are literal, with no conclusions included in them.

`uniform01` is Lebesgue measure restricted to (0,1]; this is a probability,
equivalent to the continuous uniform law on [0,1]. `JointIgnorable L`
requires, for **each** Boolean b and **every** Borel f:R^2->R with
f(Y0,Y1) integrable,

`E[1_{A=b}f(Y0,Y1)|X] = p_b(X) E[f(Y0,Y1)|X]` P-a.s.

`UnknownModel L` means all four conditions: the pushforward law of X is
uniform01, JointIgnorable L, each Yb belongs to {0,1} a.s., and
1/4<=e(X)<=3/4 a.s. Individual armwise ignorability is inherited from L.
Propensity is not an input to the statistical procedures below.

`fairBool` is the Bernoulli measure assigning mass 1/2 to each Boolean.
`baselineLaw` is the pushforward of the product
`uniform01 × fairBool × fairBool` under
`(x,a,b) -> (x,a,(0,1_{b=true}))`.
Consequently its full law has independent uniform X, fair treatment A,
fair Bernoulli Y1, and Y0=0.

`populationProbability L` retains P as a `ProbabilityMeasure U`, forgetting
the e and ignorability fields. `unknownPopulations` is the set of these
P for L satisfying UnknownModel. For any probability P on U,
`populationEffect P = integral(Y1-Y0)dP`.

For any n, `ObservedUnit = R × Bool × R` and `observedSample n` maps a
sequence of full units to the function on Fin n taking coordinate i to
`(X_i,A_i,Yobs_i)`. The sample law is the iid countable product P^N.
For any measurable seed space R of the stated universe and probability Q
on R, the data-and-seed law is the product P^N × Q. Thus the seed is
independent of the whole sample and has the same law under every P.

For a class M of probabilities and population-dependent event A_P, define

`U_M(A) = sup ({0} union {(P^N×Q)(A_P) : P in M})`,
`L_M(A) = inf ({1} union {(P^N×Q)(A_P) : P in M})`.

These are `modelEventSup` and `modelEventInf`. An estimator E is one
sequence of measurable maps
`E_n : ((Fin n -> ObservedUnit) × R) -> R` (last R means the real line,
not the seed space). In the following formulas write seed space as Rseed
to disambiguate, D_n for observedSample n, and theta(P) for populationEffect.
The derived definitions are:

* `wholeRisk M Q E n eta = U_M({eta <= |E_n(D_n,seed)-theta(P)|})`;
* `wholeStrictRisk ... = U_M({eta < |E_n(D_n,seed)-theta(P)|})`;
* for measurable extended-real endpoints lo_n,hi_n,
  `wholeCoverage ... = L_M({lo_n(D_n,seed)<=theta(P)<=hi_n(D_n,seed)})`;
* `wholeWidthRisk ... = U_M({lo_n(D_n,seed)+(1/6)<hi_n(D_n,seed)})`;
* `widthProb Q lo hi n` is the same width-event probability under the
  **single** law baselineLaw^N × Q, with no supremum.

The theorem first asserts **existence** of a CausalLaw S with
S.measure=baselineLaw, S.propensity identically 1/2, UnknownModel S,
and `integral(Y1-Y0)dS=1/2`.

It then quantifies in this order: **every** set M of probability measures
on U; a hypothesis unknownPopulations subset M; a hypothesis that
Y1-Y0 is integrable for **every** P in M; **every** measurable seed space
Rseed and probability Q on it. The conclusion is a conjunction:

1. **For every** estimator sequence E with each E_n measurable,
   **for every** natural n>=1,
   `wholeRisk M Q E n (1/12)>=1/2`; and **there exists** a real eta>0
   (after M,Q,E have been chosen) such that
   `limsup_{n->infinity} wholeStrictRisk M Q E n eta > 0`.
2. **For every** pair of endpoint sequences lo,hi with each endpoint
   map measurable, and **every** real alpha satisfying 0<alpha<1/2,
   **if** `liminf_n wholeCoverage M Q lo hi n >= 1-alpha`, then:
   `liminf_n widthProb Q lo hi n >= 1-2alpha`,
   `liminf_n wholeWidthRisk M Q lo hi n >= 1-2alpha`,
   `1-2alpha>0`, and neither width-probability sequence tends to zero.

The endpoints take values in EReal=R union {-infinity,+infinity}; there is
no endpoint-ordering assumption. A reversed endpoint interval is empty.
The interval branch assumes asymptotic **uniform** coverage, not merely
coverage separately at every fixed P. The first branch rules out uniform
consistency, not pointwise consistency. Both procedures see only the n
observed units and seed. The theorem docstring advertises precisely this
model, containing-class extension, fixed baseline, and lack of a separate
testability/sufficiency assertion.

### Totalization and junk-value audit

All printed rational constants use real division by nonzero positive
integers, then exact coercions to EReal when needed. No score divisions,
logarithms, square roots, rpow, or truncated natural subtraction enter the
T3 statement's dependency closure. At n=0, Fin 0 is empty and the observed
sample is the unique empty function; E_0 can depend only on the seed.
The finite-sample conclusion requires n>=1, and asymptotic conclusions
ignore that initial term. The seed space is allowed to be an arbitrary
measurable type, but the existence of a probability Q rules out an empty
seed space. The statistical domain and the containing model are nonempty
once the baseline existence assertion is established.

The conditional-expectation defaults do not apply: sigma(X) is legitimate,
all populations are probabilities, and the tests explicitly require
integrability; multiplying by an indicator preserves integrability.
The mean-effect integral would default to zero for a nonintegrable
difference, but the containing-class hypothesis explicitly excludes this;
the hard submodel and baseline have bounded outcomes. It does **not**
require separate moments of Y0 and Y1 for additional laws of M.
The model itself uses an existential propensity witness, not a supplied
propensity input to any estimator.

Every measure in an event probability is a probability, so `toReal` never
converts infinity to zero. The event sets in the conclusions are
measurable by the explicit procedure measurability and measurable
coordinate observations; products with arbitrary Q remain legitimate.
`modelEventSup` includes zero and `modelEventInf` includes one. Their
sets are nonempty and contained in [0,1], so they use ordinary finite
real suprema/infima. On an empty model these definitions would return
zero and one respectively, but M contains the asserted baseline law.
All sequences used in real limsup/liminf are bounded in [0,1]; their
eventual upper/lower-bound sets are nonempty and bounded in the needed
direction. Thus no unbounded/empty real limsup/liminf default is involved.

Width uses `lo+(1/6)<hi`, avoiding subtraction of infinities. For finite
ordered endpoints this is exactly hi-lo>1/6. If lo=-infinity and hi is
finite or +infinity, or if hi=+infinity and lo is finite, the event holds.
If lo=hi=-infinity or lo=hi=+infinity, or the interval is reversed, it is
false. This matches the width of the corresponding interval of real
parameter values (empty in the equal-infinity cases), and never relies
on an infinity-minus-infinity convention. The finite shift introduces no
ambiguous opposite-infinity addition. No partial-function default occurs.
