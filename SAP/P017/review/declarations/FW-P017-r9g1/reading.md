# Blind reading of P017-T1 through P017-T5

This file was written before opening `claims.json` or `record.json`. I read the
five Challenge declarations and all the named declarations in their elaborated
closures, including the generated proof declarations (printed with
`scratch/Blind.lean`). The Challenge proofs themselves are stubs, as expected.

## SAP.P017.T1

Source: `SAP/P017/Challenge/Part1.lean:11-14`, with statement in
`SAP/P017/Defs/Part3.lean:16-57`.

This is a closed conjunction, with no hypotheses and no input parameters. Its
population space is the Borel space R x (R x R), with coordinates (u,(b,a)). The
measure is the product of Lebesgue measure restricted to (0,1),
`(delta_{-1}+delta_1)/2`, and `(delta_0+delta_1)/2`. These are independent
coordinates. The potential outcomes are Y0=b and Y1=b+u, the effect is
tau=Y1-Y0=u, and the observed record is
O=(a, a(b+u)+(1-a)b). The IPW summand is
H=2 O.first O.second - 2(1-O.first) O.second. On the population's full-measure
set this is `2(b+u)` when a=1 and `-2b` when a=0.

For this theorem, population mean means the real Bochner integral under the
specified measure. Effect support means the closed topological support of the
pushforward law of tau: a real t belongs precisely when every open neighborhood
has positive pushforward measure. If its extended-real infimum and supremum are
L,U and its mean is mu, its radius is
`max(0,min(U-mu,mu-L))` in [0,infinity]. The target of x is x at infinite
radius, and otherwise `min(mu+c,max(mu-c,x))`. An admissible weight is a
measurable, everywhere nonnegative real function w, with w and w*tau Bochner
integrable and integral(w)>0. Its weighted mean is
`integral(w*tau)/integral(w)`. A target is representable when such a weight
exists with that weighted mean. Probability is `(measure(event)).toReal`.

The sampling space is sequences of population points with the countable product
measure, so the coordinates really are IID. At n, the mean of H is
`sum_{i=0}^{n-1} H(s_i)/n`; the observed empirical law is
`(1/n) sum_{i=0}^{n-1} delta_{O(s_i)}`.

The conjunction asserts, in order:

1. tau is measurable and integrable; its mean is 1/2, support is [0,1],
   radius is 1/2 and positive, and its masses at 0 and 1 both vanish.
2. Almost surely, 0<tau<1 and |H|<4. Integral(H)=1/2,
   integral(H^2)=14/3, and integral((H-1/2)^2)=53/12.
3. For every natural n>=1, the sample mean has expectation 1/2 and mean squared
   deviation from 1/2 equal to 53/(12n).
4. The laws of sqrt(n)(sample mean-1/2) converge weakly to the centered real
   Gaussian with **variance** 53/12. Mathlib's distributional convergence also
   requires almost-everywhere measurability at every index, including zero.
5. For every real function w on the population, if w is measurable, everywhere
   nonnegative, integrable, and has strictly positive integral, its weighted
   effect mean is strictly between 0 and 1. Integrability of w*tau follows here
   from the bounded effect and these hypotheses.
6. For every n>=1, let B_b be the sequences with b_i=b and a_i=0 for all i<n.
   Both B_{-1} and B_1 have probability (1/4)^n>0 and are disjoint. For **every**
   s in B_{-1}, every sampled H is 2, its mean is 2, its clipped target is 1,
   its observed empirical law is delta_(0,-1), and its target is not
   representable. For **every** s in B_1 the analogous quantities are -2, -2,
   0, delta_(0,1), and nonrepresentability. These pointwise assertions do not
   restrict the u coordinates, even outside their almost-sure range.

Junk conventions and relevance: n=0 gives an empty real sum divided by zero,
hence zero; the empirical law is also zero because an infinite ENNReal scalar
times zero is zero. All finite-n assertions use n>=1; only convergence statements
include the harmless initial term. Natural casts are exact nonnegative casts,
so sqrt(n) uses no negative-input convention. The restricted Lebesgue measure
has mass one. The countable product construction would return zero for a
nonprobability factor, but the factors here are probabilities. Real division
by zero is zero, but admissible denominators are positive. Real Bochner
integrals return zero for nonintegrable functions, but tau and the stated
moments are integrable by these explicit bounded constructions. Pushforward of
a non-AE-measurable function would be a default Dirac measure for a nonzero
source measure; all pushforwards here are of measurable functions. `pr` would
turn infinite measure into zero, but these measures are probabilities.
Extended-real inf(empty)=+infinity and sup(empty)=-infinity and extended-real
arithmetic have total conventions, but the support here is explicitly [0,1].
The radius conversion truncates negative values to zero; here both distances
are 1/2. `ENNReal.toReal infinity=0` is bypassed by the infinite-radius branch
of the clipping definition. No log, rpow, limsup, liminf, or partial lookup is
used in this closure.

The docstring describes an IID IPW construction with asymptotic normality and
positive-probability clipping to unattainable endpoints, which is what this
conjunction says.

## SAP.P017.T2

Source: `SAP/P017/Challenge/Part1.lean:16-23` and
`SAP/P017/Defs/WholeW1.lean:16-78`.

Quantifier order: for every type Omega, measurable space structure, probability
measure G on Omega, and real function tau, **if** tau is measurable and Bochner
integrable, the following conjunction holds. Within it every t is an arbitrary
real, with no common target fixed beforehand. No heterogeneity or positive
radius is assumed.

Write Q for the pushforward law G.map(tau), S for its closed topological support
(positive measure in every neighborhood), and L=inf S, U=sup S in the extended
reals. Write p(A)=(G(A)).toReal and I(f)=the real Bochner integral under G.
Representability of t means there exists a measurable w:Omega->R such that
w>=0 everywhere, w and w*tau are integrable, I(w)>0, and I(w*tau)/I(w)=t.
All SAP notions in the statement are the following explicit assertions:

1. For every t, representability is equivalent to
   `p(tau=t)>0 OR (p(tau<t)>0 AND p(tau>t)>0)`.
2. Every real strictly between L and U is representable. Every real equal to
   either extended-real endpoint is representable iff its atom has positive
   mass. Every real strictly below L or strictly above U is unrepresentable.
   Targets in gaps of S can therefore be representable.
3. For every t with p0=p(tau=t)>0, the **specified** weight
   w0=1_{tau=t}/p0 is admissible, satisfies 0<=w0(omega)<=1/p0 at every
   omega, I(w0)=1, and I(w0*tau)=t.
4. For every t with p-=p(tau<t)>0 and p+=p(tau>t)>0, define
   m-=I(tau 1_{tau<t})/p-, m+=I(tau 1_{tau>t})/p+ and
   alpha=(m+-t)/(m+-m-). Then m-<t<m+, m+-m->0,
   0<alpha<1, and the **specified** function
   w=alpha 1_{tau<t}/p- + (1-alpha) 1_{tau>t}/p+
   is admissible. At every omega it lies between zero and
   alpha/p-+(1-alpha)/p+. It satisfies I(w)=1 and I(w*tau)=t.

Junk conventions and relevance: all divisions are total real division, giving
zero at denominator zero. The atom and conditional-mean formulas exist even
on zero-mass regions but all conclusions using them require positive masses;
the conditional means are strictly ordered before the coefficient is used.
Integrable tau implies integrability of the indicator products and bounded
weights and their weighted effects. The admissibility predicate excludes a
zero denominator or undefined expectation. Every measure evaluated by `pr` is
finite. For measurable tau under a probability measure on R its support is
nonempty; unbounded support gives genuine extended-real endpoints, not an
accidental real sInf/sSup value. An empty Omega cannot carry a probability
measure, whereas nonempty concrete examples exist. No sqrt, log, rpow,
subtraction on naturals, limsup/liminf, or partial function is used. The
nonmeasurable-map fallback described under T1 is excluded by Measurable tau.

The docstring says this is the corrected attainability fact, including its
specified bounded atom and two-region constructions and support consequences.
The explicit conjunction includes all of those claims.

## SAP.P017.T3

Source: `SAP/P017/Challenge/Part1.lean:25-32` and
`SAP/P017/Defs/WholeW1.lean:80-124`.

Quantifier order: for every type Omega, measurable structure, probability G,
and tau:Omega->R, assume measurability, Bochner integrability, and strictly
positive radius c. Set mu=integral(tau), S=support(G.map tau), L=inf S and
U=sup S in EReal, and c=max(0,min(U-mu,mu-L)) in ENNReal. For real x define
C(x)=x if c=infinity, otherwise min(mu+c_real,max(mu-c_real,x)). Here
c_real=c.toReal. Write Rep(t) for existence of a measurable, nonnegative,
integrable weight with positive integral, integrable w*tau, and normalized
weighted effect integral equal to t. The entire following conjunction is
inside those three hypotheses:

1. For every real x, L<=C(x)<=U. Also Rep(C(x)) iff either
   L<C(x)<U, or (C(x)=L or C(x)=U) and G(tau=C(x))>0.
2. For every real x with ofReal(|x-mu|)<c, C(x)=x and Rep(C(x)).
   If c is finite, additionally L<=mu-c_real<x<mu+c_real<=U.
3. If c=infinity, then L=-infinity, U=+infinity, and for every real x,
   Rep(C(x)).
4. If c is finite, and for **every real t** that both equals a clipping endpoint
   mu-c_real or mu+c_real and equals an effect-support endpoint L or U,
   the event tau=t has positive mass, then **every real x** has Rep(C(x)).
   This asks for atoms only at endpoints that bind the support bound.
5. If there exists a finite set F of real numbers with tau in F G-almost
   surely, then **every real x** has Rep(C(x)). This means a finite set of
   possible effect values, not merely that each real-valued effect is finite.
6. For every further type Xi, measurable structure, probability measure P,
   and sequence hat:natural->Xi->R: if every hat_n with n>=1 is measurable,
   and there exists a nonnegative-real **variance** v>0 such that the laws of
   sqrt(n)(hat_n-mu) under P converge weakly to N(0,v), then both
   P(ofReal(|hat_n-mu|)<c) and P(Rep(C(hat_n))) tend to one. The definition
   of distributional convergence itself includes AE measurability at every
   index. There is no independence assumption between hat and the population,
   no IID requirement on hat, and no assertion that a representing weight is
   recoverable from observed data or a measurable function of x.

Junk conventions and relevance: `populationMean` is the Bochner integral, but
tau is integrable. All probability measures are finite, so their `toReal`
values are ordinary probabilities. The support pushforward is measurable and
has nonempty support in R. Unbounded endpoints are retained in EReal; because
mu is real, the distances to the endpoints do not subtract infinity from
itself. Radius conversion truncates negatives, but c>0 excludes that branch.
Infinite c is handled explicitly; every use of c_real in a conclusion is
guarded by c!=infinity. All weight denominators are positive by admissibility.
sqrt(n) has nonnegative arguments and is zero at n=0. The finite-set condition
cannot be satisfied by an empty set under probability G. No log, rpow,
limsup/liminf, truncated natural subtraction or partial functions occur.
Measurability of the representation event is supplied mathematically by the
explicit interior/endpoint characterization; it is not an extra premise.

The docstring describes the exact interior/atom criterion, strict-inside bounds,
three sufficient conditions for all-realization representation, and the two
asymptotic probabilities. Its phrase "almost surely finite-valued" is read
here as a finite set of possible values, as explicitly required by the code.

## SAP.P017.T4

Source: `SAP/P017/Challenge/Part1.lean:34-38` and
`SAP/P017/Defs/Part3.lean:104-150`.

For every type Omega with a measurable space, probability measure G and real
effect tau, first assume tau measurable, tau Bochner integrable, and c>0.
Let mu=integral(tau), S=support(G.map tau), L=inf S, U=sup S in EReal,
and c=max(0,min(U-mu,mu-L)) in ENNReal. Let
D_d(x)=min(mu+d,max(mu-d,x)). Representability means existence of a
measurable everywhere nonnegative w with w and w*tau integrable,
integral(w)>0 and integral(w*tau)/integral(w) equal to the target.
The conjunction asserts:

1. There exists a **real** d>0 with ofReal(d)<c.
2. For **every** real d>0 with ofReal(d)<c, all the following hold:
   - For every real x, D_d(x) is representable.
   - For every real x, |D_d(x)-mu|<=|x-mu|.
   - For every real x, D_d(x)=x iff |x-mu|<=d.
   - For every further measurable space Xi, probability P on it and real
     function hat:Xi->R, and then every real eta>0 and a>0,
     P(|hat-D_d(hat)|>eta*a)<=P(|hat-mu|>d). No measurability premise is
     attached to this first inequality, so formally these are outer-measure
     probabilities for an arbitrary hat.
   - For the same P and hat, if hat is measurable and
     max(sup(support(P.map hat))-mu,mu-inf(support(P.map hat)))<=d
     in EReal, then P(hat=D_d(hat))=1.
   - For every real c'>d there exists real x with |x-mu|<=c',
     D_{c'}(x)=x and D_d(x)!=x. The obstruction is to replacing the smaller
     clipping interval by any larger one in the equality event.
3. If c is finite, c_real/2 is a positive real whose ofReal value is <c.
4. If c=infinity, every positive real d has ofReal(d)<c.
5. Every real t strictly between L and U is representable. For every real
   t equal to L or U, representability is equivalent to positive mass at
   tau=t. Every real t outside [L,U] is unrepresentable.
6. If c=infinity **or** every real t which is both mu-c_real or mu+c_real
   and a support endpoint has positive mass at tau=t, then for **every real x**
   the original radius-c clipped target (identity at infinity) is representable.

The existential d precedes the separate universal assertion over **all** valid
d; no selected d is used to weaken the universal assertion. The additional P
and hat occur only inside item 2. No root-n hypothesis or sequence is present.

Junk conventions and relevance: Bochner-integral and admissible-denominator
guards are as above. `pr` applies to finite probability measures, although
the first probability comparison accepts nonmeasurable sets via outer measure;
the inequality still follows from a pointwise event inclusion. Pushforwards
whose supports are used require measurable tau or measurable hat. The
probability laws on R have nonempty support; unbounded infima/suprema use
EReal infinities. EReal distances subtract only a finite mu. c_real/2 is
used under c!=infinity. In item 6 the possibly meaningless finite endpoints
when c=infinity occur only in the unused second disjunct; the first disjunct
already proves the implication's premise. Negative c' cannot occur since
c'>d>0. Natural sample-size casts, log, sqrt, rpow, limsup/liminf and partial
function values do not occur in this closure.

The docstring describes existence and universality of smaller positive radii,
finite deterministic/probability companions, support consequences, and the
obstruction for a larger radius. It makes no claim of a measurable/data-based
choice of weights.

## SAP.P017.T5

Source: `SAP/P017/Challenge/Part1.lean:40-44` and
`SAP/P017/Defs/Part4.lean:15-38`.

This is another closed conjunction with no external hypotheses or parameters.
The population is the Borel space R x R, coordinates (z,b), with product law
N(0,1) x (delta_{-1}+delta_1)/2. The potential outcomes are Y0=0 and
Y1=b, so tau=b. The sampling law P is the countable product of this population
law (independent, identically distributed pairs). Define
A_n=sum_{i<n} z_i/n, h_n=A_n+1/n, Z_n=sqrt(n) A_n,
eps_n=1/sqrt(n), C(x)=min(1,max(-1,x)), and D_n=A_n-C(h_n).
The intermediate error D_n is distinct from the actual clipping error h_n-C(h_n).

The conjunction asserts:

1. tau is measurable and integrable, integral(tau)=0, its closed pushforward
   support is {-1,1}, and its radius computed as the nonnegative extended-real
   minimum distance of the mean to the support bounds is 1.
2. There exists variance v>0 with laws of sqrt(n) h_n converging weakly to
   N(0,v). (The definition does not specify v=1 in this clause.)
3. For every n>=1, Z_n is measurable and has law N(0,1), eps_n is measurable
   with integrable square, and sqrt(n) h_n=Z_n+eps_n almost surely.
   This is exactly the defined Gaussian-plus-remainder condition; it imposes
   no independence between Z_n and eps_n, or between different n.
4. The deterministic random variables sqrt(n)/n tend to zero in probability:
   for every real eta>0, P(|sqrt(n)/n|>eta) tends to zero.
5. For every n>=1, A_n has law N(0,1/n). For **every** sequence s,
   D_n equals A_n+1 when A_n<-1-1/n; equals -1/n when that first inequality
   fails and A_n<=1-1/n; and equals A_n-1 otherwise. Moreover D_n=0 iff
   A_n=1. Consequently P(D_n!=0)=1. Also
   P(|A_n|>1)=2 Phi(-sqrt(n))<1 and 2 Phi(-sqrt(n))<=1/n,
   where Phi(x)=N(0,1)((-infinity,x]).
6. For every n>=2 and **every** sequence s with |A_n|<=1/2,
   D_n=-1/n and h_n-C(h_n)=0. Also P(|A_n|<=1/2)>=1-4/n and
   P(|D_n|/(1/n)>=1/2)>=1-4/n. The lower bounds may be nonpositive for
   small n; they are informative eventually.
7. For every eta>0, P(|n D_n+1|>eta) tends to zero.
8. It is **not** the case that for every eta>0,
   P(|D_n|>eta/n) tends to zero. This is the exact negation of the defined
   little-o-in-probability assertion D_n=o_p(1/n).

Junk conventions and relevance: at n=0 both A_n and 1/n are zero, sqrt(n)=0,
eps_n=0 and the associated variance 1/n is zero. Mathlib defines zero-variance
Gaussian as a Dirac mass. All finite-n law, decomposition and nonzero-error
assertions require n>=1; central-event assertions require n>=2. The limits
ignore finitely many initial values. The rate 1/n is not positive at index zero,
but is positive at every relevant positive sample size, so its use in an
asymptotic little-o assertion has no limiting defect. In the definition
`LittleOp P V a` there is no built-in positivity premise on a: it literally
means the eta-threshold probability limit stated above. The rate used here is
eventually positive. No real logarithm, rpow or truncated subtraction occurs.
All square roots have nonnegative natural arguments; all finite-n divisions
have positive denominators. All measures are probabilities, measurable
projections and finite sums have genuine pushforward laws, and normal moments
and epsilon's square are integrable. Empty-sum and default integral conventions
do not generate the asserted failure. Its nonzero intermediate error on a
central event is the ordinary deterministic shift 1/n.

The docstring describes a shifted-normal example with almost-surely nonzero
intermediate error, failure of an every-positive-sequence assertion, and zero
**actual** clipping error on a central event. It does not itself specify the
scope of the printed assertion being challenged.

## Generated closure declarations and total-operation audit

All generated unit declarations in `closure.json` were printed and read:

- `T1Statement._proof_1`, `_proof_2`, `_proof_4`, `_proof_5`, `_proof_6`,
  `_proof_7` are the proofs that the natural numerals 2,4,14,3,53,12,
  respectively, satisfy `AtLeastTwo`; they control numeral elaboration only.
- `T1Statement._proof_3` is the ordinary OuterMeasureClass instance for measures
  on R x (R x R); `_proof_8` is OpensMeasurableSpace R; `_proof_9` proves each
  repeated IID sampling measure is a probability; `_proof_10` proves the
  N(0,53/12) limit measure is a probability.
- `fairPair._proof_1` supplies the ENNReal scalar tower and `_proof_2` the
  `AtLeastTwo` proof for 2.
- `RootNNormal._proof_1` supplies OpensMeasurableSpace R and `_proof_2` the
  probability instance for every Gaussian with NNReal variance.
- `T5Statement._proof_1` is the IID sampling probability instance;
  `_proof_2` proves 0<=1/(n:R) for every n, including n=0, for a NNReal
  variance; `_proof_3` and `_proof_4` supply `AtLeastTwo` for 2 and 4.

No generated declaration adds a mathematical hypothesis or encodes any target
conclusion. Across these closures there are no uses of real log, real powers,
limsup, liminf, partial-function defaults, or finite-type sums over an
unconstrained empty type. The only finite sets summed over are `range n`.
