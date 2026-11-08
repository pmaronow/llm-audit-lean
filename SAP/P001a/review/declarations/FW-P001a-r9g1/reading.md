# Blind reading

This file was written from `closure.json`, the Challenge docstrings, the listed
Defs sources, and Mathlib, before opening `claims.json` or `record.json`.
No mathematical claim is inferred from the theorem's certified proof. The
statements below are readings of its elaborated proposition and definitions.
All integrals below are Mathlib Bochner integrals; all almost-everywhere
statements use the indicated Mathlib measure. Real-valued probabilities mean
`ENNReal.toReal` of the measure of an event.

## SAP.P001a.T1

Source: `Challenge/Part1.lean:12–15`, `Defs/Part2.lean:208–217`.
This is a closed conjunction, with no external hypotheses or parameters.

Let, for natural numbers k and n,

* q(k) = 2^(-(k+1));
* q_n(k) = (1 - (n:real)^(-3)) q(k) + (n:real)^(-3)
  times q(k-n) if n <= k, and times zero otherwise;
* F_r(x) = sum over all natural k of r(k) 1_{(k:real)<=x};
* M(r) = sum over natural k of (k:real) r(k);
* S(r) = sum over natural k of (k:real)^2 r(k).

Here the sums are Mathlib `tsum` on real sequences. Saying that r is a
`FiniteMomentLaw` means, in order: every r(k) is nonnegative, r is summable,
its sum is one, the sequence k r(k) is summable, and the sequence k^2 r(k)
is summable. Thus this is a probability mass function on the nonnegative
integers with a finite second moment, not a placeholder probability predicate.

The conjunction asserts:

1. q is such a law, M(q)=1, and S(q)=3.
2. For every natural n, if 2 <= n, then q_n is such a law, every q_n(k) is
   strictly positive, M(q_n)=1+n^(-2), S(q_n)=3+n^(-1)+2n^(-2), and
   (M(q_n)-M(q))/n^(-2)=1.
3. As natural n tends to infinity, S(q_n)-M(q_n)^2 tends to 2, and n^(-2)
   tends to 0.
4. For every real epsilon>0, eventually for all natural n, for every real x,
   abs((F_{q_n}(x)-F_q(x))/n^(-2)) < epsilon.

The last quantifier order is uniform in x, not pointwise convergence.
The docstring calls this a finite-moment perturbation witness against the
printed claim and explicitly omits several identities, exact sup bounds,
and a general predicate denying Hadamard differentiability. The proposition
itself asserts the witness facts, not that general predicate.

Junk/default conventions:

* Real inverse at zero is zero. At n=0 the perturbation is q and the scaled
  CDF quotient is zero. All exact mean-quotient claims require n>=2; both
  limits and the eventual assertion ignore a finite initial segment. Thus
  zero inverse does not supply their intended mathematical content.
* k-n is truncated natural subtraction, but the shifted mass uses it only
  in the branch n<=k, so it is the genuine nonnegative integer difference.
* A real `tsum` of a nonsummable sequence defaults to zero. The explicitly
  asserted summability of q and, for n>=2, q_n and their first two moments
  rules this out. The CDF subseries is dominated by a summable nonnegative
  mass function. At n=0,1 the masses are also genuine summable masses.
* All natural-to-real casts are exact; k+1 is computed in the naturals.
  No empty finite index type, integral, log, sqrt, real rpow, toReal,
  supremum, or liminf is used in this statement.

Closure read: `FiniteMomentLaw`, `T1Statement`, `geoMass`, `massCDF`,
`massMean`, `massSecond`, `mixMass`; also the listed auxiliary declarations
`geoMass._proof_1`, `estimatedMatchIntercept._proof_2`, and
`signProductLaw._proof_2`. The last three were printed in
`scratch/BlindCheck.lean`; they only certify that small natural numerals are
at least two and add no mathematical assumption or behavior.

## SAP.P001a.T2

Source: `Challenge/Part1.lean:17–19`, `Defs/Part2.lean:220–228`.
The proposition is the conjunction of a universally quantified sampling
theorem and the full closed perturbation conjunction used in T1.

First, for every type Omega in universe u1 with any measurable space, every
measure mu on Omega with total mass one, and every sequence
X_i:Omega -> real, assume, in this order:

1. Every X_i is measurable, the family is Mathlib `iIndepFun` (joint
   independence), and every X_i has Mathlib `IdentDistrib` with X_0 under
   mu and mu (AE measurability and equal pushforward distributions).
2. X_0 belongs to Mathlib `MemLp` with exponent 2 under mu: AE strong
   measurability and finite L2 seminorm.
3. v = `ProbabilityTheory.variance X_0 mu` is strictly positive.

Let m = integral X_0 dmu, A_n(omega) = (sum_{i<n} X_i(omega))/(n:real),
and P_n(omega) = (n:ENNReal)^(-1) times the sum of Dirac measures at
X_i(omega), i<n. Then:

* for every natural n>0, for every omega, integral id dP_n(omega)
  equals A_n(omega);
* the variables sqrt(n)(A_n-m) converge in distribution to the real
  Gaussian measure with mean zero and variance v. Precisely, for every
  real x at which t -> (Gaussian((-infinity,t])).toReal is continuous,
  the real probabilities mu{omega:sqrt(n)(A_n(omega)-m)<=x}.toReal
  converge to Gaussian((-infinity,x]).toReal.

The variance is the toReal of the nonnegative extended integral of
|X_0-integral X_0 dmu|^2. The Gaussian's second parameter is a
nonnegative real, formed using the proof v>=0 obtained from v>0; it is a
variance rather than a standard deviation.

Second, the statement also asserts the following independently of Omega,
mu, and X. For q(k)=2^(-(k+1)) and
q_n(k)=(1-n^(-3))q(k)+n^(-3)1_{n<=k}q(k-n), q is a nonnegative
summable normalized mass with summable kq(k) and k^2q(k), whose first
two moments are 1 and 3. For every n>=2 the same summability and
normalization hold for q_n, every mass is positive, its moments are
1+n^(-2) and 3+n^(-1)+2n^(-2), and its mean difference divided by
n^(-2) is 1. Its second moment minus its squared mean tends to 2;
n^(-2) tends to zero. For every epsilon>0, eventually for every real x,
the absolute CDF difference divided by n^(-2) is below epsilon, where
each CDF is the infinite sum of masses at integers <=x.

The sampling conclusion is not conditional on this witness or vice versa.
No Hadamard-derivative existence/nonexistence predicate or general delta
method is explicitly stated.

Junk/default conventions:

* The real mean is zero by convention if its Bochner integral is
  undefined; the L2 condition and finite probability measure give genuine
  integrability. The variance's `toReal` sends infinity to zero; L2 rules
  out infinite variance and strict positivity excludes degeneracy.
* `prob` and CDFs use `toReal`, which sends infinity to zero. All measures
  actually used for these probabilities are probability measures.
* The empirical measure at n=0 uses the ENNReal inverse 0^(-1)=infinity
  times the zero sum of measures, yielding the zero measure. The sample
  mean is 0/0=0. The empirical-mean identity is asserted only for n>0.
  The CLT ignores n=0 and sqrt is evaluated only at nonnegative naturals.
* Real sqrt outside its nonnegative domain is zero, but no such input
  occurs here. Gaussian variance zero would produce a Dirac measure;
  the strict positivity hypothesis excludes it.
* Infinite sums, natural subtraction, and real inverse in the geometric
  witness have exactly the safeguards described in the preceding T1
  section: summability, an n<=k branch, and n>=2 or eventual assertions.
* There is no supremum/infimum, log, real rpow, partial-function default,
  or empty finite-index assertion that changes the conclusion.

Closure read: `CD`, `FiniteMomentLaw`, `IID`, `T1Statement`,
`T2Statement`, `cdf`, `empirical`, `geoMass`, `massCDF`, `massMean`,
`massSecond`, `mean`, `mixMass`, `prob`, `sampleMean`, `var`, and all
five listed auxiliaries. `T2Statement._proof_1` supplies v>=0 from v>0;
`empirical._proof_1` is the ENNReal scalar-tower instance; the remaining
three are the numeral certificates described above. Their full printed
terms were read, and none encodes the conclusion.

## SAP.P001a.T3

Source: `Challenge/Part1.lean:21–24`, `Defs/Part2.lean:196–205,231–257`.
This is another closed conjunction with fixed witness data, plus the
negation of a separately defined universal contract.

Let g(x)=1/2 on [-2,-1] union [1,2], and zero elsewhere. Let U[a,b]
denote Lebesgue measure with density 1_{[a,b]}(b-a)^(-1). Let nu be
the product of the measure with density g and U[-1,1]. Coordinates on
real pairs are X(x,y)=x and Y(x,y)=y. Let
b(x)=x(1-x^2)^2 for |x|<1, and zero otherwise.

For arbitrary mu, X, Y and m, the definition `IsCEF mu X Y m` means:
m is measurable; Y and m composed with X are integrable; and for
every measurable subset A of the covariate space,
integral over X^(-1)(A) of Y equals the integral there of m(X).
Thus this is a global measurable version of a conditional mean, with
values outside the covariate law left unrestricted by the integral
identity. `HasPDF` (and its pair-space `HasJointPDF` counterpart)
means AE measurability of the real density with respect to Lebesgue
measure, pointwise nonnegativity, Lebesgue integrability, and equality
of the measure with Lebesgue measure weighted by ENNReal.ofReal of
that density. Normalization is not part of these predicates alone.

The negated contract says: for every type Omega in universe zero,
measurable space and probability measure mu, for every real-valued
measurable X,Y with X integrable, every PDF f_X of the law of X, and
every two global CEF versions m,m', if each version is differentiable
at every x where f_X(x)>0, there exists one real a such that both m
and m' have derivative a at integral X dmu. This contract contains no
requirement that the mean lie in {x:f_X(x)>0}, nor even that these
versions be differentiable at the mean. The theorem negates it.

The fixed-witness conjunction asserts:

* nu is a probability measure and has pair density
  g(x) times 1_{[-1,1]}(y)/2;
* nu equals the product of its two marginals, X has PDF g, and Y has
  law U[-1,1];
* almost surely X is in [-2,2] and Y in [-1,1]; integral X dnu=0,
  and g(0)=0;
* the zero function is a CEF, b is C1 on the entire real line, and b
  vanishes wherever g is positive;
* the derivative at zero of the zero function is zero;
* for every real a, x -> a b(x) is a CEF and its derivative at
  integral X dnu is a.

A second block repeats probability normalization, the joint density,
the zero mean, the zero and b CEF versions, C1 smoothness of b, and
the derivatives 1 and 0 at the mean. Finally the zero function is C1
and {x:g(x)>0} is exactly [-2,-1] union [1,2].

The docstring explicitly identifies the negated statement as a stronger
global-extension reading, and says that this witness does not assert
a PDA counterexample at an admissible evaluation point.

Junk/default conventions:

* A Bochner integral defaults to zero when integrability fails. The
  compactly supported normalized law makes both coordinates integrable;
  `IsCEF` explicitly requires the other used integrals to be integrable.
  In the general contract X integrability is a hypothesis, and CEF
  hypotheses include Y and m(X) integrability.
* `deriv` returns zero for a function not differentiable at the point.
  All fixed derivative assertions concern globally C1 functions (also
  constant multiples of b), so their derivatives are genuine. The
  contract uses `HasDerivAt`, not the totalized derivative value.
* Uniform-law inverse is evaluated at b-a=2, strictly positive. Although
  the definition degenerates for a>=b, no such parameters occur.
* `ENNReal.ofReal` truncates negative inputs to zero; PDF nonnegativity
  and the explicit nonnegative densities prevent this from changing the
  intended laws. Endpoints of intervals carry no Lebesgue atoms.
* No log, sqrt, real rpow, empty-index sum, toReal of infinity, sInf/sSup,
  liminf, truncated subtraction, or partial-function default is used.

Closure read: `HasJointPDF`, `HasPDF`, `IsCEF`, `T3Statement`,
`gapJointLaw`, `gapPDF`, `mean`, `pdaBump`,
`pda_at_mean_printed_contract`, `uniformLaw`, and every listed
auxiliary. `T3Statement._proof_1` is the outer-measure interface of
the measure of pairs, and the contract auxiliary is continuous real
scalar multiplication. The numeral auxiliaries add no content.

## SAP.P001a.T4

Source: `Challenge/Part1.lean:26–32`, `Defs/WholeW1.lean:18–58`.
The proposition is a conjunction of two universal principles and a
fixed one-dimensional example. Write R^K for `Fin K -> real`, with
its usual finite-product topology and Lebesgue volume. The auxiliary
`partialAt M x k` is the Mathlib derivative at t=0 of
t -> M(update x k (x_k+t)).

First, for every natural K, open subset U of R^K, and continuous
functions m,m':U -> real, suppose for Lebesgue almost every ambient
x under volume restricted to U, for every proof hx:x in U,
m(x,hx)=m'(x,hx). Then m=m'. Moreover, for every x in the subtype
U, every coordinate k:Fin K, every real a, and every pair of global
functions M,M':R^K -> real restricting to m,m', respectively, if
t -> M(update x k (x_k+t)) has derivative a at 0, the corresponding
line through M' has derivative a at 0 and their `partialAt` values
are equal. Equality of representatives itself does not assume
derivative existence. The point x can be any point of U, not just
a mean.

Second, for every type Omega in universe u, measurable space,
probability measure mu, natural K, functions X:Omega -> R^K and
Y:Omega -> real, assume, in order:

* X is measurable and each coordinate X_k is integrable;
* f:R^K -> real is an AE measurable, pointwise nonnegative, integrable
  Lebesgue density of the pushforward mu.map X;
* U is open, the vector xbar=(integral X_k dmu)_k lies in U, and
  f(x)>0 for every x in U;
* m,m':R^K -> real are global CEF versions: each is measurable,
  Y and its composition with X are integrable, and integrals of Y
  and of that composition agree over the inverse image of every
  measurable covariate set;
* both m and m' are continuous on U.

Then m=m' pointwise on U. For every coordinate k and real a, if
the k-coordinate line through m at xbar has derivative a at 0,
the line through m' has derivative a at 0 and their `partialAt`
values agree.

Third, let nu=U[-1,1], namely Lebesgue density 1/2 on [-1,1], and
let h(x)=1/2 on [-1,1] except at x=0, where h is zero; elsewhere h
is also zero. The theorem says h is an integrable nonnegative PDF
of nu; id is nu-integrable with mean zero; h(0)=0; and for every
real function m, if m is continuous on (-1,1) and equals zero
nu-almost everywhere, it equals zero everywhere on (-1,1) and
has derivative zero at zero. This witnesses version uniqueness
despite the absence of a pointwise-positive PDF neighborhood for
this chosen density version.

Junk/default conventions:

* `partialAt` uses total `deriv`, zero for a nondifferentiable line.
  Each derivative-transfer conclusion has an explicit genuine
  `HasDerivAt` premise and conclusion, so equality of zeros is not
  being used as substitute for existence.
* Means are totalized Bochner integrals; coordinate integrability
  and the uniform example's explicit id integrability prevent
  undefined means. CEF hypotheses include integrability of Y and
  the composed versions. Values of global representatives outside
  U remain unconstrained, but derivative locality makes them irrelevant.
* `HasPDF` and `HasVectorPDF` use `ofReal`, which discards negative
  inputs; pointwise nonnegativity excludes this issue. The uniform
  interval has length two, so inverse zero is irrelevant. The hole
  at zero changes a density only on a null set, not the law.
* K may be zero; R^0 is the one-point finite-product space. Its
  product volume is nonzero. The coordinate quantifier is then empty,
  as appropriate for the absence of coordinates. U may be empty
  in the first principle, making equality valid on the empty domain;
  the second principle explicitly requires xbar in U. Nonempty
  ordinary positive-dimensional cases are included.
* No unbounded/empty infimum or supremum, liminf, log, sqrt, real
  rpow, natural subtraction, or toReal probability is involved.

Closure read: `HasPDF`, `HasVectorPDF`, `IsCEF`,
`T4WholeStatement`, `mean`, `partialAt`, `uniformLaw`,
`wholeHolePDF`, and all three auxiliaries. The two statement
auxiliaries supply the outer-measure interface on R^K and real
continuous scalar multiplication. The hole-PDF auxiliary is the
numeral certificate for 2. All were printed and read.

## SAP.P001a.T5

Source: `Challenge/Part1.lean:34–47`, `Defs/WholeW4.lean:17–115`.
This proposition combines rate identities, a universally quantified
iid experiment with existence and failure assertions, and a separate
finite-experiment endpoint principle.

The degree schedules are J(n)=Nat.floor((n:real)^(3/4:real)) and
E(n)=Nat.sqrt n (the integer square root). The rates asserted are
J(n) -> infinity and J(n+1)/(n+1) -> 0. For every natural t,
E(t^2)=t.

For a natural n, a data vector is a pair (x,y) of functions
Fin n -> real. For b:Fin(d+1) -> real, its polynomial is
P_b=sum_{k=0}^d C(b_k) X^k, using ordinary Mathlib polynomial
addition, multiplication and evaluation. A sequence
fit:natural -> Omega -> Polynomial real is a `BorelSieveLSW4`
fit for observations X_i,Y_i and degree schedule D exactly if:

1. For every n and omega, the natural degree of fit_n(omega) is
   at most D(n); and for every real polynomial p with degree at
   most D(n), the sum over i<n of (Y_i-fit_n(X_i))^2 is at most
   the corresponding squared residual sum for p.
2. For every n there exists a Borel measurable function b from
   the pair of n-vectors to Fin(D(n)+1) -> real such that, for
   every omega, fit_n(omega) is P_{b(x(omega),y(omega))}.

The quantifier in (2) permits a different coefficient statistic at
each n. It requires dependence only on the first n observations,
not merely measurability in the entire experiment.

Now for every type Omega in universe u with a measurable space,
every probability measure mu and sequences X_i,Y_i:Omega -> real,
suppose the pairs (X_i,Y_i) are all measurable, jointly independent,
and identically distributed (as expressed by `IID`), and the law
of (X_0,Y_0) is U[0,1] product Gaussian(0,variance 1). Then the
following conjunction holds:

* X_0 has law U[0,1], Y_0 has the standard real Gaussian law,
  and X_0,Y_0 are independent. The function f(x)=1 on [0,1]
  and zero elsewhere is an AE measurable nonnegative integrable
  density of X_0's law, and f(x)>0 iff x is in [0,1].
* The zero function is smooth of every order (`ContDiff real
  infinity`) and is a CEF for Y_0 given X_0: it is measurable,
  the outcome and zero composition are integrable, and their
  integrals agree over all measurable inverse images under X_0.
* For every natural k, X_0^k and Y_0^k are integrable. For every
  real delta with 0<delta<=1, the event X_0 in [0,delta] has
  probability delta.
* A `BorelSieveLSW4` fit exists for D=J.
* For every such fit, for every real delta with 0<delta<=1:
  for every real epsilon>0,
  liminf over natural t of
  mu{omega:epsilon < integral_{[0,delta]} fit_{t^4}(omega)(x)^2 dx}
  is at least 1/2. In addition that local integral does not
  converge in probability to zero along all n. The latter uses
  `CP`: for every epsilon>0, mu{epsilon<=distance(Z_n,0)}
  would have to tend to zero; its negation is asserted.
* A `BorelSieveLSW4` fit exists for D=E.
* For every such fit and every natural t>=2,
  mu{|fit_{t^2}(1)|>1/4} >= 1/4.

Probabilities in those sentences are the real `toReal` values.
The local risk is the Lebesgue integral, not an empirical residual
and not an evaluation at the single endpoint. Because the design
law is uniform on [0,1], this is also the local population squared
L2 error for the zero CEF. Quantifiers over fits precede delta and
epsilon; neither is chosen as part of the fit.

Finally the finite-experiment clause says: for every natural t>=2,
every type Omega in universe u with a measurable space and
probability measure mu, and every measurable data statistic
Z:Omega -> (real^{t^2} x real^{t^2}) whose law is
(product_{i<t^2} U[0,1]) product (product_{i<t^2} Gaussian(0,1)),
for every Borel measurable b:data -> real^{t+1}, if for every
omega the polynomial P_{b(Z(omega))} minimizes squared residuals
over every polynomial of degree at most t, then
mu{|P_{b(Z)}(1)|>1/4} >= 1/4. The coefficient representation
already ensures degree at most t. This clause makes no assumption
about coupling to experiments at other sample sizes.

The docstring makes the same distinction between the main local
error failure and the separate endpoint statement, excludes t=1
from the endpoint bound, and states that usual measure-theoretic
conditions are assumed.

Junk/default conventions:

* Real rpow is evaluated only at nonnegative natural numbers,
  with positive exponent 3/4, so no negative-base convention is
  used. Nat.floor sends a negative real to zero, but its argument
  is nonnegative. Nat.sqrt is the genuine integer floor square
  root. All natural-to-real casts are exact. The rate denominator
  is n+1 and never zero.
* At n=0 the index set Fin 0 is empty and every residual sum is
  zero. J(0)=E(0)=0; constants, including the zero polynomial,
  are allowed. `natDegree` of the zero polynomial is zero. These
  conventions give a feasible initial fit and cannot explain an
  asymptotic or t>=2 failure.
* Coefficient vectors use Fin(D(n)+1), always nonempty. The
  coefficient-polynomial construction does not use a partial
  inverse or a default estimator at a singular design: it simply
  specifies all polynomials by their finite coefficients, and
  minimization is imposed for every data point.
* The local-risk Bochner integral could default to zero if
  undefined in general, but a real polynomial squared is continuous
  and integrable on every finite compact interval [0,delta]. The
  asserted delta is positive and at most one. Consequently the
  displayed risk is a genuine finite nonnegative number for every
  sample, without a moment assumption on the random coefficients.
* The probability `toReal` sends infinity to zero in general;
  all event measures here are bounded by one. Event measurability
  follows from Borel data coefficients, measurable observations,
  finite polynomial evaluation and the finite compact integral.
* `Filter.liminf` is a totalized order construction on real
  sequences, but here it acts on probabilities in [0,1] along the
  nontrivial atTop filter on naturals. Upper and lower bounds rule
  out an empty/unbounded infimum/supremum artifact.
* Means in `IsCEF` could default on nonintegrable inputs, but its
  integrability requirements and the uniform/Gaussian laws rule
  that out. The uniform-law denominator is 1 and densities are
  nonnegative, so neither division by zero nor `ofReal` clipping
  alters the model. Gaussian variance is 1, not the Dirac branch.
* No log, derivative default, real sqrt, truncated subtraction,
  empty supremum, or partial-function default enters the claim.

Closure read: `BorelSieveLSW4`, `CP`, `FiniteEndpointBoundW4`,
`HasPDF`, `IID`, `IsCEF`, `IsSieveLS`, `SieveDataW4`,
`SieveModelFactsW4`, `T5WholeStatementW4`,
`coefficientPolynomialW4`, `endpointDegreeW4`,
`finiteSampleLawW4`, `localRiskW4`, `mainDegreeW4`, `prob`,
`uniformLaw`, `unitDensityW4`, and the three listed auxiliaries.
The latter are only certificates that 2, 3, and 4 are at least
two, printed in `scratch/BlindCheck.lean` and read in full.
