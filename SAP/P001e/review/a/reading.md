# Blind reading of the Challenge

Saved before opening `claims.json` or `record.json`. This reads the proposition
types, not the promises in the Challenge docstrings. There are 19 theorem stubs,
`SAP.P001e.T77` through `SAP.P001e.T95`. Each imports only the supplied Defs, which
ultimately import Mathlib. No Solution or Comparator was inspected.

## Shared notation and expansion to Mathlib

All real arithmetic below is in the ordinary field of real numbers. Lean makes
division total (`x/0 = 0`); real-valued Bochner integrals are zero when their
integrands are not integrable. These conventions must be checked against the
hypotheses, rather than silently interpreted as existence assertions.

* Write `P_mu(A) = (mu A).toReal`. This is Mathlib's extended nonnegative measure
  converted to a real; infinity is converted to zero. All probability spaces in
  the statements explicitly have total mass one. Restricted respondent measures
  are finite, and fitted laws are explicitly asserted to have mass one.
* `E_mu Z` is the Mathlib Bochner integral `integral mu Z`; a set integral is an
  integral under `mu.restrict A`. An unspecified measure in an integral over real
  `y` is Lebesgue measure. `Integrable` includes almost everywhere strong
  measurability and a finite integral of the norm, not just existence of a
  conditionally convergent improper integral.
* `CM(mu,X,Z,m)` means: `m` is measurable, `Z` and `m o X` are integrable under
  `mu`, and, for every measurable subset A of the codomain of X,
  `integral_{X in A} Z dmu = integral_{X in A} m(X) dmu`. It is a supplied
  conditional-mean version with equality of integrals, not an extra primitive.
* `CI(mu,X;V,W)` means: for every measurable A and B in the respective codomains
  of V and W,
  `E[1_{V in A,W in B} | sigma(X)] = E[1_{V in A}|sigma(X)] E[1_{W in B}|sigma(X)]`
  mu-almost everywhere. Here `sigma(X)` is `MeasurableSpace.comap X` of the given
  codomain sigma-algebra. It uses Mathlib `condExp`. That operator is zero if the
  conditioning sigma-algebra is not subordinate, its trimmed measure is not
  sigma finite, or its argument is not integrable. Wherever this abbreviation is
  used, X is explicitly measurable, mu is a probability measure, and the relevant
  indicators are measurable or almost everywhere measurable and bounded. For
  process-valued V the codomain is the product measurable space on `R -> R`.
* `IID(mu,Z)` means every Z_i is measurable, their generated sigma-algebras are
  mutually independent, and every Z_i has the same image measure as Z_0. More
  explicitly, for every finite set of indices and measurable events in their
  separate generated sigma-algebras, the probability of their intersection is
  the product of their probabilities. `IdentDistrib` also includes almost
  everywhere measurability of both functions, as well as equality of image
  measures.
* `bar Z_n = (sum_{i=0}^{n-1} Z_i)/n`; at n=0 the definition is zero. Convergence
  in probability to c means: for every real epsilon>0, the real probabilities
  `P_mu{epsilon <= dist(Z_n,c)}` tend to zero along n tending to infinity.
* `C(mu,X,Z,x) = (integral_{X=x} Z dmu)/P_mu{X=x}`. Thus a zero-mass cell has
  value zero under this definition, rather than a chosen conditional version.
* `record(y,r)=yr-99(1-r)`; `complete(z,r,c)=zr+c(1-r)`;
  `realize(y0,y1,d)=y1*d+y0*(1-d)`.
* `lower(y,d,a,b)=yd+a(1-d)-y(1-d)-bd` and
  `upper(y,d,a,b)=yd+b(1-d)-y(1-d)-ad`.
* `Q(X,Y,b)=sum_i (Y_i-(Xb)_i)^2`. The supplied least-squares coefficient
  function is `(X^T X)^(-1) X^T Y`. Mathlib's square matrix inverse is
  `Ring.inverse(det A)` times its adjugate, and is the zero matrix for a singular
  matrix. The concrete OLS statements separately assert nonzero determinant.
* `ell(X,Y,b,s)=-n log(s)-(n/2)log(2*pi)-Q(X,Y,b)/(2*s^2)`.
  Mathlib's real logarithm is total, but the maximizing-scale statement compares
  only positive scales.
* `Fhat(X,nu)=(1/n) sum_i (nu_i product delta_{X_i})`, where the scalar is formed
  in the extended nonnegative reals and acts on measures.
* An infinite real sum `sum'` is Mathlib's unconditional sum over all finite
  subsets; if not summable its defined value is zero. The countable-cell
  statement supplies integrability conditions intended to justify summability.

Mathlib sources followed: `Basic/ENNReal/Basic.lean` (`toReal`, `toReal_top`),
`MeasureTheory/Integral/Bochner/Basic.lean` (`integral`),
`MeasureTheory/Function/ConditionalExpectation/Basic.lean` (`condExp`),
`Probability/IdentDistrib.lean` (`IdentDistrib`),
`Probability/Independence/Basic.lean` (`iIndepFun`),
`Probability/Independence/Kernel/IndepFun.lean` and `Kernel/Indep.lean`
(generated sigma-algebras, finite intersection factorization),
`Topology/Algebra/InfiniteSum/Defs.lean` (`HasSum`, `Summable`, `tsum`, generated
by the additive counterparts of the product definitions), and
`LinearAlgebra/Matrix/NonsingularInverse.lean` (`Matrix.inv`).

## T77

For every type Omega, natural parameter dimension tau, subset Theta of R^tau,
function Y:Omega->R, natural covariate dimension K, function X:Omega->R^K,
function g:R->R^K->R^tau->R, and proof that g(y,x,t)>=0 for every y,x and every
t in Theta, there exists a function L:Omega->Theta->[0,infinity) such that,
for every omega and parameter t in the subtype Theta, the real value of L(omega,t)
equals g(Y(omega),X(omega),t). The codomain is finite nonnegative reals, not
extended reals. There are no measurability, density-normalization, Gaussian,
nonempty-Theta, or probability-space assumptions or conclusions. The existential
L follows all these universal data; the pointwise equality follows L.

## T78

For every n,K in N with n>0, real n by (K+1) matrix X, vector Y in R^n, and
coefficient bstar in R^(K+1), assume bstar globally minimizes Q among all real
coefficient vectors and Qstar=Q(X,Y,bstar)>0. Then sstar=sqrt(Qstar/n) is positive,
sstar^2=Qstar/n, and for every coefficient vector b and real s>0,
`ell(X,Y,b,s)<=ell(X,Y,bstar,sstar)`. The matrix need not have an intercept column
or full rank. No uniqueness, residual-mean identity, or centered variance
identity is asserted. All data and the minimizer are universally quantified
before the conclusion, and b,s are universally quantified only in its last
conjunct.

## T79

For every n,K with n>0, every list X_i in R^K and every list of probability
measures nu_i on R, Fhat(X,nu) is a probability measure. Moreover, for every y in
R and then every x in R^K, its mass on
`{(z,w): z<=y and w_k<=x_k for every k}` equals
`(1/n) sum_i [1_{X_ik<=x_k for every k} * nu_i((-infinity,y])]`, with measure
masses converted to reals. No fitted parameter common to the nu_i, density,
population law, or functional of Fhat is quantified.

## T80

This is a conjunction of a universal probability theorem and a closed example.
First, for every measurable Omega, probability measure mu, measurable Y,R:
Omega->R, reals a,b, and pointwise hypotheses `a<=Y(omega)<=b` and
`R(omega)=0 or R(omega)=1`, define
`L=E_mu complete(record(Y,R),R,a)` and
`U=E_mu complete(record(Y,R),R,b)`. Then `L<=E_mu Y<=U`. For every real c in
[L,U], there exists Y':Omega->R which is measurable, is pointwise in [a,b], has
expectation c, and satisfies the equality of functions
`record(Y',R)=record(Y,R)`. The completion Y' may depend on c and all preceding
data; R is unchanged. There is no separate a<=b or positive response-rate
assumption; the probability space and bounded Y imply a<=b.

Second, on six indices the recorded vector is [1,-99,1,0,1,-99] and response
vector is [1,0,1,1,1,0]. The arithmetic means after completing with 0 and 1
are respectively 1/2 and 5/6. No equality of observable-law distributions is
used in place of the stronger pointwise preservation of records.

## T81

There are no hypotheses. On indices 0,...,5 the score vector is
[33,14,73,35,78,70]/100. Respondents are {0,2,3,4}, nonrespondents {1,5}.
`UniqueNearest(i,j,C)` means j belongs to C and, for every k in C other than j,
the score distance from i to j is strictly smaller than that from i to k.

The eight asserted distances, in the order (donor,recipient), are
(0,1)=19/100, (3,1)=21/100, (2,1)=59/100, (4,1)=64/100,
(0,5)=37/100, (2,5)=3/100, (3,5)=35/100, (4,5)=8/100.
Donor 0 is uniquely nearest for recipient 1, and donor 2 uniquely nearest for
recipient 5. For every respondent k other than 0, the distance from recipient 1
to respondent 3 is no larger than the distance to k; its distance exceeds the
nearest distance by 2/100. With donor vector [0,0,2,3,4,2] and source outcomes
[2,0,3,10,12,0], the completed outcome vector is [2,2,3,10,12,3] and has mean 16/3.

## T82

For every pair of measurable spaces Omega,E, probability measure mu, measurable
X:Omega->E and R:Omega->Bool, assume `0<P_mu(R=true)<1`. There exist first a
function p:E->R and then a family kappa:E->Measure(Bool) such that:

1. p is measurable and 0<=p(x)<=1 for every x.
2. Every kappa(x) is a probability measure, and for every measurable B subset
   Bool the extended-real-valued function x->kappa(x)(B) is measurable.
3. For every measurable A subset E and every measurable B subset Bool,
   `mu{X in A,R in B}=integral_A kappa(x)(B) d(mu.map X)(x)`, an equality of
   extended nonnegative reals using the nonnegative integral.
4. For every x, both kappa(x)({true}) converted to a real and the expectation
   under kappa(x) of the real indicator of true equal p(x).
5. `CM(mu,X,1_{R=true},p)` holds.
6. For every m:E->R, if `CM(mu,X,1_{R=true},m)` holds, then
   `m(X)=p(X)` mu-almost everywhere.
7. For every real q, `q not in [0,1]` iff `1<q or q<0`.

Separately, outside that universally quantified block, for every real q,
`0<q or q<1`. This last statement is a tautological disjunction, not the assertion
that both inequalities hold. E has no standard-Borel or countability assumption.

## T83

For every measurable Omega,E, probability measure mu, measurable X:Omega->E,
measurable Y,R:Omega->R, and integrable Y, assume R is binary pointwise. For
every p:E->R with `CM(mu,X,R,p)`, assume there exists a real epsilon>0 such that
`epsilon<p(X(omega))` for every omega, and assume `CI(mu,X;Y,R)`. Then
`E_mu Y=E_mu[record(Y,R)*R/p(X)]`. All these objects and hypotheses precede the
conclusion. There is no upper bound on p explicitly assumed; the conditional
mean property gives the appropriate almost everywhere bound. The pointwise
lower bound prevents any evaluated reciprocal from dividing by zero.

## T84

There are no hypotheses. Let x=[-1,0,1], N=[4,4,4], r=[2,3,2], and outcome sums
S=[3/4,3/2,3/4]. Let `q(a,b,x)=exp(a+b*x)/(1+exp(a+b*x))` and
`l(a,b)=sum_j [r_j log q(a,b,x_j)+(N_j-r_j)log(1-q(a,b,x_j))]`.
For every real a,b, `l(a,b)<=l(log(7/5),0)` and equality holds iff
`a=log(7/5) and b=0`. For every j there are strictly between zero and N_j
respondents, and the fitted q is 7/12. The IPW expression
`sum_j S_j/q(log(7/5),0,x_j)/12` is 3/7, while the cell plug-in expression
`sum_j N_j*S_j/r_j/12` is 5/12. The two are unequal and their difference is 1/84.
This asserts a particular unequal pair; it does not directly contain a
universally quantified negation of any general estimator claim.

## T85

For every finite type E with decidable equality, functions N,r,q:E->R and real
n, assume n>0, every N_x>0, every r_x>0, every q_x>0, and `sum_x N_x=n`.
For any S:E->R abbreviate
`I(S)=sum_x S_x/q_x / n`, `P(S)=sum_x N_x*S_x/r_x / n`,
`W=sum_x r_x/q_x / n`, and `H(S)=I(S)/W`. Then:

1. For every S, `I(S)-P(S)=sum_x S_x*(1/q_x-N_x/r_x)/n`.
2. `[for every S, I(S)=P(S)]` iff `[for every x, q_x=r_x/N_x]`.
3. If every q_x=r_x/N_x, then W=1 and, for every S, both I(S)=P(S) and H(S)=P(S).

S is universally quantified separately in each conclusion, and saturation is a
hypothesis only in the third conjunct, not in the criterion's other direction.
There is no r<=N, integrality of N or r, q<=1, observed sample, or relation between
S and individual responses. An empty E cannot satisfy positive n and the total
size equality. The stabilized denominator is certified to be one where used in
the equality conclusion.

## T86

For every measurable Omega,E, probability mu, measurable X:Omega->E and
R:Omega->R with R binary pointwise, and every p:E->R with `CM(mu,X,R,p)`, assume
there is epsilon>0 with `epsilon<p(X(omega))<=1` for all omega. Then
`CM(mu,X,R/p(X),constant 1)`, `E_mu[R/p(X)]=1`,
`E_mu[1/p(X)]>=1`, and
`E_mu[1/p(X)]=1 iff p(X)=1 mu-almost everywhere`.
The first conjunct includes integrability of the response-weighted reciprocal;
the bounded reciprocal itself is integrable by the hypotheses. There is no
sequence, fitted p, finite sample estimator, or consistency conclusion.

## T87

This is the conjunction of two separately universally quantified statements;
their data and hypotheses are not shared across the conjunction.

Stable component: for every measurable Omega,E, probability mu, measurable X,
measurable real Y,R, integrable Y, pointwise binary R, and positive masses of
both R=1 and R=0, take any m:E->R with
`CM(mu.restrict{R=1},X,Y,m)`. Then
`CM(mu.restrict{R=1},X,record(Y,R),m)` and
`CM(mu,(R,X),record(Y,R),h)`, where
`h(r,x)=m(x)` if r=1 and -99 otherwise. m is required to be integrable when
composed with X only under the respondent restricted measure in the hypotheses.

MAR component: for every measurable Omega,E, probability mu, measurable X,
measurable real Y,R, integrable Y, and pointwise binary R, take p,m:E->R.
Assume `CM(mu,X,R,p)`, some epsilon>0 with `epsilon<p(X(omega))` for every
omega, `CI(mu,X;Y,R)`,
`CM(mu.restrict{R=1},X,record(Y,R),m)`, and additionally full-population
integrability of m o X. Then `CM(mu,X,Y,m)`. The respondent version is supplied;
there is no existence assertion for m in either component.

## T88

For every measurable Omega, probability mu, sequences of functions Y0_i,Y1_i,D_i
from Omega to R, assume every coordinate of each sequence is measurable. Take
reals a,b with a<=b. Assume, for each i, almost surely Y0_i and Y1_i lie in [a,b]
and D_i is 0 or 1. Assume `0<P_mu(D_0=1)<1`. Assume the observed pairs
`(realize(Y0_i,Y1_i,D_i),D_i)` are IID in the exact sense above. Independence of
the full latent triples is not assumed.

Define Y_i=realize(Y0_i,Y1_i,D_i), L_i=lower(Y_i,D_i,a,b),
U_i=upper(Y_i,D_i,a,b), p=P_mu(D_0=1), m1=C(mu,D_0,Y_0,1), and
m0=C(mu,D_0,Y_0,0). Here Y_0 in the cell-mean expressions denotes the observed
outcome at sample index zero, not the untreated potential outcome. Put
`ell=m1*p+a*(1-p)-[m0*(1-p)+b*p]` and
`u=m1*p+b*(1-p)-[m0*(1-p)+a*p]`. The conclusion is the conjunction:

1. E_mu L_0=ell and E_mu U_0=u; u-ell=b-a.
2. E_mu(Y1_0-Y0_0) belongs to [ell,u].
3. For every t in [ell,u] there exist measurable functions A0,A1:Omega->R
   such that, almost surely, both lie in [a,b] and
   `realize(A0,A1,D_0)=Y_0`, and E_mu(A1-A0)=t. They may depend on t.
4. For every natural n>0, E_mu(bar L_n)=ell and E_mu(bar U_n)=u.
5. bar L_n converges in probability to ell, and bar U_n to u, meaning for every
   epsilon>0 the probabilities of absolute errors >=epsilon tend to zero.

## T89

There are no hypotheses. All probabilities are the finite sums of weights 1/6
on six states. A finite conditional independence assertion for variables V,W
given X means: for every conditioning value x, value v and value w, if P(X=x)>0
then `P(X=x,V=v,W=w)*P(X=x)=P(X=x,V=v)*P(X=x,W=w)`.
These are singleton tests on finite-supported variables, so they express the
usual conditional independence in this example.

Let Z=[0,1,1,0,1,1], X=[0,0,1,0,1,1], D=[0,0,0,1,1,1],
X0=[0,0,1,0,0,1], X1=[0,1,1,0,1,1]. Then (Z,Z,X1,X0) is independent of D,
expressed as finite conditional independence given a constant unit-valued
variable. Also P(D=1)=1/2, realize(X0_i,X1_i,D_i)=X_i for every i, and
E(Z-Z)=0. The pair (Z,Z) is not conditionally independent of D given X.
P(Z=1,X=1,D=1)=1/3, and P(X=0)=P(X=1)=1/2. For every x in {0,1} and every
d in {0,1}, P(X=x,D=d)>0. The conditional means of Z in cells
(X,D)=(0,1),(1,1),(0,0),(1,0) are respectively 0,1,1/2,1. The contrast of
the two conditional-on-D mean functions averaged with marginal X weights is
`(0*(1/2)+1*(1/2))-((1/2)*(1/2)+1*(1/2))=-1/4`.

## T90

There are no hypotheses. Put s(d)=1 if d=1/2, and s(d)=0 otherwise. The
pushforward of Lebesgue measure restricted to [0,1] under d->(0,d,0) equals
its pushforward under d->(s(d),d,0). Additionally
s(1/2)-s(0)=1, s(1/2)-s(1/4)=1, and 0 differs from 1. The tuples are ordinary
real triples. The probability space has total mass one since [0,1] has length
one; the spike is Borel measurable. The proposition does not explicitly assert
process independence, support, or continuity conditions.

## T91

For every measurable Omega and countable measurable E whose singletons are
measurable, probability mu, measurable X:Omega->E, measurable D:Omega->R,
and dose-indexed potential process Y:R->Omega->R, assume Y_t is measurable and
integrable for every real t, and that the diagonal observed outcome
Z(omega)=Y_{D(omega)}(omega) is separately measurable and integrable. Assume
`CI(mu,X;omega->(t->Y_t(omega)),D)`. For every pair of real doses d,dprime,
assume for every x with P(X=x)>0 that both
P(X=x,D=d)>0 and P(X=x,D=dprime)>0. No distinctness of d,dprime is required.

Then for every such positive-mass x,
C(mu,X,Y_d,x)=C(mu,(X,D),Z,(x,d)) and likewise for dprime. Define
`S(t)=sum'_x [if P(X=x)>0 then C(mu,(X,D),Z,(x,t))*P(X=x) else 0]`.
The additional conclusions are E_mu Y_d=S(d), E_mu Y_dprime=S(dprime), and
`E_mu(Y_dprime-Y_d)=S(dprime)-S(d)`. All doses and the positivity assumption
follow the process and its measurability, all-dose integrability, diagonal
integrability and independence assumptions. No positive-mass assertion is made
for zero-mass covariate cells, which are explicitly assigned zero summands.

## T92

There are no hypotheses. The six rows of the regression have
Y=[2,5,3,10,2,0], D=[1,0,1,1,1,0], X1=[1,8,10,3,5,7],
X2=[7,2,3,1,2,0] and design rows [1,D_i,X1_i,X2_i]. The determinant of X^T X
is a unit of R (equivalently nonzero), and the computed OLS vector equals
`b=[13563,6178,-759,-1778]/2437`.
Write f(x1,x2,d)=b0+b1*d+b2*x1+b3*x2. For any supplied vector z, define
`Partial(z)=(1/6)sum_i [if D_i=1 then Y_i-f(z_i,X2_i,0)
else f(z_i,X2_i,1)-Y_i]` and
`Full(z)=(1/6)sum_i [f(z_i,X2_i,1)-f(z_i,X2_i,0)]`.
At z=[1,8,9,3,5,7], Partial is 12103/4874 and Full is 6178/2437. Their
difference is -253/4874 and they are unequal. Thus the evaluation vector has
9 in its third row while the actual fitted design has 10.

## T93

First, for every n>0, vectors Y,D,g in R^n and beta in R, assume D_i is binary
for every i and that the two sums
`sum_i (Y_i-g_i-beta*D_i)` and `sum_i D_i*(Y_i-g_i-beta*D_i)` are both zero.
Then both
`sum_i [D_i*(Y_i-g_i)+(1-D_i)*(g_i+beta-Y_i)]/n=beta` and
`sum_i [(g_i+beta)-g_i]/n=beta`. g is an arbitrary supplied vector; deriving
these normal equations from a minimization problem is not a conclusion.

Separately, for the fixed design, outcomes, coefficient vector, and Partial/Full
definitions of T92, the determinant is nonzero, the computed OLS vector equals
b, and Partial(X1)=b1, Full(X1)=b1, and b1=6178/2437. Here X1 has third entry
10, not 9. No population conditional treatment-effect assertion is present.

## T94

This is a conjunction of two separate universal statements.

Population component: for every measurable Omega, probability mu, natural
dimensions K,tau, X:Omega->R^K, real D,Y0,Y1, assume X and D are measurable and
Y0,Y1 are integrable. Assume D is binary pointwise. For every p:R^K->R assume
CM(mu,X,D,p) and some epsilon>0 with
`epsilon<p(X(omega))<1-epsilon` for every omega. Assume
CI(mu,X;(Y0,Y1),D). Take arbitrary real-valued
g(y,d,x,theta) and theta in R^tau and set
`m(d,x)=integral_R y*g(y,d,x,theta) dy`. Assume, for each d in {0,1},
for mu-almost every omega, that inner integrand at (d,X(omega),theta) is
integrable. Assume
`CM(mu,(D,X),realize(Y0,Y1,D),(d,x)->m(d,x))`, which in particular supplies
global measurability of that integrated mean function and integrability of its
observed composition. Assume in addition that m(0,X) and m(1,X) are integrable
under the population measure. Then E_mu Y0=E_mu m(0,X) and
E_mu Y1=E_mu m(1,X). There are no positivity or normalization assumptions on
g as a density; its correct conditional mean is supplied directly.

Estimator component: for every n,K,tau with n>0, every g as above, real dose d,
list X_i in R^K, parameter theta, and separate covariate x in R^K, assume the
inner integrand y*g(y,d,X_i,theta) is integrable for every i and
y*g(y,d,x,theta) is integrable. Then the function named fittedPotentialAverage
equals `(sum_i integral_R y*g(y,d,X_i,theta)dy)/n` (its defining formula),
and `(sum_{i=0}^{n-1} m(d,x))/n=m(d,x)`. It does not assert that these two
expressions are equal to each other, or that either estimator is consistent.

## T95

There are no hypotheses. Retain the score vector and distances from T81, and
the Y,D vectors from T92. The T81 distance and hot-deck-nearest facts are
asserted again. In addition, the unique nearest members of the opposite arm
{1,5} for treated indices 0,2,3,4 are respectively 1,5,1,5. The T81 donor facts
give the other direction: treated donor 0 for control 1, and treated donor 2
for control 5. The combined donor vector is [1,0,5,1,5,2].

The completed control column keeps observed control outcomes and otherwise
takes the donor outcome, producing [5,5,0,5,0,0]. The completed treatment column
keeps observed treated outcomes and otherwise takes the donor outcome,
producing [2,2,3,10,2,3]. Their means are 15/6 and 22/6 respectively, and the
mean of their paired differences is 7/6.
