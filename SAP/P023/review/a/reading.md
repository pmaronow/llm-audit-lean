# Blind reading of the Challenge statements

This file was written from `SAP/P023/Defs.lean`, all six `Defs/Part*.lean`
files, and `Challenge/Part1.lean`, before opening `claims.json` or
`record.json`. The notation below expands the SAP predicates; it does not
take the Challenge docstrings as the statements.

## Common objects and conventions, expanded to Mathlib

All scalars are real unless otherwise specified. A finite index type is
an arbitrary type with a `Fintype` instance, not necessarily nonempty.
Sums range over every element of that type. `Fin n` has indices
0 through n-1. Natural subtraction is truncated, although the design
branches use `j-1` only after `j>=2`. Natural division in `(J+1)/2` is
integer division. Natural ceiling is the least nonnegative integer above
its argument. Absolute value, square root, logarithm and pi are Mathlib's
real operations. In particular real division by zero is defined as zero.

For a real design matrix X with finite row and column types,
`predict X c i = sum_j X_ij c_j`, and `dot a b = sum_i a_i b_i`.
`IsOLS X y c` means every column is orthogonal to y-Xc:
`for every j, sum_i X_ij (y_i-sum_l X_il c_l)=0`.
`FullRank X` means `for every c, [(for every i, (Xc)_i=0) implies c=0]`.
`olsCoefficients` is a Hilbert-choice coefficient vector satisfying those
normal equations, if one exists; the definition itself asserts neither
existence nor uniqueness. The polynomial matrix of degree J has columns
`1,d,x,x^2,...,x^J` (only `1,d` if J=0). Write `b_J(x,d;y)` for its chosen
coefficient on d, i.e. `polynomialOLS J x d y`.

Write C_k(x)={i:-k<x_i<=k}. `TwoParty x d` means, for every i,
`-1<=x_i<=1`, `d_i=0 or d_i=1`, `x_i>0 implies d_i=1`, and
`x_i<0 implies d_i=0`; either party value is allowed at a tie.
`Condition1 k x` means there exists an i with `0<x_i<k` and there
exists an i with `-k<x_i<0`. These witnesses need not be specified in
advance. Let n1=sum_{C_k} d_i and n0=sum_{C_k}(1-d_i). Then
`R_k(x,d;y)=sum_{C_k}d_i y_i/n1-sum_{C_k}(1-d_i)y_i/n0` is `rd`.
`Localized k x E` means `for all outcome vectors y,y', if y_i=y'_i
for all i in C_k(x), then E(y)=E(y')`.

For k define q=ceil_N((1-k)/(2k)) and M=2q=`binCount k`.
For bin j=0, `inBin k 0 t` means `-M-1<=t/k<=-M+1`;
for j>0 it means `2j-M-1<t/k<=2j-M+1`. Its indicator is 0 or 1.
`binLabel k t` is `min(M,ceil_N((t/k+M-1)/2))`, valued in
{0,...,M}; `centralLabel k` is q. The printed coarsened design has
columns `1,d,1_bin1,...,1_binM`, omitting the bin-0 dummy.
For any finite label type and labels B_i, let I_j={i:B_i=j},
`bar(z)_j=sum_{I_j}z_i/|I_j|`, and `tilde(z)_i=z_i-bar(z)_{B_i}`.
`IsBinOLS B d y a beta` means
`for every j, sum_{i:B_i=j}(y_i-a_{B_i}-beta*d_i)=0`, and
`sum_i d_i(y_i-a_{B_i}-beta*d_i)=0`.
`CoarsenedOLS k x d y beta`, abbreviated CO, means there exists a real
bin-intercept vector a satisfying these equations for B_i=binLabel(k,x_i).
No full-rank condition on all dummy columns is required.

For a real measure mu, write E_mu f for the real Bochner integral.
`ProbabilityLaw mu` means mu(univ)=1 in the extended nonnegative reals.
`MarginSupport mu` means mu(R\[-1,1])=0. `party t=D(t)=1_{t>=0}`.
`marginLaw nu=mu` is the pushforward of the pair law nu by first projection.
`ConditionalMean nu m` means both Y and m(X) are integrable and, for
every measurable real t bounded on the whole real line,
`integral t(X)Y dnu=integral t(X)m(X) dnu`.
Mathlib integrability includes almost-everywhere strong measurability and
finite integral of the norm. A real Bochner integral of a nonintegrable
function is defined to be zero. The measurable first projection is a
genuine pushforward; Mathlib's map has a fallback for non-a.e.-measurable
maps, so measurability of witness maps matters.

For degree J, `IsProjection mu J p` means p is a real polynomial of
natural degree <=J and, for every natural j<=J,
`E_mu[(D-p)x^j]=0`. Here even the zero polynomial has natural degree 0.
Let p_J be a Hilbert choice satisfying this predicate, r_J=D-p_J,
v_J=E_mu r_J^2, A_J=E_mu|r_J|/v_J, and
`B_J(h)=E_mu(r_J*h)/v_J`. These are respectively `projection`,
`popResidual`, `residualVariance`, `amplification`, `biasFunctional`.
The population coefficient b_J(mu,m) is the d coefficient of a Hilbert
choice satisfying `for every column j, E_mu[X_j(m-Xc)]=0`,
with X=(1,D,x,...,x^J). `MomentPositiveDefinite mu J` means for every
nonzero real c in R^(J+2), `E_mu[(c0+c1 D+sum_{j=1}^J c_{j+1}x^j)^2]>0`.
`populationRD mu m k`, abbreviated rho_mu(m,k), is
`integral_(0,k] m dmu / mu((0,k]).toReal
 - integral_(-k,0) m dmu / mu((-k,0)).toReal`.
In particular this population definition excludes X=0 on both sides.
The `toReal` of an infinite extended mass is zero.

`U=uniformMargins` is half Lebesgue measure restricted to [-1,1].
`noiseLaw` gives masses 1/2 to -1/10 and +1/10. `W(mu,h)=witnessLaw mu h`
is the pushforward of mu times that independent noise law by
`(X,e)->(X,1/2+h(X)+e)`.
`predictionRisk nu f=integral(Y-f(X))^2 dnu`.
`fittedRisk nu J` is the real infimum of these risks over all vectors c
in the polynomial matrix (1,D,x,...,x^J), not over arbitrary predictors.
`supError h p=sup_{[-1,1]}|h-p|` uses Mathlib's real conditional supremum;
`rmsError mu h p=sqrt(E_mu[(h-p)^2])`. Real suprema/infima have their
usual extremal meaning for nonempty appropriately bounded sets, which
must be checked, rather than silently assumed.

For a finite design, regress d on (1,x,...,x^J) using the same normal-
equation choice, put r_i=d_i-fitted_i, V=sum_i r_i^2 and w_i=r_i/V.
These are `finiteResidual`, its squared norm and `finiteWeight`.
The coarsened weights are
`u_i=1_{C_k}(d_i/n1-(1-d_i)/n0)`.

For any measurable sample space Omega and measure P,
`Z_N ->_P z` means: for every real epsilon>0,
`P{omega:|Z_N(omega)-z|>epsilon}->0` in the topology of [0,infinity].
There is no separate measurability requirement on Z in that predicate.
`IIDSample P nu sample` means P is a probability law, every sample_i
is measurable, its pushforward law is nu for every i, and the entire
countable family is independent in Mathlib's `iIndepFun` sense (finite
joint events factor). The sample estimators use the first N observations,
indexed by Fin N, with d_i=D(X_i).
Write `OLSvalid(degrees)` for the assumption that the P-mass of
non-full-rank matrices (1,D,X,...,X^(degrees N)) tends to zero.
Write `RDvalid(k)` for the assumption that the P-mass of samples with
n1<=0 or n0<=0 in C_(k_N) tends to zero. These are precisely
`OLSAdmissible` and `RDAdmissible`; they are assumptions about designs,
not estimator convergence assumptions.

## T1: no hypotheses; a specified six-observation example

Let x=(-3/4,-1/4,-1/400,1/400,1/4,3/4),
d=(0,0,0,1,1,1), k=1/200, and
y=(37/80,39/80,3999/8000,4801/8000,49/80,51/80).
Let y'=y+(1/100)e_5 and
w=(20299/139202,-59901/139202,-49800/69601,49800/69601,
59901/139202,-20299/139202).
The theorem asserts all of the following:

* TwoParty, Condition1, and full rank of (1,d,x); y is exactly fitted by
  coefficients (1/2,1/10,1/20).
* For every real outcome vector z, b_1(x,d;z)=sum_i w_i z_i.
  The values on y,y' are 1/10 and 1371721/13920200; their difference is
  the nonzero number -20299/13920200.
* y and y' agree on C_k; their only change is the displayed change at 5.
  Both RD values equal 401/4000. M=200 and bin labels are
  (25,75,100,100,125,175).
* CO holds at beta=401/4000 for y and y'. For every beta, CO for either
  outcome vector implies beta=401/4000. Every entry of both outcomes
  is strictly between 0 and 1. The polynomial estimator is not Localized.
* C_k={2,3}; R_k(y)=y_3-y_2; the RD estimator is Localized.
  For every pair of outcome vectors z,z' and every beta,beta', agreement
  on C_k together with CO(z,beta) and CO(z',beta') implies beta=beta'.

## T2: no hypotheses; a specified sixteen-observation example

Let x=(-1,-7/8,-3/4,-5/8,-1/2,-3/8,-1/4,-1/8,
1/8,1/4,3/8,1/2,5/8,3/4,7/8,1), d=0 on indices 0..7 and 1 on 8..15,
k=1/5, and y_i=1/2+d_i/10+x_i/20+x_i^7/100.
(This is the explicit rational vector named `degree7Y`.)
Let y'=y+(1/100)e_15 and
w=(-175,725,-685,-643,554,1289,239,-2911,2911,-239,-1289,
-554,643,685,-725,175)/1607.
The assertions are TwoParty, Condition1, full rank of (1,d,x,...,x^7),
and exact fit by (1/2,1/10,1/20,0,0,0,0,0,1/100).
For every z the d coefficient is sum_i w_i z_i. Its values on y,y' are
1/10 and 3249/32140, differing by the nonzero number 7/6428.
The two outcomes agree on C_k and have exactly the indicated change.
Both RD estimates and their unique CO coefficients are
11796481/104857600; CO solutions at this coefficient exist for both.
M=4 and labels are (0,0,0,0,1,1,1,2,2,3,3,3,4,4,4,4).
Every outcome is in (0,1), the polynomial estimator is not Localized,
and every w_i is nonzero. Finally C_k={7,8} and RD(y)=y_8-y_7.

## T3: conjunction of eight universal statements/examples

1. **PrintedBinEquivalence.** For every finite type, k with 0<k<1,
   x,d,y satisfying TwoParty, and every beta, CO(k,x,d,y,beta) iff
   there exists a printed coarsened-regression coefficient vector c
   satisfying all its normal equations and having d coefficient beta.
2. **CoarsenedWeights.** For every finite type, 0<k<1, TwoParty x,d,
   outcome y, positive n1,n0, and every beta satisfying CO,
   beta=sum_i u_i y_i=R_k(y). Every outside-window u_i is zero;
   an inside winner has weight 1/n1 and an inside loser -1/n0.
3. **CoarsenedLocalization.** For every finite type, 0<k<1, TwoParty
   x,d, positive n1,n0, outcome vectors y,y' agreeing on C_k, and
   beta,beta' with the respective CO equations, beta=beta'.
4. **FinitePolynomialWeights.** For every finite type with decidable
   equality, every J>=1, and every TwoParty full-rank polynomial
   design x,d: sum r_i d_i=V>0; sum r_i x_i^j=0 for every natural
   j<=J; for every y, b_J(y)=sum r_i y_i/V=sum w_i y_i;
   sum w_i=0, sum w_i x_i^j=0 for every 1<=j<=J, sum w_i d_i=1.
   For every y, i, and real delta, changing y_i by delta changes
   b_J by exactly w_i delta.
5. **FiniteNonlocality.** Universally quantify finite type with
   decidable equality, J>=1, 0<k<1, TwoParty full-rank x,d, existence
   of at least one d=1 and one d=0, and positive close n1,n0.
   There are at most J distinct negative x values with w_i=0 and at
   most J distinct positive x values with w_i=0. If there are more
   than 2J distinct nonzero x values outside C_k, then there exist an
   outside index i and two outcome vectors y,y' equal at all other
   indices and on C_k, with different polynomial estimates but equal
   RD estimates. For every pair of CO coefficients of these outcomes,
   positive close n1,n0 imply their equality. No range restriction on
   these existential outcome vectors is imposed.
6. **ConditionalMoments.** For every finite type, measurable space
   Omega, probability P, J>=1, TwoParty full-rank fixed x,d, real
   alpha,beta, any real function h, and integrable outcomes Y_i on
   Omega with E_P Y_i=alpha+beta*d_i+h(x_i):
   E_P b_J(Y)-beta=sum r_i h(x_i)/V. For every polynomial p of degree
   <=J matching h at every observed x_i, E_P b_J(Y)=beta.
   Let u_i=Y_i-(alpha+beta*d_i+h(x_i)). If every u_i^2 is integrable
   and E_P(u_i u_l)=0 for every distinct pair i,l, then
   E_P[(b_J(Y)-E_P b_J(Y))^2]=sum_i w_i^2 E_P u_i^2.
   For every i and real s>0, w_i!=0 implies w_i^2*s>0.
7. **UniformIllustration.** Under U, for every real x,
   p_1(x)=1/2+3x/4 and
   p_7(x)=1/2+(11025x-40425x^3+63063x^5-32175x^7)/4096.
   v_1=1/16, v_7=1225/65536;
   r_1(9/10)/v_1=-14/5 and r_7(9/10)/v_7=-20283449/6125000.
   E_U[1_{|x|>=1/2}r_1^2]/v_1=1/8 and
   E_U[1_{|x|>=1/2}r_7^2]/v_7=572158921/10276044800.
   For m1=1/2+D/10+x/20 and m7=m1+x^7/100,
   b_1(U,m1)=b_7(U,m7)=1/10. For every 0<k<=1 their population
   RD values are 1/10+k/20 and 1/10+k/20+k^7/400, respectively;
   both tend to 1/10 as k tends to zero from above.
8. **SharedConsistency.** For every measurable Omega, P, any sample
   sequence, fixed J, bandwidth sequence k, and real beta, assume
   P is a probability, J>=1, every k_N>0, OLSvalid(const J), RDvalid(k),
   sample polynomial ->_P beta, and sample RD ->_P beta. Then their
   difference ->_P 0. IID, k_N->0 and N*k_N->infinity are not hypotheses
   of this component.

## T4: a clipped-linear uniform family and its sample limits

Define s_(a,eta)(x)=a max(-1,min(1,x/eta)).
For every a>0 and 0<eta<=1: s is continuous, s(0)=0, s(-x)=-s(x)
for every x, and |s(x)-s(x')|<=(a/eta)|x-x'| for every x,x'.
Under W(U,s), the conditional mean is 1/2+s. For every 0<k<=eta,
rho_U(1/2+s,k)=a*k/eta, and its right limit at zero is zero.
For every J>=1,
`b_J(U,1/2+s)=2a-(a/v_J)*integral_[0,eta] r_J(x)(1-x/eta) dx`;
this displayed integral is **Lebesgue**, not an integral under U.
In particular b_1=2a(1-eta)^2. The U squared error of approximating s
by a(2D-1) is a^2 eta/3. For every J>=1 the infimum over polynomial
design coefficients of the U squared error in fitting 1/2+s lies
between zero and a^2 eta/3. For every fixed J>=1 and a>0,
b_J(U,1/2+s_(a,eta))->2a as eta decreases to zero.

At a=1/20, eta=1/10000, the degree-1 coefficient is
99980001/1000000000; the degree-7 coefficient is
4896723787999993532000048047999857/49000000000000000000000000000000000.
W(U,s)-almost every Y is in [7/20,13/20]; a^2 eta/3=1/12000000.

For every a>0 and 0<eta<=1, nu=W(U,s) is a probability with margin U;
the true mean risk is 1/100. For every J>=1, fitted risk F_J satisfies
`1/100<=F_J<=1/100+a^2 eta/3`; for every measurable f with integrable
squared error, `F_J-risk(f)<=a^2 eta/3`; and
`(F_J-1/100)/F_J<=100a^2 eta/3`.
If a=1/20, the degree-7 coefficient equals
`1/10-(4096/6125)eta+(6/5)eta^2-(33/25)eta^4
 +(858/875)eta^6-(143/490)eta^8`.

For every measurable Omega, P and IID sample from the specific law at
a=1/20, eta=1/10000, and every k with positive entries, k_N->0,
N*k_N->infinity, OLSvalid(const 1), OLSvalid(const 7), and RDvalid(k),
the sample degree-1 and degree-7 coefficients converge in probability
to the displayed rationals, while RD converges in probability to zero.

For every J>=1 and every nonzero x, r_J(-x)=-r_J(x); for every x>0
the degree-1 and degree-7 residuals equal 1/2 minus the odd polynomials
in their displayed projections. The two residual variances are as above.
For the specific law and every J>=1,
`(F_J-1/100)/F_J<=1/120000`.
For every real a, a^2 eta/3->0 as eta decreases to zero.
For every real a and natural J there exists c in R^(J+2) such that for
every real x, X(x)c=1/2+a(2D(x)-1).

## T5: a clustered-density family

Let T(c,w,x)=max(w-|x-c|,0)/w^2 and
`f_d(x)=d^4/2+(1-d^4)[T(1/2,d/2,x)+T(-1/2,d/2,x)]/2`.
The margin mu_d has density max(f_d,0) on [-1,1] relative to Lebesgue
measure. Define g_d for nonnegative x by these consecutive branches:
0 if x<1/2-d; 1/2-d-x if x<=1/2-d/2; x-1/2 if x<=1/2+d/2;
1/2+d-x if x<=1/2+d; 0 otherwise. Extend it oddly to negative x.
This g_d is exactly `clusterSmooth d`.

For every 0<d<=1/2: mu_d is a probability supported on [-1,1], gives
zero mass to {0}, and gives positive mass to every (a,b) with
-1<=a<b<=1. The function f_d is continuous on R and at least d^4/2
on [-1,1]. The function g_d is continuous, odd, vanishes at 0 and at
every x with |x|<=1/2-d, is 1-Lipschitz on R, and |g_d|<=d/2 on R;
its sup norm on [-1,1] is exactly d/2. The law W(mu_d,g_d) has
conditional mean 1/2+g_d. Its margin moments are
E X=E g_d=E[(D-1/2)g_d]=0, E XD=1/4,
E X^2=(1-d^4)(1/4+(d/2)^2/6)+d^4/3, and
E Xg_d=(1-d^4)(d/2)^2/6+2d^4(d/2)^3.
Its degree-1 population coefficient is
`-(1-d^4+6d^5)/(1-d^4+2d^2)`.
For every 0<k<1/2-d the population RD value is zero.
E g_d^2<=(d/2)^2.

At d=1/1000 the coefficient equals
-499999999999503/500000999999500, and W-almost every Y is between
799/2000 and 1201/2000. As d decreases to zero the coefficient tends
to -1. There is no real C such that for every 0<d<=1/2 its absolute
value is bounded by C*d/2.

For every 0<d<=1/2, nu=W(mu_d,g_d) is a probability with margin mu_d;
the true mean risk is 1/100 and the constant-1/2 risk is
1/100+E g_d^2. For every measurable f with integrable squared error,
constant risk minus risk(f)<=(d/2)^2. For every J>=1 the fitted
polynomial risk is at most constant risk, and for every such f its
improvement to risk(f) is also at most (d/2)^2.
For every natural J, the zero polynomial has natural degree <=J and
approximates g_(1/1000) within 1/2000 everywhere on [-1,1]. Finally
d/2 tends to zero as d decreases to zero.

## T6: one fixed continuous counterexample, not a changing-law family

U is a probability supported on [-1,1]. A_J(U)->infinity as J->infinity.
There exist a real C>=0 and natural J0 such that for every J>=J0 with
J>=1, `|A_J-(4/pi)log J|<=C`.
For every J>=1, the supremum of B_J(h), over all real functions h
continuous on [-1,1], h(0)=0, and |h|<=1 there, equals A_J.

There exist a **single** real function h and a natural degree sequence
l_m such that h is continuous on [-1,1], h(0)=0, |h|<=1/12 there,
and l is strictly increasing. For every m>=1,
B_(l_m)(h)>=m/4 and b_(l_m)(U,1/2+h)>=m/4.
For every J>=1, b_J(U,1/2+h)=B_J(h).
For every real B and every natural J0 there exists J>=J0 with
b_J(U,1/2+h)>=B. The mean 1/2+h is continuous, equals 1/2 at zero,
and lies in [5/12,7/12] on [-1,1]. Its coefficients along l_m tend to
positive infinity; its full sequence of coefficients does not tend to
zero. Its population RD tends to zero as k decreases to zero.
There is no real L bounding |h(x)-h(x')| by L|x-x'| for every pair
x,x' in [-1,1].

## T7: general population bias, constants, and fixed-design bias

First, for every pair law nu which is a probability with margin mu
supported on [-1,1] and integrable Y^2, every real alpha,beta, every
measurable h bounded on [-1,1], conditional mean
m=alpha+beta D+h, and every J>=1 with MomentPositiveDefinite(mu,J),
put b=b_J(mu,m), r=r_J and v=v_J. Then p_J satisfies its projection
normal equations, v>0, and for every polynomial p of degree <=J,
E(rp)=0. Also E r=0, E(rD)=v, and b=B_J(m).
For every polynomial p of degree <=J,
`b-beta=B_J(h)=B_J(h-p)`,
`|b-beta|<=A_J supError(h,p)`, and
`|b-beta|<=rmsError(mu,h,p)/sqrt(v)`.
A_J>=2. For every polynomial p of degree <=J agreeing with h mu-a.e.,
b=beta. For every real t>0,
`|b-beta|<=t iff |E(rh)|<=t*v`;
`A_J inf_{deg p<=J}supError(h,p)<=t` implies `|b-beta|<=t`;
and `inf_{deg p<=J}rmsError(mu,h,p)<=t sqrt(v)` implies the same.

Second, U is a probability supported on [-1,1]. For every J>=1,
`v_J=[choose(2n,n)/4^n]^2/4`, n=floor((J+1)/2).
Its projections of degree 1 and 7 are the functions displayed above;
v_1=1/16, v_7=1225/65536, E_U|r_1|=5/24, A_1=10/3,
1/sqrt(v_1)=4 and 1/sqrt(v_7)=256/35.
The strict rational bounds for A_7 are
47642006857252250/10000000000000000 < A_7
< 47642006857252260/10000000000000000.

Third, all of FinitePolynomialWeights from T3 holds with its stated
quantifiers and hypotheses. Finally, for every finite type, measurable
Omega, probability P, J>=1, TwoParty x,d with d_i=D(x_i) for every i,
full rank, real alpha,beta, any function h, and integrable outcomes
Y_i with E Y_i=alpha+beta*d_i+h(x_i), V>0 and
`E b_J(Y)-beta=sum_i r_i h(x_i)/V`.
The equality d=D at ties is an additional hypothesis of this final
component, but is absent from the general finite weights component.

## T8: repaired population and sampling asymptotics

Universally quantify, in order: measurable Omega; P, nu and sample;
alpha,beta,h and real c,delta,L,sigma2; the regularity assumptions
below; IIDSample(P,nu,sample); bandwidth sequence k with every k_N>0,
k_N->0 and N*k_N->infinity; RDvalid(k); OLSvalid(const J) for every
J>=1; and OLSvalid(degrees) for every degree sequence tending to infinity
which satisfies the rate below.

The regularity assumptions are: nu is a probability; its margin mu
is supported on [-1,1] with mu{0}=0; Y^2 is integrable;
c>0, 0<delta<=1, L>=0, sigma2>=0; for every measurable
A subset [-delta,delta], `c*Leb(A)<=mu(A)` in extended nonnegative
reals; h(0)=0 and h is L-Lipschitz on [-1,1]; nu has conditional
mean m=alpha+beta D+h; and for every such measurable A,
`integral_{X in A}(Y-m(X))^2 dnu<=sigma2*mu(A).toReal`.

Let lambda_J be the real infimum of `E_mu[(X_J a)^2]` over all
a in R^(J+2) satisfying sum_j a_j^2=1.
For a degree sequence l_N the rate means
`(l_N+2)^2/[N*lambda_(l_N)^3]->0` as N->infinity.
Let K=3(1+pi^4)/(4pi). The conjunction of conclusions is:

* For every J>=1, MomentPositiveDefinite(mu,J) and
  `v_J>=c*delta/[4(J+1)]`.
* For every J>=1 there exists a polynomial p of degree <=J with
  p(0)=0 and `supError(h,p)<=4KL/(J+1)`.
* For every J>=1, `|b_J(mu,m)-beta|<=8KL/sqrt(c*delta*(J+1))`;
  b_J(mu,m)->beta as J->infinity.
* For every fixed J>=1, the sample polynomial estimator converges in
  probability to b_J(mu,m).
* For every 0<k'<=delta, `|rho_mu(m,k')-beta|<=2Lk'`.
  The sample RD converges in probability to beta.
* For every epsilon>0 there exists J0 such that for every J>=J0
  with J>=1, the sample polynomial-minus-RD difference converges in
  probability to b_J(mu,m)-beta, and that limit has absolute value
  less than epsilon. J is fixed before this sample-size limit.
* For every sequence l_N->infinity satisfying the rate,
  samplePolynomial(N,l_N)-b_(l_N)(mu,m) converges in probability
  to zero, and samplePolynomial(N,l_N)-sampleRD(N) does likewise.
* There exists a degree sequence l with every l_N>=1, l_N->infinity,
  and the rate tending to zero.

## T9: a pair-indexed coarsened-regression identity

For every finite set S subset N x N, every 0<k<1, every x,d,y
defined on the subtype of pairs belonging to S, assume TwoParty x,d,
Condition1 k x, and a real beta satisfying CO. Put B_p=binLabel(k,x_p),
r=tilde(d), z=tilde(y), where means use all observed pairs in each bin.
Then for every observed pair p and every j in {0,...,M},
inBin(k,j,x_p) iff B_p=j. The central-bin observations are exactly C_k.
For every p outside C_k, r_p=0. The central residual norm
sum_{p in C_k}r_p^2 is strictly positive, and
`beta=(sum_{p in C_k}r_p^2)^(-1)*sum_{p in C_k}r_p z_p`.
No hypothesis of repeated or Cartesian-product observations is made.

## T10: localized coarsened coefficients and a negated universal

The first conjunct is CoarsenedLocalization, with exactly all the
universal hypotheses listed in T3(3). The second is the negation of:
for every natural n,J, real x,d on Fin n and real k, if 0<k<1,
TwoParty x,d, Condition1 k x, full rank of the degree-J polynomial
matrix, and there exists some coefficient vector c whose fitted values
are strictly between 0 and 1 at every observed point, then
b_J(x,d;.) is Localized. Equivalently, one such finite full-rank design
with an in-range fitted model exists on which the estimator changes for
two outcome vectors agreeing on the close window. J is not assumed
positive in the universal statement being negated. The in-range
condition is existential and is not a condition on every outcome vector.

## T11: every solution of the printed coarsened normal equations

For every finite type, every 0<k<1, every real x,d,y with TwoParty x,d
and Condition1 k x, and every coefficient vector c for the printed
coarsened design satisfying its normal equations, its coefficient at
column 1 (the d column) equals R_k(x,d;y). There is no hypothesis of
full rank or nonempty peripheral bins; the conclusion applies to every
solution, rather than asserting existence in this theorem itself.

## T12: negation of a fixed-law asymptotic assertion

This theorem states the negation of the following universal statement,
with this quantifier order. For every measurable Omega, P, pair law nu,
sample sequence, real functions g,f and real alpha, assume: nu is a
probability; its margin mu is supported on [-1,1]; Y^2 is integrable;
g is continuous on [-1,0), f on [0,1]; g(x)->alpha as x->0 from below;
ConditionalMean(nu,m), where m(x)=g(x) for x<0 and f(x) otherwise;
the sample is IID(P,nu); MomentPositiveDefinite(mu,J) for every J>=1;
bandwidths k_N>0, k_N->0, N*k_N->infinity; there exists k0>0 such
that for all a,b with -k0<=a<b<=k0, mu((a,b))>0; and the following
RD regularity. It consists of mu{0}=0,
N*mu((0,k_N]).toReal->infinity,
N*mu((-k_N,0)).toReal->infinity, and existence of delta>0,sigma2>=0
such that for every measurable A subset [-delta,delta],
`integral_{X in A}(Y-m(X))^2 dnu<=sigma2*mu(A).toReal`.

The universal conclusion being negated is: sampleRD ->_P f(0)-alpha,
and, for every epsilon>0, there exists J0 such that for every fixed
J>=J0 with J>=1, the sample polynomial-minus-RD difference converges
in probability to b_J(mu,m)-(f(0)-alpha), and
`|b_J(mu,m)-(f(0)-alpha)|<epsilon`.
Thus the negation requires one law and sample satisfying **all** those
conditions for which the full conjunction fails; it is not a theorem
asserting convergence of RD separately. There are no sample-design
admissibility hypotheses inside this particular negated universal.

## Mathlib tracing consulted during the blind stage

`MeasureTheory/Integral/Bochner/Basic.lean` (integral and integral_undef),
`MeasureTheory/Function/L1Space/Integrable.lean` (Integrable),
`MeasureTheory/Measure/Map.lean` (map),
`MeasureTheory/Measure/WithDensity.lean` (withDensity),
`Probability/Independence/Basic.lean` (iIndepFun),
`Algebra/Order/Floor/Defs.lean` (Nat.ceil), and
`Order/ConditionallyCompleteLattice/Basic.lean` (conditional extrema).
The remaining SAP definitions, including the unused `appendixSmooth`,
are explicit algebraic formulas; appendixSmooth subtracts alpha from
g on x<0 and alpha+beta from f on x>=0. The aggregator files add only
imports and options, with no further assumptions.
