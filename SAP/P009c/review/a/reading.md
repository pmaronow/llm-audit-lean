# Blind mathematical reading

This file was written from `SAP/P009c/Defs.lean`, all four Defs parts,
`SAP/P009c/Challenge.lean`, and its Part1, before opening `claims.json` or
`record.json`. Challenge proofs are stubs. The descriptions below expand the
statement definitions; their truth and correspondence to an external claim
are not presumed.

## Shared objects and notation (expanded definitions)

For a natural number n, the units are Fin n and the assignment space is the
entire finite set Z_n = {0,1}^n (Lean Bool, with false=0 and true=1).
A law P on a finite space has real masses P(z)>=0 and sum_z P(z)=1.
E_P X = sum_z P(z)X(z), P(A)=sum_z P(z)1_A(z), and
E_P[X|A]=E_P[1_A X]/P(A). Covariance is
E_P[(X-E_P X)(Y-E_P Y)], variance is covariance with itself, and
conditional covariance is E_P[(X-E_P[X|A])(Y-E_P[Y|A])|A].
These are actual finite sums, with no integrability assumptions or integrals.
Real division is total in Lean (in particular division by zero is zero).

An experiment E consists of a law P on Z_n and arbitrary real functions
Y_i:Z_n->R, defined even on assignments of P-mass zero. Write
p_i(b)=P(Z_i=b), and p_i=p_i(1). Let z^{i<-b} mean replacing coordinate
i by b; this is Mathlib Function.update. Set

* Y_i(b;z)=Y_i(z^{i<-b}); tau_i(z)=Y_i(1;z)-Y_i(0;z).
* tau(z)=n^{-1}sum_i tau_i(z) (`ateAt`);
  ATE=tau(0,...,0) (`ate`); EATE=E_P tau (`eate`).
* NoInterference means: for every i,z,z', z_i=z'_i implies
  Y_i(z)=Y_i(z').
* ADSE=n^{-1}sum_i {E_P[Y_i(Z)|Z_i=1]-E_P[Y_i(Z)|Z_i=0]}.
* muhat_b(z)=n^{-1}sum_i 1_{z_i=b}Y_i(z)/p_i(b),
  nhat_b(z)=sum_i 1_{z_i=b}/p_i(b), and HT=muhat_1-muhat_0.
* ArmsNonempty(E,z) means nhat_1(z)!=0 and nhat_0(z)!=0.
  HJ(z)=n*muhat_1(z)/nhat_1(z)-n*muhat_0(z)/nhat_0(z) when
  ArmsNonempty holds, and HJ(z)=0 otherwise. Thus HJ is a total,
  explicitly zero-extended function.
* BoundedEffects(E,K) means |tau_i(z)|<=K for every i and every full-cube
  assignment z, not merely supported assignments.

Interferes(E,i,j) means i=j OR there exist z,z' equal at every coordinate
other than i with Y_j(z)!=Y_j(z'). I_ij is its 0/1 indicator.
Dependent(E,i,j) means there exists a unit ell with I_{ell,i}=I_{ell,j}=1.
D_ij (`d`) is its 0/1 indicator, deg_i=sum_j D_ij, and
dbar=n^{-1}sum_i deg_i. The mandatory diagonal implies D_ii=1.
Let c_i=sum_j I_ij (the outgoing count). Then
C1=n^{-1}sum_i c_i, C2=sqrt(n^{-1}sum_i c_i^2),
Cp=(n^{-1}sum_i c_i^p)^(1/p), Cinf=sup_i c_i,
dmax=sup_i deg_i, and dRMS=sqrt(n^{-1}sum_i deg_i^2).
The suprema here are real Mathlib sSup. For positive n their index sets
are finite, nonempty, and bounded, so they are ordinary maxima.

A Pairing is a bijection rho:Fin n->Fin n with rho(rho(i))=i and
rho(i)!=i for every i. For such a pairing,
e_ij=1 iff D_ij=0 and there exists ell with I_{ell,i}=I_{rho(ell),j}=1;
otherwise e_ij=0. ebar=n^{-1}sum_{i,j}e_ij and
rSum=sum_i I_{rho(i),i}.

Bernoulli(E) requires 0<p_i<1 for every i AND, for every z,
P(z)=product_i (p_i if z_i=1, otherwise 1-p_i).
Complete(E,m) requires 0<m<n and gives every assignment having exactly
m treated units mass 1/binomial(n,m), with zero mass elsewhere.
Paired(E,rho) requires n even and gives mass 2^{-(n/2)} exactly to
assignments satisfying z_i!=z_{rho(i)} for all i, and zero elsewhere.
Here n/2 is natural division, used with an even n.

Regular(E,k,q,s), for finite real exponents, is the conjunction:
k>0; q>=2; s>=1; 1/k<=p_i<=1-1/k for all i;
E_P |Y_i(Z)|^q<=k^q for all i; and
E_P |Y_i(b;Z)|^s<=k^s for all i,b.
Real powers are Mathlib Real.rpow. Its nonnegative-base conventions are
0^0=1 and 0^a=0 for a!=0; positive powers and square roots used here
have their usual meanings. Real.sqrt is the nonnegative square root of
max(x,0); the radicands explicitly used for count and variance norms are
nonnegative.

For finite-valued maps X,Y on a finite probability space,
alpha_P(X,Y)=sup_{S,T}|P(X in S,Y in T)-P(X in S)P(Y in T)|,
with S,T arbitrary subsets of their codomains. This real sSup is of a
nonempty bounded set (empty S gives zero; all values are <=1).
masked_i(z) keeps coordinate j when I_{j,i}=1 and sets it to false
otherwise; maskedOthers_i additionally sets coordinate i to false.
Define pow0(a,theta)=0 when a=0, and a^theta otherwise; in particular
pow0(0,0)=0, rather than Mathlib's raw 0^0 convention. Then

* alphaExt(E,theta)=n^{-1}sum_{i,j}(1-D_ij)
  pow0(alpha_P(masked_i,masked_j),theta).
* alphaInt(E,theta)=sum_i pow0(alpha_P(Z_i,maskedOthers_i),theta).

The variance-estimation quantities are

* vBER(z)=n^{-2}sum_i [1_{z_i=1}Y_i(z)^2/p_i(1)^2+
  1_{z_i=0}Y_i(z)^2/p_i(0)^2].
* msq=n^{-1}sum_i (E_P tau_i(Z))^2.
* xi_ij(a)=E_P[Y_i((Z^{i<-a})^{j<-1})-
  Y_i((Z^{i<-a})^{j<-0})]. For i=j the last replacement takes priority,
  but the bias sums below exclude i=j.
* xibreve_ij=(1-p_i)xi_ij(1)+p_i xi_ij(0), and
  ybreve_i=(1-p_i)E_P[Y_i|Z_i=1]+p_i E_P[Y_i|Z_i=0].
* B1=(n*dbar)^{-1}sum_{i!=j}[xibreve_ij*xibreve_ji+
  2*ybreve_j*(xi_ij(1)-xi_ij(0))].
* B2=(n*dbar)^{-1}sum_{i!=j}sum_{a,b in {0,1}}
  (1-2a)(1-2b) Cov_P(Y_i,Y_j | Z_i=a,Z_j=b).
* sigma_i^2=Var_P(1_{Z_i=1}Y_i/p_i(1)-1_{Z_i=0}Y_i/p_i(0)).
  sdSigmaSq=sqrt(n^{-1}sum_i(sigma_i^2-n^{-1}sum_j sigma_j^2)^2).
* quadD(v)=sum_{i,j}v_i D_ij v_j; lambdaMax is the supremum of
  quadD(v) over real vectors satisfying sum_i v_i^2=1.
  For positive n this sphere is nonempty and compact, and D is a real
  symmetric nonnegative matrix, so this is its largest eigenvalue.
* vAVG=dbar*vBER; vMAX=dmax*vBER; vSR=lambdaMax*vBER.

TV(P,Q)=one half of sum_z |P(z)-Q(z)|.
For real r, L_r(z,z')=(sum_i |z_i-z'_i|^r)^(1/r), using the 0/1
real values of the bits. conjugateC(E,r) is Cinf at r=1 and
Cp with p=r/(r-1) otherwise. A coupling J of P,Q is a finite probability
law on Z_n x Z_n whose first and second marginal masses are P and Q.
W_r(P,Q) is the real infimum over couplings J of E_J L_r(Z,Z').
This is an infimum of expected distances, without a further rth root
or rth power on the expected cost. Product couplings exist, and at
r>=1 the costs are nonnegative and finite.

## Sequence and limit notation (expanded definitions)

A Study S contains N:Nat->Nat with N(t)>0 for every t and N(t)->infinity,
and experiments E_t on N(t) units. All limits below are along t->infinity;
the populations need not have each integer size or be nested.
Write n_t=N(t), and use a subscript t on any experiment quantity.
RegularSequence(S,k,q,s) means Regular(E_t,k,q,s) for every t, with the
same k,q,s. Restricted(S) means dbar_t/n_t->0.
LittleO(f,g) is exactly f(t)/g(t)->0.
BigO(f,g) means there exist C>0 and t0 such that |f(t)|<=C|g(t)| for
every t>=t0. These quotient definitions use total real division;
their denominators in the statements below are positive.

X_t->p 0 (`InProbability`) means: for every epsilon>0,
P_t(epsilon<|X_t|)->0. X_t=Op(a_t) (`Op`) means: for every
epsilon>0 there exist K>0 and t0 such that for every t>=t0,
P_t(K*a_t<=|X_t|)<=epsilon. K and t0 may depend on epsilon and S,
and are uniform over the eventually considered t.
HTClaims(S,theta,a) is HT_t-theta_t->p0 AND HT_t-theta_t=Op(a_t).
HajekClaims is the analogous conjunction for the zero-extended HJ.
EstimatorClaims is, in order, HT consistency, HJ consistency, HT rate,
and HJ rate, all for the same theta,a.
SupportedArms(S) means that for every t,z, P_t(z)>0 implies both
weighted arms nhat_1,nhat_0 are nonzero.
bernoulliRate_t=sqrt(dbar_t)/sqrt(n_t).

Conservative(S,Vhat) has the following exact, iterated-limit meaning:
there exists a function L:R->R such that for every epsilon>0,

  P_t( (n_t/dbar_t)*(Vhat_t-Var_{P_t}(HT_t)) <= -epsilon ) -> L(epsilon),

and L(epsilon)->0 as epsilon decreases to 0 through positive reals.
In particular existence of each inner limit is asserted.
PositiveLiminf(a) means there exist c>0,t0 such that a_t>=c for every
t>=t0. InDistribution(S,X,G) means that for every real x at which G
is continuous, P_t(X_t<=x)->G(x).

CompleteSequence(S) means there exists ONE fixed real p in (0,1) such
that every E_t is Complete(E_t,floor(p*n_t)). The floor is Nat.floor;
the Complete predicate also requires this count to lie strictly between
zero and n_t at every t, not just eventually.

MomentIndex is R with an added top element infinity. For a finite
exponent q, MomentBound(P,X,k,q) means E_P|X|^q<=k^q; at infinity
it means |X(z)|<=k whenever P(z)>0. WithTop.untopD(0) extracts
the real exponent in the finite branch; the infinity branch is handled
separately. RegularMix(S,k,q,s) requires k>0,q>=2,s>=1, the same
interior marginal bounds as Regular, and MomentBound with the common
k on every observed outcome (q) and every forced potential outcome (s).

AdmissibleObserved(S,q) means q>=2 and there exists a constant k>0
uniform in t,i giving the observed MomentBound. AdmissiblePotential(S,s)
means s>=1 and there exists k>0 uniform in t,i,b giving the potential
MomentBound. MaximalMoments(S,q,s) means these two bounds are attained
at q,s AND every admissible observed exponent is <=q AND every
admissible potential exponent is <=s. Constants for other admissible
exponents may vary and need not equal the RegularMix constant.
extExponent(q) is (q-2)/q for finite q and 1 at infinity;
intExponent(s) is (s-1)/s for finite s and 1 at infinity.

## Individual theorem readings

### SAP.P009c.T35

For every natural n>0 and every experiment E on n units, all four
conclusions hold:
1. If NoInterference(E), then for every full-cube z, tau(z)=ATE,
   and EATE=ATE.
2. EATE=n^{-1}sum_i(E_P Y_i(1;Z)-E_P Y_i(0;Z)).
3. If all 0<p_i<1, then ADSE=n^{-1}sum_i
   (E_P[Y_i(1;Z)|Z_i=1]-E_P[Y_i(0;Z)|Z_i=0]).
4. If Bernoulli(E), then EATE=ADSE.
The no-interference and interior-marginal assumptions apply only to
their own implications; they are not hypotheses of all four clauses.

### SAP.P009c.T36

For every n>0 and every E,
max(C1,Cinf^2/n)<=dbar AND dbar<=C2^2 AND C2^2<=Cinf^2.
There are no design, outcome-bound, or asymptotic hypotheses.

### SAP.P009c.T37

For every n>0, experiment E=(P,Y), second law Q on the same full cube,
and real K, if |tau_i(z)|<=K for all i,z, then
|E_P tau-E_Q tau|<=2*K*TV(P,Q). The outcomes stay fixed when the
design is changed to Q. No positivity of the design masses is assumed.

### SAP.P009c.T38

For every n>0, experiment E, and real K,r, if all effects are bounded
in absolute value by K and r>=1, then for EVERY ordered pair z,z' on
the full cube,
|tau(z)-tau(z')|<=2*K*n^(-1/r)*conjugateC(E,r)*L_r(z,z').
The exponent r ranges over finite real numbers, including r=1; there
is no parameter r=infinity. The conjugate count at r=1 is Cinf.

### SAP.P009c.T39

For every n>0, E=(P,Y), second law Q, and real K,r, if all effects
are bounded by K and r>=1, then
|E_P tau-E_Q tau|<=2*K*n^(-1/r)*conjugateC(E,r)*W_r(P,Q).
W_r is the expected-distance infimum defined above, and the structural
counts use the unchanged full-cube outcomes of E.

### SAP.P009c.T41

For every Study S and real k,q,s, if RegularSequence(S,k,q,s), every
E_t is Bernoulli, and dbar_t/n_t->0, then HT_t-EATE_t->p0 and
HT_t-EATE_t=Op(sqrt(dbar_t)/sqrt(n_t)). No HJ conclusion is asserted.

### SAP.P009c.T42

For every S,k,q,s, if RegularSequence, CompleteSequence, Restricted,
and C1_t/sqrt(n_t)->0, then BOTH HT and HJ are consistent for EATE_t
and both errors are Op(sqrt(dbar_t)/sqrt(n_t)+C1_t/sqrt(n_t)).
CompleteSequence includes the fixed-p, floor-count requirements above.

### SAP.P009c.T43

For every S,k,q,s, if RegularSequence, (all E_t Bernoulli OR
CompleteSequence), and dbar_t=O(1), then HT is consistent for EATE_t
with error Op(1/sqrt(n_t)); additionally, IF CompleteSequence holds,
HJ is consistent for EATE_t with that rate. The HJ conclusion is a
conditional clause, even within the outer design disjunction.

### SAP.P009c.T44

For every Study S, sequence of Pairings rho_t on Fin(N(t)), and real
k,q,s, if RegularSequence, Paired(E_t,rho_t) for every t,
dbar_t/n_t->0, ebar_t/n_t->0, and rSum_t/n_t->0, then both estimators
are consistent for EATE_t, each with stochastic error of order
sqrt(dbar_t)/sqrt(n_t)+sqrt(ebar_t)/sqrt(n_t)+rSum_t/n_t.
The pairing has no fixed points and is an involution on every population.

### SAP.P009c.T45

For every Study S, real k, and extended-real moment indices q,s, if
RegularMix(S,k,q,s), MaximalMoments(S,q,s), dbar_t/n_t->0,
alphaExt(E_t,extExponent(q))/n_t->0, and
alphaInt(E_t,intExponent(s))/n_t->0, set
theta_t=EATE_t and
a_t=sqrt(dbar_t)/sqrt(n_t)
    +sqrt(alphaExt(E_t,extExponent(q)))/sqrt(n_t)
    +alphaInt(E_t,intExponent(s))/n_t.
Then HT_t-theta_t->p0 and HT_t-theta_t=Op(a_t); ALSO, if
SupportedArms(S), the corresponding two HJ conclusions hold.
The maximality is global over constants allowed to vary with the exponent,
and includes attainment. The HJ support condition is not an HT hypothesis.

### SAP.P009c.T46

For every S, real k and extended moment indices q,s, suppose RegularMix
holds and the following observed maximality at the SAME k holds:
for every extended r>=2, if MomentBound(P_t,Y_{t,i},k,r) holds for
every t,i, then r<=q. Also suppose Restricted and
alphaExt(E_t,extExponent(q))/n_t->0. Set theta_t=ADSE_t and
a_t=sqrt(dbar_t)/sqrt(n_t)
    +sqrt(alphaExt(E_t,extExponent(q)))/sqrt(n_t).
Then HT has consistency and rate a_t about theta_t, and, conditional on
SupportedArms(S), HJ has both too. The potential index s must be
admissible at k through RegularMix but has no maximality or separation
condition. The observed maximality differs from T45's global maximality.

### SAP.P009c.T47

For every Study S and real k,q,s, if RegularSequence, q>=4, and every
E_t is Bernoulli, then all of the following hold:
1. (n_t/dbar_t)*(vBER_t-Var(HT_t))
   -(msq_t/dbar_t-B1_t-B2_t)->p0.
2. If every E_t has NoInterference, then
   n_t*(vBER_t-Var(HT_t))-msq_t->p0.
3. msq_t>=0 for every t.
There is no Restricted hypothesis. The bias quantities can vary with t;
convergence of those quantities separately is not asserted.

### SAP.P009c.T48

For every S,k,q,s, if RegularSequence, q>=4, every E_t is Bernoulli,
Restricted holds, and sdSigmaSq_t/(dbar_t/dRMS_t)->0, then vAVG is
Conservative in the exact iterated-limit sense stated above.

### SAP.P009c.T49

For every S,k,q,s, if RegularSequence, q>=4, every E_t is Bernoulli,
and EITHER dmax_t/(sqrt(n_t)*sqrt(dbar_t))->0 OR
(Restricted AND there is an eventual strictly positive uniform lower
bound for msq_t), then vMAX is Conservative in the same sense.
Restricted is explicit only in the second alternative.

### SAP.P009c.T50

This is the conjunction of two separately universally quantified claims:
1. For every S,k,q,s satisfying RegularSequence, q>=4, and Bernoulli
   designs, if EITHER lambdaMax_t/(sqrt(n_t)*sqrt(dbar_t))->0 OR
   (Restricted AND msq_t is eventually bounded below by some c>0),
   then vSR is Conservative in the same iterated-limit sense.
2. For every natural n>0 and every experiment E, dbar<=lambdaMax<=dmax.
The second clause has no regularity or design hypothesis.

### SAP.P009c.T51

The first conjunct quantifies in the following order: for EVERY Study S
and EVERY real k,alpha,x satisfying k>0, all marginal bounds
1/k<=p_{t,i}<=1-1/k, Bernoulli designs for every t, 0<alpha<1,
and 0<=x<1, there EXISTS an entire collection of replacement outcome
functions y_{t,i}:Z_{N(t)}->R. Keeping S's N, growth witnesses and
design laws and replacing only its outcomes gives a Study S' such that:

* There exist real K,q,s with RegularSequence(S',K,q,s).
* dbar'_t/n_t->0 and dbar'_t=O(n_t^x).
* If x=0, then dmax'_t=O(sqrt(n_t)).
* sqrt(n_t)/sqrt(dbar'_t) *
  (HT'_t-E_{P_t}HT'_t) converges in distribution to the law putting
  mass alpha/2 at -1, mass 1-alpha at 0, and mass alpha/2 at 1.

This is only an upper growth bound on dbar', not a two-sided asymptotic
equivalence to n^x. The limiting CDF is explicitly 0 for u<-1,
alpha/2 for -1<=u<0, 1-alpha/2 for 0<=u<1, and 1 for u>=1.

The second conjunct separately says: for every alpha in (0,1), let P
on Fin 3 have masses (alpha/2,1-alpha,alpha/2) and let X=(-1,0,1).
Then E_P X=0, Var_P X=alpha, P(|X|>=1)=alpha, AND
P(|X-E_P X|>=sqrt(Var_P X/alpha))=alpha.
It asserts equality at this finite-law Chebyshev threshold as well as
the distributional convergence in the first conjunct.

## Mathlib semantic checks

I checked the underlying definitions in Mathlib's
`Analysis/SpecialFunctions/Pow/Real.lean` (Real.rpow),
`Analysis/Real/Sqrt.lean` (nonnegative square root),
`Logic/Function/Basic.lean` (coordinate update),
`Algebra/Order/Floor/Defs.lean` (natural floor),
`Order/Filter/Defs.lean` and `Order/Filter/AtTopBot/Defs.lean`
(Tendsto and atTop), and `Topology/Defs/Filter.lean`
(nhds and nhdsWithin). Thus eventual quantification means all
sufficiently large natural indices and the outer Conservative limit
is the right-hand limit at zero. No SAP statement uses an unbounded
limsup. Real suprema/infima occur only in the count maxima, finite-space
mixing coefficients, finite-dimensional Rayleigh supremum, and coupling
cost infimum described above; these sets have the required nonemptiness
and boundedness in their theorem domains.
