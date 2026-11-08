# Blind reading of the Lean statements

This file was written and saved after reading only `SAP/P009c/Defs*.lean`,
`SAP/P009c/Defs/*.lean`, the Challenge files, and relevant Mathlib definitions.
Neither `claims.json` nor `record.json` had been opened. The mathematical
notation below expands the shared definitions; the numbered readings use that
notation. All quantifiers are universal unless explicitly existential.

## Objects and shared definitions

For a natural number n, an assignment is a function z:{0,...,n-1}->{0,1}.
The full binary cube is used, including assignments of probability zero.
Every finite-population statement below assumes n>0. A law P is a collection
of nonnegative real masses summing to one. E_P X means the finite sum
sum_z P(z) X(z); P(A) is the corresponding indicator sum. Conditional mean
E_P[X|A] means E_P[1_A X]/P(A). It is a total real-valued expression in Lean,
equal to zero when P(A)=0 because real division by zero is zero. Covariance
is E_P[(X-E_P X)(Y-E_P Y)], variance is covariance with itself, and conditional
covariance uses both conditional centering and conditional averaging.

An experiment E consists of such a law P on the cube and arbitrary real
functions Y_i(z) defined on the entire cube. Write z^{i=b} for replacing
coordinate i by b. Define Y_i(b;z)=Y_i(z^{i=b}),
tau_i(z)=Y_i(1;z)-Y_i(0;z), and T(z)=n^{-1} sum_i tau_i(z).
`ate` is T(0,...,0); `eate` is E_P T. No interference means that for every
i,z,z', equality z_i=z'_i implies Y_i(z)=Y_i(z').
Let p_i=P(Z_i=1), p_i(1)=p_i, p_i(0)=1-p_i. `adse` is
n^{-1} sum_i {E_P[Y_i(Z)|Z_i=1]-E_P[Y_i(Z)|Z_i=0]}.

For b in {0,1}, muhat_b(z)=n^{-1} sum_i 1_{z_i=b}Y_i(z)/p_i(b),
and nhat_b(z)=sum_i 1_{z_i=b}/p_i(b). The HT estimator is
H(z)=muhat_1(z)-muhat_0(z). `ArmsNonempty` means that both nhat values are
nonzero. The Hájek estimator J(z) is
n muhat_1(z)/nhat_1(z)-n muhat_0(z)/nhat_0(z) when both arms are nonzero,
and is **zero otherwise**. `SupportedArms S` means that at every time t,
every assignment of strictly positive design mass has both nonzero arms.

I_{ij}=1 if i=j or there exist two full-cube assignments differing only
possibly at coordinate i with different values of Y_j; otherwise I_{ij}=0.
Thus every diagonal is one, even for constant outcomes. D_{ij}=1 if there
exists an index l with I_{li}=I_{lj}=1, and is zero otherwise. Put
c_i=sum_j I_{ij}, d_i=sum_j D_{ij}, dbar=n^{-1}sum_i d_i,
C1=n^{-1}sum_i c_i, C2=(n^{-1}sum_i c_i^2)^{1/2},
Cp=(n^{-1}sum_i c_i^p)^{1/p}, Cinf=max_i c_i,
dmax=max_i d_i, and dRMS=(n^{-1}sum_i d_i^2)^{1/2}.
All these maxima have a nonempty finite index set here. Lambda is
sup{sum_{ij} v_i D_{ij}v_j : sum_i v_i^2=1}. For positive n this is the
maximum Rayleigh quotient of the symmetric matrix D; the set is nonempty
and bounded.

A pairing rho is a bijection of the indices with rho(rho(i))=i and
rho(i) != i for every i. Define e_{ij}=1 precisely when D_{ij}=0 and
there exists l with I_{li}=I_{rho(l),j}=1. Then
ebar=n^{-1}sum_{ij}e_{ij}, and R=sum_i I_{rho(i),i}.

Bernoulli design means 0<p_i<1 for every i and
P(z)=product_i [p_i if z_i=1, otherwise 1-p_i]. Complete(E,m) means
0<m<n and P is uniform over assignments with exactly m treated units:
mass 1/binomial(n,m) there and zero elsewhere. Paired(E,rho) means n is
even and the mass is 2^{-n/2} on every assignment with z_i != z_{rho(i)}
for all i, zero elsewhere. A pairing on a positive population forces a
positive even size. The natural quotient n/2 is exact in that use.

Regular(E;k,q,s) means k>0, real q>=2, real s>=1, and all of:
1/k <= p_i <= 1-1/k for every i;
E_P |Y_i(Z)|^q <= k^q for every i;
E_P |Y_i(b;Z)|^s <= k^s for every i,b.
The bounds apply to observed and intervened outcomes separately. On a
positive population the marginal bounds imply k>=2.

For mixing statements, q,s instead range over real numbers with an added
top element +infinity (`WithTop R`). A moment bound at finite r is the
same finite-sum r-th absolute-moment bound. At r=+infinity it is
|X(z)|<=k for every z with P(z)>0. `RegularMix` gives a common k>0,
q>=2,s>=1, all the marginal bounds, and these moment bounds at every time.
`MaximalMoments` requires q to be an attained greatest admissible observed
exponent and s an attained greatest admissible potential exponent,
**allowing a different positive uniform bound for every exponent**.
Admissibility includes respectively r>=2 and r>=1. The distinct maximality
hypothesis in T46 fixes the given k instead.

The masked assignment M_i(z) keeps coordinate j when I_{ji}=1, setting it
to zero otherwise; M_i^-(z) additionally sets coordinate i to zero.
For arbitrary finite-space random variables X,Y, alpha(X,Y) is
sup_{A,B}|P(X in A,Y in B)-P(X in A)P(Y in B)|. The supremum is over all
sets in the two target types. The values form a nonempty bounded subset of
the reals, even though the displayed definition quantifies over all sets.
Define h(a,theta)=0 when a=0, and a^theta otherwise; in particular h(0,0)=0.
Then alphaExt(theta)=n^{-1}sum_{ij}(1-D_{ij})h(alpha(M_i,M_j),theta),
and alphaInt(theta)=sum_i h(alpha(Z_i,M_i^-),theta).
The exterior exponent is (q-2)/q at finite q and 1 at infinity; the
interior exponent is (s-1)/s at finite s and 1 at infinity.

BoundedEffects(E,K) means |tau_i(z)|<=K for every index and every full-cube
assignment. Total variation between laws P,Q is (1/2)sum_z |P(z)-Q(z)|.
For real r, Lr(z,z')=(sum_i |z_i-z'_i|^r)^{1/r}, where bits are 0 or 1.
`conjugateC E r` is Cinf if r=1, and C_{r/(r-1)} otherwise.
W_r(P,Q) in this package is inf_J E_J Lr(Z,Z'), over all finite probability
laws J on pairs with marginals P,Q. It is an infimum of expected ground
distance, with no additional r-th moment or outer root. Product couplings
make this cost set nonempty; the costs are bounded below by zero for r>=1.

A Study S is a sequence indexed by t in the naturals, with positive sizes
n_t and n_t -> infinity, and an experiment E_t on each cube. No nesting or
cross-time joint law is required. Size means the real coercion of n_t.
`RegularSequence` requires the same k,q,s to give Regular at **every** t.
`CompleteSequence` means there exists a fixed p in (0,1) such that at
every t the design is Complete(E_t,floor(p n_t)). Natural floor is the
greatest nonnegative integer <= its nonnegative input; Complete also
requires 0<floor(p n_t)<n_t at every t.
`Restricted` means dbar_t/n_t ->0.

For real sequences f,g, LittleO(f,g) means f(t)/g(t)->0. BigO(f,g) means
there exists C>0 such that eventually |f(t)|<=C|g(t)|. All rate denominators
appearing here are positive (n_t>0, dbar_t>=1, dRMS_t>=1).
`InProbability S X` means: for every real epsilon>0,
P_t(epsilon<|X_t|)->0. `Op S X a` means: for every epsilon>0 there exists
K>0 such that eventually P_t(K a_t <= |X_t|)<=epsilon. In these statements
the rates a_t are positive. HTClaims(theta,a) is both InProbability(H-theta)
and Op(H-theta,a); HajekClaims uses J; EstimatorClaims is all four claims.
Write b_t=sqrt(dbar_t)/sqrt(n_t).

The Bernoulli variance estimate VBER(z) is
n^{-2}sum_i {1_{z_i=1}Y_i(z)^2/p_i^2 +
1_{z_i=0}Y_i(z)^2/(1-p_i)^2}.
MSQ=n^{-1}sum_i (E_P tau_i)^2.
Let xi_{ij}(a)=E_P[Y_i((Z^{i=a})^{j=1})-
Y_i((Z^{i=a})^{j=0})], xibreve_{ij}=(1-p_i)xi_{ij}(1)+p_i xi_{ij}(0),
and ybreve_i=(1-p_i)E_P[Y_i|Z_i=1]+p_i E_P[Y_i|Z_i=0].
Then
B1=(n dbar)^{-1}sum_{i != j}{xibreve_{ij}xibreve_{ji}
  +2 ybreve_j[xi_{ij}(1)-xi_{ij}(0)]},
and B2=(n dbar)^{-1}sum_{i != j}sum_{a,b in {0,1}}
  (1-2a)(1-2b)Cov_P(Y_i,Y_j|Z_i=a,Z_j=b).
These conditioning events are positive under the Bernoulli hypotheses in
the theorems using B2. Sigma_i^2 is the variance of the individual HT
summand 1_{Z_i=1}Y_i/p_i-1_{Z_i=0}Y_i/(1-p_i).
SDsigma=(n^{-1}sum_i (Sigma_i^2-n^{-1}sum_j Sigma_j^2)^2)^{1/2}.
VAVG=dbar VBER; VMAX=dmax VBER; VSR=Lambda VBER.

`Conservative S V` has the following exact quantifiers: there exists a
function L:R->R such that for **every** epsilon>0 the ordinary limit
as t->infinity of
P_t[(n_t/dbar_t)(V_t-Var_Pt H_t)<=-epsilon]
exists and equals L(epsilon), and lim_{epsilon->0+} L(epsilon)=0.
This is stronger syntactically than a statement using limsup or merely
convergence to zero at a selected threshold. `PositiveLiminf a` means
there exists c>0 such that eventually a_t>=c.
`InDistribution S X G` means for every real x at which G is continuous,
P_t(X_t<=x)->G(x).

Mathlib conventions checked: `Function.update` changes exactly one
coordinate (`Logic/Function/Basic.lean`); real rpow is the real part of
complex power and for a nonnegative base has the ordinary positive-base
meaning, with 0^0=1 and 0^a=0 for a!=0
(`Analysis/SpecialFunctions/Pow/Real.lean`). The explicit h convention
overrides 0^0 for mixing coefficients. Real sqrt is the nonnegative root
(zero for negative inputs); its inputs here are nonnegative sums or
positive-size expressions. `atTop` is ordinary eventual behavior as the
natural index grows; `nhdsWithin 0 (Ioi 0)` is approach to zero from the
right. Real sSup/sInf are conditional completeness operations; the sets
used above are nonempty and bounded on their stated domains, so no
out-of-domain supremum or infimum convention contributes to a conclusion.

## The individual theorems

### SAP.P009c.T35

For every natural n, then a proof n>0, then every experiment E on n units,
the following four statements hold together:

* If E has no interference, then for every z, T(z)=ate, and EATE=ate.
* EATE=n^{-1}sum_i [E_P Y_i(1;Z)-E_P Y_i(0;Z)].
* If every p_i is strictly between zero and one, then
  ADSE=n^{-1}sum_i [E_P(Y_i(1;Z)|Z_i=1)-
  E_P(Y_i(0;Z)|Z_i=0)].
* If E has Bernoulli design, EATE=ADSE.

No regularity or design hypothesis applies to the first two components.

### SAP.P009c.T36

For every n>0 and then every experiment E,
max(C1,Cinf^2/n)<=dbar, dbar<=C2^2, and C2^2<=Cinf^2.
There is no stochastic-design or moment assumption.

### SAP.P009c.T37

For every n>0, experiment E with law P, second law Q on the same cube,
and real K, if all direct effects on the full cube have absolute value
at most K, then |E_P T-E_Q T|<=2K TV(P,Q).
Only the law is changed; the entire outcome schedule stays fixed.

### SAP.P009c.T38

For every n>0, experiment E, and real K,r, if BoundedEffects(E,K) and
r>=1, then for every ordered pair of cube assignments z,z',
|T(z)-T(z')|<=2K n^{-1/r} conjugateC(E,r) Lr(z,z').
The parameter r is a finite real; r=1 uses Cinf. There is no infinite-r
case. K is not separately assumed positive, but bounded effects on a
nonempty population imply K>=0.

### SAP.P009c.T39

For every n>0, experiment E with law P, second law Q, and real K,r,
if BoundedEffects(E,K) and r>=1, then
|E_P T-E_Q T|<=2K n^{-1/r} conjugateC(E,r) W_r(P,Q).
The order of quantification is n, positivity, E, Q, K, r, the two
hypotheses, then the conclusion.

### SAP.P009c.T41

For every Study S and then real k,q,s, assume common RegularSequence,
Bernoulli design at every t, and dbar_t/n_t->0, in that order.
Conclude HT consistency for theta_t=EATE_t and HT stochastic order b_t.
There is no Hájek conclusion.

### SAP.P009c.T42

For every S and real k,q,s, assume RegularSequence, CompleteSequence,
dbar_t/n_t->0, and C1_t/sqrt(n_t)->0, in that order.
Both HT and the totalized Hájek estimator are consistent for EATE and
both have stochastic order b_t+C1_t/sqrt(n_t).
CompleteSequence ensures both arms are nonzero on the support.

### SAP.P009c.T43

For every S and real k,q,s, assume RegularSequence; either Bernoulli at
every t or CompleteSequence; and dbar_t=O(1).
Then HT is consistent for EATE and has stochastic order n_t^{-1/2}.
In addition, **if CompleteSequence holds**, Hájek is consistent for EATE
and has the same order. That additional implication does not assert
Hájek conclusions in the Bernoulli-only case.

### SAP.P009c.T44

For every S, then a pairing rho_t on each population, then real k,q,s,
assume RegularSequence; Paired(E_t,rho_t) at every t; dbar_t/n_t->0;
ebar_t/n_t->0; and R_t/n_t->0.
Both estimators are consistent for EATE, with stochastic order
b_t+sqrt(ebar_t)/sqrt(n_t)+R_t/n_t.
Paired design and positive size give two nonzero arms on the support.

### SAP.P009c.T45

For every S, then real k, then extended-real moment exponents q,s,
assume RegularMix(S,k,q,s), globally attained MaximalMoments(S,q,s),
dbar_t/n_t->0, alphaExt_t(extExponent(q))/n_t->0, and
alphaInt_t(intExponent(s))/n_t->0.
Set theta_t=EATE_t and
a_t=b_t+sqrt(alphaExt_t(extExponent(q)))/sqrt(n_t)
       +alphaInt_t(intExponent(s))/n_t.
Conclude HTClaims(theta,a). Also, if every supported assignment at
every time has two nonzero arms, conclude HajekClaims(theta,a).
The maximality quantifies over bounds with constants that can vary with
the exponent, while RegularMix itself uses the supplied common k.

### SAP.P009c.T46

For every S, then real k, then extended-real q,s, assume RegularMix,
and assume: for every extended-real r>=2, if every observed outcome at
every time satisfies its r-moment bound **with this same k**, then r<=q.
Next assume dbar_t/n_t->0 and alphaExt_t(extExponent(q))/n_t->0.
Set theta_t=ADSE_t and
a_t=b_t+sqrt(alphaExt_t(extExponent(q)))/sqrt(n_t).
Conclude HTClaims(theta,a), and, under SupportedArms, HajekClaims(theta,a).
There is no maximality requirement for s and no interior mixing assumption.

### SAP.P009c.T47

For every S and real k,q,s, assume RegularSequence, q>=4, and Bernoulli
design at every t. Then all of the following hold:

* (n_t/dbar_t)(VBER_t-Var H_t)
  -(MSQ_t/dbar_t-B1_t-B2_t) converges in probability to zero.
* If every experiment has no interference, then
  n_t(VBER_t-Var H_t)-MSQ_t converges in probability to zero.
* For every t, MSQ_t>=0.

There is **no** Restricted assumption or variance-positivity assumption.

### SAP.P009c.T48

For every S and real k,q,s, assume RegularSequence, q>=4, Bernoulli at
every t, dbar_t/n_t->0, and
SDsigma_t/(dbar_t/dRMS_t)->0.
Then VAVG is Conservative in the exact iterated-limit sense defined above.

### SAP.P009c.T49

For every S and real k,q,s, assume RegularSequence, q>=4, Bernoulli at
every t, and the disjunction:
either dmax_t/[sqrt(n_t)sqrt(dbar_t)]->0,
or both dbar_t/n_t->0 and MSQ_t is eventually bounded below by a strictly
positive constant. Then VMAX is Conservative.

### SAP.P009c.T50

This is a conjunction of two separately universally quantified statements.
First, for every S and real k,q,s, under RegularSequence, q>=4, Bernoulli
design, and either Lambda_t/[sqrt(n_t)sqrt(dbar_t)]->0 or
[dbar_t/n_t->0 and MSQ_t eventually uniformly positive], VSR is
Conservative. Second, for every positive finite population and every
experiment E, dbar<=Lambda<=dmax, with no design or regularity assumptions.

### SAP.P009c.T51

This too has two separately quantified components. First, for every S,
then real k,alpha,x, assume k>0, the given marginal bound
1/k<=p_{ti}<=1-1/k at every t,i, Bernoulli design at every t,
0<alpha<1, and 0<=x<1, in that order. There exists a family of entire-cube
outcome schedules y_t(i,z). Replace only the outcomes of S by y to get S'.
There exist real K,q,s with RegularSequence(S',K,q,s); S' is Restricted;
dbar'_t=O(n_t^x); if x=0 then dmax'_t=O(sqrt(n_t)); and
sqrt(n_t)/sqrt(dbar'_t) [H'_t-E_Pt H'_t] converges in distribution to the
CDF G_alpha which equals 0 below -1, alpha/2 on [-1,0),
1-alpha/2 on [0,1), and 1 on [1,infinity).
The output regularity witnesses are existential and follow the choice of
outcomes. The input outcomes impose no constraint on those witnesses.

Second, for every alpha in (0,1), on a separate three-point space with
probabilities (alpha/2,1-alpha,alpha/2) and values (-1,0,1), the mean is
zero, the variance is alpha, P(|X|>=1)=alpha, and
P(|X-E X|>=sqrt(Var(X)/alpha))=alpha. There is no conclusion about actual
finite-t tails at discontinuities of the limiting CDF.
