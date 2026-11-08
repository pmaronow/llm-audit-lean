# Blind reading of the Challenge

This file was written using only `SAP/P018b/Defs*.lean`, the files in
`SAP/P018b/Defs/` and `SAP/P018b/Challenge/`, and the relevant Mathlib sources.
Neither `claims.json` nor `record.json` had been opened when this reading was saved.
The Challenge contains exactly the fourteen theorems T15 through T28 below.
Each theorem asserts its corresponding `TxxStatement`, with no additional binders
or hypotheses in the Challenge itself.

## Common mathematical dictionary (definitions fully expanded)

* `Vec k` is R^k, indexed by `Fin k`; `Mat k` is the real k by k matrices.
  `outer(x,y)=xy^t`, `dot(x,y)=sum_a x_a y_a`, and `score(x,r)=rx`.
  `sandwich(P,M)=PMP`; the second P is not transposed by definition.
  Vector norms are the maximum absolute coordinate, and the scoped matrix norm is
  the maximum absolute entry. Zero dimensional vector spaces are permitted.
* For N natural, `Dyad N` is exactly the finite set of two-element subsets of
  {0,...,N-1}. `members d` is that subset. `firstUnit d` is its minimum and
  `secondUnit d` its maximum. `overlap(d,f)` means their intersection is nonempty,
  including d=f. `neighbors d` consists of all f different from d that overlap d.
* For finite edge index E, a map s:E -> finite subsets of V, and vectors q_d,
  write M(s,q)=sum_{d,f: s_d intersects s_f} q_d q_f^t (ordered pairs, diagonal
  included), A_i(s,q)=sum_{d:i in s_d}q_d, and D(q)=sum_d q_d q_d^t.
  For record counts T_d natural and vectors q_dt, put b_d=sum_{t<T_d}q_dt,
  I(T,q)=sum_{d,t}q_dt q_dt^t,
  E_i=sum_{d:i notin s_d,t}q_dt q_dt^t, C_i=A_i(s,b)A_i(s,b)^t+E_i,
  E_i^ord=sum_{o in Fin 2}E_i=2E_i, and
  C_i^ord=A_i(s,b)A_i(s,b)^t+E_i^ord.
  Also F_i=sum_{d!=f:i in s_d and i in s_f}b_d b_f^t and
  H_i=sum_{d:i in s_d}b_d b_d^t. No positivity of T_d is implicit in this notation.
* Given sample rows X_d and responses Y_d, G=sum_d X_d X_d^t,
  bhat=G^{-1}sum_d X_d Y_d, ehat_d=Y_d-X_d^t bhat, and
  Vhat(s,X,Y)=G^{-1}M(s,(X_d ehat_d)_d)G^{-1}.
  The matrix inverse is Mathlib's nonsingular inverse: it is the usual inverse
  when the determinant is nonzero, and the zero matrix otherwise.
* `meanVec` and `meanMat` take coordinatewise real Bochner integrals.
  `covMat(mu,f,g)_{ab}=integral (f_a-E f_a)(g_b-E g_b) dmu`, and
  `varMat(mu,f)=covMat(mu,f,f)`.
  A real Bochner integral is defined to be zero when its integrand is not
  integrable (including failure of the required a.e. measurability).
  `ProbabilityTheory.variance` instead is the extended integral of the squared
  centered norm followed by `ENNReal.toReal`; infinite extended variance becomes
  zero. `ENNReal.toReal` also sends infinity to zero in probabilities; all
  probability measures here have total mass one when the corresponding
  probability hypothesis holds. `ENNReal.ofReal x=max(x,0)` as an extended
  nonnegative real. Nonnegative extended integrals in T19 can legitimately be
  infinite.
* `inProbability(mu,f)` means: for every real epsilon>0,
  mu_N{omega:epsilon<=norm(f_N(omega))}, converted to a real, tends to zero as
  natural N tends to infinity. It imposes no separate measurability condition on
  f. Measures can apply to arbitrary sets; in the statistical models the
  functions are measurable. In the abstract T18 clauses the reading is literally
  this outer-measure-style definition.
* `weakLimit(mu,f,nu)` means (in order) every f_N is a.e. measurable, nu is a
  probability measure, and for every bounded continuous real function g,
  integral g(f_N) dmu_N tends to integral g dnu.
* `centeredNormalLaw(nu,V)` means V is positive semidefinite, nu is a probability
  measure, and for every c in R^k, the pushforward of nu by x -> c^t x is the
  real Gaussian of mean zero and variance max(c^t Vc,0). Positive semidefiniteness
  makes the max harmless. Mathlib `PosSemidef` means symmetric and nonnegative
  quadratic form; `PosDef` means symmetric and strictly positive quadratic form
  on every nonzero vector. Their finite-support formulations are equivalent to
  these formulations in finite dimensions. A real Gaussian with variance zero
  is a point mass. `IsGaussian` means every continuous linear real functional
  has a real Gaussian pushforward with its mean and variance.

### Kernel models

A `Kernel U k` consists of a measure mu on a measurable space U and functions
X:U x U -> R^k, Y:U x U -> R. Let Q=E[X X^t] under mu x mu,
beta=Q^{-1}E[XY], epsilon(u,v)=Y(u,v)-X(u,v)^t beta, and
z(u,v)=X(u,v)epsilon(u,v). For N, omega=(u_0,...,u_{N-1}) has law
P_N=mu^N, design row d={i<j} is X(u_i,u_j), and its response is Y(u_i,u_j).
`scoreSum` is S_N=sum_{i<j}z(u_i,u_j), and `coefficientError` is bhat-beta.

`Standing K` is precisely this conjunction, in this order:

1. mu is a probability measure;
2. X and Y are measurable functions on U x U;
3. for every u,v, X(u,v)=X(v,u) and Y(u,v)=Y(v,u);
4. there exists one real C>=0 such that, for mu x mu almost every (u,v),
   norm X(u,v)<=C and |Y(u,v)|<=C;
5. there exists one coordinate j<k such that X(u,v)_j=1 for every u,v;
6. det Q != 0.

`SampleRank K` means there exists a deterministic natural N0 such that for every
N>=N0, det G_N != 0 for P_N almost every sample. It does not require every sample
to have rank, nor one common sample space for all N.

`Proposition1Extra K` means:

1. there exists C>=0 such that for every natural N, for P_N almost every sample,
   every fitted residual has absolute value at most C;
2. every entry Q_ab is nonzero;
3. every entry of E_{mu^3}[X(u_0,u_1) X(u_0,u_2)^t] is nonzero;
4. eventually in N, for every d, E[ehat_d^2]!=0, and for every neighbor f of d,
   E[ehat_d ehat_f]!=0.

Put D_N=N(N-1)/2 in REAL arithmetic, and
A_N=(N/D_N^2) Q^{-1}Cov(S_N)Q^{-1} (`trueTarget`). This definition is a population
score sandwich; it is not definitionally N Cov(bhat). At N=0,1 its scalar factor
is zero by real division's zero convention; these cases do not affect limits.
Let h(u)=E_v[z(u,v)], Gamma=E_u[h(u)h(u)^t], and
L=4 Q^{-1}Gamma Q^{-1} (`limitingTarget`).

For a fixed N, let F_X be the sigma algebra generated by the ENTIRE design array.
Let m_d=E[epsilon_d | F_X] and
c_df=E[(epsilon_d-m_d)(epsilon_f-m_f) | F_X]. Then
`conditionalTerm K d f` is J_df=E[c_df X_d X_f^t], and
`printedSigma K N` is sum_{d,f:overlap(d,f)}J_df.
Mathlib conditional expectation is defined to be zero if the given sigma algebra
is not a sub-sigma-algebra, if the trimmed measure is not sigma finite, or if the
integrand is not integrable. Standing probability/boundedness/measurability
provide the usual conditional expectations in these uses.

### Repeated models and UI

A `RepeatedKernel U k` consists of mu, natural T(N,d), and record functions
X(N,d,t,u,v), Y(N,d,t,u,v). Each observed record uses the smaller and larger
endpoint's unit values in that order; the unit sample law is again mu^N. The
functions may depend on N, d and t; no endpoint symmetry is part of this
structure. G_N=sum_{d,t}X_dt X_dt^t, bhat_N=G_N^{-1}sum_{d,t}X_dt Y_dt,
b_d=sum_t X_dt(Y_dt-X_dt^t bhat_N), and Vhat_N=G_N^{-1}M(members,b)G_N^{-1}.
The separately defined `repeatedBeta` uses the inverse of E G_N times
E sum X_dt Y_dt; T19 does not use it or subtract it.

`RepeatedStanding R` says: mu is a probability measure; for every N>=2 and d,
T(N,d)>0; every record's X and Y is measurable on U x U; there exists a single
C>=0 bounding their norm and absolute value mu x mu almost everywhere for every
N,d,t; and there exists a single coordinate j that equals one for all N,d,t,u,v.
The a.e. quantifier for the bound is inside the quantifiers N,d,t. It does not
itself include a rank or symmetry condition.

`uiSquares(mu,xi)` means first every coordinate of every xi_N is in L2(mu_N)
(a.e. strongly measurable with finite second absolute moment), and second:
for every epsilon>0 there exists a real C>0 such that for every natural N,
E[(sum_a xi_{N,a}^2) 1_{sum_a xi_{N,a}^2>C}]<epsilon.

## SAP.P018b.T15

First, universally quantify finite types V,E, decidable equality on each, a map
s:E -> finite subsets of V, the hypotheses |s_d|=2 for every d and s injective,
a natural k, a natural record count T_d for every d, arbitrary vectors q_dt in
R^k, and an arbitrary real matrix P. Write n=|V| and b_d=sum_t q_dt. The
conclusion is the conjunction:

* for every i, E_i^ord=2E_i;
* sum_i E_i^ord=2(n-2) I(T,q);
* sum_i C_i^ord-D(b)-(n-2)I(T,q)=M(s,b)+(n-2)I(T,q);
* sum_i P C_i^ord P-P D(b)P-(n-2)P I(T,q)P
  =P M(s,b)P+(n-2)P I(T,q)P;
* if n>=3 and P I(T,q)P!=0, that last left-hand side differs from P M(s,b)P.

Second, conjoin concrete scalar facts for the ordered edge list
(01,02,03,12,13,23), scores (1,2,3,4,5,6), one record per dyad, and four units:
D=91, M=385, sum_i A_i^2=476, sum_i E_i=182,
476+2*182-91-2*91=567!=385, I=91, sum_i E_i^ord=364,
476+182-91-2*91=385, 476+364-91-2*91=567,
567=385+182, and 6^2+10^2+12^2+14^2=476.
There is no OLS, nonzero score, or positive record-count assumption in the
universal identities.

## SAP.P018b.T16

Universally quantify V,E,s, their finiteness/decidable equality, the two-element
and injectivity hypotheses, k,T,q,P exactly as in T15, and set b_d=sum_t q_dt.
The conclusion is both corrected decomposition identities

M(s,b)=sum_i C_i-D(b)-(n-2)I(T,q),

P M(s,b)P=sum_i P C_i P-P D(b)P-(n-2)P I(T,q)P,

AND all five identities

M(s,b)-D(b)=sum_i F_i;
for every i, C_i=F_i+H_i+E_i;
sum_i H_i=2D(b);
sum_i E_i=(n-2)I(T,q);
M(s,b)=D(b)+sum_i F_i.

These are statements about arbitrary record vectors, with no statistical
assumptions; arbitrary possibly incomplete sets of distinct dyads are allowed.
Here and in T15, n-2 is a subtraction in R, not truncated natural subtraction.

## SAP.P018b.T17

This is a closed conjunction of concrete sample and population facts.
Use the six dyads above, X rows (1,x_d) with x=(1,2,3,1,2,1),
Y=(4,3,5,3,3,4), and e=(3/5,-4/5,4/5,-2/5,-4/5,3/5).
Then G=[[6,10],[10,20]], det G=20, bhat=(3,2/5), ehat_d=e_d for every d,
sum_d X_d e_d=0, Vhat=[[-17/50,21/125],[21/125,-58/625]], and both diagonal
entries of Vhat are strictly negative.

Independently define U={0,1,2,3} x {false,true} with the uniform eight-point
probability law, s(false)=-1,s(true)=1, X((a,b),(c,e))=(1,|a-c|), and
Y=|a-c|+H_ac+s(b)+s(e), where
H=[[0,1,-1,0],[1,0,0,-1],[-1,0,0,1],[0,-1,1,0]].
This kernel satisfies every Standing condition, Q=[[1,5/4],[5/4,5/2]],
beta=(1/3,11/15), and
L=[[1004/225,-48/125],[-48/125,1856/5625]], with L positive definite.
For N=4 the event u_i=(i,true) for every i has real probability 1/4096.
For EVERY sample in that event, det G=20 and its dyadic Vhat is the same
negative-diagonal matrix displayed above. No assertion here identifies L with
a distributional limit, and no sample middle-factor matrix, covariance
determinant/trace or negative-definiteness classification is asserted.

## SAP.P018b.T18

This is a conjunction of seven independently quantified assertions.

1. For all finite V,E with decidable equality, injective two-element incidence
   maps s, all k, all q_d in R^k, and every symmetric P, define B_id=1 if i in
   s_d and 0 otherwise, and S_da=q_{d,a}. Then every entry of B^t B-I_E is 1
   exactly when its two dyads overlap, and 0 otherwise;
   M=S^t(B^t B-I_E)S=(BS)^t(BS)-S^t S.
   Moreover PMP is symmetric,
   PMP=P(sum_i A_i A_i^t)P-PD(q)P, and BOTH terms on the right are positive
   semidefinite. There is no assertion that their difference is PSD.
2. For every real v, there exists se such that `standardError v=some se`
   iff v>=0. The function returns sqrt(v) when v>=0 and `none` otherwise.
3. For all real a,b, |max(a,0)-max(b,0)|<=|a-b|.
4. For every real N>=0 and v,V real with V>=0,
   |N max(v,0)-V|<=|Nv-V|.
5. For every real N>=0, v real, and V>0, v<0 implies V<=|Nv-V|.
6. For every measurable space Omega, every probability measure mu on it,
   every real N>=0, every function v:Omega->R and every real V>0,
   mu{v<0}.toReal<=mu{V<=|Nv-V|}.toReal.
7. For all sequences of measurable spaces and probability measures mu_N,
   arbitrary real functions v_N, and deterministic real V_N>=0,
   inProbability(mu,N v_N-V_N) implies
   inProbability(mu,N max(v_N,0)-V_N).
   Finally, under separately universally quantified spaces/measures/functions,
   for every FIXED real V>0, inProbability(mu,N v_N-V) implies
   mu_N{v_N<0}.toReal -> 0.

Items 3-7 contain no measurability assumption on the v functions. The integer
N in the sequences is cast to R. The final rarity limit has a fixed target,
although the preceding contraction/consistency statement allows varying V_N.

## SAP.P018b.T19

Existential quantifiers, in order: a type U, a measurable space structure on U,
a repeated kernel R with k=2, and a real v. Their joint properties are:

* RepeatedStanding R holds and T(N,d)=2 for every N,d.
* For every N>=2 and EVERY sample omega in U^N, det G_N>0; for every record
  of every such sample, |Y_dt-X_dt^t bhat_N|<=8.
* For every N>=3, both extended integrals E[(bhat_{N,1})^2] and
  E[|bhat_{N,1}|] equal infinity (coordinate 1 is the second coordinate).
* For every N>=4, E[max(Vhat_{N,11},0)]=infinity and
  E[max(-Vhat_{N,11},0)]<infinity, using extended nonnegative integrals.
* v>0, and N Vhat_N converges in the package's probability sense to
  V=[[4+v,-v],[-v,v]].
* There exists a measure nu on R^2 such that centeredNormalLaw(nu,V) holds
  and sqrt(N) bhat_N converges weakly to nu.

The last scale multiplies the coefficient itself, without subtracting a
population coefficient. No explicit unit distribution, support intervals,
conditional response mean, value of v, or directed-record re-expression is
part of the statement. Since v>0, the displayed V has determinant 4v>0.

## SAP.P018b.T20

Universally quantify, in order, a sequence of measurable spaces Omega_N,
a natural k, probability measures mu_N, functions xi_N:Omega_N->R^k,
and a measure nu on R^k. Assume, in this order:

* weakLimit(mu,xi,nu);
* uiSquares(mu,xi);
* for every coordinate a, the coordinate function x->x_a belongs to L2(nu);
* E_nu x=0.

Conclude both E_{mu_N}xi_N -> 0 and Cov_{mu_N}(xi_N) -> Cov_nu(x),
with convergence of the finite vectors/matrices in their ordinary topology.
No Gaussian assumption on nu or estimator specialization occurs here.

## SAP.P018b.T21

For every measurable U, natural k,N, and kernel K, Standing K and N>=2 imply

sum_{d in Dyad N}(J_dd+sum_{f in neighbors d}J_df)
 = sum_{d,f:overlap(d,f)}J_df.

Here J_df is the EXPECTATION of the conditional residual covariance times
X_d X_f^t, conditioned on the entire design, as defined above. There is no
claim that either side is an unconditional covariance, and no pair-count
formula is asserted.

## SAP.P018b.T22

For every natural N,T, if N>=2 and T>=1, take mutually independent standard
real Gaussians indexed by a disjoint union of N covariate slots, N unit-shock
slots, and Dyad N x Fin T record-shock slots. Under their finite product law,
let x_i be covariate slot i and e_dt=sum_{i in d}a_i+eta_dt. Then:

* the pushforward joint law of all e_dt is Gaussian;
* the whole error array and whole covariate array are independent random
  functions (independence of their generated sigma algebras);
* for every d,t, E e_dt=0;
* for every d,f,t,u,
  Cov(e_dt,e_fu)=|d intersect f|+1_{d=f and t=u};
* for every d,t, E[e_dt | sigma(x_i:all i)]=0 almost surely.

There is no defined response, regression coefficient or response conditional
mean in this theorem.

## SAP.P018b.T23

The following three universal assertions are conjoined. Put
p(t)=1/(1+exp(-t)).

1. For every k natural, x,beta in R^k and real y, set eta=x^t beta,
   ell(beta)=y eta-log(1+exp(eta)), and psi=x(y-p(eta)).
   Then 0<p(eta)<1; for every a, the derivative of ell with respect to beta_a
   exists and equals psi_a; the matrix with (a,b) entry minus the derivative
   of psi_a with respect to beta_b is p(eta)(1-p(eta))xx^t; that matrix is
   PSD; and psi psi^t=(y-p(eta))^2 xx^t. The coordinate derivatives are
   implemented by replacing one coordinate with a variable. y need not be binary.
2. For every finite E, every k, arrays X:E->R^k, Y:E->R, and beta in R^k,
   the sum of negative score Jacobians equals
   sum_d p(X_d^t beta)(1-p(X_d^t beta))X_d X_d^t, and
   sum_d psi_d psi_d^t=sum_d (Y_d-p(X_d^t beta))^2 X_d X_d^t.
3. For every measurable Omega, arbitrary parameter type Theta, k natural,
   probability measure mu, function psi:Omega->Theta->R^k and fixed theta,
   if every coordinate psi_a(.,theta) belongs to L2(mu), then
   E_mu[psi(data,theta)psi(data,theta)^t] is PSD. Both score factors use the
   SAME data argument. No smoothness or measurability on Theta is assumed.

## SAP.P018b.T24

Let the exact RATIONAL triples (H,C,D), in order, be
(69,175,265)/1000, (20,47,70)/1000, (5,10,15)/1000,
(10734,17560,24749)/1000, (2,5,8)/1000, (74,181,185)/1000,
(26,68,102)/1000, (78,188,344)/1000, (211,562,840)/1000.
The theorem conjoins all of the following:

* Their D/H ratios, as a list, are
  [265/69,7/2,3,24749/10734,4,5/2,51/13,172/39,840/211].
* Their (D+1/2000)/(H-1/2000) ratios, as a list, are
  [531/137,47/13,31/9,49499/21467,17/3,53/21,205/51,689/155,1681/421].
* 24.749/10.734=24749/10734 and .344/.078=172/39.
* For EVERY listed triple, 24749/10734<=D/H<=172/39, D/H<5,
  H<C<D, and 185/181<=D/C<=86/47.
* For every listed triple and ALL real h,d, if H-.0005<=h and
  d<=D+.0005, then d/h<10. No other bounds on h,d are required here.
* 11/8<41/25.
* For every listed triple, H-.0005>0,
  D+.0005<10(H-.0005), and (D+.0005)/(H-.0005)<=17/3.
* For ALL real b,dyadic,hc, assume
  21/2000<=|b|<=23/2000, 15/2000<=dyadic<=17/2000,
  and 3/2000<=hc<=5/2000. Conclude
  |b|/dyadic<=23/15<41/25 and 21/5<=|b|/hc with 41/25<21/5.
  Both implications occur together under ALL three interval hypotheses.
* .185/.181=185/181 and .344/.188=86/47 as rational equalities,
  and .011/.008=11/8 as a real equality.

No inference from these triples to an unprovided underlying dataset occurs in
the formal statement.

## SAP.P018b.T25

For N, define Z1_{di}=1 if i=min(d), zero otherwise, and
Z2_{di}=1 if i=max(d), zero otherwise. Set
Cshared(N,tau,sigma)=tau(Z1+Z2)(Z1+Z2)^t+sigma I,
and Crole(N,t1,t2,sigma)=t1 Z1 Z1^t+t2 Z2 Z2^t+sigma I.

The theorem NEGATES the assertion that for EVERY natural N>=3 there EXIST
real t1,t2,sigma>=0 with Cshared(N,1,1)=Crole(N,t1,t2,sigma).
Equivalently, some N>=3 admits no such triple. It does not assert failure at
every N, and the shared variances in this theorem are fixed at one.

## SAP.P018b.T26

The theorem NEGATES this universal assertion: for every measurable U, every k
natural, and every K:Kernel U k, Standing K and SampleRank K imply BOTH

1. for every N>=3, Cov_{P_N}(S_N)=printedSigma(K,N), and
2. there exists a measure nu on R^k such that sqrt(N)(bhat_N-beta) has weak
   limit nu, every coordinate x_a belongs to L2(nu), E_nu x=0, and
   A_N -> Cov_nu(x).

Thus an equivalent reading is existence of one standing, eventually-a.s.-rank
kernel for which at least one of these two clauses fails. There is NO Gaussian
requirement on nu in the negated clause and NO separate assertion refuting
clause 2; falsifying clause 1 alone suffices.

## SAP.P018b.T27

For every measurable U, k natural and K:Kernel U k, assume Standing K,
SampleRank K, and ALL of Proposition1Extra K, in that order. Conclude

N Vhat(members,design(K,omega),response(K,omega))-A_N -> 0

in the package's probability sense under P_N. A_N is the unconditional
population-SCORE covariance sandwich defined in the dictionary, not by
definition the covariance of the fitted coefficient. The residual bound is
uniform over N; the eventual sample-rank cutoff is deterministic; the last
two fitted-residual moment requirements hold only eventually. No CLT or
moment convergence of bhat is asserted.

## SAP.P018b.T28

Fix iid fair signs u_i in {-1,1}, X(u,v)=(1), and Y(u,v)=u+v.
The theorem NEGATES the conjunction of

1. N Var_{P_N}(bhat_N)-4/D_N -> 0 as N tends to infinity, and
2. N Vhat_{N,00}-4/D_N -> 0 in probability under P_N.

Here bhat is the scalar intercept-only OLS formula, D_N=N(N-1)/2 in real
arithmetic, and Var is Mathlib's real variance described above. The theorem
only asserts that at least one of these limits fails; it need not disprove
both. At N>=2 all sample designs have nonzero Gram matrix and the coefficient
is bounded, so neither singular inversion nor infinite-variance
totalization is needed to interpret the tails of these sequences.

## Mathlib source checkpoints

The semantics above follow the actual definitions, in particular:

* `LinearAlgebra/Matrix/NonsingularInverse.lean`, inverse instance at line 169;
* `MeasureTheory/Integral/Bochner/Basic.lean`, integral at line 158;
* `Probability/Moments/Covariance.lean`, covariance at line 44;
* `Probability/Moments/Variance.lean`, evariance/variance at lines 58/64;
* `MeasureTheory/Function/ConditionalExpectation/Basic.lean`, condExp at line 102;
* `MeasureTheory/Function/LpSeminorm/Defs.lean`, MemLp at line 152;
* `Probability/Distributions/Gaussian/Basic.lean`, IsGaussian at line 45;
* `Probability/Distributions/Gaussian/Real.lean`, gaussianReal at line 222;
* `Probability/Independence/Basic.lean`, IndepFun at line 144;
* `LinearAlgebra/Matrix/PosDef.lean`, PosSemidef/PosDef at lines 60/162;
* `Analysis/Normed/Group/Constructions.lean`, finite-product supremum norm;
* `Analysis/Matrix/Normed.lean`, scoped elementwise matrix norm.
