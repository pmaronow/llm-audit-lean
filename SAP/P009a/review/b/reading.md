# Blind reading

This file was written from `SAP/P009a/Defs*.lean`, `Defs/Part1`--`Part6`,
and `Challenge/Part1`--`Part2`, before opening `claims.json` or `record.json`.
Indices below start at zero. All limits are as the natural-number index tends
to infinity unless another limit is specified. The Challenge theorems have no
parameters of their own: theorem `SAP.P009a.Tj` asserts `TjStatement`, with the
quantifiers and hypotheses expanded below. Docstrings are not hypotheses.

## Objects and notation used in every reading

* A population of size n has units {0,...,n-1}, assignment space
  Z_n={false,true}^n, a mass function p:Z_n -> R with p>=0 and sum p=1,
  and arbitrary deterministic real outcomes y_i(z) on the entire cube.
  A finite distribution on any finite type has the same nonnegative,
  total-mass-one requirements. Write E_p X=sum_z p(z)X(z),
  P_p(A)=E_p 1_A, C_p(X,Y)=E_p[(X-E_p X)(Y-E_p Y)], and
  V_p(X)=C_p(X,X). Conditional mean is E_p[1_A X]/P_p(A);
  conditional covariance is the conditional mean of the product centered
  at the two conditional means. These definitions use real division,
  including the Lean convention x/0=0; relevant domain restrictions must
  come from the individual statements.
* Identify a Boolean z_i with its numeric value 0 or 1. Set
  p_ib=P(z_i=b), y_i(b;z)=y_i(z with coordinate i set to b),
  tau_i(z)=y_i(true;z)-y_i(false;z), tau(z)=sum_i tau_i(z)/n,
  tau_E=E_p tau, and tau_D=sum_i(E[y_i|z_i=true]-E[y_i|z_i=false])/n.
* muhat_b(z)=sum_i 1{z_i=b}y_i(z)/p_ib/n,
  nhat_b(z)=sum_i 1{z_i=b}/p_ib, and That=muhat_true-muhat_false.
  NoSpillovers means: for every i and every z,z', z_i=z'_i implies
  y_i(z)=y_i(z').
* I_ij=1 iff i=j OR there exist full assignments z,z' agreeing at every
  coordinate other than i for which y_j(z) != y_j(z'). Otherwise I_ij=0.
  This definition forces I_ii=1 even for a constant outcome. Write i -> j
  for this predicate. Set d_ij=1 iff some l satisfies l -> i and l -> j,
  otherwise 0; d_i=sum_j d_ij, dbar=sum_i d_i/n,
  dmax=sup_i d_i, drms=sqrt(sum_i d_i^2/n).
  Write c_i=sum_j I_ij, C1=sum_i c_i/n, Cmax=sup_i c_i,
  and rho_i=the number of j with j -> i (including i).
  R(E)=sup{sum_ij v_i d_ij v_j : v in R^n, sum_i v_i^2=1}.
  Thus R is the largest Rayleigh quotient as defined, not an absolute-value
  Rayleigh quotient. The finite suprema have nonempty domains when n>0.
* BER(E) means 0<p_i,true<1 for every i and
  p(z)=product_i[p_i,true if z_i=true, 1-p_i,true otherwise].
  CR(E,m) means 0<m<n and p(z)=1/binomial(n,m) on assignments with exactly
  m true coordinates, zero on other assignments. These are full laws,
  not merely covariance restrictions.
* Reg(E,k,q,s) means k>0, q>=2, s>=1, and for every i,
  1/k<=p_i,true<=1-1/k, E_p |y_i|^q<=k^q, and, for every b,
  E_p |y_i(b;Z)|^s<=k^s. Here q and s are finite real numbers.
  Powers are Mathlib Real.rpow of nonnegative arguments. On positive
  arguments these are exp(exponent*log(argument)); 0^a=0 for a!=0,
  and 0^0=1.
* U_i(z) is the full assignment vector with coordinates outside
  {j:j -> i} replaced by false. U_i^-(z) also replaces coordinate i by
  false. For random variables X,Y on any finite probability space,
  alpha_p(X,Y)=sup_{A,B}|P(X in A,Y in B)-P(X in A)P(Y in B)|,
  over all sets in their respective codomains. This is an ordinary
  bounded, nonempty real supremum. Set pow0(a,theta)=0 if a=0,
  otherwise a^theta (so pow0(0,0)=0).
  external(E,theta)=sum_ij (1-d_ij) pow0(alpha(U_i,U_j),theta)/n;
  internal(E,theta)=sum_i pow0(alpha(z_i,U_i^-),theta).
* VBER(z)=sum_i[1{z_i=true}y_i(z)^2/p_i,true^2 +
  1{z_i=false}y_i(z)^2/p_i,false^2]/n^2.
  VA=dbar*VBER, VM=dmax*VBER, VS=R(E)*VBER.
  Q(E)=sum_i(E_p tau_i)^2/n (square of each expectation).
* xi_ij(a)=E_p[y_i(Z with i=a,j=true)-y_i(Z with i=a,j=false)].
  xibar_ij=(1-p_i,true)xi_ij(true)+p_i,true xi_ij(false),
  ybar_i=(1-p_i,true)E[y_i|z_i=true]+p_i,true E[y_i|z_i=false].
  B1(E)=sum_{i!=j}[xibar_ij xibar_ji+
    2 ybar_j(xi_ij(true)-xi_ij(false))]/(n*dbar).
  B2(E)=sum_{i!=j} sum_{a,b in {0,1}}(1-2a)(1-2b)
    C_p(y_i,y_j | z_i=a,z_j=b)/(n*dbar).
  vi is the variance of 1{z_i=true}y_i/p_i,true -
  1{z_i=false}y_i/p_i,false; dispersion=sqrt(sum_i(vi-sum_j vj/n)^2/n).
  A_b,a,i(z)=1{z_i=b}y_i(z)^a for natural a.
* A sequence S comprises N_t>0 at every t, N_t -> infinity, and one
  finite experiment E_t on N_t units at every t. Its sample size n_t is
  the real cast of N_t. SeqReg(S,k,q,s) means Reg(E_t,k,q,s) for EVERY t,
  with the SAME constants. Sparse(S) means dbar_t/n_t ->0.
  f=o_ratio(g) means f_t/g_t ->0 using totalized real division;
  f=O(g) means there is C>0 with |f_t|<=C|g_t| eventually.
* X_t ->_p 0 means for EVERY epsilon>0, P(|X_t|>epsilon)->0.
  Conservative(S,Vhat) means there EXISTS a real function L(epsilon)
  such that for EVERY epsilon>0 the probabilities
  P((n_t/dbar_t)(Vhat_t-V_p That_t)<=-epsilon) converge to L(epsilon),
  AND L(epsilon)->0 as epsilon tends to zero through strictly positive
  reals. This includes existence of each inner probability limit.
  PositiveLower(a) means there is c>0 such that a_t>=c eventually.
* Law(S,X,G) means for EVERY real x at which G is continuous,
  P(X_t<=x)->G(x). Phi(x) is the mass of (-infinity,x] under Mathlib's
  gaussianReal 0 1, whose second parameter is variance 1.
  Cover(T,theta,Vhat,alpha) means |T-theta|<=sqrt(Vhat/alpha).
  Mathlib's real square root is nonnegative, and is zero on negative
  arguments. All displayed liminf probabilities are ordinary real
  Filter.liminf (supremum of eventual lower bounds); probabilities lie
  in [0,1], so no unbounded-liminf convention is involved.
* Moment orders in MaxOrders are in WithTop R, i.e. R plus +infinity.
  For finite r an order bound is E|X|^r<=k^r; at +infinity it is
  |X(z)|<=k at each z of positive mass. ObservedAdmissible(r) requires
  r>=2 and existence of a single k>0 valid for all t,i.
  PotentialAdmissible(r) requires r>=1 and one k>0 valid for all t,i,b
  on y_i(b;Z). MaxOrders(q,s) means both orders are admissible and every
  admissible observed (respectively potential) order is <=q (respectively s).
* Eventually means from some index onward; frequently means above every
  index there is a further index. FiniteLimsup(a,L) means for every
  epsilon>0, a_t<L+epsilon eventually, and a_t>L-epsilon frequently.
  This states a genuinely finite ordinary limsup, without using a
  default value for an unbounded real supremum.

These expansions use the Mathlib finite sums/products, function update,
cardinality, real order/arithmetic, rpow, sqrt, conditional complete real
supremum, the atTop/neighborhood filters, Gaussian measure, and measure
integrability. A general measure in T2 has total mass one. Integrable means
almost everywhere strongly measurable and finite integral of the norm;
the explicit measurability assumptions in T2 also make its events measurable.
Finite spaces here use sums rather than measure integrals.

## Fixed populations

Fair(n,y) gives every full assignment mass 2^(-n) and outcome y.
Sparse_t has n=t+1, y_0=z_0, y_i=0 for i!=0.
Identity_t has n=t+1 and y_i=z_i.
Let h(n)=max(1, floor(n/2)-1), where subtraction is natural truncated
subtraction. Cluster_t has n=t+1 and y_i=z_0 for i<h(n), zero otherwise.
D(n)=(h(n)^2+n-h(n))/n^2 with real arithmetic in this last formula.
The cancellation population C is Fair(3,y), y_1=z_0(2z_2-1),
y_0=y_2=0.

## SAP.P009a.T1

This is a conjunction about the SPECIFIED Sparse sequence, with no
external hypotheses. SeqReg(Sparse,2,4,1). For every t it is BER and has
NoSpillovers, dbar=dmax=drms=R=1. Sparse(Sparse) holds. For every t,
with n=t+1, tau_E=tau_D=Q=1/n, V(That)=1/n^2,
E VBER=2/n^2>V(That); for every assignment z,
That=2z_0/n, VBER=4z_0/n^2, and VA=VM=VS=VBER;
dispersion^2=(n-1)/n^2. All four variance estimates are Conservative.
The variable n(VBER-V(That))-Q tends to zero in probability.
At every t, P(Cover(That,tau_E,VBER,1/20))=1/2, and 1/2<19/20.
Finally, for every t, E That=1/n.

## SAP.P009a.T2

Conjunction of four independently universally quantified clauses:

1. FOR EVERY family of types Omega_t with measurable spaces, probability
   measures P_t, real random variables T_t,Vhat_t, and real sequences
   theta_t,V_t,delta_t, ASSUME, for EVERY t: T_t and T_t^2 are integrable,
   T_t and Vhat_t are measurable, integral T_t=theta_t,
   V_t=integral(T_t-theta_t)^2, V_t>0, Vhat_t(omega)>=0 for EVERY omega,
   and delta_t>0. FOR EVERY alpha with 0<alpha<1, conclude ALL of:
   (i) for EVERY t and EVERY eta in (0,1),
   P(not Cover(T_t,theta_t,Vhat_t,alpha)) <=
   P(Vhat_t<(1-eta)V_t)+alpha/(1-eta);
   (ii) IF for EVERY eta in (0,1) that lower-tail probability tends to
   zero, THEN liminf_t P(Cover(...))>=1-alpha;
   (iii) IF for EVERY epsilon>0,
   P(((t+1)/delta_t)(Vhat_t-V_t)<=-epsilon)->0,
   AND PositiveLower(((t+1)/delta_t)V_t), THEN for EVERY eta in (0,1),
   P(Vhat_t<(1-eta)V_t)->0.
2. FOR EVERY real a,V,Vhat,eta,c, IF a>0, eta>0, c<=aV,
   and Vhat<(1-eta)V, THEN a(Vhat-V)<=-eta*c.
3. FOR EVERY sequence S and finite reals k,q,s,alpha with SeqReg,
   BER at every t, any Vhat_t(z)>=0 at EVERY t,z, 0<alpha<1,
   Conservative(S,Vhat), and PositiveLower((n_t/dbar_t)V(That_t)),
   conclude: for EVERY eta in (0,1),
   P(Vhat_t<(1-eta)V(That_t))->0, AND
   liminf P(Cover(That_t,tau_E,t,Vhat_t,alpha))>=1-alpha.
4. FOR EVERY n>0, E,k,q,s, IF Reg(E,k,q,s) AND BER(E),
   THEN E_p That=tau_E.

## SAP.P009a.T3

There EXIST three two-unit experiments E,F,G, with the following full
mass and outcome formulas (at EVERY assignment and unit), and all the
following equalities and inequalities. E and G have independent arms
p_0=1/4,p_1=3/4. E has y_0=z_1,y_1=-z_0.
F has mass 1/4 on (true,false), 3/4 on (false,true), zero elsewhere,
and both outcomes constantly 1. G has y_0=1,y_1=1-z_0.
All three satisfy Reg(.,4,4,1), and E,G satisfy BER.
For E, V(muhat_true)=13/48 and sum_ij C(A_true,1,i,A_true,1,j)=0.
For F, V(nhat_true/2)=1/3 and sum_ij C(z_i,z_j)=0.
For G, V(sum_i A_true,2,i/p_i,true^2)=367/9 and
4^4 sum_ij C(A_true,2,i,A_true,2,j)=39.
Also 0<13/48, 0<1/3, 39<367/9.

## SAP.P009a.T4

Conjunction of three universal clauses:

1. FOR EVERY finite types Omega,U, finite distribution p, random variables
   X_i, real weights w_i and real K, IF for EVERY i, 0<w_i<=K, THEN
   V(sum_i w_i X_i)=sum_ij w_i w_j C(X_i,X_j), AND
   V(sum_i w_i X_i)<=K^2 sum_ij |C(X_i,X_j)|.
2. FOR EVERY n>0,E,k,q,s satisfying Reg, ALL of the following hold:
   (i) for EVERY b,
   V(muhat_b)<=k^2/n^2 sum_ij |C(A_b,1,i,A_b,1,j)|;
   (ii) IF BER, THEN for EVERY b that absolute sum equals
   sum_ij d_ij |C(A_b,1,i,A_b,1,j)|, AND
   V(muhat_b)<=k^4 dbar/n;
   (iii) for EVERY b,
   V(muhat_b)<=k^4 dbar/n+10k^4 external(E,(q-2)/q)/n;
   (iv) for EVERY b,
   V(nhat_b/n)<=k^2/n^2 sum_ij |C(1{z_i=b},1{z_j=b})|, AND
   V(nhat_b/n)<=k^2 dbar/n+k^2 external(E,(q-2)/q)/n;
   (v) IF q>=4 AND BER, THEN for EVERY b,
   V(sum_i A_b,2,i/p_ib^2)<=k^4 sum_ij |C(A_b,2,i,A_b,2,j)|,
   that absolute sum equals sum_ij d_ij |C(A_b,2,i,A_b,2,j)|,
   AND V(sum_i A_b,2,i/p_ib^2)<=k^8 n dbar;
   ALSO V(n VBER)<=4k^8 dbar/n.
3. FOR EVERY n>0,E,k,q,s with Reg, natural a equal to 1 OR 2 with
   2a<=q, units i,j, and arm b,
   |C(A_b,a,i,A_b,a,j)|<=k^(2a).

## SAP.P009a.T5

No external hypotheses. Cluster satisfies SeqReg(.,3,2,1), and for EVERY
t is BER with dbar/n=D(t+1). Its dbar/n tends to 1/4 and, for EVERY t,
dbar/n>=1/4 IFF t+1<=4. Separately D(t+1)->1/4, and for EVERY natural
n>0, D(n)>=1/4 IFF n<=4. For EVERY natural m>=3,
1/4-D(2m)=(m-2)/(4m^2). For EVERY natural m>=2,
1/4-D(2m+1)=(8m-11)/(4(2m+1)^2).

## SAP.P009a.T6

Conjunction:
1. FOR EVERY real sequence a and reals L,c, IF FiniteLimsup(a,L),
   0<c<L, THEN {t:c<=a_t} is infinite.
2. FOR EVERY n>0,E and reals k,q,s,L, IF Reg(E,k,q,s) AND 0<L<=1,
   SET M=natural ceiling of sqrt(L)*n and let F have E's design and
   full-cube outcomes
   y_i^F(z)=(n/M) z_0 [z_i p_i,true-(1-z_i)p_i,false] for i<M,
   zero otherwise. THEN dbar(F)=M^2/n+(n-M)/n>=L*n;
   for EVERY i,z, |y_i^F(z)|<=1/sqrt(L);
   tau_E(F)=p_0,true; and for EVERY z,
   That_F(z)=z_0 and |That_F(z)-tau_E(F)|>=1/k.

## SAP.P009a.T7

No external hypotheses. Sparse satisfies SeqReg(.,2,4,1) and Sparse(.).
For EVERY t it is BER, NoSpillovers, dbar=dmax=1, and V(That)>0.
n_t V(That_t)->0. For EVERY t AND Boolean b,
P((That-tau_E)/sqrt(V(That)) = (1 if b else -1))=1/2.
This standardized variable does NOT converge in law to Phi.

## SAP.P009a.T8

FOR EVERY sequence S and finite real k,q,s, ASSUME SeqReg(S,k,q,s),
BER at EVERY t, existence of ONE real D with dmax_t<=D at EVERY t,
V(That_t)>0 at EVERY t, and existence of c>0 with
n_t V(That_t)>=c eventually. THEN
(That_t-tau_E,t)/sqrt(V(That_t)) converges in law to Phi.

## SAP.P009a.T9

FOR EVERY natural r>=1 there EXISTS an experiment E of size n=4r+2
with CR(E,2r+1) and the following full outcome schedule. Let
H={0} union {2,...,2r+1}; y_0=sum_{j in H}z_j/(2r+1),
y_1=sum_{j outside H}z_j/(2r+1), and y_i=z_i for all other i.
E satisfies Reg(.,2,4,1), d_01=0,
dbar=3-4/(4r+2)<3, C1=2-2/(4r+2), Cmax=2,
and alpha(U_0,U_1)=1/4.

## SAP.P009a.T10

FOR EVERY sequence S, ASSUME for EVERY t there EXISTS m with CR(E_t,m),
there EXISTS real D with dbar_t<=D eventually, and at EVERY t the finite
set J_t={(i,j):d_ij=0} of ORDERED pairs is nonempty. THEN there EXISTS
a family of finite sets H_t of pairs such that, simultaneously:
at EVERY t, H_t is a subset of J_t; |H_t|/|J_t| ->0 (real division);
and for EVERY epsilon>0, eventually for EVERY i,j with d_ij=0 and
(i,j) outside H_t, alpha(U_i,U_j)<epsilon. A SINGLE family H works
for ALL epsilon; its choice precedes epsilon.

## SAP.P009a.T11

For EVERY natural m>=2, consider the SPECIFIED fair experiment on m^2
units partitioned into m consecutive blocks of size m. In each block
the first unit is its hub and the second its designated leaf. Every
unit's outcome is its own z_i plus z_leaf if it is the hub, otherwise
plus z_hub. (The modulo formulas in the definition select these same
units, since m>=2 and each index is below m^2.) THEN E is BER,
Reg(E,2,4,1), C1=2, dbar=m, Q=1, B1=2/m^2, B2=0,
and 0<B1<=Q/dbar. Along m=t+2, dbar/C1 -> +infinity.

## SAP.P009a.T12

Conjunction:
1. FOR EVERY n>0,E and finite real k,q,s, IF Reg, q>=4 AND BER, THEN
   |B1|<=12k^4(C1-1)/dbar,
   |B2|<=4k^4(dbar-1)/dbar, |B2|<=4k^4,
   and 0<=Q<=4k^4.
2. FOR EVERY S,k,q,s with SeqReg, q>=4, BER at EVERY t, and
   dbar_t/C1_t -> +infinity, THEN Q_t/dbar_t ->0, B1_t ->0,
   B2=O(1), AND the following implication:
   IF C1_t/(dbar_t*|B2_t|)->0 AND B2_t!=0 eventually,
   THEN (Q_t/dbar_t)/|B2_t| ->0 and B1_t/|B2_t| ->0.

## SAP.P009a.T13

The SPECIFIED cancellation population C is BER and Reg(C,2,4,1),
0 -> 1 holds, xi_10(false)=xi_10(true)=0, and xibar_10=0.
There are no external hypotheses.

## SAP.P009a.T14

Conjunction of four clauses:
1. FOR EVERY n,E,i,j, IF i!=j AND NOT i -> j, THEN for EVERY a,z,
   y_j(z with j=a,i=true)=y_j(z with j=a,i=false), AND
   xi_ji(false)=xi_ji(true)=xibar_ji=0.
2. FOR EVERY n>0,E, IF NoSpillovers(E) AND for EVERY i both p_i,true
   and p_i,false are strictly positive, THEN for EVERY i!=j,
   xi_ij(false)=xi_ij(true)=0, AND B1(E)=0.
3. In the SPECIFIED cancellation population, 0 -> 1 and xibar_10=0.
4. FOR EVERY n,E,i,j with i!=j, xibar_ji!=0 implies i -> j.
   Clauses 1 and 4 impose no nondegeneracy or design hypothesis.

## SAP.P009a.T15

The SPECIFIED Identity sequence satisfies SeqReg(.,2,4,1) and
MaxOrders(.,+infinity,+infinity). At EVERY t it is BER, NoSpillovers,
and dbar=1. It satisfies Sparse(.) and
external(E_t,1)/n_t ->0 and internal(E_t,1)/n_t ->0.
For EVERY t, 4 sum_ij C(z_i,z_j)=n_t,
4 sum_{i!=j} alpha(z_i,z_j)=0, and n_t>0.
There are no external hypotheses.

## SAP.P009a.T16

FOR EVERY n>0,E,Boolean b,real k>0, BOTH inequalities hold:
(k^2/n^2) sum_ij C(1{z_i=b},1{z_j=b})
  <= (k^2/n^2) sum_ij alpha(z_i,z_j),
and this last quantity <= k^2 dbar/n +
(k^2/n^2) sum_ij (1-d_ij) alpha(z_i,z_j).
All pairs include the diagonal; no regularity, moment or design
hypotheses are imposed beyond the finite experiment's probability law.

## SAP.P009a.T17

There EXISTS an experiment E on four units such that at EVERY z its
mass is 1/6 if exactly two units are treated, zero otherwise, and at
EVERY i,z its outcome is y_i=z_i+1{i=0}z_1.
For EVERY j, j -> 0 IFF j=0 OR j=1.
E satisfies CR(E,2), Reg(E,2,4,1), rho_0=2.
Define T_i=sum_j 1{j!=i, j -> i, z_j=true} (excluding i).
Then P(T_0=0)=1/2 and E[1{T_0=0}|z_0=true]=2/3.
The helper H(n,m,r,t)=binomial(m,t)binomial(n-m,r-t)/binomial(n,r)
uses NATURAL truncated subtraction in its binomial arguments.
At the ONLY arguments used here, H(4,2,2,0)=1/6 and
H(3,1,2,0)=1/3; none of these arguments underflow or divide by zero.
Finally 1/2!=1/6 and (2/3)/(1/2)!=(1/3)/(1/6).
