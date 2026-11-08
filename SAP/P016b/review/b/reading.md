# Blind reading

This file was written from `SAP/P016b/Defs*.lean`, the six Defs parts,
and `SAP/P016b/Challenge*.lean`, before opening `claims.json` or `record.json`.
The ten theorem stubs have no outer hypotheses: each asserts the entire
proposition described below. Hypotheses occur inside their conjunctions.
Docstring descriptions are not additional mathematical hypotheses.

## Common objects and conventions

* An outcome on n units is an arbitrary function from {0,...,n-1} to the
  real numbers. An assignment is a Boolean function on the same finite set.
  True means treated. Write z_i in {0,1} for its numeric indicator.
* N_g(z) is the number of units assigned to g; S_g(u,z) is the sum of their
  outcomes; M_g(u,z)=S_g/N_g. The pooled mean is sum(u_i)/n.
  TSS(u)=sum_i(u_i-pooledMean(u))^2 and
  RSS(u,z)=sum_i(u_i-M_{z_i}(u,z))^2.
  D(u,z)=M_1(u,z)-M_0(u,z).
* F_g(u,z;x)=#{i:z_i=g and u_i<=x}/N_g(z).
  F(u;x)=#{i:u_i<=x}/n is the whole-sample empirical CDF.
  K(u,z)=max({0} union {|F_1(u,z;u_i)-F_0(u,z;u_i)|:i<n}).
  Kplus(u,z) is the same maximum without the absolute value. Thus the
  maxima are over observed outcome coordinates, with initial value zero.
* A_t(Y,z)_i=Y_i-z_i*t; G_t(y,z)_i=y_i+z_i*t.
  C_a(Y,z)_i=Y_i/(1+z_i*(a-1)); H_a(y,z)_i=y_i*(1+z_i*(a-1)).
  Delta(y,z;t,a)_i=|H_a(y,z)_i-G_t(y,z)_i|.
* B(n,m) is the finite subtype of all Boolean assignments on n units with
  exactly m treated units. It does not itself assert m<=n or nonemptiness.
* For 2m outcomes, med(v) sorts all coordinates in ascending real order,
  then averages zero-based positions m-1 and m. The implementation uses
  natural subtraction and default-zero list lookup. Every use in these
  theorems has m>0, or m=128, so both positions are in bounds.
* c_0,...,c_5 are, in order, assignments 1100,1010,1001,0110,0101,0011.
  u4=(0,1,2,3). These are all six assignments in B(4,2).
* A finite law P on a type Omega equipped with a finite enumeration has
  real weights w(omega)>=0 and sum w=1. It can have zero-weight points.
  P(E)=sum_{omega satisfying E} w(omega). For any real score s,
  U_P(s,z)=P{s(w)>=s(z)} and L_P(s,z)=P{s(w)<=s(z)}.
  d(L,U)=min(1,2*min(L,U)). Uniform law means weight 1/|Omega|;
  its constructor requires nonempty Omega. Uniform mass and uniform
  expectation are, respectively, count(E)/|Omega| and sum(f)/|Omega|;
  these two definitions themselves do not require nonemptiness.
* For B real references r_1,...,r_B and observation x,
  L(r,x)=#{b:r_b<=x}, U(r,x)=#{b:x<=r_b} (inclusive counts), and
  p_raw(r,x)=min(1,2*min(L/B,U/B)). No observation is added to the
  reference list. All theorem uses of this definition require B>0.
* A reference vector t is a function {0,...,B}->R; coordinate 0 is the
  observation, coordinates 1,...,B are references. A measure mu on this
  real finite product is exchangeable iff pushing it forward by every
  coordinate permutation leaves mu unchanged. Probability-measure
  hypotheses mean mu(universe)=1. Write Pr_mu(E)=mu.real(E), namely
  (mu(E)).toReal. The probability hypothesis makes this ordinary finite
  probability; all count and comparison events used here are Borel.
  Almost-everywhere injectivity of t means all B+1 scores are pairwise
  distinct with probability one.
* l_corr(t)=(1+L(t_1,...,t_B;t_0))/(B+1) and
  u_corr(t)=(1+U(t_1,...,t_B;t_0))/(B+1).
  IID mass for m draws is the finite sum over every function
  {0,...,m-1}->Omega of the event indicator times the product of its m
  point weights. In particular the observed draw is also random in
  applications with B+1 draws.
* Define, literally,
  Q(M,B,c)=(2/M)*sum_{j=1}^M sum_{k=0}^c
  choose(B,k)*(j/M)^k*((M-j)/M)^(B-k).
  The exponent B-k is natural truncated subtraction; in every asserted
  use c<B (or 2c<B), so all nonzero summands have the intended exponent.
* E(s) denotes exact validity: for every finite type Omega, finite law P
  with ALL weights strictly positive, arbitrary score s, and real
  0<=alpha<=1, each of U_P,L_P,d(L_P,U_P) has probability of being <=alpha
  at most alpha, and probability of being <alpha at most alpha. There is
  no restriction on ties or on the score.
* All divisions in Lean's R are total, so x/0=0. Natural floor and ceiling
  take values in N (floor of a negative number is zero); all arguments to
  them here are nonnegative. Natural B/40 is integer division, and
  B/40-1 is natural truncated subtraction (here B=1000 or 10000).
  The real infimum in T19 is of a nonempty finite set bounded below by
  zero, so it is its usual minimum, without an empty-set convention.
* These interpretations follow Mathlib's finite sums, real field,
  `Measure.map`, `Measure.real` (MeasureSpaceDef.lean:102), probability
  measure and a.e. definitions, `Nat.floor`/`Nat.ceil`
  (Algebra/Order/Floor/Defs.lean:117,121), real conditional completeness,
  and ascending merge sort (Data/List/Sort.lean). No integrals or limits
  occur in these statements.

## SAP.P016b.T12

This asserts the conjunction of all the following.

1. For every natural n, every assignment z with N_0(z)>0 and N_1(z)>0,
   and every pair of outcomes y,y', if y_i<=y'_i at treated coordinates
   and y'_i<=y_i at control coordinates, then D(y,z)<=D(y',z).
2. K on n=4 fails that same universal property on nonempty groups;
   Kplus on n=4 also fails it. Each negation therefore asserts an
   assignment with both groups nonempty and outcomes satisfying the
   coordinate inequalities but violating the statistic inequality.
3. Exact validity E(s) as fully quantified above.
4. For every k in {0,...,5}, the exact upper-tail probability for score
   j |-> K(u4,c_j), under the uniform law on six assignments, is the kth
   entry of (1/3,1,1,1,1,1/3).
5. For every real 0<=alpha<=1, the probability under that same law that
   this upper-tail p-value is <=alpha is 0 for alpha<1/3, 1/3 for
   1/3<=alpha<1, and 1 for alpha=1.

The raw numerical K table is not an explicit conjunct.

## SAP.P016b.T13

The conjunction is:

1. For every natural B>0, every probability measure mu on R^(B+1) that
   is exchangeable and a.e. tie-free, every real 0<=alpha<1, and every
   natural c satisfying c=floor(alpha*B/2) and 2c<B, all three facts hold:
   (i) for EVERY k in {0,...,B}, the number of reference scores strictly
   below t_0 equals k with probability 1/(B+1);
   (ii) a.e., the inclusive lower count equals that strict count, and the
   inclusive upper count equals B minus the lower count;
   (iii) Pr_mu(p_raw<=alpha)=2(c+1)/(B+1).
   The rank facts (i),(ii) occur inside the alpha,c quantifiers too.
2. For every exchangeable a.e. tie-free probability measure on R^1001,
   Pr(p_raw<=1/20)=4/77>1/20. For every such measure on R^10001,
   the probability is 502/10001>1/20.
3. Set y_i=2^i for i=0,...,15. Then |B(16,8)|=12870,
   sum_i y_i=65535 and sum_i y_i^2=1431655765. For EVERY z in B(16,8),
   RSS(y,z)=1431655765-(S_1(y,z)^2+(65535-S_1(y,z))^2)/8.
   The set of these RSS scores has cardinality 6435. For EVERY z,w in
   B(16,8), their RSS values agree iff z=w or z is the coordinatewise
   Boolean complement of w.
4. For EVERY natural B>0 and natural c with 2c<B, draw B+1 assignments
   independently and uniformly from B(16,8), and score them by that RSS.
   The probability that the inclusive lower count <=c OR the inclusive
   upper count <=c equals Q(6435,B,c).
5. For EVERY natural B,c with B>0 and c<B,
   2(c+1)/(B+1)-2/6435 <= Q(6435,B,c) <= 2(c+1)/(B+1).
6. For EACH B in {1000,10000}, under the IID balanced-design draws,
   Pr(p_raw<=1/20)=Q(6435,B,B/40), and separately
   Pr(p_raw<1/20)=Q(6435,B,B/40-1).
   Q(6435,1000,25)>1/20 and Q(6435,10000,250)>1/20;
   Q(6435,1000,24)<1/20 and Q(6435,10000,249)<1/20.
7. For EVERY natural B>0, in that same IID model,
   Pr(p_raw=0)=Q(6435,B,0)
   =2*sum_{r=0}^{6433}(6434-r)^B/6435^(B+1)>0.
8. 4/77-2/6435=2326/45045 and 2326/45045>1/20.

There are no explicit decimal-approximation conjuncts or separate
cardinality-two statement for individual RSS fibers.

## SAP.P016b.T14

The conjunction is:

1. For EVERY natural B>0 and exchangeable probability measure mu on
   R^(B+1), with ties allowed, all of the following hold:
   * For EVERY natural c<=B, Pr(L<=c)<=(c+1)/(B+1) and
     Pr(U<=c)<=(c+1)/(B+1).
   * For EVERY real 0<alpha<1,
     Pr(p_raw<alpha)<=2*ceil(alpha*B/2)/(B+1).
   * For EVERY real 0<=alpha<=1, each corrected one-sided tail has
     probability of being <=alpha at most
     floor(alpha*(B+1))/(B+1); this last number is <=alpha; and
     Pr(d(l_corr,u_corr)<=alpha)<=alpha.
2. For EVERY exchangeable probability measure on R^1001,
   Pr(p_raw<1/20)<=50/1001. On R^10001 the bound is 500/10001.
   Both numerical bounds are strictly below 1/20.
3. For EVERY finite type Omega, finite law P (zero weights allowed),
   natural B (zero allowed here), real score s on Omega, permutation pi
   of {0,...,B}, and arbitrary predicate E on R^(B+1), the IID mass of
   E((s(draw(pi(i))))_i) equals the IID mass of E((s(draw(i)))_i).
4. Exact validity E(s), including its strictly-positive-point-weight
   hypothesis and both weak and strict rejection inequalities.

## SAP.P016b.T15

The conjunction is:

1. For Y=(9,11,10,12) and z=0011,
   A_(1/2)(Y,z)=(9,11,19/2,23/2), C_2(Y,z)=(9,11,5,6),
   F_1(A_(1/2)(Y,z),z;6)=0, and F_1(C_2(Y,z),z;6)=1.
2. For the whole-sample ECDF of (1,3), F(2)=1/2 and F(3)=1.
3. For EVERY real t,b, (there exists real t0 with t=t0 and b=t0)
   iff b=t.
4. There is no real t0 for which 1/2=t0 and 2=t0.

## SAP.P016b.T16

The conjunction is:

1. For EVERY n, outcome Y, assignment z, coordinate i, and real
   t,t',a,a' with a!=0 and a'!=0:
   * if z_i=false then A_t(Y,z)_i=Y_i and C_a(Y,z)_i=Y_i;
   * if z_i=true then A_t(Y,z)_i=Y_i-t and C_a(Y,z)_i=Y_i/a;
     if t!=t' their additive adjusted values at i differ;
     if a!=a' AND Y_i!=0 their multiplicative adjusted values differ.
2. For EVERY n,Y,z and real t,a,x, if N_0(z)>0 and a!=0, then
   F_0(A_t(Y,z),z;x)=F_0(Y,z;x) and
   F_0(C_a(Y,z),z;x)=F_0(Y,z;x).
3. For EVERY natural n>0, EVERY outcome u on n units and real x,
   F(u;x)=#{i:u_i<=x}/n, with the count written as a filtered finite-set
   cardinality (the definition used a sum of indicators).
4. There EXIST reals t0,b0 with 1/2=t0 and 2=b0; there is NO real t0
   with both 1/2=t0 and 2=t0.

## SAP.P016b.T17

For EVERY n,Y,z with N_0(z)>0 and N_1(z)>0, and EVERY real t, put
u=A_t(Y,z). Then for every treated coordinate i, u_i+t=Y_i; and
M_1((u_i+t)_i,z)-M_0(u,z)=D(u,z)+t=D(Y,z).
Here t is added to every coordinate in the first mean's input, although
that mean only uses treated coordinates. In addition, the statement
asserts D(u4,0011)=2 and
M_1((u4_i+10)_i,0011)-M_0(u4,0011)=12.

## Shared calibration witness in T18 and T19

There are 256 units. Assignment z has controls 0,...,127 and treated
units 128,...,255. Outcomes y are 9 on 0,...,63; 11 on 64,...,127;
8 at 128; 9 on 129,...,191; 11 on 192,...,254; 12 at 255.
Put t=34/99, a=413/396, d=Delta(y,z;t,a).
`CalibrationWitness` asserts ALL the following fixed numerical facts:

* Each group has size 128 and mean 10; TSS(y)/256=131/128; a=1+t/8.
* For every i, d_i=0 if i<129, t/8 if 129<=i<192,
  3t/8 if 192<=i<255, and t/2 otherwise.
  Exactly 127 treated coordinates have nonzero discrepancy; med(d)=0.
* M_1(H_a(y,z),z)-10=85/198; M_1(G_t(y,z),z)-10=t;
  85/198=(5/4)*t.
* 10-M_1(C_a(y,z),z)=170/413; 10-M_1(A_t(y,z),z)=t;
  (170/413)/t=495/413>1.

The outcomes are explicitly constructed, not a probabilistic normal
sample or a separately identified dataset.

## SAP.P016b.T18

The entire shared calibration witness above holds, AND for EVERY real
a, med(Delta(calibrationY,calibrationZ;34/99,a))>=0. Thus the stated
choice a=413/396 attains a global minimum zero of this criterion.

## SAP.P016b.T19

The conjunction is:

1. For EVERY natural m>0, EVERY y on 2m units, assignment z with exactly
   m treated units, EVERY real t,a, and EVERY coordinate i,
   Delta(y,z;t,a)_i=|(a-1)y_i-t| when treated and zero otherwise.
2. For EVERY such m,y,z and EVERY real t,a,
   med(Delta(y,z;t,a))=(1/2)*inf{|(a-1)y_i-t|:z_i=true}.
   This is an ordinary attained finite minimum because m>0.
3. For EVERY such m,y,z, EVERY real t, and EVERY treated coordinate j
   with y_j!=0, at a=1+t/y_j its discrepancy is zero and the overall
   median discrepancy is zero; for EVERY real a the median is >=0;
   for EVERY treated i its discrepancy at the chosen a is
   |t|*|y_i/y_j-1|, and it is nonzero if t!=0 AND y_i!=y_j.
   No nonzero or positivity hypothesis is imposed on this generated a.
4. For EVERY n,Y,z with N_1(z)>0, EVERY real t,a with a!=0,
   M_1(Y,z)-M_1(A_t(Y,z),z)=t and
   M_1(Y,z)-M_1(C_a(Y,z),z)=(1-1/a)*M_1(Y,z).
5. For EVERY m>0, EVERY y on 2m units and real t,a with a!=0, under
   uniform averaging over B(2m,m), E[M_1(y,z)]=pooledMean(y),
   E[M_1(y,z)-M_1(A_t(y,z),z)]=t, and
   E[M_1(y,z)-M_1(C_a(y,z),z)]=(1-1/a)*pooledMean(y).
6. For EVERY real mu,t,a with mu!=0, mu!=t, and a!=0,
   (1-1/a)*mu=t iff a=mu/(mu-t).
7. The entire fixed calibration witness above holds.
8. 10/(10-34/99)=495/478; 413/396!=495/478;
   10*(1-1/(413/396))=170/413; and 170/413!=34/99.

## SAP.P016b.T20

For a real matrix S on n units, assignment v, and real beta,tau, write
N_i(S,v)=sum_j v_j*S_(j,i),
q_i(v)=beta+(1-v_i)*(1-beta)*exp(-tau^2*N_i(S,v)), and
R(y,z,w)_i=(q_i(w)/q_i(z))*y_i. These expand the definitions
`treatedNeighbors`, `modelMultiplier`, and `modelMap` exactly; diagonal
matrix entries are included, and no graph structure is built into them.

The theorem asserts the conjunction of:

1. For EVERY real y0,y1,Y,tau and Boolean z, if
   Y=z*y1+(1-z)*y0 AND y1=y0+tau, then y0=Y-z*tau.
2. For EVERY n,y,z and real t,t0,
   A_t0(G_t(y,z),z)=G_(t-t0)(y,z) and A_t(G_t(y,z),z)=y.
3. For EVERY natural n and real n-by-n matrix S with ALL S_ij>=0,
   EVERY real beta,tau with beta>0 (tau arbitrary), all FOUR clauses:
   * for EVERY assignment v and coordinate i, q_i(v)>0;
   * for EVERY outcome y and assignment z, for EVERY i,
     q_i(all-control)=1, and R(y,z,all-control)_i=y_i/q_i(z);
   * for EVERY y and assignments z,w,w', R(y,z,z)=y and
     R(R(y,z,w),w,w')=R(y,z,w');
   * for EVERY outcome y0 and family of outcomes y(v), if
     for EVERY v,i, y(v)_i=q_i(v)*y0_i, then for EVERY v,
     (y(v)_i/q_i(v))_i=y0.

No symmetry, zero diagonal, binary-entry restriction, outcome-sign
restriction, or beta<=1 hypothesis occurs here.

## SAP.P016b.T21

For EVERY finite law P on B(256,128) such that EVERY assignment has
weight 1/choose(256,128), EVERY real 256-by-256 matrix S such that
S_ij=S_ji for EVERY i,j and S_ij is either 0 or 1 for EVERY i,j,
EVERY baseline outcome y0, and EVERY real statistic T(y,z), set
beta=2,tau=1/2, Y(z)_i=q_i(z)*y0_i,
u(z)_i=Y(z)_i/q_i(z), and s(z)=T(u(z),z).

All the following hold:

1. For EVERY z in B(256,128), u(z)=y0.
2. For EACH p in the finite set of functions
   {z |-> U_P(s,z), z |-> L_P(s,z),
    z |-> d(L_P(s,z),U_P(s,z))},
   P{p(z)<=1/20}<=1/20 and P{p(z)<1/20}<=1/20.
3. Under 1001 independent P draws, the probability that p_raw using
   score s of draw 0 as observation and scores of the other 1000 draws
   as references is STRICTLY less than 1/20 is <=50/1001<1/20.
4. Under 10001 independent P draws with 10000 references, the analogous
   strict-rejection probability is <=500/10001<1/20.

The observed assignment and fresh references are all IID here. A zero
diagonal for S is not required. Neither a particular statistic, normal
baseline distribution, nor graphical power-curve shape is asserted.
