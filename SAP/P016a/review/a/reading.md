# Blind reading of the Challenge statements

This file was completed and saved before opening `claims.json` or `record.json`.
The theorem declarations have no outer parameters: each asserts the entire
proposition named `TjStatement`, including every conjunct below. Quantifiers in
different numbered clauses are independent. All displayed decimal encodings in
the source denote exact rational real numbers, not floating point numbers.

## Common objects and definitions

Unit indices are `Fin n`, i.e. 0,...,n-1. An outcome is an arbitrary real vector
u=(u_i) of length n. An assignment z is an arbitrary Boolean vector of length n;
write z_i as 0 or 1 when used arithmetically. There is no implicit assignment
distribution, balance, graph condition, stochastic outcome model, or restriction
on outcome values.

For g in {0,1}, let n_g(z)=#{i:z_i=g}, U_g(u,z)=sum_{z_i=g}u_i, and
mu_g(u,z)=U_g(u,z)/n_g(z). Let bar(u)=sum_i u_i/n,
TSS(u)=sum_i(u_i-bar(u))^2,
RSS(u,z)=sum_i(u_i-mu_{z_i}(u,z))^2, and
D(u,z)=mu_1(u,z)-mu_0(u,z).
F_g(u,z;t)=#{i:z_i=g and u_i<=t}/n_g(z) is the inclusive empirical CDF.
K(u,z)=max({0} union {|F_1(u,z;u_i)-F_0(u,z;u_i)|:i<n});
Kplus(u,z)=max({0} union {F_1(u,z;u_i)-F_0(u,z;u_i):i<n}).
These are finite maxima implemented as `List.ofFn ... |>.foldr max 0`.

Gen(y,z,t)_i=y_i+z_i*t and Adj(Y,z,t)_i=Y_i-z_i*t.
For a real n by k matrix X, Q(u,X,b)=sum_i(u_i-sum_j X_ij*b_j)^2,
Fit(X,b)_i=sum_j X_ij*b_j, and L(u,X)=inf_{b in R^k} Q(u,X,b).
The actual definition of L is the real `sInf` of this range. The range is always
nonempty (the zero coefficient vector exists even for k=0) and bounded below by
zero, so the infimum has its usual meaning. B(z) has rows [1,z_i].
SameMargins(u,z,v,w) means equality, separately for g=0 and g=1, of the
multisets of observed values in group g; multiplicities are retained.

A FiniteLaw P on a finite type Omega consists of real weights p_omega>=0
whose sum is 1. Mass_P(E)=sum_{omega:E(omega)}p_omega;
E_P(f)=sum_omega p_omega*f(omega);
Cov_P(f,g)=E_P(f*g)-E_P(f)E_P(g); Var_P(f)=Cov_P(f,f).
UniformLaw requires a nonempty finite type and gives each point weight 1/card.
Upper_P(s,z)=Mass_P{s(w)>=s(z)} and Lower_P(s,z)=Mass_P{s(w)<=s(z)}
both include ties. Double(L,U)=min(1,2*min(L,U)).
UniformMass(Omega,E)=#{omega:E(omega)}/card(Omega), with no explicit
nonemptiness requirement; its only occurrences here use Balanced(8,4).
Balanced(n,m) is the subtype of Boolean n-vectors with exactly m true entries.

For an arbitrary real matrix S, Xexp(S,z)_i=sum_j S_ij*z_j,
Nexp(S,z)_i=sum_j z_j*S_ji, and deg(S)_i=sum_j S_ji.
Network(S,z) has rows [1,z_i,Nexp(S,z)_i,deg(S)_i].
Similarity(s)_ii=0; for i!=j it is 1-|s_i-s_j|/2 if both optional scores
are present, and 0 if either is absent. There is no score bound in this
definition. Distance(s)_ij=|s_i-s_j|.
For any finite, uniformly indexed bank a:Omega->Assignment(n),
C(S,a;i,g) is the ordinary arithmetic mean of Xexp(S,a(b))_i over bank
indices b satisfying a(b)_i=g (repeated bank assignments count repeatedly).
H(S,a,z)_i=Xexp(S,z)_i-z_i*C(S,a;i,1)-(1-z_i)*C(S,a;i,0).
V(h)=sum_i(h_i-bar(h))^2/(n-1), where subtraction in the denominator is
REAL subtraction. SD(h)=sqrt(V(h)); Std(h)_i=(h_i-bar(h))/SD(h).
Code(S,a,z)=Std(H(S,a,z)), for banks indexed by Fin N.
AppAdj(Y,z,e,b1,b2)_i=Y_i-z_i*b1-b2*e_i;
AppX(z,e) has rows [1,z_i,e_i].

IsDistanceMatrix(Gamma) means all entries are nonnegative, symmetry,
zero diagonal, and the triangle inequality. It does not require positive
off-diagonal entries or separation of distinct units.
For a reference vector r of length B, lc(r,o)=#{b:r_b<=o},
uc(r,o)=#{b:o<=r_b}, and RawP(r,o)=Double(lc/B,uc/B).
PrintReject(p) means p<1/20; CodeReject(p) means p<=1/20.
EffectIncreasing(T) means: for every assignment z and every y,y', if
for every i, z_i=1 implies y_i<=y'_i and z_i=0 implies y'_i<=y_i,
then T(y,z)<=T(y',z). Equality is allowed in these coordinate inequalities.

Mathlib endpoints checked: `Finset.sum` is a finite sum over `univ`
(`Algebra/BigOperators/Group/Finset/Defs.lean`); `List.ofFn` lists the
entries (`Data/List/OfFn.lean`, `mem_ofFn'`), and `foldr max 0` includes the
initial zero (`Data/List/MinMax.lean`, `le_max_of_le'`). `Multiset.map`
preserves multiplicities (`Data/Multiset/MapFold.lean`). Vector notation
is zero-indexed `Matrix.vecCons` (`Data/Fin/VecNotation.lean`). Matrix
determinant is the usual signed permutation sum
(`LinearAlgebra/Matrix/Determinant/Basic.lean`, `det_apply'`). Real square
root is the nonnegative root, returning zero on nonpositive input
(`Analysis/Real/Sqrt.lean`, `sqrt`, `sqrt_eq_zero_of_nonpos`). Real division
by zero is zero (`Algebra/GroupWithZero/Basic.lean`, `div_zero`);
real conditional suprema/infima require a nonempty bounded range for their
ordinary interpretation (`Order/ConditionallyCompleteLattice/Basic.lean`,
`isLUB_csSup`, `isGLB_csInf`, `csSup_of_not_bddAbove` and its dual).
Thus empty-group means, zero-SD standardization, or empty reference ratios
are totalized definitions, not implicit hypotheses. The actual positive-size
and positive-SD hypotheses are recorded explicitly below. All finite probability
laws force their index type to be nonempty, since an empty sum cannot be 1.

Use the following fixed tables, in the indicated index order:

* c_0,...,c_5 = 1100,1010,1001,0110,0101,0011 (`complete4`).
* b_0,...,b_3 = 1100,1001,0110,0011 (`blocked4`).
* a4 = 0101,0110,1001,1010 (`matchedBank4`).
* a6 maps any Boolean triple q to (q0,1-q0,q1,1-q1,q2,1-q2), and is
  indexed by all eight triples (`matchedBank6`).
* u4=(0,1,2,3), s4=(-1,-1/2,1/2,1), s6=(-1,-3/4,-1/2,0,1/4,1).

## SAP.P016a.T1

This is the conjunction of the following unconditional assertions:

1. c is injective; for every Boolean four-vector z,
   n_1(z)=2 iff there exists k in Fin 6 with c_k=z.
2. b is injective; for every Boolean four-vector z,
   (z0!=z2 and z1!=z3) iff there exists k in Fin 4 with b_k=z.
3. The paired population covariance, averaging over the two coordinates,
   of (0,2) with (1,3) is 1, and with (3,1) is -1. For z=c0,
   both outcome vectors (0,2,1,3) and (0,2,3,1) have RSS=4 and K=1/2.
4. For every k in Fin 6, RSS(u4,c_k)=(1,4,5,5,4,1)_k and
   K(u4,c_k)=(1,1/2,1/2,1/2,1/2,1)_k. For every k in Fin 4,
   RSS(u4,b_k)=(1,5,5,1)_k and K(u4,b_k)=(1,1/2,1/2,1)_k.
5. Under uniform k in Fin 6, the mass of RSS(u4,c_k)<=RSS(u4,c0)
   is 1/3, the mass of K(u4,c_k)>=K(u4,c0) is 1/3, and
   Cov(mu_1(u4,c_k),mu_0(u4,c_k))=-5/12. Under uniform k in Fin 4,
   the analogous RSS and K masses for b with observed b0 are both 1/2,
   and the group-mean covariance is -1/2.

## SAP.P016a.T2

The eleven independent clauses, in source order, are:

1. For every n>=2, u, z with n_0(z)>0 and n_1(z)>0,
   L(u,B(z))=RSS(u,z); for every real a,b,
   Q(u,B(z),(a,b))=RSS(u,z) iff a=mu_0(u,z) and b=D(u,z);
   and RSS(u,z)=sum_i u_i^2-n_0(z)*mu_0(u,z)^2-n_1(z)*mu_1(u,z)^2.
2. For every n>=2, u,z with both group sizes positive,
   RSS(u,z)=TSS(u)-n_0(z)*n_1(z)/n*D(u,z)^2.
3. For every n>=2, u,z,w with n_0(z)>0,n_1(z)>0 and
   n_1(w)=n_1(z), RSS(u,w)<=RSS(u,z) iff |D(u,z)|<=|D(u,w)|.
4. For every n, finite Omega, law P, n>=2, u, observed z, and
   assign:Omega->Assignment(n), if both observed groups are positive and
   every assign(omega) has the observed treated count, then
   Mass_P{RSS(u,assign(omega))<=RSS(u,z)}
   =Mass_P{|D(u,z)|<=|D(u,assign(omega))|}.
5. For every n>=2,u,z with both groups positive,
   RSS(u,z)=sum_{g=0,1} n_g(z)*(mu_g(u^2,z)-mu_g(u,z)^2).
6. For every n>=2,u,v,z,w, if both z-groups are positive and
   SameMargins(u,z,v,w), then RSS(u,z)=RSS(v,w) and K(u,z)=K(v,w).
7. For every n, finite Omega, law P, n>=2, u, assignment map, positive
   natural n0,n1, if every assignment has group counts n0,n1, then:
   for every omega, n1*mu_1+n0*mu_0=n*bar(u);
   Cov_P(mu_1,mu_0)=-(n1/n0)*Var_P(mu_1);
   and for every real x, for every omega,
   n1*F_1(x)+n0*F_0(x)=#{i:u_i<=x}, and
   Cov_P(F_1(x),F_0(x))=-(n1/n0)*Var_P(F_1(x)).
8. Fix z=c1, S with rows (0,0,1,0),(0,0,0,1),(1,0,0,1),(0,1,1,0),
   X rows [1,z_i,deg(S)_i], and v=(2,1,0,3). Then
   SameMargins(u4,z,v,z); both RSS are 4 and both K are 1/2;
   deg(S)=(1,1,2,2); Q(u4,X,(-1,-1,2))=L(u4,X)=0;
   Q(v,X,(2,-1,0))=L(v,X)=4.
9. K(u4,c1)=K(u4,c2)=1/2, while RSS(u4,c1)=4 and RSS(u4,c2)=5.
10. For every n,u,z, positive sizes of both groups imply
    RSS(u,z)=sum_{z_i=0}(u_i-mu_0)^2+sum_{z_i=1}(u_i-mu_1)^2.
11. For every n,u,z with both group sizes positive, there exists b in R^2
    such that Q(u,B(z),b)=L(u,B(z)).

## SAP.P016a.T3

All clauses are unconditional fixed examples:

1. For S=Similarity(s4), its rows are
   (0,3/4,1/4,0),(3/4,0,1/2,1/4),(1/4,1/2,0,3/4),(0,1/4,3/4,0).
   For every i, C(S,a4;i,0)=(7/8,9/8,9/8,7/8)_i and
   C(S,a4;i,1)=(1/8,3/8,3/8,1/8)_i.
   For z=c1, Xexp(S,z)=(1/4,5/4,1/4,3/4),
   Xexp(Distance(s4),z)=(3/2,3/2,3/2,5/2), and
   H(S,a4,z)=(1/8,1/8,-1/8,-1/8)=h.
   There do not exist real A,B,C with h_i=A+B*z_i+C*Xexp(S,z)_i
   for every i; nor do such A,B,C exist using the distance exposure.
2. Put S=Similarity(s6), z=101010, h=H(S,a6,z), x=Xexp(S,z),
   y=(0,1,0,1,1,0). The matrix 8S has rows
   (0,7,6,4,3,0),(7,0,7,5,4,1),(6,7,0,6,5,2),
   (4,5,6,0,7,4),(3,4,5,7,0,5),(0,1,2,4,5,0).
   For every i, x_i=(9/8,9/4,11/8,17/8,1,7/8)_i,
   C(S,a6;i,z_i)=(13/16,31/16,5/4,2,19/16,17/16)_i,
   h_i=(5/16,5/16,1/8,1/8,-3/16,-3/16)_i, and
   deg(S)_i=(5/2,3,13/4,13/4,3,3/2)_i.
   bar(h)=1/12, V(h)=49/960, and for every i,
   Std(h)_i=(sqrt(15)/42)*(11,11,2,2,-13,-13)_i.
   No real A,C satisfy h_i=A+C*x_i for all i, and no real A,B,C
   satisfy h_i=A+B*z_i+C*x_i for all i.
   L(y,AppX(z,h))=L(y,AppX(z,Std(h)))=4/3;
   L(y,AppX(z,x))=655/708;
   L(y,[1,z,x,deg(S)])=515/859.
3. The determinant of the four by four matrix with rows
   (1,1,1/4,1/8),(1,0,5/4,1/8),(1,1,1/4,-1/8),(1,0,3/4,-1/8)
   is 1/8. Also define
   Z=(0,0,1,1),
   X=(216630956840236,191947426509578,208676713418681,225467332911212)/10^13,
   E=(370753999962044,240866262449021,286925998351727,-193126413625389)/10^15.
   The matrix with rows [1,Z_i,X_i,E_i] has determinant
   -14030283848669586515272953541/10^28.
4. For those exact Z,X,E, no real A,B,C satisfy E_i=A+B*Z_i+C*X_i
   for all four i. The statement supplies no construction relating these
   rational values to a bank or score data.
5. Fix B=1000 and r_b=b+1. At o=25, lc=25,uc=976,RawP=1/20,
   CodeReject holds and PrintReject fails. At o=40, lc=40,RawP=2/25,
   lc/1000<=1/20, and CodeReject fails. At o=980, lc=980,RawP=21/500,
   lc/1000<=1/20 fails, and CodeReject holds.

## SAP.P016a.T4

1. For every n,N with n>=2, every real S satisfying symmetry and zero
   diagonal, every bank a:Fin N->Assignment(n) satisfying
   for every i and every Boolean g there exists b with a(b)_i=g,
   every finite set Omega of assignments such that SD(H(S,a,z))>0
   for every z in Omega, every real vector y0, outcome map y indexed
   by all assignments, and real b1,b2: if for every z in Omega and
   every i, y(z)_i=y0_i+z_i*b1+b2*Code(S,a,z)_i, then for every
   z in Omega, AppAdj(y(z),z,Code(S,a,z),b1,b2)=y0.
   Omega is allowed to be empty; neither bank membership of z nor positive
   treatment/control counts of z is required.
2. For every n>=2, real h,u, assignment z, if SD(h)>0, then
   sum_i Std(h)_i=0, sum_i Std(h)_i^2/(n-1)=1, and
   L(u,AppX(z,Std(h)))=L(u,AppX(z,h)). No rank or group-size
   condition on this regression is assumed.
3. For every n,N with n>=2, every real score vector s, every bank a
   satisfying the same per-unit support condition, every assignment z,
   and natural m, if n_1(z)=m and every bank assignment has m treated,
   then for S=Similarity(s) and D=Distance(s), for every i,
   Xexp(S,z)_i=m-z_i-Xexp(D,z)_i/2 and
   H(S,a,z)_i=-H(D,a,z)_i/2. Further, if SD(H(D,a,z))>0 and
   SD(H(S,a,z))>0, Code(S,a,z)_i=-Code(D,a,z)_i for every i.
   No score interval is imposed.
4. For S=Similarity(s4), h=H(S,a4,c1), SD(h)>0;
   neither h nor Std(h) is of the form A+B*c1_i+C*Xexp(S,c1)_i
   simultaneously for all i, for any real A,B,C.
5. For every positive natural B, every real reference vector r of length B
   and every real observation o, lc(r,o)/B+uc(r,o)/B>=1.
6. For every real p,alpha, (p<=alpha and not p<alpha) iff p=alpha.
7. The entire T3Statement above also holds, with no additional hypotheses.

## SAP.P016a.T6

1. For every n>=2, finite nonempty Omega, assignment map a on Omega,
   Gamma satisfying IsDistanceMatrix, function g:R^n->R^n such that
   V(g(Xexp(Gamma,a(omega))))=1 for every omega, every y0,
   y:Omega->R^n, and real b1,b2: if for every omega and every i,
   y(omega)_i=y0_i+b1*a(omega)_i+b2*g(Xexp(Gamma,a(omega)))_i,
   then for every omega,
   AppAdj(y(omega),a(omega),g(Xexp(Gamma,a(omega))),b1,b2)=y0.
   There are no group-size, nonzero-effect, nonconstant-g, injectivity,
   centering, or regression hypotheses.
2. For every real p, PrintReject(p) iff p<1/20.

## SAP.P016a.T7

1. c is injective and enumerates exactly all four-unit assignments with two
   treated, with the same universally quantified equivalence as in T1.
2. For every k in Fin 6,
   D(u4,c_k)=(-2,-1,0,0,1,2)_k;
   D(Gen(u4,c_k,10),c_k)=(8,9,10,10,11,12)_k.
   Under uniform j in Fin 6, each of the events
   |D(u4,c_j)|>=|D(Gen(u4,c_k,10),c_k)| and
   D(u4,c_j)>=D(Gen(u4,c_k,10),c_k) has mass zero.
   The corrected absolute-mean reference mass
   Mass_j{|D(u4,c_j)|>=|D(u4,c_k)|} is (1/3,2/3,1,1,2/3,1/3)_k.
3. For every real alpha>0, the uniform k mass for which the first
   (absolute-mean) inner mass in clause 2 is <alpha equals 1.
4. For every real alpha>0, the corresponding uniform rejection mass using
   the signed-mean inner mass in clause 2 equals 1.
5. For every k, Adj(Gen(u4,c_k,10),c_k,10)=u4.
6. Let y_i=i for i in Fin 8, let Omega=Balanced(8,4),
   sp(z)=Kplus(y,z), dp(z)=K(y,z). Then card(Omega)=70.
   For every z in Omega,
   Adj(Gen(y,z,-100),z,-100)=y,
   Kplus(Gen(y,z,-100),z)=K(Gen(y,z,-100),z)=1.
   UniformMass{sp>=1}=1/70 and UniformMass{dp>=1}=1/35.
   UniformMass_z{UniformMass_w{sp(w)>=sp(z)}<1/20}=1/70,
   and the analogous corrected dp rejection mass is 1/35.
   UniformMass_z{UniformMass_w{sp(w)>=Kplus(Gen(y,z,-100),z)}<1/20}=1;
   the analogous raw K versus dp comparison also has rejection mass 1.
   In each nested probability the reference w ranges independently over
   the same full seventy-assignment set.
7. For every z in Balanced(8,4) and every i,j in Fin 8, if z_i=true and
   z_j=false then Gen(y,z,-100)_i<Gen(y,z,-100)_j.
8. Both 1/70 and 1/35 are strictly less than 1/20.

## SAP.P016a.T8

1. For every n,y,z and every real t,t0,
   Adj(Gen(y,z,t),z,t0)=Gen(y,z,t-t0) and Adj(Gen(y,z,t),z,t)=y.
2. For every n, finite Omega and law P, assignment map a,
   y0 in R^n, real t, arbitrary statistic T:R^n->Omega->R,
   and real alpha satisfying 0<=alpha<=1, both:
   (a) for every predicate E on the reals,
   Mass_P{E(T(Adj(Gen(y0,a(omega),t),a(omega),t),omega))}
   =Mass_P{E(T(y0,omega))};
   (b) Mass_P{Upper_P(w->T(Adj(Gen(y0,a(omega),t),a(omega),t),w),omega)
   <=alpha}<=alpha. The inner observed omega is fixed when w varies;
   both sample and reference use P. No sampling independence is needed
   because these are exact finite-law probabilities, not random draws.
3. For every n,Y,z with both group sizes positive, and every real t,
   D(Y,z)=D(Adj(Y,z,t),z)+t, and
   D(Y,z)=D(Adj(Y,z,t),z) iff t=0.

## SAP.P016a.T9

1. For every i in Fin 4,
   F_1(u4,c5;u4_i)-F_0(u4,c5;u4_i)=(-1/2,-1,-1/2,0)_i.
   Kplus(u4,c5)=0,K(u4,c5)=1,Kplus(u4,c0)=K(u4,c0)=1.
2. TSS(u4)=5. Under the uniform six-assignment law, both inclusive
   tails of the constant statistic k->TSS(u4), observed at index 0,
   are 1, whereas Lower(k->RSS(u4,c_k),0)=1/3.
3. Fix the symmetric six-unit graph with only S_01=S_10=1 and every
   other entry zero; z=101010; u=(1,1,1,1,1,1).
   Network(S,z) has rows (1,1,0,1),(1,0,1,1),(1,1,0,0),
   (1,0,0,0),(1,1,0,0),(1,0,0,0).
   With X=Network(S,z) and W=[z,Nexp(S,z),deg(S)],
   Q(u,X,(1,0,0,0))=L(u,X)=0 and
   Q(u,W,(1,1,0))=L(u,W)=2.
4. For every k in Fin 6, RSS(u4,c_k)=(1,4,5,5,4,1)_k.
5. For every positive n, finite Omega, law P, outcome u,
   assignment map a and observed z in Omega, for every omega the
   constant assignment-statistic has value TSS(u), its event of equalling
   TSS(u) has mass 1, and its lower and upper inclusive p-values at z
   both equal 1.

## SAP.P016a.T10

1. For every n>=2,u,z with both groups positive, all three assertions in
   T2 clause 1 hold, including the universal equivalence for every a,b.
2. For every n,k,u,z with both groups positive, every real n by k matrix X
   has some coefficient vector b with Q(u,X,b)=L(u,X). For every b,c,
   if both achieve L(u,X), then Fit(X,b)=Fit(X,c). Coefficients themselves
   are not asserted unique. The assignment is otherwise unrelated to X.
3. For every n,u,z with both groups positive,
   K(u,z)=sup_{t in R}|F_1(u,z;t)-F_0(u,z;t)|,
   K(u,z)=K(u,1-z), and 0<=K(u,z)<=1.
   The supremum is the real sSup of a nonempty range bounded by 1.
4. For every n, every symmetric real S with each entry 0 or 1, every z
   with positive sizes of both groups, and every unit i,
   Nexp(S,z)_i=sum_j S_ij*z_j and deg(S)_i=sum_j S_ij.
   Zero diagonal is not assumed, and no regression or graph enumeration
   conclusion is included in this clause.

## SAP.P016a.T11

1. With z=c0, for every unit i, u4_i<=v_i if treated, and v_i<=u4_i
   if control, where v=(2,3,2,3). Yet K(u4,z)=Kplus(u4,z)=1 and
   K(v,z)=Kplus(v,z)=0. Further, for w=(0,1,4,5),
   w_i<v_i if treated and v_i<w_i if control, for every i,
   while K(w,z)=1.
2. With z=c0, q=(0,2,0,2), r=(1,2,0,2), s=(0,3,0,2),
   RSS(q,z)=4,RSS(r,z)=5/2,RSS(s,z)=13/2;
   for every i, q_i<=r_i and q_i<=s_i.
3. For every i in Fin 4,
   F_1(u4,c0;u4_i)-F_0(u4,c0;u4_i)=(1/2,1,1/2,0)_i.
4. None of K, Kplus, RSS, or -RSS on four-unit outcome/assignment
   pairs has the universally quantified EffectIncreasing property defined
   above. These are explicit negations of the full property, not
   conditional on the preceding examples or additional assumptions.
