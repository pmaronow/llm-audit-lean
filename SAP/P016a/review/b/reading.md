# Blind mathematical reading

This file was written from `SAP/P016a/Defs.lean`, all six `Defs/Part*.lean`
files, and the two Challenge files, before opening either `claims.json` or
`record.json`. The Challenge contains ten closed theorems. Each asserts the
entire proposition described below; the displayed universal quantifiers are
inside that proposition, not additional assumptions on the theorem itself.
Comments do not add hypotheses or conclusions.

## Expanded notation and Mathlib endpoints

All unit indices run through `Fin n`, i.e. integers 0,...,n-1. An outcome is an
arbitrary real vector u=(u_i); an assignment is an arbitrary Boolean vector z.
Write z_i also for its numerical indicator (true=1, false=0) where multiplied
by real numbers. Vector literals enumerate entries starting at index 0.
All sums below are finite Mathlib `Finset.univ` sums; counts are ordinary
natural-number counts, coerced to reals before real division. There are no
integrals or limits.

For a group a in {0,1}, define

* n_a(z)=#{i:z_i=a}; G_a(u,z)=sum_{i:z_i=a} u_i;
  mu_a(u,z)=G_a(u,z)/n_a(z).
* bar(u)=sum_i u_i/n; TSS(u)=sum_i (u_i-bar(u))^2.
* R(u,z)=sum_i (u_i-mu_{z_i}(u,z))^2;
  Delta(u,z)=mu_1(u,z)-mu_0(u,z).
* F_a(u,z;t)=#{i:z_i=a and u_i<=t}/n_a(z).
* K(u,z)=max({0} union {|F_1(u,z;u_i)-F_0(u,z;u_i)|:i<n}).
* Kplus(u,z)=max({0} union {F_1(u,z;u_i)-F_0(u,z;u_i):i<n}).
  These are exactly `List.ofFn` followed by `foldr max 0`, not an implicit
  supremum over all real thresholds. An empty list gives 0.
* A(Y,z;t)_i=Y_i-z_i*t (`additiveAdjust`);
  G(y,z;t)_i=y_i+z_i*t (`additiveGenerate`).

Real division uses Mathlib's field convention x/0=0. In particular an empty
group has mu_a=F_a=0. The meanings above report that convention without silently
assuming nonempty groups. When n=0, bar(u)=0.

A finite law P on a finite type Omega is a list of weights P_w>=0 with
sum_w P_w=1. Define P(E)=sum_{w:E(w)} P_w,
E_P f=sum_w P_w f(w), Cov_P(f,g)=E_P(fg)-E_P(f)E_P(g), and
Var_P(f)=Cov_P(f,f). A `FiniteLaw` therefore cannot exist on an empty type.
No positivity of individual weights, injectivity of an assignment map, or
uniformity is implicit. U(Omega) is uniform weight 1/|Omega| and is only
defined here with an explicit nonempty-type instance.

U_P(s;z)=P{s(w)>=s(z)} and L_P(s;z)=P{s(w)<=s(z)} are inclusive tails.
D(L,U)=min(1,2*min(L,U)). For a reference vector r of length B,
l(r,o)=#{b:r_b<=o}, u(r,o)=#{b:o<=r_b}, and
p(r,o)=D(l(r,o)/B,u(r,o)/B).
`printedReject(p)` is p<1/20; `codedReject(p)` is p<=1/20.

For an n by k real matrix X,
Q(u,X;b)=sum_i (u_i-sum_j X_ij b_j)^2,
fit(X;b)_i=sum_j X_ij b_j, and q(u,X)=inf_{b in R^k} Q(u,X;b).
The last is Mathlib real `sInf (Set.range ...)`. Its range is nonempty (take
b=0, also when k=0) and bounded below by 0, so this is the ordinary real
greatest lower bound. No empty-set or unbounded-set default can affect it.
`basicX(z)` has columns (1,z). `applicationX(z,e)` has columns (1,z,e).
For any real matrix S, t(S,z)_i=sum_j z_j S_ji and d(S)_i=sum_j S_ji;
`networkX(S,z)` has columns (1,z,t(S,z),d(S)).

`sameMargins(u,z,v,w)` means equality, for each a=0,1, of the multisets
{u_i:z_i=a} and {v_i:w_i=a}, including multiplicities, not just equality of
means or of empirical-distribution values at selected thresholds.
`pairedCovariance2(t,c)` is sum_{i=0,1}(t_i-bar(t))(c_i-bar(c))/2.

For any S, x(S,z)_i=sum_j S_ij z_j (`exposureSum`, a row sum, in contrast
to t and d above). For a finite assignment bank B_b, define
c(S,B;i,a)=sum_{b:B_bi=a} x(S,B_b)_i / #{b:B_bi=a}, and
h(S,B,z)_i=x(S,z)_i-z_i c(S,B;i,1)-(1-z_i)c(S,B;i,0).
The bank average weights each index equally, including repetitions; an empty
conditional cell gives 0. No probability law is passed to this definition.

Given optional scores s_i, `similarity(s)` has diagonal zero; off diagonal
it is 1-|s_i-s_j|/2 when both scores exist, and 0 if either is missing.
For nonoptional real scores, `distance(s)` has entries |s_i-s_j|.
There is no score-range hypothesis in the definition of similarity, so it
can be negative. A matrix satisfying `IsDistanceMatrix` is nonnegative,
symmetric, zero on the diagonal, and satisfies Gamma_ik<=Gamma_ij+Gamma_jk
for every i,j,k. Distinct units are allowed to have zero distance.

v(h)=sum_i(h_i-bar(h))^2/(n-1), where n-1 is REAL subtraction;
s(h)=sqrt(v(h)); Z(h)_i=(h_i-bar(h))/s(h).
These expand `sampleVariance`, `sampleSD`, and `standardize`.
Mathlib `Real.sqrt` is the nonnegative square root for nonnegative inputs
and is 0 on nonpositive inputs. `codedExposure(S,B,z)` is Z(h(S,B,z));
it is the zero vector if s(h)=0 under the division convention.
`applicationAdjust(Y,z,e;b1,b2)` is the vector Y-z*b1-b2*e.

`Balanced(n,m)` is the finite subtype {z:n_1(z)=m}; it is not assumed
nonempty in its definition. `uniformMass(Omega,E)` is #{w:E(w)}/|Omega|
and equals 0 for an empty type. Here it is used on Balanced(8,4).
`EffectIncreasing(T)` means: for every assignment z, outcomes y,y', if
y_i<=y'_i at treated units and y'_i<=y_i at controls, then T(y,z)<=T(y',z).

The following fixed objects recur:

* C=`complete4`, indexed 0,...,5, lists (1100,1010,1001,0110,0101,0011).
* B=`blocked4`, indexed 0,...,3, lists (1100,1001,0110,0011).
* u=(0,1,2,3)=`u4`.
* M4=`matchedBank4` lists (0101,0110,1001,1010).
* M6=`matchedBank6` is indexed by all b in {0,1}^3 and gives
  (b_0,1-b_0,b_1,1-b_1,b_2,1-b_2), thus eight equally indexed assignments.
* s4=(-1,-1/2,1/2,1), s6=(-1,-3/4,-1/2,0,1/4,1).

`Matrix.det` is Mathlib's ordinary determinant (the alternating sum over
permutations). `Function.Injective` has its ordinary universal meaning.
The Mathlib sources inspected for these endpoints include
`Data/List/OfFn.lean`, `Data/List/MinMax.lean`,
`Algebra/Order/Archimedean/Real/Basic.lean`, `Analysis/Real/Sqrt.lean`, and
`LinearAlgebra/Matrix/Determinant/Basic.lean`. A scratch inspection also
checked the elaborated quantifier order for T4 and T6.

## SAP.P016a.T1

No hypotheses. All of the following hold simultaneously.

1. C is injective, and for every assignment z of four units,
   n_1(z)=2 iff there exists k<6 with C_k=z.
2. B is injective, and for every assignment z of four units,
   (z_0!=z_2 and z_1!=z_3) iff there exists k<4 with B_k=z.
3. The paired covariances of (0,2) with (1,3) and with (3,1) are 1 and -1.
   For assignment C_0, outcomes (0,2,1,3) and (0,2,3,1) both have R=4
   and K=1/2.
4. For every k<6, R(u,C_k)=(1,4,5,5,4,1)_k and
   K(u,C_k)=(1,1/2,1/2,1/2,1/2,1)_k. For every k<4,
   R(u,B_k)=(1,5,5,1)_k and K(u,B_k)=(1,1/2,1/2,1)_k.
5. Under U(Fin 6), P{R(u,C_k)<=R(u,C_0)}=1/3 and
   P{K(u,C_0)<=K(u,C_k)}=1/3; the covariance of mu_1(u,C_k) and
   mu_0(u,C_k) is -5/12. Under U(Fin 4), the analogous two tail masses
   for B relative to B_0 are both 1/2, and the covariance is -1/2.

## SAP.P016a.T2

No outer hypotheses. It asserts eleven independent conjuncts, with the
following quantifiers and assumptions in each.

1. For every natural n with n>=2, every real u of length n, and every
   assignment z with n_0(z)>0 and n_1(z)>0:
   q(u,(1,z))=R(u,z); for every real a,b,
   Q(u,(1,z);(a,b))=R(u,z) iff
   a=mu_0(u,z) and b=Delta(u,z); and
   R(u,z)=sum_i u_i^2-n_0(z)mu_0(u,z)^2-n_1(z)mu_1(u,z)^2.
2. For every n>=2,u,z with both groups nonempty,
   R(u,z)=TSS(u)-[n_0(z)n_1(z)/n]Delta(u,z)^2.
3. For every n>=2,u,z,w, with both z groups nonempty and
   n_1(w)=n_1(z),
   R(u,w)<=R(u,z) iff |Delta(u,z)|<=|Delta(u,w)|.
4. For every n, finite type Omega, law P on Omega, n>=2, u, observed
   assignment zobs, and map assign:Omega->assignments, if both observed
   groups are nonempty and every assign(w) has n_1(zobs) treated units,
   P{R(u,assign(w))<=R(u,zobs)}=
   P{|Delta(u,zobs)|<=|Delta(u,assign(w))|}.
5. For every n>=2,u,z with both groups nonempty,
   R(u,z)=n_0(z)[mu_0(u^2,z)-mu_0(u,z)^2]
          +n_1(z)[mu_1(u^2,z)-mu_1(u,z)^2].
6. For every n>=2, outcomes u,v, and assignments z,w, if both z groups
   are nonempty and sameMargins(u,z,v,w), then
   R(u,z)=R(v,w) and K(u,z)=K(v,w).
7. For every n, finite Omega, law P, n>=2, u, assignment map assign,
   and positive natural n0,n1, if for EVERY w the control and treated
   counts of assign(w) are n0,n1, then:
   for every w, n1*mu_1(u,assign(w))+n0*mu_0(u,assign(w))=n*bar(u);
   Cov_P(mu_1,mu_0)=-(n1/n0)Var_P(mu_1);
   and for EVERY real x, both
   n1*F_1(u,assign(w);x)+n0*F_0(u,assign(w);x)=#{i:u_i<=x}
   for every w, and Cov_P(F_1(x),F_0(x))=-(n1/n0)Var_P(F_1(x)).
   P need not be uniform or give every assignment positive mass.
8. Fix z=C_1=1010 and
   S=[[0,0,1,0],[0,0,0,1],[1,0,0,1],[0,1,1,0]], and X=(1,z,d(S)).
   Then sameMargins(u,z,(2,1,0,3),z); both outcomes have R=4 and K=1/2;
   d(S)=(1,1,2,2); Q(u,X;(-1,-1,2))=q(u,X)=0; and
   Q((2,1,0,3),X;(2,-1,0))=q((2,1,0,3),X)=4.
9. K(u,C_1)=K(u,C_2)=1/2, while R(u,C_1)=4 and R(u,C_2)=5.
10. For every n,u,z, assuming first n_0(z)>0 and then n_1(z)>0,
    R(u,z)=sum_{i:z_i=0}(u_i-mu_0(u,z))^2
           +sum_{i:z_i=1}(u_i-mu_1(u,z))^2.
11. For every n,u,z, assuming n_0(z)>0 and n_1(z)>0, there exists a real
    two-vector b with Q(u,(1,z);b)=q(u,(1,z)).

## SAP.P016a.T3

No hypotheses. Five groups of conclusions are conjoined.

1. Let S=similarity(s4) with every score present. Its matrix is
   [[0,3/4,1/4,0],[3/4,0,1/2,1/4],[1/4,1/2,0,3/4],[0,1/4,3/4,0]].
   Relative to bank M4, (c(i,0))_i=(7/8,9/8,9/8,7/8) and
   (c(i,1))_i=(1/8,3/8,3/8,1/8).
   At z=C_1, x(S,z)=(1/4,5/4,1/4,3/4),
   x(distance(s4),z)=(3/2,3/2,3/2,5/2), and
   h(S,M4,z)=(1/8,1/8,-1/8,-1/8).
   There do not exist real A,B,C making this last vector equal, at all
   four indices, to A+B*z+C*(1/4,5/4,1/4,3/4); nor do such A,B,C exist
   using (3/2,3/2,3/2,5/2) as the last vector.
2. Let S=similarity(s6), z=101010, h=h(S,M6,z), x=x(S,z), and
   y=(0,1,0,1,1,0). Then S is 1/8 times
   [[0,7,6,4,3,0],[7,0,7,5,4,1],[6,7,0,6,5,2],
    [4,5,6,0,7,4],[3,4,5,7,0,5],[0,1,2,4,5,0]].
   At all six indices,
   x=(9/8,9/4,11/8,17/8,1,7/8),
   (c(S,M6;i,z_i))_i=(13/16,31/16,5/4,2,19/16,17/16),
   h=(5/16,5/16,1/8,1/8,-3/16,-3/16), and
   d(S)=(5/2,3,13/4,13/4,3,3/2).
   bar(h)=1/12; v(h)=49/960; Z(h)=sqrt(15)/42*(11,11,2,2,-13,-13).
   There are no real A,C with h=A+C*x at every index, and no real A,B,C
   with h=A+B*z+C*x at every index.
   q(y,(1,z,h))=q(y,(1,z,Z(h)))=4/3;
   q(y,(1,z,x))=655/708;
   q(y,(1,z,x,d(S)))=515/859.
3. The determinant of
   [[1,1,1/4,1/8],[1,0,5/4,1/8],
    [1,1,1/4,-1/8],[1,0,3/4,-1/8]] is 1/8.
   The determinant of
   [[1,0,216630956840236/10^13,370753999962044/10^15],
    [1,0,191947426509578/10^13,240866262449021/10^15],
    [1,1,208676713418681/10^13,286925998351727/10^15],
    [1,1,225467332911212/10^13,-193126413625389/10^15]]
   is -14030283848669586515272953541/10^28.
4. No real A,B,C express
   (370753999962044,240866262449021,286925998351727,-193126413625389)/10^15
   as A+B*(0,0,1,1)+
   C*(216630956840236,191947426509578,208676713418681,225467332911212)/10^13
   at all four indices. These are exact rational vectors; there is no
   assumption tying them to an external data file or rounding interval.
5. Fix 1,000 reference values r_b=b+1 for b=0,...,999.
   At o=25, l=25, u=976, p=1/20, codedReject(p), and not printedReject(p).
   At o=40, l=40, p=2/25, l/1000<=1/20, and not codedReject(p).
   At o=980, l=980, p=21/500, not l/1000<=1/20, and codedReject(p).

## SAP.P016a.T4

No outer hypotheses. Seven conjuncts:

1. For every n,N with n>=2; every real n by n S satisfying symmetry and
   S_ii=0; every bank B:Fin N->assignments such that for every i and a
   there exists b with B_bi=a; every finite SET Omega of assignments such
   that s(h(S,B,z))>0 for every z in Omega; every outcome y0, function
   y:assignments->outcomes, and real b1,b2: if for every z in Omega and
   every i, y(z)_i=y0_i+z_i*b1+b2*Z(h(S,B,z))_i, then for every z in
   Omega, applicationAdjust(y(z),z,Z(h(S,B,z));b1,b2)=y0.
   Omega is allowed to be empty; membership conditions only restrict
   the model and conclusion to it. The bank and Omega need not coincide.
2. For every n>=2, outcomes h,u, assignment z, if s(h)>0, then
   sum_i Z(h)_i=0, sum_i Z(h)_i^2/(n-1)=1, and
   q(u,(1,z,Z(h)))=q(u,(1,z,h)). No nonempty-group condition on z.
3. For every n,N with n>=2, arbitrary real scores s, bank B such that
   each unit appears in each treatment state, assignment z, and natural m:
   if n_1(z)=m and n_1(B_b)=m for every bank index b, then, setting
   S=similarity(all scores present) and D=distance(s),
   x(S,z)_i=m-z_i-(1/2)x(D,z)_i for every i;
   h(S,B,z)_i=-(1/2)h(D,B,z)_i for every i; and IF first
   s(h(D,B,z))>0 and then s(h(S,B,z))>0,
   codedExposure(S,B,z)=-codedExposure(D,B,z) at every index.
   No bounds on s_i are assumed; all bank counts must match the current
   assignment, not merely match one another.
4. For S=similarity(s4), h=h(S,M4,C_1), s(h)>0, and there are no real
   A,B,C with h=A+B*C_1+C*x(S,C_1) at all indices; there are likewise
   no real A,B,C with Z(h)=A+B*C_1+C*x(S,C_1).
5. For every natural B>0, real reference vector r of length B, and real o,
   l(r,o)/B+u(r,o)/B>=1.
6. For all real p,alpha, (p<=alpha and not p<alpha) iff p=alpha.
7. Every conjunct of T3 above, with all the same constants and meanings.

## SAP.P016a.T6

No outer hypotheses. Two conjuncts:

1. For every n>=2; every finite NONEMPTY type Omega; assignment map
   assign:Omega->assignments; matrix Gamma satisfying all four distance
   conditions stated above; function g:R^n->R^n such that, for every w,
   v(g(x(Gamma,assign(w))))=1; outcome y0; outcome map y:Omega->R^n;
   and real b1,b2: if for every w and i,
   y(w)_i=y0_i+b1*assign(w)_i+b2*g(x(Gamma,assign(w)))_i,
   then for every w,
   applicationAdjust(y(w),assign(w),g(x(Gamma,assign(w)));b1,b2)=y0.
   The variance is across unit indices with divisor n-1, separately for
   every design index w. g need not be coordinatewise, monotone, continuous,
   injective, or centered. assign need not be injective or have both groups.
2. For every real p, printedReject(p) iff p<1/20, the defining equivalence.

## SAP.P016a.T7

No hypotheses. All eight conjuncts:

1. C is injective and, for every four-unit assignment z, n_1(z)=2 iff
   there exists k<6 with C_k=z.
2. For every k<6, Delta(u,C_k)=(-2,-1,0,0,1,2)_k and
   Delta(G(u,C_k;10),C_k)=(8,9,10,10,11,12)_k.
   Under uniform j<6, both
   P{|Delta(u,C_j)|>=|Delta(G(u,C_k;10),C_k)|}=0 and
   P{Delta(u,C_j)>=Delta(G(u,C_k;10),C_k)}=0.
   The baseline absolute tail
   P{|Delta(u,C_j)|>=|Delta(u,C_k)|}=(1/3,2/3,1,1,2/3,1/3)_k.
3. For every real alpha>0, uniform k<6 give probability 1 to the event
   that the first (absolute, raw-observed versus baseline-reference)
   p-value in item 2 is strictly less than alpha.
4. For every real alpha, if alpha>0, the same probability-one claim holds
   for the second, signed upper-tail comparison in item 2.
5. For every k<6, A(G(u,C_k;10),C_k;10)=u.
6. Let y_i=i for i<8, let Omega=Balanced(8,4), sp(z)=Kplus(y,z),
   dp(z)=K(y,z). Then |Omega|=70 and, for every z in Omega,
   A(G(y,z;-100),z;-100)=y,
   Kplus(G(y,z;-100),z)=1, and K(G(y,z;-100),z)=1.
   Uniform z in Omega satisfy:
   P{sp(z)>=1}=1/70 and P{dp(z)>=1}=1/35;
   P{P_w{sp(w)>=sp(z)}<1/20}=1/70;
   P{P_w{dp(w)>=dp(z)}<1/20}=1/35;
   P{P_w{sp(w)>=Kplus(G(y,z;-100),z)}<1/20}=1; and
   P{P_w{dp(w)>=K(G(y,z;-100),z)}<1/20}=1.
   All inner and outer laws in these formulas are uniform on Omega.
7. For every z in Balanced(8,4) and i,j<8, if z_i=true and z_j=false,
   then G((0,1,...,7),z;-100)_i<G((0,1,...,7),z;-100)_j.
8. The real inequalities 1/70<1/20 and 1/35<1/20 hold.

## SAP.P016a.T8

No outer hypotheses. Three conjuncts:

1. For every natural n, outcome y, assignment z, and real t,t0,
   A(G(y,z;t),z;t0)=G(y,z;t-t0), and A(G(y,z;t),z;t)=y.
2. For every n, finite Omega, law P, assignment map assign, outcome y0,
   real t, arbitrary statistic T:R^n->Omega->R, and real alpha with
   0<=alpha<=1: for EVERY predicate E on reals,
   P_w{E(T(A(G(y0,assign(w);t),assign(w);t),w))}
     =P_w{E(T(y0,w))}; and
   P_w{U_P(s_w;w)<=alpha}<=alpha, where
   s_w(v)=T(A(G(y0,assign(w);t),assign(w);t),v).
   The reference law is the same P as the observation law; the outcome
   used in s_w is the entire adjusted outcome vector at observed w.
3. For every n, Y,z with n_0(z)>0 and n_1(z)>0, and real t,
   Delta(Y,z)=Delta(A(Y,z;t),z)+t; and
   Delta(Y,z)=Delta(A(Y,z;t),z) iff t=0.

## SAP.P016a.T9

No outer hypotheses. Five conjuncts:

1. For every i<4, F_1(u,C_5;u_i)-F_0(u,C_5;u_i)=(-1/2,-1,-1/2,0)_i;
   Kplus(u,C_5)=0, K(u,C_5)=1, Kplus(u,C_0)=1, K(u,C_0)=1.
2. TSS(u)=5. For the constant statistic k->TSS(u) on uniform k<6,
   both L and U tails at index 0 are 1. The lower tail at index 0 of
   k->R(u,C_k) is 1/3.
3. Fix the six-unit matrix S with only S_01=S_10=1 and all other entries
   zero, z=101010, u=(1,1,1,1,1,1), X=networkX(S,z), and
   W=(z,t(S,z),d(S)), i.e. X with its intercept removed. Then
   X=[[1,1,0,1],[1,0,1,1],[1,1,0,0],[1,0,0,0],[1,1,0,0],[1,0,0,0]];
   Q(u,X;(1,0,0,0))=q(u,X)=0, while
   Q(u,W;(1,1,0))=q(u,W)=2.
4. For every k<6, R(u4,C_k)=(1,4,5,5,4,1)_k.
5. For every positive n, finite Omega, finite law P, outcome u,
   assignment map assign, and observed index z in Omega:
   for every w, the function constant at TSS(u) evaluated on assign(w)
   equals TSS(u); P{that equality}=1; and the inclusive lower and upper
   tails at z of the statistic constant at TSS(u) both equal 1.

## SAP.P016a.T10

No outer hypotheses. Four conjuncts:

1. For every n>=2, u,z with both groups nonempty,
   q(u,(1,z))=R(u,z); for all real a,b,
   Q(u,(1,z);(a,b))=R(u,z) iff a=mu_0(u,z), b=Delta(u,z); and
   R(u,z)=sum_i u_i^2-n_0(z)mu_0(u,z)^2-n_1(z)mu_1(u,z)^2.
2. For every n,k, outcome u, assignment z with n_0(z)>0 and n_1(z)>0,
   and every real n by k matrix X, there exists b with
   Q(u,X;b)=q(u,X). For EVERY b,c, if both attain this infimum, then
   fit(X;b)=fit(X;c). Uniqueness of coefficients is not asserted.
3. For every n,u,z with both groups nonempty,
   K(u,z)=sup_{t in R}|F_1(u,z;t)-F_0(u,z;t)|,
   K(u,z)=K(u,1-z), and 0<=K(u,z)<=1.
   The supremum is real `sSup (Set.range ...)`; its range is nonempty
   and bounded in [0,1], so it has the ordinary supremum meaning.
4. For every n, symmetric real n by n S with S_ij in {0,1}, assignment
   z with both groups nonempty, and index i<n,
   t(S,z)_i=sum_j S_ij z_j and d(S)_i=sum_j S_ij.
   Zero diagonal and fixed group sizes are not hypotheses of this item.

## SAP.P016a.T11

No hypotheses. Four conjuncts:

1. At z=C_0, y=u4=(0,1,2,3) and y'=(2,3,2,3) satisfy y_i<=y'_i
   at treated units and y'_i<=y_i at controls. K(y,z)=Kplus(y,z)=1
   whereas K(y',z)=Kplus(y',z)=0.
   Also y''=(0,1,4,5) and y' satisfy STRICT y''_i<y'_i at treated
   units and y'_i<y''_i at controls; K(y'',z)=1.
2. At the same z, R((0,2,0,2),z)=4,
   R((1,2,0,2),z)=5/2, and R((0,3,0,2),z)=13/2.
   At every index, (0,2,0,2) is <= each of the last two outcome vectors.
3. At every i<4,
   F_1(u4,C_0;u4_i)-F_0(u4,C_0;u4_i)=(1/2,1,1/2,0)_i.
4. None of the four functions K, Kplus, R, and -R on four-unit data
   satisfies EffectIncreasing as expanded above. This asserts four
   explicit failures of a universally quantified implication; it is not
   a statement that every pair of effect-increasing changes reverses a
   statistic, or that all possible statistics fail monotonicity.
