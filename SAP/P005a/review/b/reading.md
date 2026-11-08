# Blind reading of the Challenge

This reading was written from `SAP/P005a/Defs*.lean`, `SAP/P005a/Defs/*.lean`,
and `SAP/P005a/Challenge*.lean` / `Challenge/Part1.lean`, before opening either
`claims.json` or `record.json`. Each Challenge theorem has no external hypotheses:
it asserts the entire corresponding `T…Statement` proposition below. Quantifiers
inside that proposition, including their hypotheses, are given explicitly.

## Common objects and conventions

All scalars are real. A population has natural numbers n,d and fixed arrays
x_i in R^d, Y_Ti,Y_Ci in R, indexed by i=0,...,n-1. No randomness is placed on
these arrays. Dot products are sums of coordinate products. All finite means
use the number of entries as divisor, not a degrees-of-freedom divisor.

Write D(n,m) for all m-element subsets S of {0,...,n-1}, and C=S-complement.
This is literally `Finset.univ.powersetCard m`; Mathlib's membership theorem
says S is a subset with cardinality m and its cardinality theorem gives
|D(n,m)|=binomial(n,m). Write <a>_A=|A|^{-1} sum_{i in A} a_i and <a>=<a>_U.
Write E_m f=|D(n,m)|^{-1} sum_{S in D(n,m)} f(S),
V_m(f)=E_m[(f-E_m f)^2], and P_m(B)=|{S in D(n,m):B(S)}|/|D(n,m)|.
`sampleCov A a b` is c_A(a,b)=<ab>_A-<a>_A<b>_A; `popCov` is c_U.
The centered array a^o is a-<a>. These are finite sums, with no measure integral.
Real division is total, with a/0=0, so an empty-arm mean or an expectation
over an empty assignment set would be zero. All substantive finite assertions
below avoid these cases through their hypotheses or their fixed sizes.

For 0<r<n define the formula used by `covarianceBound`:

B_r(a,b) = 2(n-r)/(r(n-1)) <(ab-<ab>)^2>
           + 2(n-r)n/(r^3(n-1)) <a^2><b^2>.

For arm t in the two-element type {T,C}, A_t=S or C and r_t=m or n-m,
respectively. The subtraction in the natural number r_C=n-m is truncated in
Lean, but m<n wherever it is used substantively.

For a population write x_A=<x>_A (coordinatewise),
G=<xx'>, h_i=x_i'x_i, kappa=max_i h_i/n when n>0,
tau=<Y_T>-<Y_C>, p=m/n, q=(n-m)/n,
b(y)=<yx>, N=p b(Y_T)+q b(Y_C),
L_A=<xx'>_A-x_A x_A', N_A(y)=<yx>_A-<y>_A x_A,
Lhat=I-p x_S x_S'-q x_C x_C', Nhat=p N_S(Y_T)+q N_C(Y_C).
Standardization means exactly x_U=0 and G=I, not an assumption on outcomes.
`Matrix.vecMulVec` is the outer product and `Matrix.mulVec` is usual matrix
times column vector. Matrix inverse is Mathlib's nonsingular inverse:
the usual inverse for nonzero determinant over R, and the zero matrix for
zero determinant. Define beta=Lhat^{-1}Nhat and beta_A(y)=L_A^{-1}N_A(y).
Noninteracted regularity means det(Lhat) != 0 for EVERY S in D(n,m);
interacted regularity means both det(L_S),det(L_C) != 0 for EVERY such S.
The dimension d may be zero unless explicitly restricted. Empty coordinate
sums are then zero and the 0-by-0 determinant is one.

`kappa` is actually the real supremum of the finite range {h_i/n}. For n>0
this range is nonempty and bounded, so it is exactly the maximum just stated;
there is no unbounded supremum in any eventual or finite substantive use.

Define the three arm vectors, for y with y^o=y-<y>:

u1_A(y)=<y^o x>_A-<y^o x>,
u2_A(y)=(L_A^{-1}-I)N_A(y),
u3_A(y)=-x_A <y^o>_A.

Their pooled versions are nu1=p u1_S(Y_T)+q u1_C(Y_C),
nu2=(Lhat^{-1}-I)Nhat, nu3=p u3_S(Y_T)+q u3_C(Y_C).
Let H(y)=c_U(h,y),
a_T(n,m)=(n-m)(n-2m)/((n-1)(n-2)m^2),
a_C(n,m)=a_T(n,n-m).
All displayed subtractions in these real coefficients are ordinary real
subtractions; the n-m used as the second argument of a_T is natural.

The adjusted effect is
  tauhat=<Y_T>_S-<Y_C>_C-(x_S-x_C)' beta.
The interacted effect is
  tauhat_I=<Y_T>_S-<Y_C>_C-x_S'beta_S(Y_T)+x_C'beta_C(Y_C).
The packaged bias estimator and debiased effect are
  Bhat=[c_C(h,Y_C)-c_S(h,Y_T)]/(n-2)+(x_C-x_S)'nu2,
  tauhat_DB=tauhat-Bhat.
For a single arm the inverse-free corrected quantity is
  D_A(y)=<y>_A-x_A'N_A(y)+(n-|A|)/((n-2)|A|) c_A(h,y).
The arm population residual is e_i(y)=y_i-<y>-x_i'b(y), and
  leading=<e(Y_T)>_S-<e(Y_C)>_C.
The observed outcome O_i equals Y_Ti for i in S and Y_Ci otherwise.

For sequences d(n),m(n),P(n), the named standing assumptions mean the
CONJUNCTION of the following, in this order:

* For every n>=3: 1<=d(n)<=n and 0<m(n)<n.
* There exists ONE real K>=0 such that for every n>=3 both outcome second
  moments and every coordinate second moment of x are <=K.
* There exists a threshold after which P(n) is standardized for every n.
* There exist ONE pair lo,hi with 0<lo<hi<1 such that for every n>=3,
  lo<m(n)/n<hi.

No requirements are placed on n<3 by the first, second, or fourth item.
`stochasticO m R r` means
  for every real epsilon>0 there exist M>0 and a natural n0 such that
  for every n>=n0, P_{m(n)}(|R(n,S)|>M r(n))<epsilon.
The M and n0 may depend on epsilon and on the sequences fixed outside.
`Asymptotics.IsBigO atTop f g` is the Mathlib condition
  there exists a real constant C such that eventually |f(n)|<=C|g(n)|.
Here `atTop` on naturals means all n beyond some threshold, and
`Tendsto … atTop (nhds a)` is the ordinary sequential real limit.
`Real.sqrt` is the nonnegative real square root (zero on negative arguments);
`Real.log` is the natural logarithm on positive arguments, is zero at zero,
and equals log|x| for negative x. All asserted logarithm comparisons have
eventually positive arguments. In particular log(1)=0.

The Mathlib endpoints checked were `Data/Finset/Powerset.lean` (powersetCard),
`Data/Matrix/Mul.lean` (outer product and mulVec),
`LinearAlgebra/Matrix/NonsingularInverse.lean` (inverse),
`Analysis/Asymptotics/Defs.lean` (IsBigO), and
`Analysis/SpecialFunctions/Log/Basic.lean` (real logarithm).

## SAP.P005a.T1

A conjunction of closed numerical assertions for n=6,m=4 and
a=(0,-3,-1,2,-4,-3), b=(2,1,3,-3,1,1):

1. 4<=6, 1<=4, 4<6, and |D(6,4)|=15.
2. <a>=-3/2, <b>=5/6, and c_U(a,b)=-23/12.
3. E_4 c_S(a,b)=-69/40 and V_4(c_S(a,b))=16607/4800.
4. B_4(a,b)=3829/1440 and B_4(a,b)<V_4(c_S(a,b)).

There are no universally quantified arrays or hypotheses here: these are
fixed arrays and exact rational calculations.

## SAP.P005a.T2

For every natural n,m, assuming 4<=n, 0<m, m<n, for every arm t and then
every pair of real arrays a,b on n units, BOTH:

* E_m c_{A_t}(a,b) = ((r_t-1)n)/(r_t(n-1)) c_U(a,b).
* V_m(c_{A_t}(a,b)) <= B_{r_t}(a^o,b^o).

This includes arm size one. It does not assume the arrays are centered:
centering occurs on the right side of the inequality.

## SAP.P005a.T3

Take n=16,d=1,m=8,
a=(8,-8,1,-1,1,-1,1,-1,1,-1,1,-1,1,-1,1,-1),
x_i=sqrt(8/71)a_i,
Y_Ti=1/64 for i<2 and 1 for i>=2, and Y_Ci=0.
For this fixed population, all of the following hold:

1. Standardization, interacted regularity, and noninteracted regularity.
2. <Y_T^2><=1, <Y_C^2>=0, and 1/4<p<3/4.
3. |D(16,8)|=12870; kappa=32/71; for EVERY unit i, h_i Y_Ti=8/71.
4. V_8(c_S(h,Y_T))=1678565511/8259174400.
5. B_8(h,Y_T)=117645319/619438080, and it is strictly smaller than
   the preceding variance.
6. The different expression
   2(16-8)/(8(16-1)) <h^2 Y_T^2>
   +2(16-8)16/(8^3(16-1)) <Y_T^2><h^2>
   equals 334349/1744896, also strictly smaller than that variance.

## SAP.P005a.T4

This is a conjunction of a finite universal statement and a sequence statement.

Finite part: for every n,d,m,P, assuming n>=4, 0<m<n and P standardized,
for every arm t, every real K, assuming <y^2><=K where y=Y_T or Y_C for that
arm, put u=h-d, v=y^o. All the following hold:

1. <h>=d.
2. For every i, 0<=h_i<=n kappa and |u_i|<=n kappa; also d<=n kappa.
3. <u^2>=<h^2>-d^2 and <u^2><=n kappa d.
4. <v^2>=<y^2>-<y>^2 and <v^2><=K.
5. <(uv-<uv>)^2><=<u^2 v^2><=n^2 kappa^2 K.
6. V_m(c_{A_t}(h,y))<=B_{r_t}(u,v), and
   B_{r_t}(u,v)<=
   2(n-r_t)/(r_t(n-1)) n^2 kappa^2 K
   +2(n-r_t)n/(r_t^3(n-1)) n kappa d K.

Sequence part: for every d,m,P satisfying the standing assumptions, and every
fixed arm t, with y(n) selected for that arm, BOTH real big-O assertions hold:

* V_{m(n)}(c_{A_t}(h,y))=O(n kappa(n)^2+kappa(n)d(n)/n).
* V_{m(n)}(c_{A_t}(h,y)/n)=O(kappa(n)^2/n+kappa(n)d(n)/n^3).

There is no inverse, regularity, or additional leverage-rate assumption in
either part. The O constants may depend on the population sequence and arm.

## SAP.P005a.T5

For the fixed n=6,d=1,m=2 population
x=(-8/5,-1,0,3/5,4/5,6/5), Y_T=x^2, Y_C=2x^2+3:

1. It is standardized and interacted-regular.
2. Each outcome second moment is <=28; 1/4<p<3/4; |D(6,2)|=15.
3. H(Y_T)=434/625 and H(Y_C)=868/625.
4. E_2[x_C'u3_C(Y_C)]-E_2[x_S'u3_S(Y_T)]=217/2500.
5. a_C(6,2)H(Y_C)-a_T(6,2)H(Y_T)=-217/2500.
6. The two expressions in items 4 and 5 are unequal.

## SAP.P005a.T6

For every n,d,m,P, assuming n>=3, 0<m<n, and ONLY x_U=0 (not G=I),
the following five equalities hold together:

1. E_m[(x_S'x_S)<Y_T^o>_S]=a_T(n,m)H(Y_T).
2. E_m[(x_C'x_C)<Y_C^o>_C]=a_C(n,m)H(Y_C).
3. E_m[x_S'u3_S(Y_T)]=-a_T(n,m)H(Y_T).
4. E_m[x_C'u3_C(Y_C)]=-a_C(n,m)H(Y_C).
5. The control expectation in item 4 minus the treated expectation in item 3
   equals -a_C(n,m)H(Y_C)+a_T(n,m)H(Y_T).

## SAP.P005a.T7

Define for every natural n, i in {0,...,n-1}:
v_i=0 if i=0, and v_i=-1+2(i-1)/(n-2) otherwise;
a_i=1 if i=0, and v_i/n^2 otherwise;
z_i=a_i-1/n; Q_n=<z^2>;
x_i=z_i/sqrt(Q_n), Y_Ti=Y_Ci=v_i, d(n)=1, m(n)=floor(n/2).
The i-1 in the source is natural subtraction, but is used only for i>=1.
These formulas define total arrays even at small n through real zero-division.
The theorem asserts the conjunction:

1. This entire sequence satisfies the standing assumptions as defined above.
2. For EVERY n>=6: standardization, both outcome second moments <=1,
   every covariate coordinate second moment =1, and 1/4<p<3/4.
3. For EVERY n>=6 it is interacted-regular for floor(n/2).
4. kappa(n) tends to 1, and kappa(n)log(1) tends to 0.
5. For EVERY n>=6, tau=0.
6. For EVERY n>=6 that is EVEN, and EVERY S in D(n,n/2),
   n-6<=|tauhat_I-tau-leading|.
7. The remainder tauhat_I-tau-leading is NOT stochasticO at rate
   sqrt(kappa(n)/n), for m(n)=floor(n/2), with the exact epsilon/M/n0
   quantifier order stated above.
8. Separately, for EVERY n>=6, Q_n>0, and for EVERY n>=6,
   kappa(n)log(1)=0.

It makes no claim that the small-n totalized arrays are standardized. The
negated stochastic-O is for the whole sequence, witnessed potentially by
the even subsequence; it is not just a claim that the rate fails to vanish.

## SAP.P005a.T9

Conjunction of:

1. For EVERY natural d>=1,
   log(max(d,2))<=log(2d)<=2log(max(d,2)).
2. For EVERY dimension sequence d and real sequence k, assuming EVENTUALLY
   d(n)>=1 and EVENTUALLY k(n)>=0:
   (a) k(n)log(2d(n))->0 iff k(n)log(max(d(n),2))->0;
   (b) k(n)log(2d(n))->0 implies BOTH k(n)->0 and k(n)log(d(n))->0;
   (c) IF EVENTUALLY d(n)>=2, then k(n)log(d(n))->0 iff
       k(n)log(2d(n))->0.

Here multiplication and max inside the logarithms are natural operations
followed by coercion to R. There is no estimator or stochastic expansion in
this proposition.

## SAP.P005a.T10

Let n=6,d=1,m=2,
a=(-3,-2,-1,0,1,5), y=a^2, s=sqrt(3/20), x=s a,
Y_T=y, Y_C=0. All of the following hold:

1. Standardization and interacted regularity.
2. <y^2><=121 and 1/4<p<3/4.
3. E_2[<y>_S-x_S'N_S(y)+(1/8)c_S(h,y)]=4913/1200.
4. E_2[<y>_S-x_S'N_S(y)+(1/2)c_S(h,y)]=20/3.
5. <y>=20/3 and the expectation in item 3 is unequal to <y>.

## SAP.P005a.T11

A conjunction of four universal statements, each with its own hypotheses.

I. For EVERY n,d,P, EVERY S,y,c (in that order), assuming n>=3, S nonempty,
and det(L_S)!=0, both algebraic identities hold:

  <y>_S-x_S'beta_S(y)-[-x_S'u2_S(y)-c c_S(h,y)]
    =<y>_S-x_S'N_S(y)+c c_S(h,y),
  <y>_S-x_S'N_S(y)+c c_S(h,y)
    =<y>_S-x_S'b(y)-x_S'[N_S(y)-b(y)]+c c_S(h,y).

There is no centering or standardization assumption in I.

II. For EVERY n,d,m,P, assuming n>=3, m>=2, m<n, and x_U=0, for EVERY real c:

1. E_m[<Y_T>_S-x_S'N_S(Y_T)+c c_S(h,Y_T)]
   =<Y_T>+A_T(c)H(Y_T), where
   A_T(c)=-(n-m)/(m(n-1))+a_T(n,m)+c(m-1)n/(m(n-1)).
2. A_T(c)=0 iff c=(n-m)/((n-2)m).
3. E_m D_S(Y_T)=<Y_T>.
4. With the alternative coefficient m/((n-2)(n-m)), the expectation is
   <Y_T>+[(m^2-(n-m)^2)/((n-2)m(n-m))]
           [(m-1)n/(m(n-1))]H(Y_T).

The iff concerns the numerical coefficient A_T(c), NOT uniqueness of c
making the expectation unbiased when H(Y_T)=0. There is no regularity or
Gram-matrix hypothesis in II.

III. For EVERY n,d,m,P, assuming n>=3, 0<m<n, n-m>=2, and x_U=0,
for EVERY real c:

1. E_m[<Y_C>_C-x_C'N_C(Y_C)+c c_C(h,Y_C)]
   =<Y_C>+A_C(c)H(Y_C), where
   A_C(c)=-m/((n-m)(n-1))+a_C(n,m)
          +c(n-m-1)n/((n-m)(n-1)).
2. A_C(c)=0 iff c=m/((n-2)(n-m)).
3. E_m D_C(Y_C)=<Y_C>.

There is no regularity or standardization assumption in III.

IV. For EVERY d,m,P satisfying the standing assumptions and EVERY fixed arm t,
with A=A_t and y selected for that arm, the random difference
  D_A(y)-[<y>_A-x_A'b(y)]
is stochasticO at rate sqrt(kappa(n)/n). No further rate or invertibility
assumption is present. The rate is a real square root.

## SAP.P005a.T12

Use a,y,s,x from T10. Define the scalar slope
b_A=c_A(x,y)/c_A(x,x); no intercept adjustment or matrix convention is hidden.
All of the following fixed-population assertions hold:

1. <x>=0 and <x^2>=1.
2. For EVERY S in D(6,2), c_S(x,x)>0 and c_C(x,x)>0.
3. <y^2><=121 and 1/4<p<3/4.
4. E_2[<x>_C b_C]=31085815448171/17062566567774.
5. E_2[(1/8)c_C(x^2,y)+<x>_C(c_S(x,x)^{-1}-1)c_C(x,y)]
   =12010469/846720.
6. E_2[(1/8)c_C(x^2,y)+<x>_C(c_C(x,x)^{-1}-1)c_C(x,y)]
   =31085815448171/17062566567774.
7. The expectations in items 4 and 5 are unequal.

The inverse in item 5 uses the treated variance, while that in item 6 uses
the control variance. All denominators are strictly positive by item 2.

## SAP.P005a.T13

For EVERY n,d,m,P, assuming n>=3, 0<m<n, standardization, and
det(L_C)!=0 for EVERY S in D(n,m), all the following hold. Put
w=m/((n-2)(n-m)), and all expectations below use E_m.

1. E[w c_C(h,Y_C)+x_C'u2_C(Y_C)]
   =E[x_C'(u1_C(Y_C)+u2_C(Y_C)+u3_C(Y_C))].
2. The latter expectation equals E[x_C'beta_C(Y_C)].
3. For EVERY S in D(n,m), x_C'u2_C(Y_C)
   =x_C'(L_C^{-1}-I)N_C(Y_C).
4. E[x_C'u1_C(Y_C)]=m/((n-1)(n-m)) H(Y_C).
5. E[x_C'u3_C(Y_C)]=-a_C(n,m)H(Y_C).
6. E[c_C(h,Y_C)]=(n-m-1)n/((n-m)(n-1)) H(Y_C).
7. m/((n-1)(n-m))-a_C(n,m)
   =mn(n-m-1)/((n-1)(n-2)(n-m)^2).
8. This last coefficient equals
   [m/((n-2)(n-m))][(n-m-1)n/((n-m)(n-1))].

There is no treated-arm regularity assumption, nor an explicit restriction
n-m>=2. With d>0 the nonzero control determinant itself excludes size one;
d=0 is allowed and gives legitimate zero-coordinate identities.

## SAP.P005a.T14

A conjunction of four statements with separate scopes.

I. For EVERY n,d,P,m,S,v (v a d-dimensional real vector), assuming n>=3,
0<m<n, S in D(n,m), and det(Lhat)!=0, the following five identities hold.
Write Delta=x_S-x_C and R=[c_S(h,Y_T)-c_C(h,Y_C)]/(n-2).

1. tauhat_DB=<Y_T>_S-<Y_C>_C-Delta'Nhat+R.
2. tauhat_DB=<Y_T-x'v>_S-<Y_C-x'v>_C-Delta'(Nhat-v)+R.
3. tauhat_DB=(<Y_T>_S-<Y_C>_C-Delta'Lhat^{-1}Nhat)
              -(x_C-x_S)'(Lhat^{-1}-I)Nhat+R.
4. -Delta'Lhat^{-1}Nhat-(x_C-x_S)'(Lhat^{-1}-I)Nhat
   =-Delta'Nhat.
5. <Y_T>_S-<Y_C>_C-Delta'Nhat
   =<Y_T-x'v>_S-<Y_C-x'v>_C-Delta'(Nhat-v).

There is no standardization assumption in I; Lhat is the formula defined
above regardless of whether it represents an empirical OLS matrix.

II. For EVERY n,d,m,P, assuming n>0, 0<m<n, x_U=0, and then EVERY S in
D(n,m), BOTH x_C-x_S=(1/p)x_C and x_C-x_S=-(1/q)x_S.

III. For EVERY n,d,m,P, assuming n>=3, 0<m<n, P standardized and
noninteracted regularity for EVERY assignment,
  E_m(tauhat)-tau=E_m[(x_C-x_S)'(nu1+nu2+nu3)].

IV. For EVERY n,d,m with n>=3 and 0<m<n, there EXISTS a single function
  F : (subsets S) -> (all n-by-d covariate arrays) -> (all n-outcome arrays) -> R
such that for EVERY population P that is standardized, and EVERY S in
D(n,m) with det(Lhat)!=0,
  (x_C-x_S)'nu2 = F(S,P.x,O(P,S)).
F is chosen before P and S, and may depend on n,d,m. Thus it cannot use
unobserved potential outcomes beyond what is determined by these arguments.

## Coverage

The Challenge contains exactly T1,T2,T3,T4,T5,T6,T7,T9,T10,T11,T12,T13,T14.
There is no T8 stub. No conclusion about why is drawn in this blind reading.
