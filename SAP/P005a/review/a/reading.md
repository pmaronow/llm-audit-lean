# Blind mathematical reading

This file was written and saved before opening either `claims.json` or
`record.json`. Its source is the supplied Defs and Challenge files and the
Mathlib definitions identified below. The Challenge contains thirteen theorems:
T1–T7 and T9–T14. Each asserts the correspondingly numbered `T*Statement`.
There is no T8 stub.

## Common objects and fully expanded notation

All population sizes, dimensions and treatment sizes are natural numbers.
Units are indexed by `Fin n`, that is, integers 0 through n−1. All data,
matrices, expectations, variances and inequalities are real.

* U is the set of all n units. D(n,m) consists of every subset S of U of
  cardinality m, each once. C=U\S is its complement. E_m f is
  (sum over S in D(n,m) of f(S))/|D(n,m)|. Pr_m(A) is the number of such
  subsets satisfying A divided by |D(n,m)|. V_m(f)=E_m[(f−E_m f)²].
* For an arm A, M_A(a)=(sum over i in A of a_i)/|A|. M(a)=M_U(a),
  a°_i=a_i−M(a), C_A(a,b)=M_A(ab)−M_A(a)M_A(b), and C(a,b)=C_U(a,b).
  Thus the arm covariance uses divisor |A|, not |A|−1.
* For t in the two-element type {treated,control}, A_t(S) is S or C,
  and s_t is m or the natural-number subtraction n−m, respectively.
* The bound function, for any natural s and arrays a,b on U, is

  B_s(a,b) = 2(n−s)/(s(n−1)) M[(ab−M(ab))²]
  + 2(n−s)n/(s³(n−1)) M(a²) M(b²).

  Here the displayed subtractions in the coefficients are in the reals;
  this notation continues to use the ambient population size n.
* A `Population n d` is arbitrary fixed data x_i in R^d and two outcome
  arrays yT_i,yC_i. The dot product is sum over k=0,...,d−1 of u_k v_k.
  Write xbar_A=M_A(x), G=M(xxᵀ). `standardized P` means xbar_U=0
  and G=I_d. Set h_i=x_i·x_i and κ=max_i h_i/n when n>0.
  `kappa` is literally the real supremum of this finite range.
* τ=M(yT)−M(yC), p=m/n, q=(n−m)/n, and b(y)=M(yx).
  The named `populationSlope` is this vector b(y), without an inverse
  Gram matrix. It is the centered population OLS slope under standardization.
* L_A=M_A(xxᵀ)−xbar_A xbar_Aᵀ,
  N_A(y)=M_A(yx)−M_A(y)xbar_A, and b_A(y)=L_A⁻¹N_A(y).
  The package's pooled quantities are
  Lhat=I_d−p xbar_S xbar_Sᵀ−q xbar_C xbar_Cᵀ,
  Nhat=p N_S(yT)+q N_C(yC), and bhat=Lhat⁻¹Nhat.
  Also N=p b(yT)+q b(yC).
* `interactedRegular P m` means, for every S in D(n,m), both det L_S
  and det L_C are nonzero. `noninteractedRegular P m` means, for every
  such S, det Lhat is nonzero. These are assertions about all assignments.
* The adjusted estimators are
  tauhat=M_S(yT)−M_C(yC)−(xbar_S−xbar_C)·bhat and
  tauhatI=M_S(yT)−M_C(yC)−xbar_S·b_S(yT)+xbar_C·b_C(yC).
* For a single arm A and outcome y, define
  u1_A(y)=M_A(y°x)−M(y°x),
  u2_A(y)=(L_A⁻¹−I_d)N_A(y), and
  u3_A(y)=−xbar_A M_A(y°).
  The pooled vectors are nu1=p u1_S(yT)+q u1_C(yC),
  nu2=(Lhat⁻¹−I_d)Nhat, nu3=p u3_S(yT)+q u3_C(yC).
* Write H(y)=C(h,y). The third-moment coefficient is
  a(n,s)=(n−s)(n−2s)/[(n−1)(n−2)s²].
  `NTTT n m` is a(n,m); `NCCC n m` is a(n,n−m), with the latter
  arm size initially obtained by natural subtraction.
* biasEstimate=[C_C(h,yC)−C_S(h,yT)]/(n−2)
  +(xbar_C−xbar_S)·nu2; tauhatDB=tauhat−biasEstimate.
* e_i(y)=y°_i−x_i·b(y), and
  leading(S)=M_S(e(yT))−M_C(e(yC)).
* The inverse-free arm estimator is
  D_A(y)=M_A(y)−xbar_A·N_A(y)
  +(n−|A|)/[(n−2)|A|] C_A(h,y).
* ScalarPopulation(a,yT,yC,s) has d=1 and x_i=s a_i.
  scalarSlope(A,x,y)=C_A(x,y)/C_A(x,x).
  Observed outcomes are yT_i for i in S and yC_i for i outside S.

The sequence predicate H(d,m,P), named `standingAssumptions`, means exactly:

1. For every n≥3: 1≤d_n≤n and 0<m_n<n.
2. There exists one real K≥0 such that for every n≥3 both M(yT²)≤K
   and M(yC²)≤K, and for every coordinate k in `Fin (d n)`, M(x_k²)≤K.
3. There exists an integer threshold beyond which every P_n is standardized.
4. There exist real lo,hi with 0<lo<hi<1 such that for every n≥3,
   lo<m_n/n<hi.

Each existential constant can depend on the chosen sequences. No assumptions
are imposed on n=0,1,2, apart from whatever is forced by the types.

`stochasticO m R r` means: for every real ε>0 there exist a real M>0
and a natural threshold n0 such that for every n≥n0,
Pr_{m_n}(|R_n(S)|>M r_n)<ε. The sign of r is not built into this
definition; the rates actually used here are real square roots.

`Asymptotics.IsBigO atTop f g` for the real sequences in these stubs
means there is a real constant c such that eventually |f_n|≤c|g_n|.
`Tendsto f atTop (nhds l)` is the usual sequence limit f_n→l.

Mathlib endpoints inspected: `Finset.powersetCard` and its membership lemma
in Data/Finset/Powerset; dotProduct, mulVec and vecMulVec in Data/Matrix/Mul;
the matrix inverse instance in LinearAlgebra/Matrix/NonsingularInverse;
IsBigO/IsBigOWith in Analysis/Asymptotics/Defs; and Real.log in
Analysis/SpecialFunctions/Log/Basic. Matrix multiplication and outer products
are ordinary finite coordinate sums and entrywise products; matrix 1 is I_d.

Total-function conventions matter: real division by zero is zero; matrix
inverse is zero for singular real square matrices; Real.log(0)=0 and its
negative-argument extension is log of absolute value; Real.sqrt is the
nonnegative square root with value zero on nonpositive arguments. Finite
empty means and empty-design expectations therefore become zero. For n>0
the leverage range is finite and nonempty, so its real supremum is its maximum.
All substantive designs in these statements have explicitly positive arm
sizes. Asymptotic sequences can have arbitrary initial total-function values.
An arbitrary dimension d may be zero in the finite universal clauses;
the sequence predicate instead explicitly requires d≥1 from n=3.

## T1

This is a closed assertion about n=6,m=4 and the arrays
a=(0,−3,−1,2,−4,−3), b=(2,1,3,−3,1,1). It has no hypotheses
and asserts the conjunction of every following fact:

* 4≤6, 1≤4, 4<6, and |D(6,4)|=15.
* M(a)=−3/2, M(b)=5/6, C(a,b)=−23/12.
* E_4 C_S(a,b)=−69/40 and V_4(C_S(a,b))=16607/4800.
* B_4(a,b)=3829/1440, and B_4(a,b)<V_4(C_S(a,b)).

## T2

For every natural n,m, under 4≤n, 0<m, m<n, for every arm choice t,
and then every pair of arbitrary real arrays a,b on the n units, both:

E_m C_{A_t}(a,b)=[(s_t−1)n/(s_t(n−1))] C(a,b),

V_m(C_{A_t}(a,b))≤B_{s_t}(a°,b°).

There is no centering or moment hypothesis on the input arrays.

## T3

Let a=(8,−8,1,−1,1,−1,1,−1,1,−1,1,−1,1,−1,1,−1),
y_i=1/64 for i=0,1 and y_i=1 otherwise. Take n=16,d=1,m=8,
x_i=sqrt(8/71)a_i, yT=y, yC=0. No hypotheses are supplied.
The statement asserts all of:

* P is standardized and both interactedRegular and noninteractedRegular hold.
* M(y²)≤1, M(yC²)=0, 1/4<p<3/4, |D(16,8)|=12870.
* κ=32/71, and for every unit i, h_i y_i=8/71.
* V_8(C_S(h,y))=1678565511/8259174400.
* B_8(h,y)=117645319/619438080 and B_8(h,y)<V_8(C_S(h,y)).
* The second expression
  [2(16−8)/(8(16−1))]M(h²y²)
  +[2(16−8)16/(8³(16−1))]M(y²)M(h²)
  equals 334349/1744896, which is also strictly less than V_8(C_S(h,y)).

## T4

This is a conjunction of a finite universal assertion and an asymptotic one.

Finite part: for every natural n,d,m and population P, under n≥4,
0<m<n and standardization, for every arm t and real K satisfying
M(y²)≤K, where y is yT or yC according to t, put u_i=h_i−d and
v=y°. All of these follow:

1. M(h)=d.
2. For every i, 0≤h_i≤nκ and |u_i|≤nκ.
3. d≤nκ.
4. M(u²)=M(h²)−d² and M(u²)≤nκd.
5. M(v²)=M(y²)−M(y)² and M(v²)≤K.
6. M[(uv−M(uv))²]≤M(u²v²)≤n²κ²K.
7. V_m(C_{A_t}(h,y))≤B_{s_t}(u,v).
8. B_{s_t}(u,v)≤[2(n−s_t)/(s_t(n−1))]n²κ²K
   +[2(n−s_t)n/(s_t³(n−1))]nκdK.

No explicit K≥0 is assumed here; it follows from the bounded nonnegative
second moment and n>0. There is no finite positive-dimension assumption.

Asymptotic part: for every d,m : N→N, every dependent population sequence
P_n with dimension d_n, under H(d,m,P), and for every arm t, both

V_{m_n}(C_{A_t}(h,y)) = O(nκ_n²+κ_n d_n/n),

V_{m_n}(C_{A_t}(h,y)/n) = O(κ_n²/n+κ_n d_n/n³).

The second left-hand side is variance of the covariance divided by n,
not variance divided by n. Constants may depend on the sequences and t.

## T5

Let n=6,d=1,m=2, x=(−8/5,−1,0,3/5,4/5,6/5), yT_i=x_i²,
yC_i=2x_i²+3. This is a closed conjunction asserting:

* Standardization and interactedRegular.
* M(yT²)≤28 and M(yC²)≤28, 1/4<p<3/4, |D(6,2)|=15.
* H(yT)=434/625 and H(yC)=868/625.
* E_2[xbar_C·u3_C(yC)]−E_2[xbar_S·u3_S(yT)]=217/2500.
* a(6,4)H(yC)−a(6,2)H(yT)=−217/2500.
* Those last two expressions are unequal.

## T6

For every n,d,m,P, under n≥3, 0<m<n and xbar_U=0 (no Gram
standardization or regularity hypothesis), all five identities hold:

1. E_m[(xbar_S·xbar_S)M_S(yT°)]=a(n,m)H(yT).
2. E_m[(xbar_C·xbar_C)M_C(yC°)]=a(n,n−m)H(yC).
3. E_m[xbar_S·u3_S(yT)]=−a(n,m)H(yT).
4. E_m[xbar_C·u3_C(yC)]=−a(n,n−m)H(yC).
5. E_m[xbar_C·u3_C(yC)]−E_m[xbar_S·u3_S(yT)]
   =−a(n,n−m)H(yC)+a(n,m)H(yT).

## T7

Define a population sequence of dimension one and m_n=floor(n/2):
v_{n,0}=0; for i≥1,
v_{n,i}=−1+2(i−1)/(n−2).
A_{n,0}=1; for i≥1, A_{n,i}=v_{n,i}/n².
z_{n,i}=A_{n,i}−1/n, Q_n=M(z_n²),
x_{n,i}=z_{n,i}/sqrt(Q_n), and yT=yC=v_n.
The index subtraction i−1 is natural subtraction, used only in the branch i≥1.
The definitions remain total for all n, including n<3.

There are no hypotheses: the assertion is the conjunction of all these facts:

1. H(1,floor(n/2),P_n) holds.
2. For every n≥6, P_n is standardized, both outcome second moments
   are ≤1, every covariate coordinate has second moment exactly 1,
   and 1/4<m_n/n<3/4.
3. For every n≥6, interactedRegular holds.
4. κ_n→1 and κ_n log(1)→0.
5. For every n≥6, τ_n=0.
6. For every even n≥6 and every S in D(n,n/2),
   n−6≤|tauhatI_n(S)−τ_n−leading_n(S)|.
7. The remainder R_n(S)=tauhatI_n(S)−τ_n−leading_n(S)
   is not O_p(sqrt(κ_n/n)), in precisely the stochasticO definition above.
8. For every n≥6, Q_n>0.
9. For every n≥6, κ_n log(1)=0.

Negating stochasticO in (7) means that there is an ε>0 such that for
every M>0 and every threshold n0 there exists n≥n0 with
Pr_{m_n}(|R_n|>M sqrt(κ_n/n))≥ε. In particular the non-order assertion
quantifies over the full integer sequence, not just the even subsequence.

## T9

First, for every natural d≥1,
log(max(d,2))≤log(2d)≤2log(max(d,2)).

Second, for every pair of sequences d:N→N and κ:N→R, under the
hypotheses that eventually d_n≥1 and eventually κ_n≥0, all of:

1. κ_n log(2d_n)→0 iff κ_n log(max(d_n,2))→0.
2. If κ_n log(2d_n)→0 then both κ_n→0 and κ_n log(d_n)→0.
3. If eventually d_n≥2, then κ_n log(d_n)→0 iff κ_n log(2d_n)→0.

There is no population sequence, estimator expansion or stochastic conclusion
in this theorem. Log arguments in its substantive tails are positive integers.

## T10

Let n=6,d=1,m=2, a=(−3,−2,−1,0,1,5), y_i=a_i²,
s=sqrt(3/20), x_i=s a_i, yT=y, yC=0. The closed assertion is:

* P is standardized and interactedRegular.
* M(y²)≤121 and 1/4<p<3/4.
* E_2[M_S(y)−xbar_S·N_S(y)+(1/8)C_S(h,y)]=4913/1200.
* E_2[M_S(y)−xbar_S·N_S(y)+(1/2)C_S(h,y)]=20/3.
* M(y)=20/3, and the first expectation is unequal to M(y).

## T11

This statement has four independently universally quantified parts.

Part 1: for every n,d,P, every subset S, outcome array y and real c,
under n≥3, S nonempty and det L_S≠0 (S need not be a prescribed-size
assignment; no standardization or centering is required), both:

M_S(y)−xbar_S·b_S(y)−[−xbar_S·u2_S(y)−c C_S(h,y)]
=M_S(y)−xbar_S·N_S(y)+c C_S(h,y),

M_S(y)−xbar_S·N_S(y)+c C_S(h,y)
=M_S(y)−xbar_S·b(y)−xbar_S·(N_S(y)−b(y))+c C_S(h,y).

Part 2: for every n,d,m,P, under n≥3, 2≤m<n and xbar_U=0,
for every real c define
f_T(c)=−(n−m)/[m(n−1)]+a(n,m)+c(m−1)n/[m(n−1)].
All four conclusions are asserted:

1. E_m[M_S(yT)−xbar_S·N_S(yT)+c C_S(h,yT)]
   =M(yT)+f_T(c)H(yT).
2. f_T(c)=0 iff c=(n−m)/[(n−2)m]. This is uniqueness of the
   cancelling coefficient, not uniqueness of an unbiased estimator when H=0.
3. E_m D_S(yT)=M(yT).
4. Using the other weight c=m/[(n−2)(n−m)] instead, the expectation is
   M(yT)+[(m²−(n−m)²)/((n−2)m(n−m))]
   [(m−1)n/(m(n−1))]H(yT).

Part 3: for every n,d,m,P, under n≥3, 0<m<n, n−m≥2 and
xbar_U=0, for every real c define
f_C(c)=−m/[(n−m)(n−1)]+a(n,n−m)
       +c(n−m−1)n/[(n−m)(n−1)]. All three conclusions hold:

1. E_m[M_C(yC)−xbar_C·N_C(yC)+c C_C(h,yC)]
   =M(yC)+f_C(c)H(yC).
2. f_C(c)=0 iff c=m/[(n−2)(n−m)].
3. E_m D_C(yC)=M(yC).

Parts 2 and 3 do not require Gram standardization or matrix regularity.

Part 4: for every d,m,P sequence satisfying H(d,m,P), and every arm t,
letting A=A_t and choosing y=yT or yC by t,

D_A(y)−[M_A(y)−xbar_A·b(y)] = O_p(sqrt(κ_n/n)).

The stochasticO quantifiers are exactly those given in the common notation.

## T12

Use the same a,y,s as T10 and the scalar array x_i=s a_i. No hypotheses.
Let V_A=C_A(x,x), K_A=C_A(x²,y), W_A=C_A(x,y), and
L=M_C(x) scalarSlope(C,x,y). The assertion is the conjunction:

* M(x)=0 and M(x²)=1.
* For every S in D(6,2), both V_S>0 and V_C>0.
* M(y²)≤121 and 1/4<p<3/4.
* E_2 L=31085815448171/17062566567774.
* E_2[(1/8)K_C+M_C(x)(V_S⁻¹−1)W_C]=12010469/846720.
* E_2[(1/8)K_C+M_C(x)(V_C⁻¹−1)W_C]
  =31085815448171/17062566567774.
* The first and second of these three expectations are unequal.

These are scalar OLS expressions; no identification with the u1+u2+u3
vectors is included in this stub.

## T13

For every n,d,m,P under n≥3, 0<m<n, standardization, and
det L_C≠0 for every S in D(n,m), all of the following hold.
Set w=m/[(n−2)(n−m)], k=(n−m−1)n/[(n−m)(n−1)].

1. E_m[w C_C(h,yC)+xbar_C·u2_C(yC)]
   =E_m[xbar_C·(u1_C(yC)+u2_C(yC)+u3_C(yC))].
2. The latter expectation equals E_m[xbar_C·b_C(yC)].
3. For every S in D(n,m),
   xbar_C·u2_C(yC)=xbar_C·[(L_C⁻¹−I_d)N_C(yC)].
4. E_m[xbar_C·u1_C(yC)]=m/[(n−1)(n−m)] H(yC).
5. E_m[xbar_C·u3_C(yC)]=−a(n,n−m)H(yC).
6. E_m C_C(h,yC)=k H(yC).
7. m/[(n−1)(n−m)]−a(n,n−m)
   =mn(n−m−1)/[(n−1)(n−2)(n−m)²].
8. mn(n−m−1)/[(n−1)(n−2)(n−m)²]=w k.

There is no explicit n−m≥2 hypothesis here: for positive dimension the
control-invertibility hypothesis already prevents a singleton control arm.
For d=0 the empty-dimensional matrices still have determinant one.

## T14

This is a conjunction of four parts, each with its own quantifiers.
Write Δ=xbar_S−xbar_C, CT=C_S(h,yT), CC=C_C(h,yC), and
A0=M_S(yT)−M_C(yC).

Part 1: for every n,d,P,m,S and vector v in R^d, under n≥3,
0<m<n, S in D(n,m), and det Lhat≠0 (no standardization hypothesis),
all five identities:

1. tauhatDB=A0−Δ·Nhat+CT/(n−2)−CC/(n−2).
2. tauhatDB=M_S(yT−x·v)−M_C(yC−x·v)
   −Δ·(Nhat−v)+CT/(n−2)−CC/(n−2).
3. tauhatDB=(A0−Δ·Lhat⁻¹Nhat)
   −(−Δ)·[(Lhat⁻¹−I_d)Nhat]+CT/(n−2)−CC/(n−2).
4. −Δ·Lhat⁻¹Nhat−(−Δ)·[(Lhat⁻¹−I_d)Nhat]=−Δ·Nhat.
5. A0−Δ·Nhat=M_S(yT−x·v)−M_C(yC−x·v)−Δ·(Nhat−v).

Part 2: for every n,d,m,P under n>0, 0<m<n and xbar_U=0,
and then for every S in D(n,m), both

xbar_C−xbar_S=(1/p)xbar_C=−(1/q)xbar_S

(two asserted equalities to the common left-hand side).

Part 3: for every n,d,m,P under n≥3, 0<m<n, standardization and
noninteractedRegular P m,

E_m tauhat−τ=E_m[(xbar_C−xbar_S)·(nu1+nu2+nu3)].

Part 4: for every n,d,m under n≥3 and 0<m<n, there exists one
function F(S,x,yobs) with domain
(subsets of U) × (arrays U→R^d) × (arrays U→R) and values in R,
such that for every population P, if P is standardized, then for every
S in D(n,m) with det Lhat≠0,

(xbar_C−xbar_S)·nu2 = F(S,P.x,observedOutcome(P,S)).

The order is ∀ n,d,m, ∃ F, ∀ P, ∀ S: F may depend on n,d,m
and on its three arguments, but not on unobserved potential outcomes.

