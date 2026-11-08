# Blind reading of the Challenge

This file was written from `SAP/P034/Defs*.lean`, `SAP/P034/Defs/*.lean`,
`SAP/P034/Challenge*.lean`, `SAP/P034/Challenge/*.lean`, and the relevant Mathlib
sources, before opening `claims.json` or `record.json`. Comments are descriptions;
the propositions below are the actual theorem types after expanding SAP definitions.

## Common objects and Mathlib meanings

A survey model on a set Ω, with values in K and k covariates, is an arbitrary tuple
of functions T:Ω→{0,1}, Y₀,Y₁:Ω→K, R₀,R₁:Ω→{0,1}, X:Ω→Kᵏ. There are no
axioms in the structure. Its realized variables are Y(ω)=Y_{T(ω)}(ω) and
R(ω)=R_{T(ω)}(ω). Boolean values are coded by the rational or real numbers 0,1
where arithmetic is required. `Fin n` consists of the integers 0,…,n−1; the
function type `Fin n → K` is an n-coordinate vector. Products here are ordinary
finite tuples, including when Lean represents them by nested pairs.

For a finite Ω and rational weights w, P_w(E)=Σ_{ω∈Ω}1_E(ω)w(ω),
E_w f=Σω w(ω)f(ω), P_w(A|E)=P_w(A∩E)/P_w(E), and
E_w(f|E)=Σω1_E(ω)w(ω)f(ω)/P_w(E). These definitions alone do not require
normalization, positivity, or a nonzero denominator. Rational division is field
division and is defined as zero for denominator zero. Finite independence of
f and g means, for every pair of values a,b, P_w(f=a,g=b)=P_w(f=a)P_w(g=b).
Conditional finite independence within E means the analogous equality with
each probability conditional on E. Failure of such independence negates this
universal cell factorization.

For a measurable Ω, `IsProbabilityMeasure μ` means μ(Ω)=1. `μ.real E` is
(μ(E)).toReal. On a probability space this is the ordinary real probability;
the extended-real conversion maps infinity to zero, which cannot occur here.
`IndepFun f g μ` means independence of their generated sigma algebras, equivalently
P(f∈A,g∈B)=P(f∈A)P(g∈B) for every measurable pair of sets A,B in their
codomains (Mathlib `Probability/Independence/Basic.lean`, definitions and
`indepFun_iff_measure_inter_preimage_eq_mul`). Bool has its discrete sigma algebra;
real numbers, finite real vectors, and their products have the usual Borel/product
sigma algebras. `MemLp f 2 μ` means almost everywhere strong measurability and
finite L² norm (`MeasureTheory/Function/LpSeminorm/Defs.lean`). For the finite
vector X the norm is the maximum coordinate absolute value; finite second moment
of that norm is equivalent to finite second moment of every coordinate, including
the usual trivial zero-dimensional case.

The SAP event measure is μ_E=μ(E)⁻¹·μ restricted to E, with an extended-nonnegative
real scalar. The SAP event mean is (∫_E f dμ)/P(E), and event probability is
P(A∩E)/P(E). Mathlib's restriction is ordinary measure restriction on the
measurable events at issue. `Measure.map` is pushforward for measurable maps;
outside almost everywhere measurable maps it has a fallback definition, so the
measurability hypotheses matter. The real Bochner integral is defined as zero
for a nonintegrable function (`MeasureTheory/Integral/Bochner/Basic.lean:158`);
the second-moment assumptions in T2 are therefore substantive guards on using
its expressions as expectations.

Matrices are functions of two finite indices. `mulVec` is ordinary matrix-vector
multiplication (finite sums); `det` is the Leibniz determinant. `IsUnit det` over
the reals is equivalently det≠0. Scalar multiplication and rational-to-real matrix
maps are entrywise. The unique-existence quantifier means existence of a solution
and equality of every solution with it.

## SAP.P034.T1

There are no hypotheses or free parameters. This asserts all the following facts
about two fixed weighted finite populations and one fixed frequency table.

World A has Ω_A={0,1}⁵, with coordinates (u,r₀,r₁,x,t), and point weights

    w_A(u,r₀,r₁,x,t) = (1/8) B(p₀(u),r₀) B(p₁(u),r₁),
    B(p,1)=p, B(p,0)=1−p,
    p_s(u)=37/50 if s=u, and 13/50 otherwise.

Its model has T=t, Y₀=Y₁=u (numerically coded), R₀=r₀, R₁=r₁, and one
covariate X=x. Thus Y=u and R=r_t. Its potential-variable bundle is
(u,u,r₀,r₁,x), and τ_A=E_A(Y₁−Y₀). The theorem states:

1. Σω w_A(ω)=1 and, for every ω∈Ω_A, w_A(ω)>0.
2. T is independent of (u,u,r₀,r₁,x), and P_A(T=1)=1/2.
3. For every ω, Y₁(ω)−Y₀(ω)=0, and τ_A=0.
4. For every t∈{0,1}, P_A(R=1|T=t)=1/2.
5. For every t,x,y∈{0,1}, the event S_{txy}={T=t,X=x,Y=y} has positive
   probability, and P_A(R=1|S_{txy})=p_t(y).
6. For every t,x∈{0,1}, R and u fail conditional finite independence within
   {T=t,x-coordinate=x}. Also R₀ and u fail unconditional finite independence.
7. For every t∈{0,1}, P_A(T=t,R=1)>0. The complete-case arm means are
   E_A(Y|T=0,R=1)=13/50 and E_A(Y|T=1,R=1)=37/50. Their difference is
   12/25 and differs from τ_A.
8. For Z=(1,T,X), the actual moments G_A=E_A(ZZᵀ|R=1) and
   h_A=E_A(ZY|R=1) equal

       G* = [[1,1/2,1/2], [1/2,1/2,1/4], [1/2,1/4,1/2]],
       h* = (1/2,37/100,1/4).

   The vector β*=(13/50,12/25,0) satisfies G*β*=h*;
   det G*=1/16; β*'s treatment coordinate equals 12/25 and differs from τ_A.
9. For every real vector β∈ℝ³, G*β=h* if and only if β=β*, with the rational
   matrix, right-hand side, and coefficients embedded in ℝ.

An observed cell is c=(t,x,o)∈{0,1}²×({missing}∪{0,1}). In World A the
observed map is O_A=(t,x,u) when R=1 and (t,x,missing) otherwise. The fixed
integer frequency table has n(t,x,missing)=50, and n(t,x,y)=37 when t=y and
13 otherwise. The theorem additionally states:

10. The total count is 400 and the completed count is 200. For every t,x the
    missing count is 50. For every x, the completed counts for
    (t,y)=(0,1),(0,0),(1,1),(1,0) are respectively 13,37,37,13.
11. Every observed cell c has P_A(O_A=c)>0.
12. Define the T-by-completion count N_{tr}=Σ_c1_{c.t=t, isSome(c.o)=r}n(c),
    and the expected count E_{tr}=(Σ_sN_{ts})(Σ_sN_{sr})/(Σ_cn(c)).
    For every t,r∈{0,1}, N_{tr}=E_{tr}=100. The Pearson statistic
    S=Σ_{t,r}(N_{tr}−E_{tr})²/E_{tr} is zero.
13. The completed sample cross-products are G_s=Σ_completed c n(c)Z_cZ_cᵀ
    and h_s=Σ_completed c n(c)Z_c y_c, with Z_c=(1,t,x).
    G_s=200G* and h_s=200h*.
14. Define pχ(s)=P_{Z∼N(0,1)}(s≤Z²). Here the Gaussian is Mathlib
    `gaussianReal 0 1`, whose second parameter is variance and which is a
    probability measure. Then pχ(S)=1 and it is not the case that pχ(S)<5/100.
15. For every β∈ℝ³, G_sβ=h_s if and only if β=β*.

World B has Ω_B={0,1}⁶, coordinates (y₀,y₁,r₀,r₁,x,t), and weights
w_B=B(13/50,y₀)B(37/50,y₁)/16. Its model has T=t, Y_s=y_s,
R_s=r_s and X=x. Its observed map O_B is (t,x,y_t) if r_t=1 and
(t,x,missing) otherwise. Finally the theorem states:

16. Σωw_B(ω)=1 and every weight is strictly positive.
17. T is independent of (y₀,y₁,r₀,r₁,x), and P_B(T=1)=1/2.
18. The pair (r₀,r₁) is independent of (y₀,y₁,x,t).
19. E_B(Y₁−Y₀)=12/25.
20. For every observed cell c, P_A(O_A=c)=P_B(O_B=c).
21. For every t,x, P_A(O_A=(t,x,missing))=1/8. For every x, probabilities
    of (t,y)=(0,1),(0,0),(1,1),(1,0) in completed cells are respectively
    13/400,37/400,37/400,13/400.

The sample is represented by multiplicities, without an ordered sequence or a
separate product-sampling measure. Positivity of all its cells is an explicit
conclusion. Both uniqueness assertions concern normal equations over real
coefficients; no optimization objective is defined separately.

## SAP.P034.T2

Quantifier order: for every type Ω, for every measurable-space structure on Ω,
for every natural number k (zero allowed), every measure μ on Ω with μ(Ω)=1,
and every model M=(T,Y₀,Y₁,R₀,R₁,X) with real outcomes and k real covariates,
the following ordered list of premises implies the conclusions below:

1. T is measurable.
2. For every t∈{0,1}, Y_t is measurable.
3. For every t∈{0,1}, R_t is measurable.
4. X is measurable.
5. For every t∈{0,1}, Y_t belongs to L²(μ).
6. X belongs to L²(μ) in the finite-vector maximum norm.
7. T is independent of the full tuple (Y₀,Y₁,R₀,R₁,X).
8. 0<P(T=1)<1.
9. For every t∈{0,1}, R_t is independent of (Y₀,Y₁,X), and P(R_t=1)>0.

There is no requirement that R₀ and R₁ be independent of each other, no equality
of their completion probabilities, no finite-support assumption, no invertibility
premise for the first conclusions, and no linear-outcome-model premise.

Put Y=Y_T, R=R_T, C={R=1}, A_t={T=t,R=1},
τ=∫(Y₁−Y₀)dμ, p=P(T=1|C), and Z=(1,T,X₀,…,X_{k−1}).
The index type is the disjoint union {intercept,treatment} ⊔ {0,…,k−1}, so even
for k=0 the intercept and treatment indices remain present. Set
G_{ij}=E(Z_iZ_j|C), h_i=E(Z_iY|C), using the event means described above.
The conclusion is the conjunction of:

1. For every t∈{0,1}, P(A_t)=P(T=t)P(R_t=1), and P(A_t)>0.
2. 0<p<1.
3. For every t∈{0,1}, E(Y|A_t)=∫Y_t dμ.
4. E(Y|A₁)−E(Y|A₀)=τ.
5. For every t∈{0,1}, the pushforward distribution of X under μ_{A_t} equals
   its pushforward distribution under μ.
6. For every covariate index j∈{0,…,k−1}, E((T−p)X_j|C)=0.
7. For every real coefficient vector β indexed by the k+2 regression columns,
   if Gβ=h then β_treatment=τ.
8. If det G is a unit (equivalently, is nonzero), there exists exactly one such
   real coefficient vector satisfying Gβ=h.
9. In the fixed World A from T1, T is independent of its full potential-variable
   bundle, both conditional completion rates P_A(R=1|T=t) equal 1/2,
   R₀ is not independent of u, and R₀ is not independent of (u,u,x).
   Also τ_A=0, G_Aβ*=h_A, β*_treatment=12/25, and β*_treatment≠τ_A.

Item 9 is syntactically inside the implication with all nine premises; it is a
fixed proposition, not a statement about the arbitrary M. The theorem does not
separately assume its identifying conclusions or existence of a normal-equation
solution. The last uniqueness implication is conditional on nonsingularity.

## SAP.P034.T3

No hypotheses or free parameters. Define
m(w,v)=a+bw+cv+dwv+Σ_{j<k}γ_jz_j, for real parameters and covariates, and the
fixed four-cell function f on Boolean factors by f(1,1)=2 and f(0,0)=f(1,0)=f(0,1)=0.
In the interpolation assertion k=0 and both γ and z are the zero empty vectors.
The asserted conjunction is:

1. For every a,b,c,d∈ℝ, [for every w,v∈{0,1}, m(w,v)=f(w,v)] if and only if
   a=0, b=0, c=0, d=2.
2. f(1,0)−f(0,0)=0.
3. (f(1,0)−f(0,0))/2+(f(1,1)−f(0,1))/2=1.
4. f(0,1)−f(0,0)=0.
5. (f(0,1)−f(0,0))/2+(f(1,1)−f(1,0))/2=1.
6. As real numbers, 0≠1.

This is a deterministic interpolation witness, with no claim about actual study
data, a stochastic model, or an estimated causal effect.

## SAP.P034.T4

Quantifier order: for every natural k, every a,b,c,d∈ℝ, and every γ,z∈ℝᵏ,
with m(w,v)=a+bw+cv+dwv+Σ_jγ_jz_j, all the following hold:

1. For every real v, m(1,v)−m(0,v)=b+dv.
2. m(1,0)−m(0,0)=b.
3. m(1,1)−m(0,1)=b+d.
4. For every real w, m(w,1)−m(w,0)=c+dw.
5. m(0,1)−m(0,0)=c.
6. m(1,1)−m(1,0)=c+d.
7. For every real q,
   (1−q)[m(1,0)−m(0,0)]+q[m(1,1)−m(0,1)]=b+qd.
8. For every real p,
   (1−p)[m(0,1)−m(0,0)]+p[m(1,1)−m(1,0)]=c+pd.
9. For every real q, b+qd=b if and only if qd=0.
10. For every real p, c+pd=c if and only if pd=0.
11. For every real q, if q>0 then [b+qd=b if and only if d=0].
12. For every real p, if p>0 then [c+pd=c if and only if d=0].

The weighted identities quantify over all real weights, including [0,1]. No
probability law for the factors or covariates is introduced. The same z is used
on both sides of each contrast, so its additive term cancels.

## SAP.P034.T5

No hypotheses or free parameters. The fixed natural-number count matrix has
13 rows and columns 0,1,2:

| row | count 0 | count 1 | count 2 | reported tenths 0,1,2 |
|---|---:|---:|---:|---|
| 0 | 818 | 777 | 1595 | 282,270,276 |
| 1 | 477 | 475 | 952 | 165,165,165 |
| 2 | 281 | 309 | 590 | 97,107,102 |
| 3 | 266 | 268 | 534 | 92,93,92 |
| 4 | 259 | 240 | 499 | 89,83,86 |
| 5 | 258 | 240 | 498 | 89,83,86 |
| 6 | 224 | 252 | 476 | 77,88,82 |
| 7 | 219 | 214 | 433 | 76,74,75 |
| 8 | 49 | 19 | 68 | 17,7,12 |
| 9 | 24 | 25 | 49 | 8,9,8 |
| 10 | 9 | 39 | 48 | 3,14,8 |
| 11 | 9 | 15 | 24 | 3,5,4 |
| 12 | 5 | 4 | 9 | 2,1,2 |

The fixed column totals are N=(2898,2877,5775). Define P_{ij}=100·count_{ij}/N_j
as a rational. A percentage x rounds to integer n tenths exactly when
n/10−1/20≤x<n/10+1/20. The theorem asserts:

1. 266+268=534; 24+25=49; 2898+2877=5775.
2. P_{3,2}=712/77, 915/100≤712/77<925/100, P_{3,2} rounds to 92 tenths,
   and it does not round to 93 tenths.
3. P_{9,2}=28/33, 75/100≤28/33<85/100, P_{9,2} rounds to 8 tenths,
   and it does not round to 9 tenths.
4. For every row i∈{0,…,12} and column j∈{0,1,2}, P_{ij} rounds to the
   displayed integer tenths in the table above.
5. For every row i, count_{i,0}+count_{i,1}=count_{i,2}.
6. For every column j, Σ_i count_{ij}=N_j.
7. 5775=3·1925 as natural numbers.

All denominators in these fixed expressions are positive. There is no variable
natural subtraction, limit, integral, or empty category index involved.
