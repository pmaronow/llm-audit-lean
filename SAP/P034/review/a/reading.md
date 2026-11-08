# Blind reading of the Challenge statements

This file was written after reading all five Defs parts, the Defs aggregator,
and both Challenge files, and before opening `claims.json` or `record.json`.
Names below are abbreviations for the displayed mathematics, not additional
assumptions. Every Challenge theorem is a `sorry` stub; the reading concerns
its type, not a proof.

## Common definitions and Mathlib meanings

`SurveyModel Ω K k` is just a collection of functions: treatment
`T : Ω → {0,1}`, potential outcomes `Y_t : Ω → K`, potential completion
indicators `R_t : Ω → {0,1}`, and covariates `X : Ω → K^k`.
The record itself imposes no probabilistic, measurable, or moment conditions.
Realized variables are `Y(ω)=Y_{T(ω)}(ω)` and
`R(ω)=R_{T(ω)}(ω)`. Boolean false/true are coded numerically as 0/1 by
`bitQ` and `bitR`.

For a finite type Ω and rational weights w, the SAP definitions are

* `P_w(E) = Σ_{ω∈Ω} 1_E(ω) w(ω)`;
* `E_w f = Σ_ω w(ω) f(ω)`;
* `P_w(E | F) = P_w(E∩F)/P_w(F)`;
* `E_w[f | F] = (Σ_{ω∈F} w(ω) f(ω))/P_w(F)`.

These definitions alone do not require nonnegative weights, normalization,
or nonzero conditioning probabilities. Their rational division is total
(division by zero gives zero). `finiteIndependent w f g` means, in order,
for every a in the codomain of f and every b in the codomain of g,
`P_w(f=a,g=b)=P_w(f=a)P_w(g=b)`. The conditional version makes the same
assertion using each of the three probabilities conditional on the given
event. Negation of one of these propositions means that factorization fails
for at least one pair of values.

In the general probability-space definitions, `μ.real E=(μ E).toReal`.
Mathlib measures take values in the extended nonnegative reals; `toReal`
maps infinity to zero, although a probability measure never gives an event
infinite mass. The SAP event measure is `μ(E)⁻¹ • μ.restrict E`, and the
event mean and event probability are respectively
`(∫_E f dμ)/μ.real E` and `μ.real(A∩E)/μ.real E`. These definitions also
make sense with totalized values at a null event. Mathlib's Bochner integral
is zero for a nonintegrable function. Measurability, moment assumptions,
and positive event probabilities therefore matter to their interpretation.

`IndepFun f g μ` is independence of the sigma algebras pulled back from the
codomains of f and g. With the measurability assumptions present below,
it is ordinary independence, equivalently factorization of probabilities
of inverse images of all measurable pairs of sets. Real codomains carry
their Borel measurable spaces; finite products and finite vectors carry
the corresponding product structures. `MemLp f 2 μ` says that f is almost
everywhere strongly measurable with finite L² norm. For a finite real
covariate vector it is equivalent to all coordinates having finite second
moments (the finite vector uses the usual finite supremum norm).

`Matrix.mulVec G β` is the vector with coordinate `Σ_j G_ij β_j`;
`det` is the ordinary finite determinant. Over the reals, `IsUnit (det G)`
means `det G ≠ 0`. Matrix `map` in the statements is entrywise rational
to real coercion. Measure `map X` is the pushforward measure; here X is
assumed measurable. Mathlib's `gaussianReal 0 1` is the real normal
probability measure with mean 0 and variance 1.

Sources followed: Mathlib `Probability/Independence/Basic.lean` and
`Probability/Independence/Kernel/IndepFun.lean` (`IndepFun` and `Indep`);
`MeasureTheory/Function/LpSeminorm/Defs.lean` (`MemLp`);
`MeasureTheory/Integral/Bochner/Basic.lean` (`integral`);
`MeasureTheory/Measure/{Real,Restrict,Map}.lean`;
`Data/Matrix/Mul.lean`; `LinearAlgebra/Matrix/Determinant/Basic.lean`;
`Probability/Distributions/Gaussian/Real.lean`.

## SAP.P034.T1

There are no hypotheses or user-supplied parameters. It asserts a conjunction
about two explicitly fixed finite distributions and a fixed data multiset.

World A has Ω_A={0,1}^5, with coordinates `(u,r₀,r₁,x,t)`. Write
`p_t(u)=37/50` if t=u and `13/50` otherwise, and
`B(p,r)=p` for r=1 and `1-p` for r=0. Its point weight is
`w_A=(1/8) B(p₀(u),r₀) B(p₁(u),r₁)`.
Its model is `T=t`, `Y₀=Y₁=u` (rational coding), `R₀=r₀`, `R₁=r₁`,
and the single covariate is X=x. The Boolean bundle
`(u,u,r₀,r₁,x)` encodes the actual full potential-variable bundle.
Define τ_A=E_A(Y₁−Y₀), `m_t=E_A[Y | T=t,R=1]`,
Z=(1,T,X)', `G_A=E_A[ZZ' | R=1]`, and `h_A=E_A[ZY | R=1]`.
The following are all asserted:

1. `Σ_ω w_A(ω)=1`, and for every ω, `w_A(ω)>0`.
2. T is independent of `(u,u,r₀,r₁,x)`, and `P_A(T=1)=1/2`.
3. For every ω, `Y₁(ω)−Y₀(ω)=0`, and τ_A=0.
4. For every t∈{0,1}, `P_A(R=1 | T=t)=1/2`.
5. For every t, then x, then y in {0,1}, the event
   `{T=t,X=x,Y=y}` has strictly positive probability, and
   `P_A(R=1 | T=t,X=x,Y=y)=p_t(y)`.
6. For every t and x, R and u fail to be conditionally independent within
   `{T=t,X=x}`. Also R₀ and u fail to be unconditionally independent.
7. For every t, `P_A(T=t,R=1)>0`.
8. `m₀=13/50`, `m₁=37/50`, `m₁−m₀=12/25`, and `m₁−m₀≠τ_A`.
9. The computed G_A and h_A equal

   ```text
   G = [ 1    1/2  1/2 ]       h = (1/2,37/100,1/4)'
       [ 1/2  1/2  1/4 ]       β* = (13/50,12/25,0)'.
       [ 1/2  1/4  1/2 ]
   ```

   Moreover `det G=1/16`, `G β*=h`, the treatment coordinate
   `β*_1=12/25`, and `β*_1≠τ_A`.
10. For every real vector β∈ℝ³, in that quantifier order,
    `G β=h` if and only if `β=β*`, with the rational entries embedded in ℝ.

An observed cell is `(t,x,o)∈{0,1}²×Option {0,1}`, where o is missing
or an observed y. World A's observed-cell map is `(t,x,some u)` when
R=1 and `(t,x,none)` otherwise. The fixed data multiset assigns count 50
to every missing cell and count 37 to an observed cell with y=t,
13 to an observed cell with y≠t. It asserts:

11. The sum of all cell counts is 400; the sum of the completed counts is
    200. For every t,x, the missing count is 50. For each x the four
    completed counts for `(t,y)=(0,1),(0,0),(1,1),(1,0)` are
    13,37,37,13 respectively. Every observed cell has positive population
    probability under world A.
12. For every t and r, the T-by-completion table count is 100 and its
    Pearson expected count, computed as row total times column total
    divided by total sample count, is 100. Pearson's sum of
    `(observed−expected)²/expected` over all four cells is zero.
13. The sample design cross-product over completed records is `200 G`,
    and the sample design-outcome cross-product is `200 h`. Missing cells
    contribute zero to both sums. For every real β, the completed-sample
    normal equations hold if and only if β=β*.
14. With `pχ(s)=P_{Z∼N(0,1)}(s≤Z²)`, the p-value at the rational
    Pearson statistic embedded in ℝ is 1, and it is not less than 5/100.

World B has Ω_B={0,1}^6 with coordinates `(y₀,y₁,r₀,r₁,x,t)` and weight
`w_B=B(13/50,y₀) B(37/50,y₁)/16`. Its model is T=t, Y₀=y₀,
Y₁=y₁, R₀=r₀, R₁=r₁, X=x. Its observed-cell map is
`(t,x,some y_t)` if r_t=1 and `(t,x,none)` otherwise. It asserts:

15. `Σ_ω w_B(ω)=1` and, for every ω, `w_B(ω)>0`.
16. T is independent of `(y₀,y₁,r₀,r₁,x)`, and `P_B(T=1)=1/2`.
    The pair `(r₀,r₁)` is independent of `(y₀,y₁,x,t)`.
17. `E_B(Y₁−Y₀)=12/25`.
18. For every observed cell c, its probability is equal under A and B.
    For every t,x the missing-cell probability under A is 1/8; for every
    x the completed-cell probabilities in the order
    `(0,1),(0,0),(1,1),(1,0)` of (t,y) are
    13/400,37/400,37/400,13/400.

The sample positivity clause is positivity of each of its cell probabilities;
the type contains no explicit product sampling measure or sample-event
probability. Both coefficient uniqueness clauses concern real normal-equation
solutions. No explicit minimization objective is defined.

## SAP.P034.T2

Quantifier order: for any type Ω (any Lean universe admitted by `Type*`),
then any measurable-space structure on Ω, then every natural k, every measure
μ on Ω, every instance asserting μ is a probability measure, and every
model `M : SurveyModel Ω ℝ k`, the following hypotheses imply the stated
conjunction. The hypotheses occur in this order:

1. T is measurable.
2. For every t∈{0,1}, Y_t is measurable.
3. For every t∈{0,1}, R_t is measurable.
4. X as a finite real vector is measurable.
5. For every t, Y_t belongs to L²(μ).
6. X belongs to L²(μ).
7. T is independent of the **joint** bundle `(Y₀,Y₁,R₀,R₁,X)`.
8. `0<P(T=1)<1`.
9. For every t∈{0,1}, R_t is independent of the **joint** bundle
   `(Y₀,Y₁,X)` and `P(R_t=1)>0`.

Set E={R=1}, A_t={T=t,R=1},
`p=P(T=1 | E)`, `τ=∫(Y₁−Y₀)dμ`,
and `Z=(1,T,X₀,…,X_{k−1})'`. Coordinates of Z are indexed by the
disjoint sum `Fin 2 ⊕ Fin k`; `inl 0` is the intercept and `inl 1` the
treatment. Set `G_ij=E[Z_i Z_j | E]` and `h_i=E[Z_i Y | E]` using the
event-integral definitions above. The conclusions are:

1. For every t, `P(A_t)=P(T=t)P(R_t=1)` and `P(A_t)>0`.
2. `0<p<1`.
3. For every t, `E[Y | A_t]=∫Y_t dμ`.
4. `E[Y | A_1]−E[Y | A_0]=τ`.
5. For every t, the law of X under normalized restriction to A_t equals
   its original law: `(μ(A_t)⁻¹ • μ|A_t).map X=μ.map X`.
6. For every covariate coordinate j∈Fin k,
   `E[(T−p)X_j | E]=0`.
7. For every real coefficient vector β indexed by `Fin 2 ⊕ Fin k`,
   if `G β=h`, then its treatment coordinate `β_(inl 1)=τ`.
8. If `det G` is a unit in ℝ, there exists exactly one real coefficient
   vector solving `G β=h`.

In addition, **under the same antecedents**, it concludes the following
fixed finite-world proposition about world A from T1; this proposition has
no dependence on Ω, μ, k, or M:

* T is independent of `(u,u,r₀,r₁,x)`;
* for every t, `P_A(R=1 | T=t)=1/2`;
* R₀ is independent of neither u nor `(u,u,x)`;
* τ_A=0, `G_A β*=h_A`, `β*_1=12/25`, and `β*_1≠τ_A`.

There is no hypothesis asserting the identification conclusion, no assumption
that the general G is nonsingular, and no assumption that the two potential
completion rates are equal. The last uniqueness conclusion is conditional.
For k=0 only the covariate-coordinate conclusion is an empty conjunction;
the two regression columns and all other conclusions remain.

## SAP.P034.T3

There are no hypotheses or external parameters. Define a real four-cell
function F by `F(1,1)=2` and `F(0,0)=F(1,0)=F(0,1)=0`.
The general fitted function in the definitions is

`m(w,v;z)=a+bw+cv+dwv+Σ_j γ_j z_j`.

Here it is specialized to k=0, so the covariate sum is an actual empty
sum and is identically zero. The first conjunct quantifies, in order,
over every real a,b,c,d and says

`(for every Boolean w, then every Boolean v,
  a+bw+cv+dwv=F(w,v))`
`if and only if a=0 and b=0 and c=0 and d=2`.

The remaining conjuncts say

* `F(1,0)−F(0,0)=0`;
* `½(F(1,0)−F(0,0))+½(F(1,1)−F(0,1))=1`;
* `F(0,1)−F(0,0)=0`;
* `½(F(0,1)−F(0,0))+½(F(1,1)−F(1,0))=1`;
* as real numbers, 0≠1.

It is a fixed interpolation and contrast example. It contains neither a
probability distribution nor random assignment, potential outcomes, or a
causal-effect definition. The four cells are constructed data, not asserted
to be the paper's empirical estimates.

## SAP.P034.T4

Quantifier order: for every natural k, then every real a,b,c,d, then every
pair of finite real vectors γ,z∈ℝ^k, all the following identities and
equivalences hold, with m as defined in T3:

1. For every real v, `m(1,v;z)−m(0,v;z)=b+dv`.
2. `m(1,0;z)−m(0,0;z)=b` and `m(1,1;z)−m(0,1;z)=b+d`.
3. For every real w, `m(w,1;z)−m(w,0;z)=c+dw`.
4. `m(0,1;z)−m(0,0;z)=c` and `m(1,1;z)−m(1,0;z)=c+d`.
5. For every real q,
   `(1−q)[m(1,0;z)−m(0,0;z)]+q[m(1,1;z)−m(0,1;z)]=b+qd`.
6. For every real p,
   `(1−p)[m(0,1;z)−m(0,0;z)]+p[m(1,1;z)−m(1,0;z)]=c+pd`.
7. For every real q, `b+qd=b ↔ qd=0`; for every real p,
   `c+pd=c ↔ pd=0`.
8. For every real q, if q>0 then `b+qd=b ↔ d=0`; for every real p,
   if p>0 then `c+pd=c ↔ d=0`.

There are no other hypotheses. In particular p and q need not lie in
[0,1]; the claimed identities include those probability weights as special
cases. The covariate vector z is held fixed within every contrast. There
are no causal or statistical identification assumptions.

## SAP.P034.T5

There are no hypotheses or external parameters. The fixed counts and
reported corrected percentages (in tenths of one percent) are:

| i | count: no information, information, total | corrected tenths: same order |
|---|---|---|
| 0 | 818,777,1595 | 282,270,276 |
| 1 | 477,475,952 | 165,165,165 |
| 2 | 281,309,590 | 97,107,102 |
| 3 | 266,268,534 | 92,93,92 |
| 4 | 259,240,499 | 89,83,86 |
| 5 | 258,240,498 | 89,83,86 |
| 6 | 224,252,476 | 77,88,82 |
| 7 | 219,214,433 | 76,74,75 |
| 8 | 49,19,68 | 17,7,12 |
| 9 | 24,25,49 | 8,9,8 |
| 10 | 9,39,48 | 3,14,8 |
| 11 | 9,15,24 | 3,5,4 |
| 12 | 5,4,9 | 2,1,2 |

Column totals D are (2898,2877,5775). For every row i∈Fin 13 and column
j∈Fin 3, the rational percentage is `P_ij=100 C_ij/D_j`.
`roundsToTenth(x,n)` means exactly
`n/10−1/20 ≤ x < n/10+1/20`; this resolves half-ties upward for these
nonnegative quantities. The theorem asserts all of the following:

1. In natural numbers, `266+268=534`, `24+25=49`, and
   `2898+2877=5775`.
2. `P_3,2=712/77`, `915/100≤712/77<925/100`,
   `roundsToTenth(P_3,2,92)`, and not `roundsToTenth(P_3,2,93)`.
3. `P_9,2=28/33`, `75/100≤28/33<85/100`,
   `roundsToTenth(P_9,2,8)`, and not `roundsToTenth(P_9,2,9)`.
4. For every i, then every j, P_ij rounds to the corresponding listed
   corrected tenths.
5. For every row i, `C_i,0+C_i,1=C_i,2`.
6. For every column j, `Σ_i C_ij=D_j`.
7. In natural numbers, `5775=3·1925`.

Only count equalities use natural arithmetic; percentages, interval
endpoints, and division use rationals. No truncated subtraction occurs in
the percentage or rounding definitions.
