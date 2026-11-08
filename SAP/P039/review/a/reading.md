# Blind reading of P039

This file was written from `SAP/P039/Defs*.lean`, `SAP/P039/Defs/*.lean`, and
`SAP/P039/Challenge*.lean` / `Challenge/Part1.lean` before opening either
`claims.json` or `record.json`. The Challenge has seven closed propositions,
`SAP.P039.T1` through `SAP.P039.T7`. None has an outer hypothesis or an
unmentioned typeclass parameter. Each is exactly its corresponding `TjStatement`.
The comments are not additional logical hypotheses.

## Common meanings, including Mathlib definitions

All scalars are real numbers unless indicated otherwise. `Fin n → ℝ` is the
ordinary space of n real coordinates, indexed 0 through n−1. Matrices are
functions of two such indices. `dotProduct v w` is Σᵢ vᵢwᵢ
(Mathlib `Data/Matrix/Mul.lean:72`), `A *ᵥ v` has ith coordinate
Σⱼ Aᵢⱼvⱼ (`:698`), and `squaredLength v` is Σᵢvᵢ².
Matrix transpose, matrix multiplication, scalar multiplication, and identity
matrix have their usual finite-dimensional meanings. Matrix rank is the real
dimension of the image of its linear map (`LinearAlgebra/Matrix/Rank.lean:134`).

For an n-by-p design A and response y, abbreviate

* `FCR(A)`: the map β ↦ Aβ is injective (full column rank).
* β̂(A,y) = (AᵀA)⁻¹Aᵀy; e(A,y) = y−Aβ̂(A,y); SSE(A,y) = ‖e(A,y)‖².
* Vⱼ(A,y) = SSE(A,y)/(n−p) · ((AᵀA)⁻¹)ⱼⱼ.
* SEⱼ(A,y) = √Vⱼ(A,y), s(A,y) = √(SSE(A,y)/(n−p)).
* tⱼ(A,y) = β̂ⱼ(A,y)/√Vⱼ(A,y), and τⱼ(A,y) = β̂ⱼ(A,y)²/Vⱼ(A,y).
* LS(A,y,β): for every competing vector b, ‖y−Aβ‖² ≤ ‖y−Ab‖².
* L(x) = [1,x], D(Z,x) = [Z,x], P(Z)=Z(ZᵀZ)⁻¹Zᵀ, M(Z)=I−P(Z).

Subtraction in n−p in the variance formulas is **real** subtraction. Matrix
inverse is Mathlib's determinant/adjugate inverse, zero on singular matrices
(`LinearAlgebra/Matrix/NonsingularInverse.lean:168`). Real division is total,
with division by zero equal to zero. `Real.sqrt` is the nonnegative square
root for nonnegative inputs and zero on negative inputs
(`Analysis/Real/Sqrt.lean:112`). Thus the above definitions alone are total
formulas; any nondegeneracy must come from the assertions below.

`gaussianReal m v` is the normal probability measure with mean m and
**variance** v, with v a nonnegative real; v=0 gives the Dirac measure at m
(`Probability/Distributions/Gaussian/Real.lean:222`). `Measure.pi` is finite
product measure (`MeasureTheory/Constructions/Pi.lean:210`), `.prod` is binary
product measure (`MeasureTheory/Measure/Prod.lean:171`), and `.map f` is
pushforward for an almost-everywhere measurable f. The latter has an arbitrary
Dirac fallback for a nonmeasurable map of a nonzero measure
(`MeasureTheory/Measure/Map.lean:99`); the displayed maps here are built from
Borel operations on real coordinates. Let χ²ν be the law of Σᵢ₌₁^ν Gᵢ² for
independent standard normals. Let Tν be the law of
G₀/√((Σᵢ₌₁^ν Gᵢ²)/ν), from ν+1 independent standard normals. This definition
uses zero for a zero denominator; in every theorem occurrence ν is 3 or 4,
so that exceptional event has probability zero.

The covariance definition is
Cμ(ε)ᵢⱼ = ∫(εᵢ−∫εᵢdμ)(εⱼ−∫εⱼdμ)dμ.
These are real Bochner integrals, which are zero by convention for
nonintegrable integrands (`MeasureTheory/Integral/Bochner/Basic.lean:204`).
`Integrable` requires almost-everywhere strong measurability and a finite
integral of the norm (`MeasureTheory/Function/L1Space/Integrable.lean:59`).
The explicit integrability clauses below are part of the assertions.

## T1

A quarter-growth series h is **any** function ℕ→ℝ, not just a sixteen-tuple.
For d∈ℝ put

N(d,h)=h₁₆/3+Σₖ₌₀^13 d^(k+1)h₁₅₋ₖ,
D(d)=1/3+Σₖ₌₀^13 d^(k+1), and G=N/D.
Put N⁺(d,h)=h₁₆/3+Σₖ₌₀^14 d^(k+1)h₁₅₋ₖ,
D⁺(d)=1/3+Σₖ₌₀^14 d^(k+1), and G⁺=N⁺/D⁺.
The natural subtraction 15−k never truncates on these summation ranges.
Let h* be 1 at quarter 1 and zero at every other natural number.

The theorem is the conjunction of the following, with no external hypotheses:

1. For every real d, **if d≥0**, then D(d)>0 and D⁺(d)>0;
   for every pair h,h′, if hq=h′q for every natural q with 2≤q≤16,
   then N(d,h)=N(d,h′) and G(d,h)=G(d,h′);
   for every h, N⁺(d,h)−N(d,h)=d¹⁵h₁;
   and D⁺(d)−D(d)=d¹⁵.
2. 0<1/2<1; h*₁=1; for every q with 2≤q≤16, h*q=0;
   N(1/2,h*)=G(1/2,h*)=0;
   N⁺(1/2,h*)=1/32768; D⁺(1/2)=131069/98304;
   G⁺(1/2,h*)=3/131069>0 and differs from G(1/2,h*).
3. 0<9/10<1; N(9/10,h*)=G(9/10,h*)=0;
   N⁺(9/10,h*)=205891132094649/10¹⁵;
   D⁺(9/10)=22440939433444477/(3·10¹⁵);
   G⁺(9/10,h*)=617673396283947/22440939433444477>0 and
   differs from G(9/10,h*).
4. (1/2)¹⁵=1/32768;
   1/3+32767/32768=131069/98304;
   (9/10)¹⁵=205891132094649/10¹⁵.

## T2

Using exactly the N,D,G,N⁺,D⁺,G⁺ just defined, this is the conjunction:

1. For every real d and every series h, **if d≥0**, then
   D(d)≥1/3, D(d)>0, D⁺(d)>0; for every h′ agreeing with h at
   all natural q with 2≤q≤16, N(d,h)=N(d,h′) and G(d,h)=G(d,h′);
   N⁺(d,h)=N(d,h)+d¹⁵h₁; D⁺(d)=D(d)+d¹⁵;
   G⁺(d,h)−G(d,h)=d¹⁵(h₁−G(d,h))/D⁺(d);
   and G⁺(d,h)=G(d,h) **if and only if** d=0 or h₁=G(d,h).
2. For every series h, D(0)=1/3 and G(0,h)=h₁₆;
   D(1)=43/3 and G(1,h)=(3/43)(h₁₆/3+Σₖ₌₀^13 h₁₅₋ₖ);
   0⁰=1; for every natural k, 1ᵏ=1; and for every natural k with
   1≤k, 0ᵏ=0.

## T3

The concrete six-vectors are
u=(1,−1,0,0,0,0), v=(0,0,1,−1,0,0), w=(0,0,0,0,1,−1),
y=u+(3/2)v+w, and Z=[1,u]. Write r=e(Z,y).
There are no outer hypotheses. The theorem asserts all of:

* ZᵀZ=diag(6,2), FCR(Z), r=(0,0,3/2,−3/2,1,−1),
  SSE(Z,y)=13/2, M(Z)ᵀ=M(Z), M(Z)²=M(Z), rank M(Z)=4,
  and M(Z)y=r.
* Each of the following designs has full column rank; each displayed β̂
  minimizes squared residual length; and for **every** coefficient vector b,
  if LS holds for b then b equals the displayed β̂ (uniqueness).
  The residuals, SSE, tested-coordinate variance V, and τ are:

| design, response; tested coordinate | β̂ | residual | SSE | V | τ |
| --- | --- | --- | --- | --- | --- |
| L(v),r; 1 | (0,3/2) | w | 2 | 1/4 | 9 |
| D(Z,v),y; 2 | (0,1,3/2) | w | 2 | 1/3 | 27/4 |
| L(u+v),r; 1 | (0,3/4) | (−3/4,3/4,3/4,−3/4,1,−1) | 17/4 | 17/64 | 36/17 |
| D(Z,u+v),y; 2 | (0,−1/2,3/2) | w | 2 | 1/3 | 27/4 |

* (u+v)ᵀM(Z)(u+v)=2, ‖u+v‖²=4, and 3/4=(3/2)·2/4.
* Define the real functions
  f₄(t)=1−(3/2)z+(1/2)z³, z=t/√(4+t²), and
  f₃(t)=1−(2/π)(arctan q+q/(1+q²)), q=t/√3.
  Then t₁(L(v),r)=3, t₂(D(Z,v),y)=3√3/2,
  f₄(t₁(L(v),r))<1/20<f₃(t₂(D(Z,v),y)).
  FCR of Z,L(v),D(Z,v) is repeated in this conjunct.
* f₄(3)=1−45/(13√13)<1/20;
  f₃(3√3/2)=1/2−(2/π)(arctan(1/5)+6/13)>1/20.
* FCR of all five designs is repeated; τ₁(L(v),r)=9 and
  τ₂(D(Z,v),y)=27/4 are explicitly unequal; the slopes
  β̂₁(L(u+v),r)=3/4 and β̂₂(D(Z,u+v),y)=3/2 are explicitly unequal.
* For **every** nonnegative real σ, **if σ>0**, then for **every**
  γ∈ℝ², let μ be the product of six N(0,σ²) measures, and, for ε∈ℝ⁶,
  set S(ε)=t₁(L(v), e(Z,Zγ+ε)), U(ε)=vᵀε/(σ√2),
  V(ε)=SSE(D(Z,v),Zγ+ε)/σ². Then
  the μ-law of (U,V) is N(0,1)×χ²₃;
  for **every ε**, S(ε)=U(ε)/√(V(ε)/4);
  the μ-law of S is the law of √(4/3)T₃;
  ∫S²dμ=4, ∫t²dT₃=3, ∫t²dT₄=2;
  the μ-law of S is different from T₄; and S² under μ and t²
  under each of T₃,T₄ are all integrable.

The two f-functions are analytic real expressions in this proposition; no
equation identifies them with probabilities of sets under T₃ or T₄.

## T4

This is a conjunction of two universally quantified statements.

First: for **every natural n,k**, every real n-by-k matrix Z and every
x,y∈ℝⁿ, **if**, in order, FCR(Z), there exists c∈ℝᵏ with Zc=1,
there does not exist c∈ℝᵏ with Zc=x, and k+1<n, then the following
conclusions all hold. Define P=P(Z), M=M(Z), r=My,
x̄=(Σᵢxᵢ)/n, xc=x−x̄1, sm=xᵀMx, sc=‖xc‖²,
c=xᵀr, a=c/sc, b=c/sm, sr=‖r‖²−c²/sc, sf=‖r‖²−c²/sm.

* Pᵀ=P, P²=P, Mᵀ=M, M²=M, MZ=0;
  Σᵢrᵢ=0, Mxc=Mx, xcᵀr=c, c=xᵀMy.
* sc=sm+‖Pxc‖², sm>0, sm≤sc;
  sm=sc iff Pxc=0; Pxc=0 iff for **every** column j of Z,
  xcᵀZⱼ=0.
* β̂(L(x),r)=(−ax̄,a), LS(L(x),r,(−ax̄,a)),
  SSE(L(x),r)=sr; there exists **exactly one** β with
  LS(D(Z,x),y,β); the last coordinate of β̂(D(Z,x),y) is b;
  SSE(D(Z,x),y)=sf.
* a=b·sm/sc; a>0 iff b>0; a<0 iff b<0; |a|≤|b|;
  a=b iff b=0 or Pxc=0; sf≤sr.
* V₁(L(x),r)=sr/((n−2)sc), and
  Vlast(D(Z,x),y)=sf/((n−k−1)sm).
* **If sf>0**, then
  τ₁(L(x),r)=(n−2)c²/(sc‖r‖²−c²),
  τlast(D(Z,x),y)=(n−k−1)c²/(sm‖r‖²−c²), and
  τ₁(L(x),r)/(n−2) ≤ τlast(D(Z,x),y)/(n−k−1).
  Also, **if Pxc=0**, then a=b,
  e(L(x),r)=e(D(Z,x),y), and
  t₁(L(x),r)=√((n−2)/(n−k−1))·tlast(D(Z,x),y).
  Under these same two conditions, **if k≥2 and the full-model t is
  nonzero**, its absolute value is strictly smaller than the residual-line
  t's absolute value.

Second: for **every type Ω**, every measurable-space structure on Ω,
every measure μ on Ω **which is a probability measure**, every natural n,k,
every real n-by-k Z, x∈ℝⁿ, γ∈ℝᵏ, function ε:Ω→ℝⁿ and real σ,
assume, in order:
σ>0; FCR(Z); ∃c,Zc=1; ¬∃c,Zc=x; k+1<n;
for every i the coordinate εᵢ is μ-integrable;
for every i,j the product εᵢεⱼ is μ-integrable;
for every i, ∫εᵢdμ=0; and Cμ(ε)=σ²I.
With M=M(Z) and r(ω)=M(Zγ+ε(ω)), conclude:
for **every ω**, r(ω)=Mε(ω);
Cμ(r)=σ²M; rank M=n−k; rank Cμ(r)=n−k;
and Cμ(r)≠σ²I. Here n−k in the rank equations is natural
subtraction, but k+1<n ensures that it is the ordinary positive difference.
There is no general distributional assertion about a Student law in T4.

## T5

The index j is `Fin 5` (0 through 4). There are three finite samples:
E₀=E₂={1948,1952,…,2012} (17 elections four years apart),
E₁=E₃={1972,1976,…,2012} (11 elections), and
E₄={1960,1964,1968,1972,1984,1996,2004,2008} (8 elections).
Let ej(t) be the exact rational table `depositedExtremism`; all values are
listed in the data appendix below, and the function is zero outside its table.
The definition `relativeExtremism(i,c,r)=(|i−r|−|c−r|)/2` is **not used**
to reconstruct any table value or as a hypothesis in T5 or T6.

This closed proposition asserts:

* 1972 and 1980 belong to both E₁ and E₃;
  |e₁(1972)|−|e₁(1980)|=85077519648341/250000000000000>0 and
  |e₃(1972)|−|e₃(1980)|=307808774046123/1000000000000000>0,
  where positivity is asserted as the two strict magnitude comparisons.
* 1980,1984∈E₂; e₂(1980)<0<e₂(1984);
  −2.23e₂(1984)=−1526436622492473/2500000000000000<0;
  this product is unequal to 1.38;
  and for **every t∈E₂**, e₂(t)≤e₂(1984).
* For **every j**, let sj be respectively
  (1984,1996,1984,2012,1968). Then sj∈Ej and ej(sj)>0;
  for **every t∈Ej**, **if t≠sj**, ej(t)<ej(sj).
* For **every j**, ej(sj) is respectively
  (0.235890938802093,0.336875932107128,0.27380029103004,
  0.34241131733838,0.116), exactly, not approximately.

## T6

Use the same Ej and ej. Let mj=(1980,1972,1980,1972,1964),
cj=(1972,2004,1972,2008,1968), and
δj=(33171961114209/250000000000000,
85752092421407/500000000000000,
20648643625509/125000000000000,
12092835415297/50000000000000,13/125).
Let Ej(false)=Ej, and Ej(true)=Ej with 1948 removed when j=0 or 2,
otherwise Ej(true)=Ej. Define H(β,j)=βej(mj).

The theorem is the conjunction of:

* For **every j**, mj∈Ej, ej(mj)<0, and for **every t∈Ej**,
  **if t≠mj**, |ej(t)|<|ej(mj)|.
* For **every j**, δj>0, cj∈Ej, cj≠mj,
  |ej(mj)|−|ej(cj)|=δj, and for **every t∈Ej**,
  **if t≠mj**, δj≤|ej(mj)|−|ej(t)|.
* For **every j and every Boolean bp**, mj∈Ej(bp) and for **every
  t∈Ej(bp)** with t≠mj, |ej(t)|<|ej(mj)|.
  Also |Ej(false)|−5 is 12 for j=0,2, 3 for j=4, and 6 otherwise;
  |Ej(true)|−6 is 10 for j=0,2, 2 for j=4, and 5 otherwise.
  These differences use natural subtraction; the actual cardinalities are
  (17,11,17,11,8) and (16,11,16,11,8), so no truncation occurs.
* For **every real β,g and every j**: for **every real x**,
  (g+βx)−(g+β·0)=βx; and for **every t∈Ej**,
  |βej(t)|≤|H(β,j)|.
* For **every real β and every j**,
  H(β,j)>0 iff β<0; H(β,j)=0 iff β=0; H(β,j)<0 iff β>0.
* (−2.23)(−0.62)=1.3826, lying in [1.375,1.385);
  e₂(1980)∈[−0.625,−0.615).
* For **every j**, ej(mj) is respectively
  (−0.498138285011637,−0.51177218671487,−0.621023999873778,
  −0.60215659702977,−0.22), exactly.

## T7

This closed proposition is a conjunction of five parts.

1. **For every natural n,k₁,k₂**, every n-by-k₁ Z₁, n-by-k₂ Z₂,
   and q∈ℝⁿ, assume, in order: for every coefficient vector a there exists
   b with Z₁a=Z₂b; FCR(D(Z₁,q)); FCR(D(Z₂,q)); k₁+1<n; k₂+1<n.
   Let Ri=SSE(Zi,q). Then there exists a least-squares coefficient
   vector for each control fit attaining Ri; R₁>0,R₂>0,R₂≤R₁;
   the last diagonal of (D(Zi,q)ᵀD(Zi,q))⁻¹ equals 1/Ri for each i.
   **For every response y**, **if both full-design SSEs are positive**,
   let si=√(SSE(D(Zi,q),y)/(n−ki−1)) and
   sei=√Vlast(D(Zi,q),y). Then sei=si/√Ri for each i,
   se₁/s₁≤se₂/s₂ and se₁≤se₂s₁/s₂.
   No intercept assumption is imposed in this general part.
2. **For every** 17-by-2 Z₁, 17-by-3 Z₂, and q,y∈ℝ¹⁷,
   assume the same column-space inclusion, FCR of both augmented designs,
   SE₂(D(Z₁,q),y)∈[1.35,1.45],
   SE₃(D(Z₂,q),y)∈[0.955,0.965],
   s(D(Z₁,q),y)∈[4.615,4.625],
   s(D(Z₂,q),y)∈[4.695,4.705]. Then **False**.
   All four intervals are closed; positive SSE is not a separate premise here.
3. 0.965·4.625/4.695=7141/7512<0.951, and
   27/20−7141/7512=15001/37560>0.
4. **For every** Z₁,Z₂,q,y with those same dimensions, assume column-space
   inclusion; FCR of both augmented designs; both full SSEs positive;
   SE₃(D(Z₂,q),y)≤0.965; s(D(Z₁,q),y)≤4.625;
   s(D(Z₂,q),y)≥4.695. Then SE₂(D(Z₁,q),y)≤7141/7512.
5. Use the fixed 17-row table in the data appendix, y its first column,
   A₁=[1,income,tenure], A₂=[1,income,tenure,fatalities], and
   A₃=[1,income,tenure,fatalities,extremism]. Each fit has **exactly one**
   least-squares coefficient vector. The tested coordinate is income (index 1).
   The income coefficients, with exact equalities and rounding intervals, are:

   β̂₁(A₁,y)=7146187962914975000000/1117667657915636289559
   ∈[6.385,6.395);

   β̂₁(A₂,y)=315309901567374756223272228924480076940000000/
   49481205176565031631955325062456554157036059
   ∈[6.365,6.375);

   β̂₁(A₃,y)=560959205595590684404193874010188762669512981839878401170000000/
   87848341864933029922153613743599975715147930782629447955391927
   ∈[6.385,6.395).

   V₁(A₁,y)=7736251837253462080128985902187500000000000/
   8744266954854366478686864008983610246901367
   ∈[0.935²,0.945²), and SE₁(A₁,y)∈[0.935,0.945).
   SE₁(A₂,y)∈[0.955,0.965).
   SE₁(A₃,y) belongs to both [0.95,1.05) and [1.005,1.015).

No p-value or significance assertion, no probability-tail identification, and
no alternative residual scale √(SSE/n) appears in T7.

## Exact data appendix

The following tables are direct decimal renderings of the finite rational
constants in Defs; all terminating decimals denote exact rationals.

### Extremism scores

| Election | e₀ | e₁ | e₂ | e₃ | e₄ |
| --- | --- | --- | --- | --- | --- |
| 1948 | 0.186449401704861 | outside sample | 0.239968577629729 | outside sample | outside sample |
| 1952 | 0.068356278600414 | outside sample | 0.0879775359846345 | outside sample | outside sample |
| 1956 | -0.039661945232703 | outside sample | -0.051046667334368 | outside sample | outside sample |
| 1960 | -0.041319840049504 | outside sample | -0.0531804508563835 | outside sample | -0.068 |
| 1964 | -0.24728138844441 | outside sample | -0.318262019168295 | outside sample | -0.22 |
| 1968 | 0.170508105389464 | outside sample | 0.219451428379582 | outside sample | 0.116 |
| 1972 | -0.365450440554801 | -0.51177218671487 | -0.455834850869706 | -0.60215659702977 | -0.041 |
| 1976 | 0.044642638216102 | -0.231688492759438 | 0.0508461944446885 | -0.22548493653085 | outside sample |
| 1980 | -0.498138285011637 | -0.171462108121506 | -0.621023999873778 | -0.294347822983647 | outside sample |
| 1984 | 0.235890938802093 | -0.0356144375420135 | 0.27380029103004 | 0.00229491468593002 | 0.0385 |
| 1988 | 0.153129340875841 | -0.296507211564452 | 0.173195729075055 | -0.276440823365235 | outside sample |
| 1992 | 0.133646079679683 | -0.061530236247573 | 0.192515613229452 | -0.00266070269781005 | outside sample |
| 1996 | -0.104467146002477 | 0.336875932107128 | -0.14605008654561 | 0.295292991563994 | 0.0415 |
| 2000 | -0.0859714651726795 | 0.237764496391801 | -0.169644956461836 | 0.154091005102645 | outside sample |
| 2004 | 0.048727587431465 | -0.340268001872056 | 0.249490683526865 | -0.139504905776655 | 0.052 |
| 2008 | -0.061819369305165 | -0.30311773910617 | -0.119001518922825 | -0.36029988872383 | -0.0045 |
| 2012 | 0.0294616125544001 | 0.33154260332366 | 0.0403303265691201 | 0.34241131733838 | outside sample |

### Regression inputs

| Election | Outcome | Income | Tenure | Fatalities | Extremism |
| --- | --- | --- | --- | --- | --- |
| 1948 | 4.48 | 3.869657666 | 16 | 0 | 0.239968578 |
| 1952 | -10.85 | 2.417476109 | 20 | 190.4152679 | 0.087977536 |
| 1956 | 15.4 | 0.576370472 | 4 | 0 | -0.051046667 |
| 1960 | -0.17 | 0.01682935 | 8 | 0 | -0.053180451 |
| 1964 | 22.58 | 3.258883307 | 4 | 0.948843002 | -0.318262019 |
| 1968 | -0.7 | 1.398802867 | 8 | 145.6291504 | 0.219451428 |
| 1972 | 23.15 | 2.429039464 | 4 | 0 | -0.455834851 |
| 1976 | -2.06 | 0.78535125 | 8 | 2.086606979 | 0.050846194 |
| 1980 | -9.74 | -0.828480492 | 4 | 0 | -0.621024 |
| 1984 | 18.21 | 2.566651066 | 4 | 0 | 0.273800291 |
| 1988 | 7.72 | 1.512362024 | 8 | 0 | 0.173195729 |
| 1992 | -5.56 | 0.77430623 | 12 | 0 | 0.192515613 |
| 1996 | 8.51 | 1.135307588 | 4 | 0 | -0.146050087 |
| 2000 | 0.51 | 1.675421874 | 8 | 0 | -0.169644956 |
| 2004 | 2.46 | 1.039046624 | 4 | 3.860627651 | 0.249490684 |
| 2008 | -7.27 | -0.699703182 | 8 | 13.98476601 | -0.119001519 |
| 2012 | 3.84 | 0.347024884 | 4 | 4.8 | 0.040330327 |
