# Blind reading of SAP.P042.T1–T5

Saved at stage 1, before opening `claims.json` or `record.json`. The sources read were
the five Challenge docstrings and statements and every declaration listed in their
`closure.json` entries. The 81 distinct generated proof declarations were also
printed in `scratch/Closure.lean` and read: they establish numeral `AtLeastTwo`,
`NeZero`, and `3 ≤ 4` facts only; none supplies a statistical assumption.

Throughout, a finite sum is the Mathlib `Finset` sum. On a probability measure μ,
write EμX for the real Bochner integral, VarμX for
`(∫⁻ ω, ‖X ω − EμX‖ₑ ^ 2 ∂μ).toReal`, and Covμ(X,Y) for
`∫ ω, (X ω − EμX)(Y ω − EμY) ∂μ`. `MemLp X 2 μ` includes almost-everywhere
strong measurability and finite L² seminorm. For real random variables on probability
spaces it supplies the integrability of all the means and covariance products below.

## SAP.P042.T1

This is an unconditional conjunction about two explicitly defined finite laws and a
Gaussian quantile. There are no externally quantified populations or assumptions
about historical data. Local universal quantifiers are described below.

For any finite real vector v define wⱼ = (vⱼ)⁻¹, W = Σⱼwⱼ,
aⱼ = wⱼ/W, and Vdiag(v) = Σⱼaⱼ²vⱼ. These unfold `precisionWeight`,
`totalWeight`, `normalizedWeight`, and `diagonalVariance`.

**Six-voter law.** Subjects are `Fin 6` = {0,…,5}; treatment labels are `Fin 3`.
The rational outcome Y(i,g) is 1 if i < 3 and 0 otherwise, independently of g.
The sample space S consists of ordered pairs (A,B) of disjoint two-element subsets
of `Fin 6`, uniformly weighted. Its control group is C = {0,…,5} \ (A ∪ B).
For any subset G define M(G) = (Σᵢ∈G Y(i,0))/2, and on every ordered pair define
D₁ = M(A) − M(C), D₂ = M(B) − M(C). For a finite set S, rational expectation
is (Σₛ∈S f(s))/|S|; rational variance is the expectation of (f − Ef)², and
rational covariance is the expectation of (f − Ef)(g − Eg).

The first conjunct asserts all of these:

- For every i and g, Y(i,g) = Y(i,0).
- |S| = 90 and choose(6,2) choose(4,2) = 90.
- For every (A,B) ∈ S, |A| = |B| = |C| = 2 and A,B are disjoint.
- ED₁ = ED₂ = 0, VarD₁ = VarD₂ = 3/10, Cov(D₁,D₂) = 3/20.
- For v = (3/10,3/10), a₀ = a₁ = 1/2 and Vdiag(v) = W⁻¹ = 3/20.
- Var((D₁+D₂)/2) = E[((D₁+D₂)/2)²] = 9/40.
- This variance equals (3/2)(3/20) and is strictly greater than 3/20.

**Product-binomial law.** Every x₀,x₁,x₂ ranges over `Fin 101` = {0,…,100}.
For general natural n and x : `Fin (n+1)`, pₙ(x) = choose(n,x)/2ⁿ ∈ ℚ.
An arm expectation is Σₓp₁₀₀(x)f(x). The triple expectation is
Σₓ₀ p₁₀₀(x₀) Σₓ₁ p₁₀₀(x₁) Σₓ₂ p₁₀₀(x₂)f(x₀,x₁,x₂).
Thus the three counts are independent binomial(100,1/2) counts, with their
entire product law specified by the sum. Triple variances and covariances are
the corresponding centered second moments. The rational contrasts are
D₁ = (x₁−x₀)/100, D₂ = (x₂−x₀)/100, and P = (D₁+D₂)/2.

Define Covers(e,r) to mean e−r ≤ 0 and 0 ≤ e+r. For natural r define

    K(r) = Σ_{x=0}^{100} choose(100,x)
             Σ_{t=max(0,2x−r)}^{min(200,2x+r)} choose(200,t),
    C(r) = K(r)/2^300 ∈ ℚ.

These are exactly `coversZero`, `coverageCount`, and `binomialCoverage`; the
max in the lower limit unfolds natural-number truncated subtraction.
The second conjunct asserts:

- p₁₀₀(x) ≥ 0 for every x and the arm expectation of 1 is 1.
- ED₁ = ED₂ = 0, VarD₁ = VarD₂ = 1/200, Cov(D₁,D₂) = 1/400,
  and Var(x₀/100) = 1/400.
- For v = (1/200,1/200), a₀ = a₁ = 1/2, Vdiag(v) = W⁻¹ = 1/400.
- For all x₀,x₁,x₂, P = (x₁+x₂−2x₀)/200.
- EP = 0, VarP = 3/800 = (3/2)(1/400), and 1/400 < VarP.
- (49/25)√(1/400) = 49/500.
- For all x₀,x₁,x₂, put q = x₁+x₂−2x₀ in ℤ. Covers(P,49/500) iff
  |q| ≤ 19, and Covers(P,(49/25)√(3/800)) iff |q| ≤ 24.
- 24² < 200²(49/25)²(3/800) = 14406/25 < 25².
- The product-law expectations of the two real interval indicators, with
  radii (49/25)√(1/400) and (49/25)√(3/800), are C(19) and C(24).
- C(19) =
  56571224212801903286613058436266763680981055287737934836552182663205237639665445537726383
  / 2^295, and this numerator is coprime to 2^295.
- 888/1000 < C(19) < 889/1000 < 95/100 < C(24).

**Actual quantile and variable multiplier.** Let Φ(x) be the real-valued mass of
(−∞,x] under Mathlib `gaussianReal 0 1` (normal mean 0, variance 1), and let
z* = inf{x ∈ ℝ : 39/40 ≤ Φ(x)}. The theorem asserts that this set is nonempty
and bounded below, Φ(z*) = 39/40, and 19599/10000 ≤ z* ≤ 49/25.
Next, for every real z, first assuming 19599/10000 ≤ z and then z ≤ 49/25,
it asserts: for all x₀,x₁,x₂, Covers(P,z√(1/400)) iff |q| ≤ 19 and
Covers(P,z√(3/800)) iff |q| ≤ 24; and the expectations of these indicators
are C(19), C(24). It also asserts those same facts at z = z* separately.

**Junk-value inventory.** Real/rational inversion at zero and division by zero
are totalized to zero. Here the two variance vectors are strictly positive and
have two entries; every numerical denominator, 2ⁿ, and 2^300 is nonzero. The
finite rational mean would be zero on an empty support, but S has 90 elements;
every arm support has 101 elements. `sixGroupMean` always divides by 2 even
on a malformed subset, but the law uses it only on three groups of size 2.
`sixControl`, D₁, D₂ are defined on all subset pairs; only pairs in S are averaged.
Natural `2*x-r` truncates at zero, correctly intersecting the integer event with
the nonnegative count support. The signed count q is computed in ℤ, so negative
contrasts are not truncated. All natural-to-integer/rational/real casts are exact.
`Real.sqrt` is zero on nonpositive arguments; all its variance arguments here
are strictly positive. Gaussian `.real` uses `ENNReal.toReal`, which sends ∞
to zero, but a probability law has no infinite set masses. The real `sInf`
definition has default value zero for empty or non-bounded-below sets; the
certificate asserts neither case occurs, as a conclusion rather than an assumed
certificate. No nonintegrable Bochner integral, empty index type, logarithm,
real power, limsup/liminf, or partial-function default enters this theorem.

## SAP.P042.T2

The theorem is the conjunction of eight universal laws. Each law separately
quantifies a type Ω : `Type`, a measurable-space structure, a measure μ and a
proof it is a probability measure. There is no common data set across laws.
All functions below are real-valued. Expectations, variances, covariances and
L² hypotheses have the Mathlib meanings given above.

For any finite real v, wⱼ = vⱼ⁻¹, W(v) = Σⱼwⱼ, aⱼ(v) = wⱼ/W(v),
Vdiag(v) = Σⱼaⱼ(v)²vⱼ. For coefficient vector b and random variables D,
P(b,D)(ω) = ΣⱼbⱼDⱼ(ω). Define Q(b,Σ) = ΣⱼΣₖbⱼbₖΣⱼₖ and
O(b,Σ) = Σ_{j<k} bⱼbₖΣⱼₖ, where j,k : `Fin J`. For a subset R of a
finite type, aᴿⱼ(v) = vⱼ⁻¹/(Σₖ∈R vₖ⁻¹) if j ∈ R, and zero otherwise.
These formulas unfold every pooling/weight/covariance-form SAP definition.

1. **Linear pooling.** After Ω,μ, universally quantify natural J, b : `Fin J → ℝ`,
   D : `Fin J → Ω → ℝ`; assume every Dⱼ ∈ L²(μ). Then
   E[P(b,D)] = ΣⱼbⱼEDⱼ;
   VarP(b,D) = Q(b,(Cov(Dⱼ,Dₖ))ⱼₖ);
   Q(b,CovD) = Σⱼbⱼ²VarDⱼ + 2O(b,CovD).
2. **Precision pooling.** After Ω,μ, quantify natural J, assume J > 0, quantify D,
   assume every Dⱼ ∈ L² and VarDⱼ > 0. Put vⱼ = VarDⱼ, a = a(v), Σ = CovD.
   The conclusions are W(v)>0, every aⱼ>0, Σⱼaⱼ=1, Vdiag(v)=W(v)⁻¹,
   VarP(a,D)=W(v)⁻¹+2O(a,Σ), and
   [VarP(a,D)=W(v)⁻¹ iff O(a,Σ)=0]. If all off-diagonal Σⱼₖ vanish,
   VarP=W⁻¹. If all off-diagonal Σⱼₖ ≥ 0 and some j<k has Σⱼₖ>0,
   W⁻¹<VarP. For every real z, z√VarP = z√Q(a,Σ); for every real z>0,
   [z√VarP=z√(W⁻¹) iff O(a,Σ)=0]. The latter z quantifiers are inside
   the conclusions, after D and its hypotheses.
3. **Shared control.** After Ω,μ, quantify A,B,C : Ω→ℝ; assume each ∈ L² and
   Cov(A,B)=Cov(A,C)=Cov(B,C)=0. Then Cov(A−C,B−C)=VarC.
4. **Independent observations.** After Ω,μ, quantify naturals n₀,n₁,n₂ and assume
   all three are positive. Quantify X indexed by the disjoint sum
   `Fin n₀ ⊕ (Fin n₁ ⊕ Fin n₂)`; assume every Xᵢ ∈ L² and every distinct
   pair is independent (`IndepFun`, factorization of the corresponding
   measurable inverse-image events). Quantify real σ², assume σ²>0 and
   VarXᵢ=σ² for every i. Let C,A,B be the arithmetic means in the three
   groups, each dividing by its positive natural size, D₁=A−C,D₂=B−C.
   Then VarD₁=σ²(1/n₁+1/n₀), VarD₂=σ²(1/n₂+1/n₀), Cov(D₁,D₂)=σ²/n₀,
   and Cov(D₁,D₂)/(√VarD₁ √VarD₂) =
   √[n₁n₂/((n₁+n₀)(n₂+n₀))]. No identical-distribution or equal-mean
   hypothesis is present, only a common positive variance.
5. **Covariance bound.** After Ω,μ, quantify natural J, b,s : `Fin J → ℝ` and D.
   Assume every Dⱼ ∈ L², bⱼ≥0, sⱼ>0 and VarDⱼ=sⱼ². Then
   |Cov(Dⱼ,Dₖ)|≤sⱼsₖ for all j,k and VarP(b,D)≤(Σⱼbⱼsⱼ)².
   Moreover, for every Z : Ω→ℝ, if Z∈L², EZ=0, VarZ=1, and for every j,
   Dⱼ−EDⱼ=sⱼZ almost everywhere, equality holds in the variance bound.
   This is a conditional equality statement, not an existential assertion of Z.
6. **Difference of pools.** After Ω,μ, quantify a finite type ι with decidable
   equality and subsets N,A; assume both nonempty and disjoint. Quantify D,
   assume every Dⱼ∈L² and VarDⱼ>0 (including indices outside the pools).
   Put vⱼ=VarDⱼ, bⱼ=aᴺⱼ(v)−aᴬⱼ(v). Then
   Var(P(aᴺ,D)−P(aᴬ,D))=Q(b,CovD), and it also equals
   VarP(aᴺ,D)+VarP(aᴬ,D)−2Cov(P(aᴺ,D),P(aᴬ,D)).
7. **Three-contrast block.** After Ω,μ, quantify J>0, D with each Dⱼ∈L² and
   VarDⱼ>0. Quantify an embedding e : `Fin 3 ↪ Fin J` and real a,c₁₂,c₁₃,c₂₃.
   Assume a(v) at every e(g) equals a. Assume, for all distinct j,k, their
   covariance is c₁₂ on the unordered pair {e(0),e(1)}, c₁₃ on
   {e(0),e(2)}, c₂₃ on {e(1),e(2)}, and zero otherwise.
   Then VarP(a(v),D)=W(v)⁻¹+2a²(c₁₂+c₁₃+c₂₃).
   Further, c₁₂=c₁₃ → c₁₃=c₂₃ → VarP=W⁻¹+6a²c₁₂.
8. **Finite population.** Quantify natural N≥2, then n : `Fin 3 → ℕ` with
   every n(g)>0 and Σg n(g)≤N, then arbitrary fixed Y : `Fin N → Fin 3 → ℝ`.
   The finite support S is all functions z : `Fin N → Fin 4` with exactly n(g)
   subjects labelled g for g=0,1,2. Label 3 contains all unused subjects.
   Define M_g(z)=(Σᵢ 1{z(i)=g}Y(i,g))/n(g), D₁=M₁−M₀,D₂=M₂−M₀,
   τ₁(i)=Y(i,1)−Y(i,0), τ₂(i)=Y(i,2)−Y(i,0).
   For any finite support, E_S f=(Σₛ∈S f(s))/|S|,
   Cov_S(f,h)=E_S[(f−E_Sf)(h−E_Sh)]. For population vectors,
   Ȳ=(ΣᵢY(i))/N and S(Y,V)=(Σᵢ(Y(i)−Ȳ)(V(i)−V̄))/(N−1).
   The conclusions are: S is nonempty;
   Cov_S(D₁,D₂)=S(Y₀,Y₀)/n₀−S(τ₁,τ₂)/N;
   S(τ₁,τ₂)=S(Y₁,Y₂)−S(Y₁,Y₀)−S(Y₀,Y₂)+S(Y₀,Y₀);
   and, if every i has Y(i,1)=Y(i,0) and Y(i,2)=Y(i,0),
   Cov_S(D₁,D₂)=S(Y₀,Y₀)/n₀.

The Challenge docstring presents this as general mathematical content, explicitly
excluding historical-data applications, covariance estimates, numerical pool/mail
recalculations, staged sizes, block-specific numbers, and editorial corrections.

**Junk-value inventory.** Bochner integrals are zero for nonintegrable functions;
variance converts infinite extended variance to zero. L² hypotheses on a probability
measure prevent these conventions from affecting every probabilistic identity.
Inversion at zero and division by zero would collapse precision weights; positive
variances and nonempty precision index/pools prevent that in laws 2,6,7. Law 1
allows J=0, giving the valid identity 0=0 without any denominator. Law 5 also
allows J=0, when its bound is 0≤0 and an equality implication can be vacuous.
The embedding in law 7 entails J≥3. A probability measure on an empty Ω cannot
exist, but the laws also have nonempty models. Sample-mean denominators n₀,n₁,n₂
are positive. The correlation denominator is positive from the displayed positive
contrast variances; all square roots in law 4 have nonnegative arguments.
Square roots in law 2 apply to variances, their equal covariance forms, or W⁻¹>0.
The finite mean is zero on an empty support, but law 8 asserts support nonempty;
positive n and their sum bound ensure a genuine allocation exists. `N−1` is
natural subtraction, with no truncation issue since N≥2 (in fact N≥3 follows).
All natural casts are exact. No logarithm, real power, extrema, limsup/liminf,
or partial-function default appears.

## SAP.P042.T3

This is an unconditional conjunction about two fixed real input vectors and
universal algebra/monotonicity laws. Put d=(58247/25000,21649/25000),
s=(1741/3125,40891/50000) on `Fin 2`; vⱼ=sⱼ², wⱼ=vⱼ⁻¹, W=Σwⱼ,
aⱼ=wⱼ/W, μF=Σaⱼdⱼ, VF=W⁻¹, Q=Σwⱼ(dⱼ−μF)²,
C=W−(Σwⱼ²)/W, τ²=max(0,(Q−1)/C), uⱼ=vⱼ+τ²,
wRⱼ=uⱼ⁻¹, WR=ΣwRⱼ, μR=Σ(wRⱼ/WR)dⱼ, VR=WR⁻¹.
These formulas unfold all `robo*`, precision and normalized-weight definitions.

The exact fixed calculation asserts

    v₀ = 3031081/9765625,
    v₁ = 1672073881/2500000000,
    W  = 23906548994140625/5068191371295361,
    μF = 114191974724271/61200765425000,
    VF = 5068191371295361/23906548994140625.

It also asserts 18655/10000<μF<18665/10000 and 17205/10000<μF.
For every real z, first assuming 19599/10000≤z and then z≤49/25, it asserts

    9625/10000 < μF−z√VF,
    3065/10000 < 9625/10000,
    μF+z√VF < 27685/10000,
    27685/10000 < 31345/10000.

The exact alternative calculation asserts

    Q = (d₀−d₁)²/(v₀+v₁) = 5357654416/2448030617,  1<Q,
    C = 2/(v₀+v₁) = 5000000000/2448030617,
    τ² = 2909623799/5000000000,
    wR₀ = 5000000000/4461537271,
    wR₁ = 5000000000/6253771561,
    μR = 12592252377/7319600000,
    VR = 27901434903721350031/53576544160000000000.

It asserts 17195/10000≤μR<17205/10000. For every real z in the same closed
multiplier range, the alternative lower endpoint belongs to
[3055/10000,3065/10000), and its upper endpoint belongs to
[31345/10000,31355/10000).

Let Φ(x)=(gaussianReal 0 1)((−∞,x]).toReal and
z*=inf{x:39/40≤Φ(x)}. It asserts nonemptiness and boundedness below of this
set, Φ(z*)=39/40, and 19599/10000≤z*≤49/25. It additionally asserts
τ²=5819247598/10000000000, the two fixed endpoint inequalities at z*,
and the two alternative endpoint half-open bins at z*.

**Square-root-free law.** For every μ,L,U,z,V : ℝ in that order, assuming
L<μ, μ<U, z≥0, V≥0, the following eight equivalences all hold:

    L < μ−z√V  iff z²V < (μ−L)²;
    L ≤ μ−z√V  iff z²V ≤ (μ−L)²;
    μ−z√V < L  iff (μ−L)² < z²V;
    μ−z√V ≤ L  iff (μ−L)² ≤ z²V;
    μ+z√V < U  iff z²V < (U−μ)²;
    μ+z√V ≤ U  iff z²V ≤ (U−μ)²;
    U < μ+z√V  iff (U−μ)² < z²V;
    U ≤ μ+z√V  iff (U−μ)² ≤ z²V.

**Monotonicity law.** For every μ,V : ℝ, assuming V≥0, the lower endpoint
is antitone in all real z, the upper endpoint is monotone in all real z, and
z↦z²V is monotone on [0,∞). Furthermore, for every real a,b,z, assuming
0≤a, a≤z, z≤b, the theorem asserts

    μ−b√V ≤ μ−z√V ≤ μ−a√V,
    μ+a√V ≤ μ+z√V ≤ μ+b√V,
    a²V ≤ z²V ≤ b²V.

The docstring describes exact stipulated inputs, the mismatch of fixed-effect
rounding with Note 5, agreement of alternative rounding, and no inference about
historical intent. No stochastic calibration or distribution of these estimates
is asserted.

**Junk-value inventory.** Every explicit denominator is a nonzero positive integer.
All vⱼ>0, W>0, C>0, τ²>0 and uⱼ>0 for these inputs, so inversion and
division never use zero. The max in τ² is the actual truncation of the DL
estimate at zero, not a logical convention; here Q>1 so it chooses the positive
branch. VF,VR>0. The generic square and monotonicity laws explicitly assume
V≥0; z≥0 and positive gaps guard their squared equivalences. `Real.sqrt`
on negative values cannot affect any asserted comparison. Gaussian set masses
are finite; the quantile-set nonemptiness and lower bound are proved conjuncts,
so the default `sInf` value for bad sets is not being used. No empty index,
nonintegrable mean, natural subtraction, logarithm, real power, limsup/liminf,
or partial-function default appears.

## SAP.P042.T4

The fixed and alternative inputs and formulas are independently as follows.
On `Fin 2`, d=(58247/25000,21649/25000), s=(1741/3125,40891/50000),
vⱼ=sⱼ², wⱼ=vⱼ⁻¹, W=Σwⱼ, aⱼ=wⱼ/W, μF=Σaⱼdⱼ, VF=W⁻¹.
Set Q=Σwⱼ(dⱼ−μF)², C=W−Σwⱼ²/W, τ²=max(0,(Q−1)/C),
uⱼ=vⱼ+τ², wRⱼ=uⱼ⁻¹, WR=ΣwRⱼ, μR=Σ(wRⱼ/WR)dⱼ, VR=WR⁻¹.

The theorem unconditionally asserts

    v₀=3031081/9765625, v₁=1672073881/2500000000,
    W=23906548994140625/5068191371295361,
    μF=114191974724271/61200765425000,
    VF=5068191371295361/23906548994140625,
    18655/10000 ≤ μF < 18665/10000.

For every real z, assuming first 19599/10000≤z and then z≤49/25,

    9625/10000 ≤ μF−z√VF < 9635/10000,
    27675/10000 ≤ μF+z√VF < 27685/10000.

For every real z, assuming 0≤z and z≤49/25, μF−z√VF>0.

Its stochastic law universally quantifies Ω : `Type`, a measurable structure,
a probability measure μ, then D : `Fin 2 → Ω → ℝ`. Assuming every Dⱼ∈L²,
VarDⱼ=vⱼ for each j, and Cov(D₀,D₁)=0, it concludes

    Var(ω ↦ Σⱼ aⱼDⱼ(ω)) = VF.

There is no mean restriction on these Dⱼ and no claim of independence.
The zero-covariance hypothesis is explicit. Finally it asserts all of

    Q=(d₀−d₁)²/(v₀+v₁)=5357654416/2448030617, 1<Q,
    C=2/(v₀+v₁)=5000000000/2448030617,
    τ²=2909623799/5000000000,
    wR₀=5000000000/4461537271, wR₁=5000000000/6253771561,
    μR=12592252377/7319600000,
    VR=27901434903721350031/53576544160000000000,
    17195/10000 ≤ μR < 17205/10000.

For every real z with 19599/10000≤z≤49/25, the alternative lower endpoint
μR−z√VR belongs to [3055/10000,3065/10000), and the upper endpoint μR+z√VR
belongs to [31345/10000,31355/10000).

The docstring describes rounding to 1.866 and (0.963,2.768), positive lower
endpoint, conditional actual variance, and alternative rounding agreement.
It explicitly omits an actual-normal-quantile enclosure and editorial/program
changes. Thus z is an arbitrary multiplier in a fixed rational range here,
not a defined or certified normal quantile.

**Junk-value inventory.** Fin 2 is nonempty. Explicit denominators are positive;
vⱼ>0, W>0, C>0, τ²>0, uⱼ>0, WR>0. Inversion/division by zero cannot
affect any concrete result. The DL max correctly truncates a heterogeneity
estimate, and here takes its positive branch. VF and VR are positive, so no
negative-argument square root appears. The stochastic law's L² hypotheses on
a probability measure guarantee finite integrals and extended variance before
`toReal`; no zero-from-infinite-variance shortcut is used. There is no sInf,
normal-CDF toReal, empty finite support, natural subtraction, logarithm, real
power, limsup/liminf, or partial-function default in the statement's closure.

## SAP.P042.T5

The statement is a conjunction of two negated universal formulas. It is not a
positive corrected-variance theorem and does not quantify or identify historical
studies. The two negations have independent choices of data.

The first formula being negated universally quantifies, in order: Ω : `Type`,
a measurable structure on Ω, a measure μ, a proof μ is a probability measure,
natural J, a hypothesis J>0, and D : `Fin J → Ω → ℝ`. Its further hypotheses
are Dⱼ∈L²(μ) and VarDⱼ>0 for every j. Write vⱼ=VarDⱼ, wⱼ=vⱼ⁻¹,
W=Σⱼwⱼ, aⱼ=wⱼ/W. The formula asserts

    Var(ω ↦ Σⱼ aⱼDⱼ(ω)) = W⁻¹.

The theorem asserts this universally quantified implication is false.
Classically this means some probability space, J>0 and an L² family with
every marginal variance positive has actual variance different from W⁻¹.
There is no off-diagonal covariance or independence premise to violate.

The second formula being negated universally quantifies, in order: Ω : `Type`,
a measurable structure, a probability measure μ, a type ι : `Type`, its Fintype
and decidable equality, finite subsets N,A of ι, hypotheses N nonempty, A
nonempty and disjointness, then D : ι→Ω→ℝ. It assumes Dⱼ∈L² and VarDⱼ>0
for every j, including unused indices. With vⱼ=VarDⱼ, define

    WN=Σⱼ∈N vⱼ⁻¹, WA=Σⱼ∈A vⱼ⁻¹,
    aNⱼ = vⱼ⁻¹/WN if j∈N, else 0,
    aAⱼ = vⱼ⁻¹/WA if j∈A, else 0.

The negated universal conclusion is

    Var(ω ↦ Σⱼ aNⱼDⱼ(ω) − Σⱼ aAⱼDⱼ(ω)) = WN⁻¹ + WA⁻¹.

Thus the theorem asserts existence, classically, of admissible data for which
this equality fails. Disjoint index sets do not imply statistical independence.
The Challenge docstring limits the result to these two variance readings and
explicitly disclaims rejection of particular historical empirical assertions.
It says the nine estimates, counts and intervals, the historical mail comparison,
and qualitative historical explanations are omitted.

**Junk-value inventory.** For either potential witness all L² hypotheses on a
probability measure exclude nonintegrable means/covariance products and infinite
extended variance. Positive marginal variance prevents each zero inversion.
J>0 or nonempty pools ensure positive W,WN,WA, so normalized weights are
well-defined mathematically. Empty Ω has no probability instance and cannot be
a witness; empty J or empty pools are expressly excluded. An arbitrary finite
type may contain unused indices but they also must have positive finite
variance. There is no square root, sInf/sSup, logarithm, real power,
natural subtraction, limsup/liminf, or partial-function default in the closure.
