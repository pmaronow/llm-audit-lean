# Blind reading of the Challenge statements

This file was written from `SAP/P001b/Defs*.lean`, `SAP/P001b/Defs/*.lean`, and `SAP/P001b/Challenge/*.lean`, before opening either `claims.json` or `record.json`. The theorem names below are in namespace `SAP.P001b`. Every theorem has no outer mathematical hypotheses: its entire content is the proposition defined as `TnnStatement`. Hypotheses inside those propositions are specified below. No Solution or Comparator was inspected.

## Conventions traced to Mathlib

Write λ for ordinary real Lebesgue measure and λ² for its product on ℝ². `volume` on a product is the product of the two volumes (`Measure/Prod.lean`, `prod.measureSpace`). All real intervals and arithmetic below have their ordinary meanings, except for the explicitly noted total operations.

`probability μ A` is `(μ A).toReal`. Mathlib measures take values in [0,∞]; `toReal` sends ∞ to 0 (`Basic/ENNReal/Basic.lean:228,284`). In the statements using this operation, μ is a probability measure (`IsProbabilityMeasure` means μ(Ω)=1), so all its values are finite. The events whose probabilities are used are measurable under the stated hypotheses. `distributionFunction μ X x` is this real probability of {ω : X(ω)≤x}.

`Density ν f` means: f:ℝ→ℝ agrees λ-almost everywhere with a Borel measurable function; f(x)≥0 at every x; f is λ-integrable; and ν is the measure with density `ofReal(f)` relative to λ. Here `ofReal(r)=max(r,0)` embedded in [0,∞]. Thus for measurable B, ν(B)=∫_B f dλ. `JointDensity` is exactly the same definition on ℝ² with λ². These definitions do not by themselves assume ν has total mass one; individual quantified clauses also assume it is a probability measure. Integrability is almost-everywhere strong measurability and finite integral of the norm (`Function/L1Space/Integrable.lean:59`).

`∫` is the Bochner integral (`Integral/Bochner/Basic.lean:158`), defined as 0 for nonintegrable real functions. `∫ x in B` means integration against the restriction of the measure to B; it is not an oriented interval integral. `∫⁻` is the nonnegative extended Lebesgue integral, which can be ∞. An almost-everywhere assertion refers to the displayed measure. `ν.map X` is pushforward when X is almost everywhere measurable; all maps actually used as laws here are measurable. Mathlib has a fallback definition for nonmeasurable maps (`Measure/Map.lean:99`), which is not needed in these statements. `ν.prod η` is product measure.

Real division is total, with r/0=0. Real `sqrt r` is 0 when r≤0. `deriv F x` is the ordinary derivative when it exists, and 0 otherwise (`Calculus/Deriv/Basic.lean:148`). `DifferentiableAt ℝ F x` asserts the existence of a real derivative; `HasDerivAt F a x` asserts derivative a at x. `ContinuousAt F x` is ordinary two-sided continuity, expressed by convergence on neighborhoods.

An indexed real sum `∑'` is the unconditional limit of sums over finite subsets, and is defined as 0 if the family is not summable (`InfiniteSum/Defs.lean:106–145`, additive definitions generated from products). `Summable` explicitly asserts existence of that finite real limit. Finite sums have their usual meanings; `Fin n` is {0,…,n−1}, and `Fin 0` is empty. `Countable S` for a type and `S.Countable` for a set mean at most countable, including finite/empty possibilities. `StrictMono X` on `Fin n` means i<j implies X(i)<X(j).

Important order convention: in this Mathlib, `ContDiff` has order in `ℕ∞ω = WithTop ℕ∞`. Its literal order `⊤` is ω (analytic), whereas the embedded top of ℕ∞ is ∞ (smooth). Thus `ContDiff ℝ ⊤ f` below asserts real analyticity, including analyticity of the Taylor derivative fields, not just C∞. On these complete real spaces it is equivalent to real analyticity everywhere (`Calculus/ContDiff/Defs.lean:91,1056–1072,1196`).

## Finite probability and the fixed electorate definitions

For w:Fin n→ℝ and a predicate A, put P_w(A)=Σ_i 1_A(i)w_i. Write E_w(Y)=Σ_i w_iY_i and

    M_w(Y | X=x) = (Σ_{i:X_i=x} w_iY_i) / P_w(X=x).

These are raw finite sums; they are probabilities/conditional means only when w is nonnegative and normalized, and the conditioning mass is positive. `FiniteConditionalIndependence w Y Z X` asserts, in quantifier order, for every x in the codomain of X, every y in the codomain of Y, and every z in the codomain of Z: if P_w(X=x)>0 then

    P_w(X=x,Y=y,Z=z) P_w(X=x)
      = P_w(X=x,Y=y) P_w(X=x,Z=z).

The fixed electorate has atoms i=0,1,2,3, with

| i | w_i | U_i (`electorateType`) | D_i (`displayedGender`) | Y_i(0) | Y_i(1) | observed Y_i |
|---|---|---|---|---|---|---|
| 0 | 3/8 | 0 | 0 | 20 | 25 | 20 |
| 1 | 1/8 | 0 | 1 | 20 | 25 | 25 |
| 2 | 1/8 | 1 | 0 | 60 | 65 | 60 |
| 3 | 3/8 | 1 | 1 | 60 | 65 | 65 |

Here Y_i(d)=20+40U_i+5d for every real d, and observed Y_i=Y_i(D_i). For Boolean d, the leaflet is the triple (0,d,false). Voter k∈{0,…,99} votes no exactly when k+1≤20+40u+5·1_{d=true}. `countedVoteShare i d` is the real-valued cardinality of the voters voting no with u=U_i. It is a percentage on a population of exactly 100 voters.

## T20

The conjunction of two universal assertions about raw nonnegative arm-mass functions; no normalization, probability measure, or positive total arm masses is assumed.

1. For every type E, then functions t,c:E→ℝ, if t≥0 pointwise and c≥0 pointwise, then both: (a) {x:t(x)>0}={x:c(x)>0} if and only if for every x with t(x)+c(x)>0, 0<t(x)/(t(x)+c(x))<1; (b) if there exists a real ε>0 such that for every x with t(x)+c(x)>0, ε<t(x)/(t(x)+c(x))<1−ε, then those positive sets are equal.
2. For every type E, then t,c:E→ℝ, assuming successively pointwise nonnegativity of t, pointwise nonnegativity of c, finiteness of {x:t(x)+c(x)>0}, and equality of their positive sets, there exists a real ε>0 satisfying the same strict two-sided bound at every x with positive combined mass.

E may be empty and both functions may vanish; neither situation is required. Every ratio used in a bound has strictly positive denominator.

## T21

A closed conjunction about precisely the four-atom electorate above, without any quantified inputs or antecedents. It asserts all of the following:

1. Every w_i is nonnegative and Σ_i w_i=1.
2. For every Boolean d the leaflet's first coordinate is 0, its second is d, and its third is false.
3. For every atom i and Boolean d the counted vote share is Y_i(1_d).
4. For every i, observed Y_i=Y_i(1)D_i+Y_i(0)(1−D_i); both potential shares and the observed share belong to [0,100]; and Y_i(1)−Y_i(0)=5.
5. P_w(D=1)=P_w(D=0)=1/2, and M_w(D | X=0)=1/2 for the constant variable X=0.
6. P_w((Y(0),Y(1))=(60,65),D=1)=3/8; P_w((Y(0),Y(1))=(60,65))=1/2; and the product of that latter probability with P_w(D=1) is 1/4.
7. The pair (Y(0),Y(1)) and D fail the finite conditional independence definition given X=0.
8. M_w(observed Y | D=1)=55 and M_w(observed Y | D=0)=30; their difference is 25; E_w(Y(1)−Y(0))=5; and 25≠5.

The voting rule is a definition of the fixed model, rather than a universally quantified premise about arbitrary voting behavior. All conditioning cells in the numerical assertions have positive mass.

## T22

Literally the same proposition as T21: `T22Statement := T21Statement`. It asserts exactly the full fixed-model conjunction just listed, with no additional general identification or functional-response assertion.

## T23

For every type Ω, a measurable-space structure on Ω, measure μ, and assumption μ(Ω)=1, then sets A,B, assuming A and B measurable, all of the following hold:

1. A⊆B if and only if every ω∈A is in B.
2. If A⊆B then Pμ(A)≤Pμ(B), and if A⊆B then Pμ(B\A)=Pμ(B)−Pμ(A).
3. Pμ(∅)=0, and 0≤Pμ(A)≤1.
4. Pμ(Aᶜ)=1−Pμ(A).
5. Pμ(A∪B)=Pμ(A)+Pμ(B)−Pμ(A∩B).
6. If A⊆B and A≠B, it is false that every ω∈B is in A.

The set-inclusion assumption is local to the indicated conclusions; it is not assumed for the entire theorem.

## T24

A conjunction of three assertions.

1. For every Ω with a measurable-space structure, probability measure μ, countable index type ι, and family A:ι→Set Ω, assume, in order, all A_i measurable, all A_i nonempty, pairwise disjointness for unequal indices, and ⋃_i A_i=Ω. For every measurable B, simultaneously:
   - Pμ(B)=Σ'_i Pμ(B∩A_i).
   - If every Pμ(A_i)>0, then Pμ(B)=Σ'_i [Pμ(B∩A_i)/Pμ(A_i)]Pμ(A_i).
   - For every measurable C, Pμ(C)≥0; [C and Cᶜ are nonempty] iff [C≠∅ and C≠Ω]; and Pμ(B)=Pμ(B∩C)+Pμ(B∩Cᶜ).
   - Pμ(∅)≥0 and Pμ(∅) is not strictly positive.
2. For every type Ω and every A⊆Ω, define the set of sets F_A={C:C is nonempty and (C=A or C=Aᶜ)}. Every member is nonempty; every two distinct members are disjoint; and ⋃F_A=Ω. No measure, measurability, or nonemptiness of Ω is assumed for this assertion.
3. The real arithmetic identity 1/8+1/12=5/24.

The countable family in clause 1 has no explicit nonempty-index assumption, but its covering property on a probability space prevents an empty index type. Positivity of cell mass is assumed only in the ratio version, not in the intersection version.

## T25

A closed numerical counterexample on one atom of weight 1, with the constant integer/real value 0: P_w(0<4)=1; Σ_{k∈ℤ,1≤k≤3}P_w(0=k)=0; and these two values are unequal. No second distribution or general universal statement occurs.

## T26

For every q:ℤ→ℝ, assuming successively q(k)≥0 for every k, summability of q over ℤ, and Σ'_k q(k)=1, define F_q(x)=Σ'_{k∈ℤ} 1_{k≤x}q(k). The conclusion is the conjunction

    Σ'_{k∈ℤ} 1_{k<4}q(k) = F_q(3),
    F_q(3) − Σ_{k=1}^3 q(k) = F_q(0),
    [F_q(3)=Σ_{k=1}^3 q(k)] iff [F_q(0)=0].

The integer inequalities in F use integer-to-real coercions. No positivity of the integer-valued variable itself is assumed. No fair-die specialization occurs in this proposition.

## T27

Let I be the dependent disjoint union of Fin(2^m) over m∈ℕ. For i=(m,k), put a_i=(2k+1)/2^{m+1}, w_i=(1/2)^{2m+1}, and F(x)=Σ'_{i∈I}1_{a_i≤x}w_i. With no antecedents, the theorem asserts:

1. The weights are summable, their total sum is 1, and every w_i>0.
2. {a_i:i∈I} is countable.
3. For every real a,b, if 0<a, a<b, and b<1, then F(a)<F(b).
4. F is continuous at 1/3.
5. There does not exist a real ε>0 such that for every real x with |x−1/3|<ε, F(x)=F(1/3).

There is no explicit injectivity assertion, exact description of the range, per-level mass calculation, or separate singleton-mass assertion.

## T28

The conjunction of four assertions:

1. For every measurable space Ω, probability measure μ, and measurable X:Ω→ℝ, assuming the type `Set.range X` is countable, for every real x,

       Pμ(X≤x)=Σ'_{t∈range(X)} [if t≤x then Pμ(X=t) else 0].

2. For every natural m and weights w on Fin(m+1), assuming w≥0 pointwise and Σ_i w_i=1, then every strictly increasing X:Fin(m+1)→ℝ, then every real x: if x<X_0, P_w(X≤x)=0; for every l∈Fin m, if X_l≤x<X_{l+1}, P_w(X≤x)=Σ_{i≤l}w_i; and if X_m≤x, P_w(X≤x)=1. The finite family is nonempty even when m=0.
3. For every natural n and weights w on Fin n, assuming nonnegativity and normalization, then X:Fin n→ℝ and real a,b, assuming a≤b and that no i has a<X_i≤b, the two finite CDF values at a and b agree. No ordering of X is assumed in this clause.
4. On six atoms of weights 1/6 and values X_i=i+1, the CDF at −1,1,3/2,2,6,7 equals respectively 0,1/6,1/6,1/3,1,1.

## T29

Define U(x)=max(0,min(1,x)), f_c=1_[0,1], f_o=1_(0,1), and f_m(x)=3/2 when x=1/3, otherwise f_c(x). The closed proposition asserts:

1. For every real x all three functions are nonnegative.
2. For every real x each integral ∫_{u≤x} f_c(u), ∫_{u≤x} f_o(u), and ∫_{u≤x} f_m(u) equals U(x).
3. The three functions are pairwise unequal as pointwise functions.
4. U is not differentiable at 0 and is not differentiable at 1.
5. For every real h with 0<h≤1, the four quotients [U(−h)−U(0)]/(−h), [U(h)−U(0)]/h, [U(1−h)−U(1)]/(−h), [U(1+h)−U(1)]/h equal respectively 0,1,1,0.
6. f_c(0)=f_c(1)=1.

Integrability is not a separate asserted conjunct here, but these specific bounded finite-support functions are integrable.

## T30

A conjunction of six clauses, each with its own quantifiers:

1. For every real probability measure ν and functions f,g:ℝ→ℝ, if `Density ν f` and `Density ν g`, then: f=g λ-almost everywhere; at λ-almost every x the function F(t)=Pν((−∞,t]) has derivative f(x) at x; at every x where F is differentiable its derivative is nonnegative; and ∫f dλ=1.
2. For every real probability measure ν and f,h:ℝ→ℝ, assuming `Density ν f`, h≥0 everywhere, and h=f λ-almost everywhere, then `Density ν h`, and for every real x, F(x)=∫_{t≤x}h(t)dλ. No independent measurability/integrability assumption is imposed on h.
3. For every planar probability measure ν and f,g:ℝ²→ℝ, if both are joint densities of ν, then f=g λ²-almost everywhere.
4. For every y∈(0,1), the function u↦[derivative at v=y of v↦U(u)U(v)] is not differentiable at u=0.
5. For every x,y∈[0,1], U(x)U(y)=xy. This is an identity of functions; no probability law is introduced for this particular clause.
6. For every planar probability measure ν, then f:ℝ²→ℝ and f_x,f_y:ℝ→ℝ, assuming `JointDensity ν f`, `Density (ν.map fst) f_x`, and `Density (ν.map snd) f_y`,

       ν=(ν.map fst)⊗(ν.map snd)
         iff f(x,y)=f_x(x)f_y(y) for λ²-almost every (x,y).

There is no discrete-PMF clause.

## T31

Define an interval J_w for every finite Boolean list w recursively. J_[]=[0,1]. If J_w=[a,b], put c=(a+b)/2 and g=4^{−(|w|+1)}. J_{false::w}=[a,c−g/2], J_{true::w}=[c+g/2,b]. Let C_n be the union of all these closed intervals for lists of length n, and C=⋂_{n≥0}C_n. On the subtype C with its inherited measurable space let ν_C=2·(λ.comap inclusion), and put f_C(x)=2 if x∈C, 0 otherwise.

With no hypotheses, the theorem asserts C is closed, λ(C)=1/2, ν_C is a probability measure, the inclusion C→ℝ is measurable, f_C is a density of its pushforward law, the literal range of the inclusion equals C, {x:f_C(x)>0}=C, and for every real a<b the interval [a,b] is not a subset of C.

The pullback `comap` is defined as zero if the map is not injective or fails to send measurable sets to null-measurable sets (`Measure/Comap.lean:64`); here the inclusion of the asserted closed set is a measurable embedding, so it is the ordinary restriction/pullback of λ. No stage-length or removed-length formula is asserted.

## T32

A conjunction:

1. For every measurable space Ω, probability measure μ, measurable X:Ω→ℝ, then every f:ℝ→ℝ with `Density (μ.map X) f`, all fibers {ω:X(ω)=t} have μ-measure zero for every real t; the literal range of X is not countable; and the type Ω is not countable.
2. Put C=[0,1/2]\ℚ, where ℚ denotes the range of the rational-to-real embedding. There exists a measure ν on the subtype C such that: C is measurable and λ(C)=1/2; ν is a probability measure; inclusion C→ℝ is measurable with range exactly C; its pushforward has density 2·1_C; C is not countable as a set and its subtype is not countable as a type; and for every real a<b, [a,b] is not contained in the range of this inclusion.

The existence of ν is inside the conjunction after the fixed definition of C. The first clause does not posit that the range is an interval or contains an interval.

## T33

For every type Ω, then every function X:Ω→ℝ and functions g,h:ℝ→ℝ, equality g∘X=h∘X as pointwise functions on Ω holds if and only if for every real x in the actual range of X, g(x)=h(x). There are no measurable-space, measurability, probability, distributional-equality, or almost-everywhere hypotheses. Ω may be empty.

## T34

Let f(x,y)=1 when 0<x<1 and −1<y<0, and 0 otherwise. With no hypotheses, f is everywhere nonnegative and λ²-integrable; ∫f dλ²=1; ∫_{0≤x≤1,y≤x} f(x,y)dλ²=1; ∫_{x∈[0,1]}(∫_{y∈[0,x]}f(x,y)dy)dx=0; and the last two integrals are unequal. This is phrased in terms of density integrals, with no separately named probability law. No second density occurs.

## T35

For every planar probability measure ν, then f:ℝ²→ℝ, assuming `JointDensity ν f`, define E={0≤x≤1,y≤x}, T={0≤x≤1,0≤y≤x}, N={0≤x≤1,y<0}, and I=∫_{x∈[0,1]}∫_{y∈[0,x]}f(x,y)dy dx. The conclusion simultaneously states Pν(T)=I; Pν(E)=I+Pν(N); and [Pν(E)=I] iff [Pν(N)=0]. No support restriction, pointwise continuity, or global Borel measurability is assumed beyond the joint density definition.

## T36

Fix the everywhere real-valued function

    f(x,y) = (exp(x)/(1+exp(x)))² / [π(1+y² exp(2x))].

With no hypotheses it is `ContDiff ℝ ⊤` (real analytic in the Mathlib order convention above), is strictly positive at every (x,y), is λ²-integrable with ∫f dλ²=1, satisfies ∫⁻_{x∈ℝ}ofReal(f(x,0))dλ=∞, and for every real y≠0 the function x↦f(x,y) is λ-integrable. The zero slice uses an extended nonnegative integral, not the totalized real Bochner integral. No boundedness, explicit slice value, limiting value, CDF, or CDF derivative is asserted.

## T37

Two independently quantified assertions:

1. For every planar probability measure ν and f:ℝ²→ℝ, if `JointDensity ν f`, then for λ-almost every y the extended integral H(y)=∫⁻_x ofReal(f(x,y))dλ is finite. Further, for every g:ℝ→ℝ, if g≥0 everywhere and ofReal(g(y))=H(y) for λ-almost every y, then g is a density of ν.map snd and for every real y the marginal CDF is ∫_{v≤y}g(v)dλ. No global Borel measurability assumption on f or g is added to this clause.
2. For every f:ℝ²→ℝ, assuming global Borel measurability and everywhere nonnegativity, then for every real x, assuming the selected slice y↦f(x,y) is integrable and its real integral M is strictly positive, the slice y↦f(x,y)/M is integrable, is nonnegative at every y, and has real integral 1. There is no probability measure, joint normalization, conditional kernel, or disintegration assertion in this clause. The denominator is explicitly finite and strictly positive.

## T38

Let W be the pushforward of the standard Gaussian `gaussianReal 0 1` by the constant map x↦0. Mathlib's `gaussianReal m s` uses s∈ℝ≥0 as the variance (not the standard deviation), and its zero-variance case is the Dirac measure (`Probability/Distributions/Gaussian/Real.lean:219–233`). The theorem is a closed conjunction asserting:

1. W=δ_0, W({0})=1, no real function is a `Density W`, and for every real m and nonnegative real variance s>0, W≠gaussianReal m s.
2. For every real x, 0·x=0.
3. Both 1 and −1 belong to [−1,1]. At both these values ρ, 1−ρ²=0, 2(1−ρ²)=0, and 2π√(1−ρ²)=0.
4. Define the total real expression

       B(mx,my,sx,sy,ρ;x,y)
        = exp(−[((x−mx)/sx)²+((y−my)/sy)²
                     −2ρ(x−mx)(y−my)/(sx sy)]/[2(1−ρ²)])
            /[2π sx sy √(1−ρ²)].

   For every real pair (x,y), B(0,0,1,1,1;x,y)=B(0,0,1,1,−1;x,y)=0, and both real integrals over ℝ² equal 0; also 0≠1.

The values in clause 4 use Lean's r/0=0 convention at the zero denominator. The actual mathematical endpoint observation independent of that convention is the explicit denominator-zero assertion in clause 3. There is no assertion about arbitrary nonzero linear combinations of several normal variables.
