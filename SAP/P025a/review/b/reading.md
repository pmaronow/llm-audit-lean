# Blind reading of the Challenge

Saved before reading `claims.json` or `record.json`. Sources at this stage are only the supplied Defs and Challenge files and the Mathlib definitions they use. The theorem bodies are stubs; this reading makes no inference from a proof.

## Common notation, expanded definitions, and Mathlib semantics

`Fin n` is the ordered set of integers 0 through n−1. All sums below are ordinary finite sums over that set, or the indicated filtered subset. Real numerals and natural cardinalities in real expressions are coerced to the real numbers. A cut k counts a prefix, so its prefix is i<k and its tail is i≥k. Define

- R(y,a,w) = (Σᵢ aᵢwᵢyᵢ)/(Σᵢ aᵢwᵢ).
- W(α,β) = {w : ∀i, 1/β ≤ wᵢ ≤ 1/α}; B(γ) = {w : ∀i, 1 ≤ wᵢ ≤ γ}.
- Lᵏᵢ = γ if i<k, and 1 otherwise; Hᵏᵢ = 1 if i<k, and γ otherwise. These depend on γ. Write lₖ(y,a,γ)=R(y,a,Lᵏ), hₖ(y,a,γ)=R(y,a,Hᵏ). These are defined also at natural cuts k outside `Fin n`.
- LC(y,a,γ,k): k∈{0,…,n−1}, lₖ≤yₖ, and for every j∈{0,…,n−1} with lⱼ≤yⱼ, k≤j. HC is the same first-index condition using h instead of l. PLC uses the reversed test yⱼ≤lⱼ: yₖ≤lₖ and k≤every index passing that test. Thus a cut predicate asserts membership as well as minimality.
- A(y,a,α,β) = {v∈ℝ : ∃w, w∈W(α,β) and R(y,a,w)=v}; Aₙ(y,a,γ) uses B(γ). E₋=inf A and E₊=sup A are real-valued `sInf` and `sSup`.
- `IsLeast S x` means x∈S and ∀z∈S, x≤z; `IsGreatest S x` means x∈S and ∀z∈S, z≤x. In particular, these assert attainment. A real infimum/supremum has its usual order characterization for nonempty sets bounded in the relevant direction; outside that domain the total Mathlib operation must not be read as an extended real extremum.
- `Monotone y` means ∀i≤j, yᵢ≤yⱼ; `StrictMono y` means ∀i<j, yᵢ<yⱼ. `separation y a γ` means ∀k∈{0,…,n−1}, yₖ≠hₖ and yₖ≠lₖ.
- The arithmetic mean is M(y)=(Σᵢyᵢ)/n. R is a total real division: inversion of 0 is 0 in Mathlib. No positivity is built into R, A, or the endpoint definitions themselves.
- Nₖ(y,a,γ)=γΣᵢ<ₖaᵢyᵢ+Σᵢ≥ₖaᵢyᵢ, and Dₖ(a,γ)=γΣᵢ<ₖaᵢ+Σᵢ≥ₖaᵢ.
- Pₖ(y,a,γ), the `Option ℝ` called `printedLowerExpression`, is undefined (`none`) unless 2≤k≤n. In that domain it is `some` of (γΣᵢ<ₖaᵢyᵢ+Σᵢ≥ₖ₋₂aᵢyᵢ)/(γΣᵢ<ₖaᵢ+Σᵢ≥ₖ₋₂aᵢ). Thus the last two prefix terms also appear in this tail. Natural subtraction k−2 is guarded by k≥2. It does not silently provide a value for k=0 or 1.
- For a finite outcome set Ω, samples S(ω) and real masses p(ω), inclusion Iᵢ=Σω p(ω)1{i∈S(ω)}. Class total for class c(i)=j is Σᵢ:c(i)=j Iᵢ. Neither construction by itself asserts that p is a probability distribution.
- Q(p,π₁,π₀)=(p/π₁)/(p/π₁+(1−p)/π₀). B₋(p,γ)=p/(γ(1−p)+p); B₊(p,γ)=γp/((1−p)+γp); I(p,γ)=[B₋,B₊]. O(pG,pE)=pG(1−pE)/((1−pG)pE).
- Quota(N,s) consists of all s-element subsets of {0,…,N−1}. Its marginal m(N,s,i) is the number of those subsets containing i divided by the total number of subsets, with real division. The list of pairs used below is [(48,44),(16,4),(864,291),(288,288),(12,4),(1156,291),(289,288)].
- F(x,z)=(c₁+xp u+zq v)/(c₂+xp+zq), with its eight real parameters as in the theorem below.
- `[a,b]` is the Mathlib set `{x : a≤x ∧ x≤b}`. Nonempty means an element exists; a nonempty intersection means a common element exists. `Real.sqrt` is the nonnegative square root on nonnegative inputs and 0 on negative inputs.

The Mathlib definitions checked include `Order/Bounds/Defs.lean` (`IsLeast`, generated dual `IsGreatest`, lower and upper bounds), `Order/Monotone/Defs.lean`, `Order/Interval/Set/Defs.lean`, `Data/Set/Defs.lean`, `Data/Finset/Powerset.lean` (`powersetCard` and its membership characterization), `Algebra/GroupWithZero/Defs.lean` (`inv_zero`), `Order/ConditionallyCompleteLattice/Basic.lean`, and `Analysis/Real/Sqrt.lean`. Arrays such as ![0,1] are the indicated functions on `Fin`.

## SAP.P025a.T1

This is a conjunction of closed numerical statements and a universally quantified assertion.

For y=(0,1), masses a=(1,1), γ=2: 0<1/2≤1; y is nondecreasing; PLC holds at k=0; l₀=1/2; l₁=1/3; HC holds at k=1; h₁=2/3; 1/2−1/3=1/6. For every u,v∈ℝ, successively assuming 1≤u, u≤2, 1≤v, v≤2, one has 1/3≤v/(u+v)≤2/3.

The original-scale attainable set A(y,1,1/2,1) equals [1/3,2/3], and 1/3∉[1/2,2/3].

There is fixed finite sampling data Ω={0,1}, S(0)={1}, S(1)={0,1}, p(0)=p(1)=1/2. All outcome masses are nonnegative; their sum is 1; the two inclusion probabilities are (1/2,1); and the mass of outcomes whose sample is {0,1} is 1/2.

Finally, for every natural n, proof/assumption 0<n, function y:Fin n→ℝ, and assumption that y is nondecreasing, and then every γ∈ℝ with 1≤γ: PLC(y,1,γ,0) holds and l₀=M(y). If additionally γ>1 and ∃i, y₀<yᵢ, then l₁<l₀ and l₀ is not a least member of Aₙ(y,1,γ). The existential i occurs only in that last antecedent; the conclusion makes both strict-decrease and non-minimality assertions.

## SAP.P025a.T2

This has no free parameters and no antecedents. Put y=(0,1), a=(1/2,1), γ=2. Every aᵢ lies in [1/2,1]; y is strictly increasing; M(y)=1/2; PLC holds at k=0; l₀=2/3; l₁=1/2; h₁=4/5; and for each k=0,1, yₖ differs from both hₖ and lₖ. Also 1/2<2/3. For every u,v∈ℝ, in order assuming 1≤u, u≤2, 1≤v, v≤2, the bounds 1/2≤v/(u/2+v)≤4/5 hold. This assertion contains no population/class-size construction and does not itself call a=(1/2,1) a class total.

## SAP.P025a.T3

For every natural n, assumption 0<n, y:Fin n→ℝ and assumption that y is nondecreasing, then α,β∈ℝ with the successive assumptions 0<α, α≤β, β≤1, set γ=β/α. Both hₙ₋₁≤yₙ₋₁ and lₙ₋₁≤yₙ₋₁ hold. There exist indices kL,kH∈Fin n, in that order and depending on the preceding data, such that all the following hold jointly:

1. LC holds at kL, and HC holds at kH.
2. wL=(1/β)Lᵏᴸ and wH=(1/β)Hᵏᴴ both lie in W(α,β); R(y,1,wL)=lₖᴸ and R(y,1,wH)=hₖᴴ.
3. lₖᴸ is an attained least member of A(y,1,α,β), and hₖᴴ is an attained greatest member. E₋=lₖᴸ and E₊=hₖᴴ, and A(y,1,α,β)=[lₖᴸ,hₖᴴ].
4. For every real z∈[lₖᴸ,hₖᴴ], there exists real t∈[0,1] such that wᵢ=(1/β)((1−t)Lᵏᴸᵢ+tHᵏᴴᵢ) is in W(α,β) and R(y,1,w)=z. The quantifier order is ∃kL,kH ∀z ∃t, and no continuity predicate occurs.
5. For every k∈Fin n, lₖ₊₁−lₖ=(γ−1)(yₖ−lₖ)/(ΣᵢLᵏ⁺¹ᵢ), and hₖ₊₁−hₖ=(1−γ)(yₖ−hₖ)/(ΣᵢHᵏ⁺¹ᵢ). Thus the final increment includes the cut n.
6. Let m=lₖᴸ. For every i<kL, yᵢ<m; for every i≥kL, m≤yᵢ. For every function u:Fin n→ℝ satisfying u∈B(γ), R(y,1,u)−m=Σᵢ(uᵢ−Lᵏᴸᵢ)(yᵢ−m)/(Σᵢuᵢ); each summand in that numerator is nonnegative; and R(y,1,u)−m≥0.

Here n−1 is natural subtraction under the explicit assumption n>0.

## SAP.P025a.T4

For every natural J, assumption J>0, functions y,mass:Fin J→ℝ, assumption that y is strictly increasing, assumption ∀j, massⱼ>0, and α,β∈ℝ with 0<α≤β≤1, there exist kL,kH∈Fin J such that LC(y,mass,β/α,kL) and HC(y,mass,β/α,kH), lₖᴸ is an attained least element of A(y,mass,α,β), hₖᴴ is an attained greatest element, E₋=lₖᴸ and E₊=hₖᴴ. No class-size, population, separation, specific attaining weight function, or full-image equality is asserted or assumed.

## SAP.P025a.T5

This is a conjunction of explicit equalities, inequalities, finite-set assertions, and quota assertions. There are no external hypotheses.

Population-count arithmetic: 48/(48+16)=864/(864+288)=3/4; 48/(48+12)=1156/(1156+289)=4/5. Natural sample-count sums are 44+4=48 and 291+288=579.

The following probability bounds are asserted individually: 11/12∈[1/4,1], 97/288∈[1/4,1], 1/4≤1/3, 291/1156∈[1/4,1], and 288/289∈[1/4,1]. The assertion 1/3≤1 does not separately occur.

The four reweighted values and directional selection ratios are

| p | π₁ | π₀ | Q | asserted ratio and comparison |
|---|---|---|---|---|
| 44/48 | 11/12 | 1/4 | 3/4 | π₁/π₀=11/3>3 |
| 291/579 | 97/288 | 1 | 3/4 | π₀/π₁=288/97<3 |
| 44/48 | 11/12 | 1/3 | 4/5 | π₁/π₀=11/4<3 |
| 291/579 | 291/1156 | 288/289 | 4/5 | π₀/π₁=384/97>3 |

Both products (11/3)(288/97) and (11/4)(384/97) equal 1056/97. Also B₋(44/48,4)≤3/4<4/5≤B₊(291/579,4).

For rounded-input variants, each of 249/917, 503/1491, 332/917, 503/1988 lies in [1/4,1]. The forward sample-prevalence formulas are

- ((3/4)·1)/((3/4)·1+(1−3/4)(249/917))=917/1000;
- ((3/4)(503/1491))/((3/4)(503/1491)+(1−3/4)·1)=503/1000;
- ((4/5)·1)/((4/5)·1+(1−4/5)(332/917))=917/1000;
- ((4/5)(503/1988))/((4/5)(503/1988)+(1−4/5)·1)=503/1000.

The ratios 1491/503 and 917/332 are each <3.

For each of the seven listed pairs (N,s), Quota(N,s) is nonempty, and for every unit i its marginal is respectively 11/12, 1/4, 97/288, 1, 1/3, 291/1156, 288/289. Separately, for every pair of naturals N,s, if (N,s) belongs to that fixed list, then Quota(N,s) is nonempty, Σₜ∈Quota(N,s) 1/|Quota(N,s)|=1, and every t∈Quota(N,s) has |t|=s. There is no joint distribution on strata here.

The exact rounding inequalities are 91.7−0.05≤100(44/48)<91.7+0.05 and 50.3−0.05≤100(291/579)<50.3+0.05. Finally each of 3/4 and 4/5 belongs both to I(44/48,4) and to I(291/579,4).

## SAP.P025a.T6

The conjunction consists of these assertions, with the universal quantifiers in each item independent of the others:

1. For every real pG,pE,γ, successively assuming 0<pE, pE<pG, pG<1, and 1≤γ: I(pG,γ)∩I(pE,γ) is nonempty iff B₋(pG,γ)≤B₊(pE,γ); that latter inequality is equivalent to O(pG,pE)≤γ²; and intersection nonemptiness is equivalent to sqrt(O(pG,pE))≤γ.
2. O(917/1000,503/1000)=455749/41749, with (3.30)²<455749/41749<(3.31)². O(44/48,291/579)=1056/97, with (3.29)²<1056/97<(3.30)². Both odds ratios are strictly between 9 and 16. Also (11/3)(288/97)=1056/97 with 288/97<3, and (11/4)(384/97)=1056/97 with 11/4<3.
3. For every real γ≥1, the rounded-data intersection is nonempty iff sqrt(455749/41749)≤γ, and the exact-count intersection is nonempty iff sqrt(1056/97)≤γ.
4. Both intersections in item 3 are empty at γ=3 and nonempty at γ=4.
5. For every real p,π₁,π₀, assuming in order 0<p, p<1, π₁>0, π₀>0, put q=Q(p,π₁,π₀). Then q=pπ₀/(pπ₀+(1−p)π₁) and q/(1−q)=(p/(1−p))(π₀/π₁).
6. For every real pG,pE,g₁,g₀,e₁,e₀, assuming 0<pE<pG<1 and all four g/e parameters positive: Q(pG,g₁,g₀)=Q(pE,e₁,e₀) iff (g₁/g₀)(e₀/e₁)=O(pG,pE).
7. For every real pG,pE,g₁,g₀,e₁,e₀,γ, assuming 0<pE<pG<1, all four g/e parameters positive, equal reweighted prevalences, g₁/g₀≤γ and e₀/e₁≤γ, conclude O(pG,pE)≤γ². There is no explicit assumption γ≥1 in this item and no upper bound 1 on the positive selection parameters.
8. 3.30399<sqrt(455749/41749)<3.30400 and 3.29948<sqrt(1056/97)<3.29949.

## SAP.P025a.T7

First define the printed sample assertion C: for every n>0, every nondecreasing real y on Fin n, and every α,β with 0<α≤β≤1, there exist kL,kH∈Fin n such that PLC(y,1,β/α,kL), HC(y,1,β/α,kH), lₖᴸ is an attained least element of A(y,1,α,β), hₖᴴ is an attained greatest element, and A(y,1,α,β)=[lₖᴸ,hₖᴴ]. T7 asserts ¬C. This negation refutes the conjunction just specified; it does not independently assert the failure of each conjunct.

In addition, for every n>0, nondecreasing y:Fin n→ℝ, and α,β with 0<α≤β≤1, there exists kH∈Fin n such that HC(y,1,β/α,kH) and hₖᴴ is an attained greatest element of A(y,1,α,β). These parameters are universally quantified anew, independently of the negation of C.

## SAP.P025a.T8

Define the printed class assertion D: for every J>0, every strictly increasing y:Fin J→ℝ, every positive mass:Fin J→ℝ, and every 0<α≤β≤1, there exist kL,kH∈Fin J such that PLC(y,mass,β/α,kL), HC(y,mass,β/α,kH), lₖᴸ is an attained least member of A, hₖᴴ is an attained greatest member of A, Pₖᴸ(y,mass,β/α)=some(E₋), and E₊=hₖᴴ. T8 asserts ¬D. In particular this is a refutation of a conjunction that includes both a lower optimizer assertion and the separately defined optional printed expression. It does not assert their independent failure.

In addition, for every J>0, strictly increasing y, positive mass, and 0<α≤β≤1, there exists kH∈Fin J such that HC holds, hₖᴴ is an attained greatest element of A(y,mass,α,β), and E₊=hₖᴴ. There is no separation hypothesis or conclusion in D or the surviving upper statement.

## SAP.P025a.T9

For every J>0, functions y,mass:Fin J→ℝ, assumption that y is strictly increasing, assumption every mass is positive, then every real α,β with 0<α≤β≤1, setting γ=β/α, the following hold:

1. For every natural k≤J, R(y,mass,w) with wᵢ=1/α for i<k and wᵢ=1/β otherwise equals Nₖ/Dₖ.
2. For every k∈Fin J, if LC(y,mass,γ,k), then E₋=Nₖ/Dₖ.
3. For every natural k, and successive assumptions 2≤k and k≤J, let u=k−2, v=k−1 (valid indices), N=Nₖ and D=Dₖ. Then Pₖ=some((N+massᵤyᵤ+massᵥyᵥ)/(D+massᵤ+massᵥ)), and this displayed ratio minus N/D equals (massᵤ(yᵤ−N/D)+massᵥ(yᵥ−N/D))/(D+massᵤ+massᵥ).
4. P₀=none and P₁=none.

These last assertions refer to optional undefined indices, not numeric equalities at those indices.

## SAP.P025a.T10

This is a conjunction of closed statements. For y=(0,1,2,3), mass=(1,1,1,1), γ=2: y is strictly increasing; LC holds at k=2; l₂=7/6; P₂=some(1); PLC holds at k=0; P₀=none; 1≠7/6; and for every w:Fin 4→ℝ with 1≤wᵢ≤2 for every i, R(y,1,w)≥7/6. Also l₀=3/2 and l₁=6/5.

The fixed six-unit data are outcomes (0,0,1,1,2,3) and class labels (0,0,1,1,2,3). The outcome space for a design is Fin 2×Fin 2. For ω=(r,s), S(ω)={r,s+2,4,5}; every such outcome has probability 1/4. These probabilities are nonnegative and sum to 1. Each unit's inclusion probability is respectively (1/2,1/2,1/2,1/2,1,1); every class total is 1; class sizes are (2,2,1,1); and the six-unit mean is 7/6. Finally, for every class j, class size divided by class total is L²ⱼ for γ=2, namely (2,2,1,1). The definition shows outcomes agree with class labels, but the statement does not separately assert this equality as a conjunct.

## SAP.P025a.T11

This is the conjunction of three independent universal assertions.

First, for every n>0, real nondecreasing y:Fin n→ℝ, and every γ≥1:

- For every k∈Fin n, hₖ₊₁−hₖ=(1−γ)(yₖ−hₖ)/(ΣᵢHᵏ⁺¹ᵢ).
- If γ=1, then for every natural k, hₖ=M(y), lₖ=M(y), and for every real vector w on Fin n, w∈B(γ) iff w is identically 1. The last vector assertion is inside the universal k but independent of k.
- If γ>1, the set {k∈Fin n : hₖ≥hₖ₊₁} equals {k∈Fin n : hₖ≤yₖ}.
- For every k∈Fin n, if hₖ≤yₖ then hₖ₊₁≤yₖ.
- If γ>1, for every k∈Fin n, hₖ₊₁−hₖ≤0 iff hₖ≤yₖ.

Second, for all real c₁,c₂,p,q,u,v,a,b, successively assuming c₂≥0, p>0, q>0, a>0, a≤b, u<v, let X=c₂u−c₁+aq(u−v), Y=c₁−c₂v+bp(u−v). Then

- (c₂+ap+aq)(c₂+bp+aq)(F(a,a)−F(b,a))=(a−b)pX;
- (c₂+bp+bq)(c₂+bp+aq)(F(b,b)−F(b,a))=(a−b)qY;
- X+Y=(c₂+bp+aq)(u−v), and X+Y<0.

Third, universally quantify the same eight real parameters again with the same six assumptions. If a<b, then F(a,a)>F(b,a) iff X<0, F(b,b)>F(b,a) iff Y<0, and at least one of F(a,a),F(b,b) is strictly larger than F(b,a). If a=b, then F(a,a)=F(b,a) and F(b,b)=F(b,a). c₁ and the signs of u,v have no restrictions beyond u<v. No normalized stationary-index existence or global maximization conclusion is present.
