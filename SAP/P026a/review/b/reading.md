# Blind reading

This file was written from `SAP/P026a/Defs.lean`, all sixteen `Defs/Part*.lean`
files, and the Challenge files, before opening either `claims.json` or
`record.json`. The Challenge theorem names below are in namespace `SAP.P026a`.
The comments in those Lean files were visible, but the readings below follow
the actual propositions, including their bundled assumptions.

## Common objects and fully expanded notation

All sums and products are finite. `Fintype` supplies a finite set containing
every element; `Finset.univ` is that set, `univ.erase i` removes just i, and
`univ.filter p` keeps exactly the elements satisfying p. Thus off-diagonal
sums below are **ordered**, with both (i,j) and (j,i) when applicable.
`Fin n` means {0,...,n-1}. A vector literal lists entries in that order.
`↥J` is the type of elements of the finite set J, so a fitting vector is the
entire function on J, not one of its coordinates. Decidable equality is only
an implementation assumption. These meanings were checked against Mathlib's
`Data/Fintype/Defs.lean`, `Data/Finset/Erase.lean`,
`Data/Finset/Filter.lean`, and `Algebra/BigOperators/Group/Finset/Defs.lean`.

An `AssignmentDesign D` is just a function q:Ω→R of weights and a function
A:Ω×I→{0,1} of assignments (Bool true = 1, false = 0). Ω and I are finite.
It does not itself require probabilities. In the examples R=ℚ; in the
universally quantified laws below R=ℝ. The generic helper definitions allow
any linearly ordered field. Write

* E[f]=Σω qω fω (`mean`), Cov(f,g)=E[fg]−E[f]E[g], Var(f)=Cov(f,f).
* Sᵃᵢ(ω)=1{Aᵢ(ω)=a}; πᵃᵢ=E[Sᵃᵢ]; πᵃᵇᵢⱼ=E[SᵃᵢSᵇⱼ].
* A probability law means qω≥0 for **every** ω and Σω qω=1.
  Positive marginals means π¹ᵢ>0 and π⁰ᵢ>0 for every i.
* Observed response Yᵢ(ω)=xᵢ if Aᵢ(ω)=1, and zᵢ otherwise.
  Fixed totals are Σᵢxᵢ. The average effect is (Σx−Σz)/N.
* Hₐ(y)=ΣᵢSᵃᵢyᵢ/πᵃᵢ (`htSum`), H_N(x,z)=(H₁(x)−H₀(z))/N.
* Gₐ(y,f)=Σᵢ[Sᵃᵢyᵢ/πᵃᵢ−Sᵃᵢfᵢ/πᵃᵢ+fᵢ]
  (`adjustedSum`), G_N(x,z,f)=(G₁(x,f)−G₀(z,f))/N.
* dᵢⱼ=E[1{Aᵢ≠Aⱼ}] (`disagreementProbability`). Directed support
  means π¹⁰ᵢⱼ>0 for **each ordered** pair i≠j.
* O(f)=ΣᵢΣⱼ≠ᵢfᵢⱼ. Uₐᵦ(f)=ΣᵢΣⱼ≠ᵢ,πᵃᵇᵢⱼ=0 fᵢⱼ
  (`unavailablePairSum`). No diagonal pair enters U.

Every division is ordinary field division, which is totalized in Lean by
0⁻¹=0. The universal statements use strictly positive marginals, and N is
the cardinality of a nonempty unit type. Joint-probability denominators in
the following definitions have the displayed guards; the one unguarded
same-arm estimator below is asserted only with positive same-arm support.

Here are the estimators and population expressions in full. Put
δ(p)=1 if p=0, and δ(p)=0 otherwise. For any arms a,b define

    Kₐᵦᵢⱼ(ω) = Sᵃᵢ Sᵇⱼ / (πᵃᵇᵢⱼ+δ(πᵃᵇᵢⱼ))
                   ·(πᵃᵇᵢⱼ−πᵃᵢπᵇⱼ)·(Yᵢ/πᵃᵢ)·(Yⱼ/πᵇⱼ).
    Lₐᵢⱼ(ω) = SᵃᵢYᵢ²/(2πᵃᵢ)+SᵃⱼYⱼ²/(2πᵃⱼ).
    Vp_N = [Σᵢ(S¹ᵢ(Yᵢ/π¹ᵢ)²+S⁰ᵢ(Yᵢ/π⁰ᵢ)²)
              +O(K₁₁+K₀₀−2K₁₀)+U₁₁(L₁)+U₀₀(L₀)]/N².

`Vp` denotes `printedVarianceEstimate`. The zero-omitted covariance
continuation (`covarianceWithZeroOmission`) is

    C0 = ΣᵢΣⱼ≠ᵢ [0 if π¹⁰ᵢⱼ=0, otherwise
              S¹ᵢS⁰ⱼ/π¹⁰ᵢⱼ ·(π¹⁰ᵢⱼ−π¹ᵢπ⁰ⱼ)
                 ·(Yᵢ/π¹ᵢ)·(Yⱼ/π⁰ⱼ)]
         −ΣᵢS¹ᵢYᵢ²/(2π¹ᵢ)−ΣᵢS⁰ᵢYᵢ²/(2π⁰ᵢ).

It is explicitly a continuation when some directed probabilities vanish.
The correction and repaired estimators are

    Q = U₁₀((i,j)↦S¹ᵢYᵢ²/π¹ᵢ+S⁰ⱼYⱼ²/π⁰ⱼ),
    Cr = C0−Q/2,   Vr_N = Vp_N+Q/N².

For fixed vectors x,z,y define

    Va(y) = Σᵢπᵃᵢ(1−πᵃᵢ)(yᵢ/πᵃᵢ)²
               +O((πᵃᵃᵢⱼ−πᵃᵢπᵃⱼ)(yᵢ/πᵃᵢ)(yⱼ/πᵃⱼ));
    Cpop(x,z) = O((π¹⁰ᵢⱼ−π¹ᵢπ⁰ⱼ)(xᵢ/π¹ᵢ)(zⱼ/π⁰ⱼ))−Σᵢxᵢzᵢ;
    Bcov(x,z) = O((π¹⁰ᵢⱼ−π¹ᵢπ⁰ⱼ)(xᵢ/π¹ᵢ)(zⱼ/π⁰ⱼ))
                     −Σᵢxᵢ²/2−Σᵢzᵢ²/2;
    Barm_a(y) = Σᵢπᵃᵢ(1−πᵃᵢ)(yᵢ/πᵃᵢ)²
            +ΣᵢΣⱼ≠ᵢ,πᵃᵃᵢⱼ>0(πᵃᵃᵢⱼ−πᵃᵢπᵃⱼ)(yᵢ/πᵃᵢ)(yⱼ/πᵃⱼ)
            +Uₐₐ((i,j)↦yᵢ²/2+yⱼ²/2);
    Vhat_a(x,z) = ΣᵢSᵃᵢ(1−πᵃᵢ)(Yᵢ/πᵃᵢ)²
               +ΣᵢΣⱼ≠ᵢ,πᵃᵃᵢⱼ>0 Kₐₐᵢⱼ + Uₐₐ(Lₐ);
    Rbias(x,z) = Σᵢ(xᵢ−zᵢ)²
                +U₁₁((i,j)↦(xᵢ+xⱼ)²)/2
                +U₀₀((i,j)↦(zᵢ+zⱼ)²)/2
                +U₁₀((i,j)↦(xᵢ−zⱼ)²).

`splitPopulationCovariance`, denoted Cs(x,z), sums over **all** ordered
pairs including i=j:

    Cs = ΣᵢΣⱼ [ (π¹⁰ᵢⱼ−π¹ᵢπ⁰ⱼ)(xᵢ/π¹ᵢ)(zⱼ/π⁰ⱼ) if π¹⁰ᵢⱼ≠0,
                 0 otherwise ] −ΣᵢΣⱼ [xᵢzⱼ if π¹⁰ᵢⱼ=0, 0 otherwise].

`fullSupportArmEstimate` is the first (diagonal) sum of Vhat_a plus
O(SᵃᵢSᵃⱼ/πᵃᵃᵢⱼ ·(πᵃᵃᵢⱼ−πᵃᵢπᵃⱼ)·(Yᵢ/πᵃᵢ)·(Yⱼ/πᵃⱼ)),
without a zero-denominator guard or unavailable-pair adjustment.

`appendixDisplay`, denoted App, is

    ΣᵢS¹ᵢ(1−π¹ᵢ)(Yᵢ/π¹ᵢ)² + ΣᵢΣⱼ≠ᵢ,π¹¹ᵢⱼ>0 K₁₁ᵢⱼ
       −ΣᵢS¹ᵢYᵢ²/(2π¹ᵢ)−ΣᵢS⁰ᵢYᵢ²/(2π⁰ᵢ).

A `UnitLaw I` is a probability law on **all** binary functions w:I→Bool,
with q(w) real, q≥0, Σq=1, both marginal probabilities strictly positive
for every i, and assignment Aᵢ(w)=w(i). Zero-weight allocations are allowed.
A `ClusterLaw U C` consists of finite U,C, a fixed **surjective** map
c:U→C, and a UnitLaw on C. Its cluster design uses Aₖ(w)=w(k); its unit
design uses Aᵢ(w)=w(c(i)), with exactly the same weights. Its totals are
Xₖ=Σᵢ:c(i)=k xᵢ, Zₖ=Σᵢ:c(i)=k zᵢ. Where written below as the common cluster
premise, the quantifiers are, in order: arbitrary types U,C; finiteness and
decidable equality on U; nonempty U; finiteness and decidable equality on C;
nonempty C; E:ClusterLaw U C; and **Sep**: dₖₗ>0 for all k≠l. Thus both
positive marginals, the probability conditions, and nonempty clusters are
already assumptions. N=|U|; expressions using X,Z have index type C.

`finiteIndependent D f g`, written f ⟂ g, means literally
∀u:range-type(f)→R, ∀v:range-type(g)→R,
E[u(f)v(g)]=E[u(f)]E[v(g)]. It quantifies over all functions, with no
measurability assumption; because Ω is finite this is ordinary independence
of the induced finite-valued random variables. For J⊆I, W_J(w) is the full
assignment vector (w(j))j∈J and Y_J(w) the full response vector (Yⱼ(w))j∈J.
`independentAssignments` is the factorization
∀(Fᵢ:{0,1}→R), E[∏ᵢFᵢ(Aᵢ)]=∏ᵢE[Fᵢ(Aᵢ)].
`independentBlocks D c`, for a finite block type B and map c:I→B, is the
same factorization for arbitrary functions F_b of each entire block
assignment vector W_{j:c(j)=b}. Empty fibers are allowed in this latter
helper; the function domain for an empty vector is a singleton.

## Explicit designs and numerical formulas

All designs in this section have uniform weights and rational arithmetic.
Assignments below are written as 0/1 strings in the literal state order.

* A=`asymmetricPairLaw`: I=Fin 2, Ω=Fin 3, states 00,01,11; each weight 1/3.
* B=`asymmetricSixLaw`: I=Fin 6, Ω=Fin 14, weight 1/14; states
  000111,001011,001101,001110,010011,010101,010110,
  011001,011010,011100,110001,110010,110100,111000.
* X6=`xorSixLaw`: I=Fin 6, Ω=Fin 4, weight 1/4; states
  010101,011010,100110,101001. Potential outcomes x≡1,z≡0 are used in
  its fitting formula. Put h(u,v)=u+v−2uv. Then `xorSixFit` is
  (h(Y₂,Y₄),1−h(Y₂,Y₄),h(Y₀,Y₄),1−h(Y₀,Y₄),h(Y₀,Y₂),1−h(Y₀,Y₂)).
* X3=`xorThreeLaw`: I=Fin 3, Ω=Fin 4, weight 1/4; states
  000,011,101,110. Again x≡1,z≡0. `xorThreeFit` is
  (h(Y₁,Y₂),h(Y₀,Y₂),h(Y₀,Y₁)); `productFit` is (0,0,Y₀Y₁).
* F4=`twoOfFourLaw`: I=Fin 4, Ω=Fin 6, weight 1/6; states
  1100,1010,1001,0110,0101,0011. `appendixNullOutcomes` is (1,2,4,7).
* T=`paperTableDesign`: ten clusters; Ω=Fin 6×Fin 15; every state has
  weight 1/90. The first four cluster assignments are F4; independently,
  the last six choose exactly two treated clusters, all 15 choices in
  lexicographic order of the treated pair (01,02,03,04,05,12,13,14,15,
  23,24,25,34,35,45). The sixteen units have cluster indices
  c=(0,0,1,1,2,3,4,4,4,5,5,6,6,7,8,9), responses
  y=(1,1,1,1,1,0,1,1,0,1,1,1,1,0,0,0), covariates
  x=(4,0,4,1,4,2,4,1,2,5,4,1,4,2,2,3).
  Unit assignments are cluster assignments composed with c.
  The deterministic prediction mᵢ is 1/4+xᵢ/8 on units 0..5, and
  70/93+xᵢ/31 on units 6..15. The cluster residual rₖ is
  Σᵢ:c(i)=k(yᵢ−mᵢ). The explicit HT outcome vector is
  t=(2,2,1,0,2,2,2,0,0,0); the prior residual is
  p=(1,1,1/2,−1/2,1/2,1,1,−1/2,−1/2,−1/2).

For the numerical coefficient formulas, blocks are units 0..5 and 6..15.
Define x̃ᵢ=xᵢ−(5/2 or 14/5), ỹᵢ=yᵢ−(5/6 or 3/5), and
t̃ᵢ(ω)=S¹ᵢ(ω)−the unit mean of S¹ in its block (denominators 6 and 10).
Let

    sᵢ(ω)=t̃ᵢ(ω)−[Σⱼx̃ⱼt̃ⱼ(ω)/Σⱼx̃ⱼ²]x̃ᵢ,
    b(ω)=Σᵢsᵢ(ω)ỹᵢ/Σᵢsᵢ(ω)² (`paperFeEstimate`).

The unused auxiliary definitions also specify
βx(ω)=Σx̃ᵢ(ỹᵢ−b(ω)t̃ᵢ)/Σx̃ᵢ² and fitted values
(block mean of y)+b(ω)t̃ᵢ+βx(ω)x̃ᵢ. No optimization property is part of
these definitions. In the cluster indexing, the natural subtraction i−4
in the second block is only used under i≥4.

For rational v,r, `roundsToThree(v,r)` is exactly
r−1/2000≤v<r+1/2000. `sdRoundsToThree(v,r)` is exactly
(r−1/2000)²≤v<(r+1/2000)²; all r to which it is applied here are positive
and larger than 1/2000, so it describes rounding √v with the same half-open
interval. It is not a separately defined real square root.

## T1

No hypotheses or outer variable quantifiers: a conjunction of facts about
the two fixed laws A and B, with x=z≡1 throughout.

For A: it is a probability law with positive marginals. For every ordered
i≠j, dᵢⱼ>0, π¹¹ᵢⱼ>0 and π⁰⁰ᵢⱼ>0. π¹⁰₀₁=0 and π¹⁰₁₀=1/3.
For every state ω, S¹₀S⁰₁=0,
H₂(1,1)(ω)=(−9/4,0,9/4)ω and Vp₂(1,1)(ω)=(57/16,3/2,57/16)ω.
E[H₂]=0, Var(H₂)=27/8, E[Vp₂]=23/8<27/8,
Cov(H₁(1),H₀(1))=−13/4, E[C0(1,1)]=−9/4, and −13/4<−9/4.

For B: it is a probability law with positive marginals; every state treats
exactly three indices. For every ordered i≠j, dᵢⱼ>0, π¹¹ᵢⱼ>0 and
π⁰⁰ᵢⱼ>0, and π¹⁰ᵢⱼ=0 iff (i,j)=(0,1).
Var(H₆(1,1))=9/700; E[Vp₆(1,1)]=−269/6300<9/700;
Cov(H₁(1),H₀(1))=27/175; E[C0(1,1)]=202/175.

## T2

A conjunction of separately quantified assertions; no later conjunct
implicitly assumes the conclusion of an earlier one. In items 1–10 below
the common cluster premise is quantified first, including Sep, followed by
the listed additional objects in their stated order. All X,Z,R below are
cluster totals of the displayed arbitrary real unit vectors x,z,r.

1. For all i,j∈C, assuming i≠j, dᵢⱼ=π¹⁰ᵢⱼ+π¹⁰ⱼᵢ.
2. For all i,j∈C, assuming i≠j, dᵢⱼ>0 iff π¹⁰ᵢⱼ>0 or π¹⁰ⱼᵢ>0.
3. For all x,z:U→ℝ, Cov(H₁(X),H₀(Z))=Cpop(X,Z).
4. For all x,z, N²(E[Vp_N(X,Z)]−Var(H_N(X,Z))) equals
   Σᵢ(Xᵢ−Zᵢ)²+U₁₁((Xᵢ+Xⱼ)²)/2+U₀₀((Zᵢ+Zⱼ)²)/2−2U₁₀(XᵢZⱼ).
5. For all x,z, E[Cr(X,Z)]−Cov(H₁(X),H₀(Z)) equals
   −Σᵢ(Xᵢ−Zᵢ)²/2−U₁₀((Xᵢ−Zⱼ)²)/2; also
   E[Cr(X,Z)]≤Cov(H₁(X),H₀(Z)).
6. For all x,z, N²(E[Vr_N(X,Z)]−Var(H_N(X,Z)))=Rbias(X,Z),
   and Var(H_N(X,Z))≤E[Vr_N(X,Z)].
7. For all c:U→ℝ, then assuming π¹¹ᵢⱼ,π⁰⁰ᵢⱼ>0 for all i≠j,
   write Cᵢ for its cluster totals: E[Vr_N(C,C)]−Var(H_N(C,C))
   =U₁₀((Cᵢ−Cⱼ)²)/N². Equality of the two moments holds iff
   ∀i,j with i≠j and π¹⁰ᵢⱼ=0, Cᵢ=Cⱼ.
8. For all x,z, then ω:C→Bool, then assuming qω>0,
   Vr_N(X,Z)(ω)=[Vhat₁(X,Z)(ω)+Vhat₀(X,Z)(ω)−2Cr(X,Z)(ω)]/N².
9. For all x,z,r:U→ℝ,
   N²(E[Vr_N(X−R,Z−R)]−Var(G_N(X,Z,constant R)))
   =Rbias(X−R,Z−R), and that variance is ≤ that expectation.
10. For all x,z, Rbias(X,Z)≥0.

In addition there are four conjuncts:

11. For B with c=(1,2,1,1,1,1), Var(H₆(c,c))=2759/12600,
    E[Vp₆(c,c)]=151/1400, E[Vr₆(c,c)]=3109/12600, and
    2759/12600<3109/12600.
12. Quantify U,C with finiteness, decidable equality, nonempty U,C,
    then E:ClusterLaw U C, then x,z,r:U→ℝ, **without Sep**.
    Totals(x−r)=X−R and Totals(z−r)=Z−R, and, as functions of ω,
    G_N(X,Z,constant R)=H_N(Totals(x−r),Totals(z−r)).
13. For A, d₀₁>0 and π¹⁰₀₁=0.
14. For B and the same c as item 11,
    E[Vp₆(c,c)]−Var(H₆(c,c))=−1/9 and
    E[Vr₆(c,c)]−Var(H₆(c,c))=1/36.

## T3

Four conjuncts, each independently quantified where indicated.

1. Quantify the common cluster premise, then directed support, then arbitrary
   x,z:U→ℝ. The assertions are E[C0(X,Z)]−Cov(H₁(X),H₀(Z))
   =−Σᵢ(Xᵢ−Zᵢ)²/2; E[C0]≤that covariance;
   N²(E[Vp_N(X,Z)]−Var(H_N(X,Z)))
   =Σᵢ(Xᵢ−Zᵢ)²+U₁₁((Xᵢ+Xⱼ)²)/2+U₀₀((Zᵢ+Zⱼ)²)/2;
   Var(H_N)≤E[Vp_N]. Further, if Xᵢ=Zᵢ for every i and both same-arm
   probabilities are positive for all i≠j, then E[Vp_N]=Var(H_N).
   This last condition is equality of cluster totals, not an assumption of
   equality of the two unit outcomes.
2. Quantify the common cluster premise, directed support, then x,z,r.
   Var(G_N(X,Z,constant R))≤E[Vp_N(X−R,Z−R)]. If all Xᵢ=Zᵢ and both
   same-arm off-diagonal supports are positive, equality holds.
3. The fixed table law T is a probability law with positive marginals and
   directed support. For every i≠j, π¹⁰ᵢⱼ≥1/6, π¹¹ᵢⱼ≥1/15,
   π⁰⁰ᵢⱼ≥1/6 and dᵢⱼ>0. There exist (separately for each probability)
   distinct i,j attaining each of these three bounds.
4. The residual identities of T2 item 12, with exactly its quantifiers and
   with no Sep or directed-support assumption.

## T4

No outer hypotheses; two conjuncts about fixed laws, using x≡1,z≡0.

For X6: probability law, positive marginals, π¹ᵢ=π⁰ᵢ=1/2 for each i.
For every i,j with floor(i/2)≠floor(j/2), and every a,b∈Bool,
πᵃᵇᵢⱼ=1/4. Every state treats exactly three units. For every state and
index, xorSixFitᵢ=S¹ᵢ. For every i, Cov(S¹ᵢ,xorSixFitᵢ)=1/4.
For every state, G₁(1,fit)=3, G₀(0,fit)=3,
G₆(1,0,fit)=0 and H₆(1,0)=1. The average effect is 1 and
E[G₆]−1=−1.

For X3: probability law, positive marginals; for each i≠j and a,b,
πᵃᵇᵢⱼ=1/4. For every state and index, xorThreeFitᵢ=S¹ᵢ;
Cov(S¹ᵢ,xorThreeFitᵢ)=1/4 for every i. E[G₃(1,0,xorThreeFit)]=0.
Cov(S¹₂,productFit₂)=−1/8, E[G₃(1,0,productFit)]=7/6, and the average
effect is 1. No exact fitting-set characterization or explicit probability
comparison for failure of vector independence is asserted here.

## T5

Six separately universally quantified propositions.

1. Quantify finite nonempty I with decidable equality; E:UnitLaw I;
   arbitrary type Θ; i∈I; finite J⊆I; y1,y0:I→ℝ;
   deterministic G:(J→ℝ)→Θ; P:Θ→ℝ; then the assumption
   Aᵢ ⟂ W_J. The conclusions are Aᵢ ⟂ G(Y_J),
   Aᵢ ⟂ P(G(Y_J)), and Cov(S¹ᵢ,P(G(Y_J)))=0.
2. Exactly the same quantifier order and conclusions, but the assumption
   is Aᵢ ⟂ Y_J instead of Aᵢ ⟂ W_J.
3. Quantify finite nonempty I, E:UnitLaw I, x,z:I→ℝ,
   a choice J:I→Finset I, then Gᵢ:(Jᵢ→ℝ)→ℝ for every i,
   then assume Aᵢ ⟂ W_{Jᵢ} for **every** i. Define
   fᵢ(ω)=Gᵢ(Y_{Jᵢ}(ω)). Conclusions:
   E[G₁(x,f)]=Σx, E[G₀(z,f)]=Σz, and
   E[G_|I|(x,z,f)]=(Σx−Σz)/|I|.
4. Quantify finite nonempty I, E, i,J,x,z, a∈ℝ, coefficients b:J→ℝ,
   then assume Aᵢ ⟂ Aⱼ for every j∈J. The covariance of S¹ᵢ with
   a+Σⱼ∈JbⱼYⱼ equals Σⱼ∈Jbⱼ(xⱼ−zⱼ)Cov(S¹ᵢ,S¹ⱼ), and equals zero.
   The algebraic covariance identity is itself under that independence
   assumption in this statement.
5. Quantify finite I with decidable equality (no Nonempty instance),
   E:UnitLaw I, assume independentAssignments E, then quantify i∈I.
   Conclusion: Aᵢ ⟂ W_{I\{i}}.
6. Quantify finite I,B with decidable equality, E:UnitLaw I, c:I→B,
   assume independentBlocks E c, then quantify i∈I. Conclusion:
   Aᵢ ⟂ W_{j:c(j)≠c(i)}.

## T6

No hypotheses; all statements use the explicitly defined table law T and
the deterministic formulas in the common section.

1. Σx̃ᵢ²>0; for **every** ω∈Fin 6×Fin 15, Σsᵢ(ω)²>0.
2. The vector r of cluster residuals equals
   (1,7/8,1/4,−1/2,−15/31,19/93,1/3,−76/93,−76/93,−79/93).
3. E[H₁₆(r,r)]=0; Var(H₁₆(r,r))=E[Vp₁₆(r,r)]=v=38307/634880;
   Var(Vp₁₆(r,r))=u=2400328658503/15687787688755200.
4. v>265/10000; v>(1625/10000)²; u>(75/10000)².
5. For b=`paperFeEstimate`, −145/10000<E[b]<−135/10000 and
   775/10000<Var(b)<785/10000. Both √Var(b) and
   √(Var(b)+E[b]²) round to 279/1000 by the square-interval definition;
   v<Var(b)+E[b]².

There is no assertion that m is obtained by OLS or that b solves any
regression or minimizes squared loss. The FE moments are bounded and
rounded, not stated as exact rational equalities.

## T7

No hypotheses. The same positive-denominator assertion as T6 item 1.
The same four exact moments v,u as T6 item 3. In addition √v rounds to
246/1000; v rounds to 60/1000; √u rounds to 12/1000.
The same FE interval, rounding and strict MSE comparison assertions as
T6 item 5. For every cluster k, Σᵢ:c(i)=k yᵢ=tₖ and
Σᵢ:c(i)=k(yᵢ−1/2)=pₖ. Finally

    E[H₁₆(t,t)]=0,
    Var(H₁₆(t,t))=E[Vp₁₆(t,t)]=353/1920,
    E[H₁₆(p,p)]=0,
    Var(H₁₆(p,p))=E[Vp₁₆(p,p)]=233/2560,

with these last two variances rounding to 184/1000 and 91/1000.
No statement about all other table columns, or about fitting optimality,
is included. RMSE is represented by √(variance+bias²) with true effect 0
for the numerical equal-potential-outcome population.

## T8

Four independent universal conjuncts.

1. Common cluster premise, then x,z: Cov(H₁(X),H₀(Z))=Cpop(X,Z).
2. Common cluster premise, then x,z:
   Cov(H₁(X),H₀(Z))−Bcov(X,Z)=Σᵢ(Xᵢ−Zᵢ)²/2.
3. Common cluster premise, then directed support, then x,z:
   E[C0(X,Z)]=Bcov(X,Z); this expectation is at most
   Cov(H₁(X),H₀(Z)); equality holds iff ∀i,Xᵢ=Zᵢ.
4. Common cluster premise, then x,z:
   Bcov(X,Z)≤Cov(H₁(X),H₀(Z)), without directed support.

## T9

No outer hypotheses. F4 is a probability law with positive marginals and
directed support. For all i≠j, π¹¹ᵢⱼ=π⁰⁰ᵢⱼ=1/6 and π¹⁰ᵢⱼ=1/3.
Use x=z=(1,2,4,7). For every state, App has values
(−68,−52,2,−62,−20,−52). E[App]=−42.
Cov(H₁(x),H₀(x))=Cpop(x,x)=E[C0(x,x)]=−28;
Var(H₁(x))=28; −42≠−28; and separately Bcov(x,x)=−28.
Exact marginals, C0's pointwise values, and Barm's value are not asserted.

## T10

Three independent universal conjuncts. In each, quantify finite U,C with
decidable equality, **nonempty U** (no explicit Nonempty C), and
E:ClusterLaw U C. Surjectivity ensures every cluster is nonempty.
There is no Sep assumption.

1. Then quantify y:U→ℝ, a:Bool, w:C→Bool. The unit-design HT total
   equals the cluster-design HT total of Totals(y), pointwise at w.
2. Then quantify x,z:U→ℝ and w. Their unit-design contrast with N=|U|
   equals the cluster-design contrast of the two cluster-total vectors,
   with the same N, at w.
3. Then quantify y,a,w as in item 1. Let
   J1=ΣₖΣᵢ:c(i)=k Sᵃ_unit,i yᵢ/πᵃ_unit,i,
   J2=ΣₖΣᵢ:c(i)=k Sᵃ_cluster,k yᵢ/πᵃ_cluster,k,
   J3=Σₖ Sᵃ_cluster,k(Σᵢ:c(i)=k yᵢ)/πᵃ_cluster,k.
   All four displayed identities hold: H_unit,a(y)=J1, J1=J2,
   J2=J3, J3=H_cluster,a(Totals(y)).

## T11

Three independent universal conjuncts, each starting with the common
cluster premise, including Sep.

1. Then quantify a:Bool and y:U→ℝ:
   Var(Hₐ(Totals(y)))=Va(Totals(y)).
2. Then quantify a and x,z:U→ℝ, and set y=X if a=1, y=Z if a=0.
   Barm_a(y)−Var(Hₐ(y))=Uₐₐ((yᵢ+yⱼ)²)/2;
   E[Vhat_a(X,Z)]=Barm_a(y); Var(Hₐ(y))≤E[Vhat_a(X,Z)].
   If πᵃᵃᵢⱼ>0 for every i≠j, then E[Vhat_a(X,Z)]=Var(Hₐ(y)).
3. Then quantify a,x,z, and assume πᵃᵃᵢⱼ>0 for all i≠j.
   E[fullSupportArmEstimate_a(X,Z)]=Var(Hₐ(X if a=1 else Z)).

## T12

Five independent universal conjuncts. Each begins with finite nonempty I
with decidable equality and E:UnitLaw I; thus a probability law with both
positive marginals. No separation, support, independence or sharp-null
assumption is present.

1. Then quantify x,z:I→ℝ:
   Var(H_|I|(x,z))=[Var(H₁(x))+Var(H₀(z))−2Cov(H₁(x),H₀(z))]/|I|².
2. Then quantify a:Bool,y:I→ℝ. Three identities hold:
   Var(Hₐ(y))=ΣᵢΣⱼCov(Sᵃᵢ,Sᵃⱼ)(yᵢ/πᵃᵢ)(yⱼ/πᵃⱼ);
   Var(Hₐ(y))=ΣᵢVar(Sᵃᵢ)(yᵢ/πᵃᵢ)²
             +O(Cov(Sᵃᵢ,Sᵃⱼ)(yᵢ/πᵃᵢ)(yⱼ/πᵃⱼ));
   Var(Hₐ(y))=Va(y).
3. Then quantify a,b:Bool and x,z:I→ℝ:
   Cov(Hₐ(x),H_b(z))=ΣᵢΣⱼ(πᵃᵇᵢⱼ−πᵃᵢπᵇⱼ)
                                      (xᵢ/πᵃᵢ)(zⱼ/πᵇⱼ).
4. Then quantify x,z:
   Var(H_|I|(x,z))=[V1(x)+V0(z)−2Cs(x,z)]/|I|².
5. Then quantify x,z: Cov(H₁(x),H₀(z))=Cs(x,z).

The absent directed pairs, including the diagonal, are retained explicitly
in Cs's negative product sum. None of these are infinite sums, integrals,
limits or limsups.
