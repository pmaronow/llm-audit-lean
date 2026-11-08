# Blind reading

Written before opening either `claims.json` or `record.json`. Sources read:
`closure.json`, the five Challenge declarations and their docstrings, and every
named source declaration in their closures. All 128 distinct generated auxiliary
declarations were also printed and read using `scratch/BlindProofs.lean` (output
in `scratch/BlindProofs.out`). They are numeral side-condition proofs
(`Nat.AtLeastTwo`, `NeZero`) except for the ordinary `Option.casesOn` matcher for
the survival indicator. They add no mathematical assumptions. The declarations
`positiveHazard._proof_1` and `positiveStudyGram._proof_3/_proof_4` in other
closures are shared numeral proofs, not dependencies on those full definitions.

Conventions used below are explicit mathematical abbreviations, not additional
SAP predicates. All decimals denote exact real rational numbers. For a finite
real matrix X with n rows and k columns, put

- G = XᵀX, B(X,Y) = G⁻¹XᵀY, u(X,Y) = Y − XB(X,Y).
- M(X,u) has entry Σᵢ uᵢ² Xᵢⱼ Xᵢₗ.
- H(X,Y) = [n/(n−k)] G⁻¹M(X,u(X,Y))G⁻¹.

These are precisely the unfolded `olsCoefficients`, `olsResidual`, `robustMeat`
and `hc1Covariance`. Matrix inverse is Mathlib's nonsingular inverse. The HC1
subtraction is real subtraction after casting both natural cardinalities, as
confirmed by `#print`; it is not truncated natural subtraction.
Let Φ be the CDF of Mathlib's real Gaussian measure of mean 0 and variance 1,
and P(z)=2Φ(−|z|). Thus `normalTwoSided` is the actual Gaussian tail. Define
K(z)=3 if P(z)<.01, otherwise 2 if P(z)<.05, otherwise 1 if P(z)<.10, otherwise
0. A printed interval at v means the closed interval [v−.0005,v+.0005].

## SAP.P041.T6

`Challenge/Part1.lean:36–39` states `T6Statement` (`Defs/Part8.lean:12`).
The docstring says that outcomes depending on rank and own treatment have the
average direct effect as their expected contrast, while scrutiny separates
direct, planned and implemented effects.

For each natural m let Rₘ={0,…,2m−1}, let Zₘ be the finite set of all subsets
z of Rₘ of cardinality m, and define

    Dₘ(z,Y) = (Σᵣ∈z Yᵣ)/m − (Σᵣ∈Rₘ\z Yᵣ)/m,
    Eₘ(f) = (Σz∈Zₘ f(z)) / |Zₘ|,
    A(z,r) = 1 if there exists s<r with s∉z, and 0 otherwise.

These unfold `balancedSequences`, `citationContrast`, `balancedExpectation`
and `scrutinyOutcome` to finite sets, finite sums and ordinary real arithmetic.
The theorem is the conjunction of these six blocks, with independent
quantifiers in each block:

1. For every m∈ℕ, then proof m≥1, then every function
   g:Rₘ→{false,true}→ℝ,
   Eₘ(z↦Dₘ(z,r↦g(r,1[r∈z]))) = Σᵣ(g(r,true)−g(r,false))/(2m).
2. For every m∈ℕ with m≥1, and every fixed c:Rₘ→ℝ,
   Eₘ(z↦Dₘ(z,c))=0.
3. For every g:{0,1,2,3}→{false,true}→ℝ, the formula in block 1 holds
   at m=2 with denominator 4.
4. For every m≥1: for every two subsets z,z' of Rₘ, then every rank r,
   if membership agrees at every s≠r, A(z,r)−A(z',r)=0. These two subsets
   need not be balanced. Also Eₘ(Dₘ(z,0))=0,
   Eₘ(Dₘ(z,A(z,·)))=1/[m(m+1)], and this last expectation is positive.
5. At m=2 the implemented expectation is 1/6, the fixed-zero expectation is
   0, and for every z,z',r the same off-r agreement implies zero own contrast.
6. E₂(D₂(z,(0,0,1,1)))=0 and E₅₀(D₅₀(z,A(z,·)))=1/2550.

There are no other hypotheses and no probabilistic independence assumption in
this finite single-assignment statement. All functions are total, finite-domain
real functions. No distribution of repeatedly sampled assignments is defined.

Junk-value audit: real division is total and a zero divisor would give 0.
Every contrast in the assertion uses m≥1 or m=2/50. The set Zₘ is nonempty
(choose the first m ranks), even at m=0, so the average's cardinality divisor
is never zero. R₀ is empty but occurs in no asserted contrast. Casts of m,
2m and cardinalities are ordinary exact natural-to-real casts; no subtraction
of naturals occurs. There is no log, sqrt, real power, integral, extended-real
conversion, extremum, limit, or default value of a partial function.

## SAP.P041.T7

`Challenge/Part1.lean:41–50` states `T7WholeStatement`
(`Defs/WholeW1.lean:90`). The docstring claims the actual four-cell binary OLS
fit and HC1 variance, corrected SE rounding, erroneous p rounding to .62 under
both normal and Student(197) references, and corrected significance against
genuine 1% critical values. It disclaims an exact sampling-law assertion.

Unfold the fixed arrays as

    A = [[1,0,0],[1,1,0],[1,0,1],[1,1,1]],
    a = (12,25,23,42), q = (102,67,65), b=(21/100,8/25,7/25),
    G = [[200,100,100],[100,100,50],[100,50,100]],
    J = [[3/200,−1/100,−1/100],[−1/100,1/50,0],[−1/100,0,1/50]],
    f = (21/100,53/100,49/100,81/100),
    r = (1833/200,2509/200,2493/200,1353/200), V=2047/492500.

The initial `T7Statement` conjunction says, without hypotheses:

- Σc 50 A꜀ⱼA꜀ₗ=Gⱼₗ; Σc a꜀A꜀ⱼ=qⱼ; GJ=JG=I; Jq=b;
  b₁=.320=(1/2)((25−12)/50+(42−23)/50); and G⁻¹=J.
- A b=f; each r꜀ equals a꜀(1−f꜀)²+(50−a꜀)f꜀²;
  Σc r꜀=2047/50; for each of four cells (J₁·A꜀)²=1/10000;
  (200/197)Σc r꜀(J₁·A꜀)²=V.
- .320/.645=64/129<1; .0635²≤V<.0645² and
  .0635≤√V<.0645; .645²=16641/40000≠V;
  (8/25)²/V=50432/2047>24; 2.61²<24; and
  (8/25)/√V>4.89 and >2.61.
- The entire vector (J₁·A꜀)c is (−1/100,1/100,−1/100,1/100).

The remaining conjunction says:

1. For every n∈ℕ, then cell:{0,…,n−1}→{0,1,2,3}, then
   y:{0,…,n−1}→Bool, if n=200, each cell contains exactly 50 observations,
   and the numbers with y=true in the cells are a, define
   Xᵢⱼ=A(cell(i),j) and Yᵢ=1 if yᵢ=true, otherwise 0. Then
   XᵀX=G, XᵀY=q, det(XᵀX) is a unit (equivalently nonzero over ℝ),
   (XᵀX)⁻¹=J, B(X,Y)=b, and (XB(X,Y))ᵢ=f(cell(i)). Also the sums
   of squared residuals in the four cells equal r, the full sum is 2047/50,
   J₁·Xᵢ is the indicated signed 1/100 for that cell, and H(X,Y)₁₁=V.
2. .06446<√V<.06447.
3. .615<P(64/129)<.625; for every real x with |x|<1, .10<P(x);
   and there exists c>0 with P(c)=.01, unique among nonnegative d having
   P(d)=.01, and 2.5755<c<2.5765.
4. Put d(t)=Γ(99)/[√(197π)Γ(197/2)] (1+t²/197)^(−99), using
   Mathlib's real Gamma and real power, and Q(x)=1−2∫₀^|x| d(t)dt.
   Then .615<Q(64/129)<.625, .10<Q(1),
   .01<Q(2.6005), Q(2.6015)<.01; and for every real x with |x|<1,
   .10<Q(x).
5. There exist real cN then cT, such that cN>0, P(cN)=.01,
   cN is unique among nonnegative roots, 2.5755<cN<2.5765;
   cT>0, Q(cT)=.01, cT is unique among nonnegative roots,
   2.6005<cT<2.6015; both are <2.61. For the fixed t=(8/25)/√V,
   t²=50432/2047, |t|>4.89, cN<|t|, cT<|t|,
   P(t)<.01 and Q(t)<.01.

Junk-value audit: the matrix inverse would be zero on a singular matrix;
the fixed inverse identities and the derived nonzero determinant rule that
out here. The only actual HC1 calculation has n=200,k=3, divisor 197.
All literal denominators are positive. V>0, so √V is the genuine positive
root, rather than Mathlib's 0 value on negative inputs. In the Student
density 197π>0, Γ(197/2)>0 and 1+t²/197≥1; its real power has positive
base for every real t. The density is continuous and all integration
intervals [0,|x|] are bounded, so the Bochner integral never falls back to
0 for failure of integrability. The normal law has finite real endpoints.
Empty n is impossible under the input condition; all other indices have
fixed positive cardinalities. No truncated subtraction, log, toReal of
infinity, infimum/supremum, limsup/liminf or partial-function default is used.

## SAP.P041.T8

`Challenge/Part1.lean:52–61` states `T8WholeStatement`
(`Defs/WholeW1.lean:133`). The docstring describes four uniform rectangles,
center approximations, strongest tiers 3,2,2,2, genuine normal critical
values, weaker nested levels for the first three and failure of the fourth
printed 1% assertion.

For real h,s define W(h,s)=h log(h)/s with Mathlib's real logarithm.
For each row below, h and s are independently universally quantified over
the closed intervals of radius .0005 centered at h₀,s₀. The theorem
asserts 0<h<1, s>0, the closed |W| and P(W) bounds in that row,
and the additional strict bounds in the last two columns.

|h₀|s₀|closed |W| enclosure|closed P(W) enclosure|extra |W| bound|extra P(W) bound|
|---|---|---|---|---|---|
|.670|.095|[2.8064,2.8426]|[.004416378,.005073862]|>2.80|(.0044,.0051)|
|.480|.174|[2.0181,2.0314]|[.041792640,.044011941]|(2.01,2.04)|(.041,.045)|
|.274|.162|[2.1820,2.1974]|[.027554610,.029563591]|(2.18,2.20)|(.027,.030)|
|.316|.149|[2.4345,2.4520]|[.013945057,.015189259]|(2.43,2.46)|(.0139,.0152)|

For the same universally quantified pairs, row 1 has P(W)<.01 and K(W)=3;
rows 2–4 have .01<P(W)<.05 and K(W)=2. Another independent universal
clause says that for all real p₁,p₂,p₃,p₄, if p₁<.01 and
.01<pⱼ<.05 for j=2,3,4, then p₁<.05, p₂<.10, p₃<.10 and
not p₄<.01. No nonnegativity condition is imposed in this purely ordered
real implication.

At the four centers W<0 and |W−z|<.00001,
|P(W)−p|<.0000001, for (z,p) respectively
(−2.82442,.0047366), (−2.02474,.0428938),
(−2.18967,.0285475), (−2.44319,.0145578).

Finally there exist real c₁,c₅,c₁₀, in that order. Each is positive, has
P(c) equal respectively to .01,.05,.10, and is unique among nonnegative
roots at its level. Their absolute errors from 2.5758293,1.9599640,
1.6448536 respectively are <.0000001. For every real z,

    K(z)=3 iff c₁<|z|,
    K(z)=2 iff c₅<|z|≤c₁,
    K(z)=1 iff c₁₀<|z|≤c₅,
    K(z)=0 iff |z|≤c₁₀.

Additionally c₁<2.80, c₅<2.01, 2.04<c₁,
c₅<2.18, 2.20<c₁, c₅<2.43, and 2.46<c₁.

Junk-value audit: `Real.log 0=0`, and Mathlib extends the real log to
negative arguments using log of absolute value, while division by 0 is 0.
Every occurrence of W has h,s in the displayed positive intervals (the
center values also are positive), so neither convention affects this
statement. P is the genuine standard normal tail everywhere, including
negative z by absolute value; the tier function is a total finite case
split with explicit strict boundaries. The critical values are genuine
existential roots, not an sInf of a potentially empty set. No sqrt,
nonintegrable SAP integral, real power, extended-real conversion, empty
index, natural subtraction, limit, extremum or partial default occurs.

## SAP.P041.T9

`Challenge/Part1.lean:63–73` states `T9WholeStatement`
(`Defs/WholeW1.lean:273`). Its docstring describes complement identities,
unchanged HC1 when its divisor exists, three balanced designs, twelve
survival slopes, and the initialization/replacement coding rule.

First, for every n,k∈ℕ, then j₀∈{0,…,k−1}, then real n×k matrix X,
then real vector S of length n, if det(XᵀX)≠0 and Xᵢⱼ₀=1 for every i,

    B(X,1−S)=eⱼ₀−B(X,S), u(X,1−S)=−u(X,S),
    M(X,u(X,1−S))=M(X,u(X,S)).

Here eⱼ₀ has 1 in coordinate j₀ and 0 elsewhere (`Pi.single`). If k<n,
also H(X,1−S)=H(X,S) and for every coordinate j the square roots of the
two diagonal entries agree.

For any study map v:{0,…,n−1}→{0,…,r−1} and treatment map
t:{0,…,n−1}→Bool, balanced cells mean exactly 50 observations of each
pair (study,treatment). Write U_b=Σᵢ:tᵢ=b Yᵢ and V_w=Σᵢ:vᵢ=w Yᵢ.
The theorem independently universally quantifies n,v,t,Y and states:

- For r=3 and balanced cells, n=300. The rows X⁺ᵢ are
  (1,1[tᵢ=true],1[vᵢ=1],1[vᵢ=2]); their Gram matrix is
  [[300,150,100,100],[150,150,50,50],[100,50,100,0],[100,50,0,100]],
  its determinant is nonzero, X⁺ᵀY=(U_true+U_false,U_true,V₁,V₂),
  and B(X⁺,Y)₁=U_true/150−U_false/150.
- For r=2 and balanced cells, n=200. Rows Xᶜᵢ are
  (1,1[tᵢ=true],1[vᵢ=1]); their Gram matrix is
  [[200,100,100],[100,100,50],[100,50,100]], its determinant is
  nonzero, XᶜᵀY=(U_true+U_false,U_true,V₁), and
  B(Xᶜ,Y)₁=U_true/100−U_false/100.
- Without a study map, if exactly 75 observations have t=true and 76 have
  t=false, n=151. Rows Xᶠᵢ=(1,1[tᵢ=true]) have Gram matrix
  [[151,75],[75,75]], nonzero determinant, XᶠᵀY=(U_true+U_false,U_true),
  and B(Xᶠ,Y)₁=U_true/75−U_false/76.

The horizon index h∈Fin 4 labels columns, in the order 6,12,24,168 hours
according to the source comment (it is not itself a real time). Define the
following explicit real arrays; rows are positive, cited, former:

    A = [[105,98,90,68],[67,63,58,34],[72,72,72,68]],
    D = [[88,75,68,49],[35,26,19,11],[75,75,75,73]],
    B = [[17/150,23/150,11/75,19/150],
         [8/25,37/100,39/100,23/100],
         [−51/1900,−51/1900,−51/1900,−307/5700]],
    F = [[.113,.153,.147,.127],[.320,.370,.390,.230],
         [−.027,−.027,−.027,−.054]].

For each of the three designs above, independently for every n, study map
where applicable, treatment map, real Y, and column h, assume the indicated
cell/arm counts and U_true=A_mh, U_false=D_mh. The conclusion is
B(X,Y)₁=B_mh, B(X,1−Y)₁=−B_mh, B_mh≠0,
|B_mh−F_mh|≤.0005 and not |−B_mh−F_mh|≤.0005.
There is no assumed regression conclusion in these hypotheses.
Independently for every m∈Fin 3 and h∈Fin 4,
A_mh/N_Tm−D_mh/N_Bm=B_mh, and the same nonzero and two precision
assertions hold, where N_T=(150,100,75), N_B=(150,100,76).

For every n,v:Fin n→Fin 3,t:Fin n→Bool,Y:Fin n→ℝ, assume balanced
cells, U_true=105, U_false=88, V₁=91, V₂=65. Then

    X⁺ᵀY=(193,105,91,65), X⁺ᵀ(1−Y)=(107,45,9,35),
    B(X⁺,Y)=(47/150,17/150,27/50,7/25),
    B(X⁺,1−Y)=(103/150,−17/150,−27/50,−7/25).

Finally for every optional real removal time r and every real h, let
S(none,h)=1 and S(some t,h)=1 if h<t, otherwise 0; let R(r,h)=1−S(r,h).
The theorem says that the rule “0 if there is t with r=some t and t≤h,
otherwise 1” equals S(r,h), and the rule “1 under that condition,
otherwise 0” equals R(r,h). The boundary is removal at the horizon, not
after it. `none` explicitly means no removal, not an arbitrary chosen time.

Junk-value audit: all regression uses carry, or derive from cell counts,
a nonzero Gram determinant. For the generic theorem the HC1 part alone
has k<n, so its real divisor is positive; its other conclusions also cover
the square, n=k case without evaluating an asserted HC1 result. Under
these conditions H is positive semidefinite, so its diagonal square roots
are ordinary nonnegative SEs; equality does not exploit negative sqrt's
0 convention. Fixed arm denominators are 150,100,75,76. Generic j₀∈Fin k
forces k>0, and the nonzero determinant excludes n=0 in that case;
balanced designs force the stated nonempty sizes. Negative real removal
times are allowed, and have the stated before-horizon behavior. Option
pattern matching is exhaustive. No log, real power, integral, extended-real
conversion, extremum, limit, truncated subtraction or default choice occurs.

## SAP.P041.T10

`Challenge/Part1.lean:75–92` states `T10WholeStatement`
(`Defs/WholeW2.lean:53`). The docstring describes first-election year to
tenure, complete coefficient/covariance changes, reciprocals and their
SEs, defined Wald invariance, both Table B rectangles, and the exact
132/125 illustration.

Unfold the hazard functions as

    H_Y(h₀,b,a,g,Y,T,w)=h₀ exp(bY+aT+gTY+w),
    H_L(h₀,b,a,g,C,L,T,w)
      =h₀ exp(Cb) exp(−bL+(a+Cg)T−gTL+w),
    L(C,Y)=C−Y.

The theorem is a conjunction of the following independently quantified
blocks, in the order written:

1. For all real h₀,a,b,g,C,L,T,w,
   b(C−L)+aT+gT(C−L)+w=Cb−bL+(a+Cg)T−gTL+w, and
   H_L(h₀,b,a,g,C,L,T,w)=H_Y(h₀,b,a,g,C−L,T,w).
2. For all real h₀,a,b,g,C,L,w with h₀≠0,
   H_L(...,T=1,...)/H_L(...,T=0,...)=exp((a+Cg)−gL).
3. For all real a,g,C,L, exp(−g)=1/exp(g), and increasing L by 1
   multiplies exp((a+Cg)−gL) by 1/exp(g). In the same block, for
   every r>0, r<1 iff 1<1/r, and 1<r iff 1/r<1.
4. For all real h₀,b,C,L,w, exp(−b)=1/exp(b) and
   H_L(h₀,b,0,0,C,L+1,0,w)=H_L(h₀,b,0,0,C,L,0,w)/exp(b).
5. For every real r in each printed interval below, respectively,
   the following strict reciprocal bounds hold:
   .989 → 1.0106<1/r<1.0117 and 1<1/r;
   .981 → 1.0188<1/r<1.0199 and 1<1/r;
   1.056 → .9465<1/r<.9475, 1/r<1, and
   946.5≤1000/r<947.5;
   1.004 → .9955<1/r<.9966 and 1/r<1.
   The 1.056 clause applies to both identically printed rows.
6. For every n∈ℕ, real C, and β:Fin 3⊕Fin n→ℝ, define
   A(C)=[[-1,0,0],[0,1,C],[0,0,-1]], and
   Q_n(C)=blockdiag(A(C),I_n). Define β' on the first three
   coordinates as (−β₀,β₁+Cβ₂,−β₂) and on every remaining
   coordinate as β itself. Then β'=Q_n(C)β and applying this
   transformation a second time gives β back.
7. For every n,C and arbitrary real matrix V on these same coordinates,
   (Q_n(C)VQ_n(C)ᵀ)₂₂=V₂₂, with 2 in the three-coordinate block.
8. For every n, then type Ω, then a measurable-space structure on Ω,
   then probability measure μ, real C, and random coefficient vector X,
   assume each coordinate Xᵢ is in Mathlib MemLp 2 μ: it is almost
   everywhere strongly measurable and its L² seminorm is finite. Then
   every transformed coordinate is also in L², and

       Cov(β'(X))=Q_n(C) Cov(X) Q_n(C)ᵀ,
       Cov(X)ᵢⱼ=∫(Xᵢ−∫Xᵢ dμ)(Xⱼ−∫Xⱼ dμ)dμ.

   These are actual centered-product Bochner integrals, not an arbitrary
   supplied matrix. C is fixed over Ω.
9. For all real g,V,s, if V≥0 and s=exp(g)√V, then
   exp(−g)√V=s/(exp(g))². For all real g,V with V>0,
   (−g)²/V=g²/V, |−g/√V|=|g/√V|,
   P(−g/√V)=P(g/√V), and for every real α the two strict
   P<α decisions are equivalent.
10. For every r,s∈ℝ with r in the 1.056 printed interval and s in
    either the .020 or .019 printed interval, P(W(r,s))<.01,
    P(W(1/r,s/r²))=P(W(r,s)), and both corresponding K values are 3.
    Here W(r,s)=r log(r)/s as above.
11. Let F(T,Y)=exp(log(132/125)T(Y−2009)). Then L(2014,2009)=5,
    L(2014,2008)=6; F(0,2009)=F(0,2008)=F(1,2009)=1;
    F(1,2008)=125/132; 1<132/125, 125/132<1,
    (132/125)(125/132)=1, 132/125=1.056;
    L(2014,1993)=21 and L(2014,2013)=1.

Junk-value audit: exponential denominators are always strictly positive.
The actual hazard ratio has h₀≠0, ruling out its 0/0 value. The general
hazard equalities allow zero or negative baselines but assert genuine
algebraic equalities for them, not a positive-rate probabilistic claim.
All printed reciprocal intervals stay strictly above 0. In the SE
formula V≥0; V=0 legitimately gives SE 0 on both sides, with no zero
denominator. Wald comparisons assume V>0; both numerical Wald rectangles
have positive r and positive s and produce positive reciprocals and SEs.
The illustration logs the strictly positive constant 132/125. Thus the
totalized logarithm, real division and sqrt conventions cannot change
any intended test or hazard-ratio conclusion. L² on a probability space
ensures first moments and integrability of all centered products, so
covariance cannot use the nonintegrable-integral value 0. This also
implies sigma-finiteness. The n=0 nuisance block is empty but the core
three coordinates remain; it simply expresses a model with no other
coefficients. Real year subtraction is ordinary subtraction. No rpow,
toReal of infinity, infimum/supremum, limsup/liminf, natural truncation,
or partial-function default occurs.
