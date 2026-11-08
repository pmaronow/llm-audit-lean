# Blind statement reading

Saved before opening either `claims.json` or `record.json`. The five Challenge docstrings, every source declaration in their elaborated dependency closures, and the types of every generated auxiliary proof in those closures have been read. `scratch/BlindPrint.lean` compiled successfully. This document records only what the supplied Lean statements say.

## Common expansions used in each section

These formulas are definitions of the notation below, not additional hypotheses. A population consists of a finite type Ω, real weights p(ω) ≥ 0 with Σω p(ω)=1, functions W,V:Ω→ℕ and X,Y,Z:Ω→Bool. Write Boolean values as 0 or 1 when used arithmetically, and embed natural counts into ℝ before subtraction. Thus

* E[f]=Σω p(ω)f(ω), P(D)=Σω p(ω)1_D(ω), E[f|D]=Σω p(ω)1_D(ω)f(ω)/P(D).
* Var(f)=E[f²]−E[f]² and Var(f|D)=E[f²|D]−E[f|D]².
* Dzy={ω:Z(ω)=z,Y(ω)=y}, mzy=E[V|Dzy], β=m11−m01, γ=P(Z=1), δ=E[Y|Z=1]−E[Y|Z=0].
* M (monotonicity): for every ω of strictly positive weight, Y(ω)=1 implies X(ω)=1.
* L (no liars/design effects): for every ω of strictly positive weight, V(ω)=W(ω)+X(ω)Z(ω) as a real equality.
* I (treatment independence): for every function f:ℕ→Bool→Bool→ℝ and each z∈Bool,
  E[1_{Z=z}f(W,X,Y)]=P(Z=z)E[f(W,X,Y)]. This is independence of Z from the entire actual triple (W,X,Y).
* N (nondegeneracy): for all four z,y, P(Dzy)>0 and Var(V|Dzy)>0, and Var(Z)>0 and Var(Y)>0. `standing` means M∧L∧I∧N.

For an ordered sample s:{0,…,n−1}→Ω, its weight is ∏i p(s(i)). The sample law is genuinely iid, including its normalization and nonnegativity. Let Nzy=Σi 1_{Dzy}(s(i)). For a specified real completion c, the cell mean is c if Nzy=0 and otherwise Σi 1_{Dzy}V(s(i))/Nzy. The cell sample variance is 0 if Nzy<2 and otherwise Σi 1_{Dzy}(V(s(i))−cellMean(0))²/(Nzy−1). Here the subtraction in Nzy−1 is in ℝ. The placebo estimate β̂(c1,c0) is cellMean11(c1)−cellMean01(c0); its variance estimate v̂(cV) is cV if either affirmative cell has fewer than two observations, and otherwise sampleVariance11/N11+sampleVariance01/N01.

Write A(b)=1 for true and 0 for false; write sign(b)=1 for true and −1 for false. The influence function used below is

ψ(ω)=Y(ω)/q · (Z(ω)−γ)/(γ(1−γ)) · (W(ω)−E[W|Y=1]), where q=P(Y=1).

Let G be Mathlib's probability measure `gaussianReal 0 1`, the real normal law with mean 0 and variance 1. Φ(t)=G((−∞,t]), converted from extended nonnegative reals to ℝ. The completed studentized statistic is T(b,b0,v)=(b−b0)/√v when v>0, and 0 otherwise; its two-sided normal p-value is p(b,b0,v)=2Φ(−|T(b,b0,v)|). For a five-vector p, F(p)=−2Σj log(pj). χ²10 is the image of ten independent G coordinates under x↦Σj xj².

For every occurrence of `WeakLimit P T Q`, the exact assertion is: for every real function f on the target space, if f is continuous and there exists a real C such that |f(x)|≤C for all x, then, as n→∞ through ℕ, Σs(∏i p(s(i)))f(Tn(s)) tends to the Bochner integral ∫f dQ. The target spaces here are ℝ or ℝ⁵ with their usual Borel spaces and topologies. For the probability measures in these statements this is the usual bounded-continuous-test definition of convergence in distribution.

All common population definitions are in `Defs/Part1.lean:11–75,82–91`; sample definitions in `Defs/Part2.lean:12–16,22–28,43–47,74–82`; analytic definitions in `Defs/Part4.lean:13–35,49–52`.

## SAP.P019a.T6

Source: `Challenge/Part1.lean:49–52`, expanded proposition `Defs/Part5.lean:87–100`. The docstring describes the corrected affirmative-group comparison of control V with treated V−1 under Assumptions 1–3 and positive affirmative cells.

Quantifiers, in order: for every universe-u type Ω, every finite enumeration of Ω, every population (p,W,X,Y,Z,V) as above, assume M, then L, then I, then P(D01)>0, then P(D11)>0. Conclude q≠0 and, for every real t, the following four equations jointly:

1. P(V=t|D01)=P(W=t|Y=1).
2. P(V−1=t|D11)=P(W=t|Y=1).
3. P(V=t|D01)=P(V−1=t|D11).
4. P(V=t|D01)=P(V=t+1|D11).

Each conditional probability is exactly the finite conditional expectation of the corresponding 0/1 indicator defined in the common expansion. No nondegeneracy or independence between observations is hypothesized; this is a population identity. No separate bound on W is present, although finiteness makes its range bounded. Equality at all points determines the full conditional laws because the counts have finite range.

Junk-value audit: the general conditional-mean definition divides by P(D), with 1/0=0 in ℝ. Both cell denominators are strictly positive by hypotheses, and the conclusion establishes q≠0 before using it. No null-event conditional law is relied on. Zero-mass atoms may violate M or L without changing any sum. Ω cannot be empty because nonnegative weights sum to 1. W,V are natural-valued but all differences V−1 and t+1 in this statement are in ℝ, with no truncated subtraction. There are no integrals, logs, square roots, powers with domain issues, extended-real conversions, partial functions, extrema, or limit conventions in this closure.

## SAP.P019a.T7

Source: `Challenge/Part1.lean:54–60`; `T7WholeStatement` at `Defs/WholeW1.lean:204–211`. There are no external hypotheses or free data: this is a conjunction of facts about two fixed populations. `T7Statement` at `Defs/Part5.lean:102–106` supplies facts about the first.

For the first population Ω={0,…,15}, p=1/16. Let B,C,X,Z be bits 0,1,2,3 of the atom index: bit k is the Boolean test ((index div 2^k) mod 2=1). Put W=B+C, Y=X·1_{C=Z}, V=B+C+XZ. Define potential responses Y(z)=X·1_{C=z}. The full statement is:

* Every four-bit assignment has probability (1/2)^4. For every atom W≤2 and Y=Y(Z).
* M,L,N hold, δ=0, β=2, β≠1, and I fails.
* P(X=0,Y=0)=1/2, P(X=1,Y=0)=1/4, P(X=1,Y=1)=1/4.
* All four cells have positive probability, with the exact table below (mean and variance refer to V):

  | (Z,Y) | probability | mean | variance |
  |---|---:|---:|---:|
  | (0,0) | 3/8 | 7/6 | 17/36 |
  | (1,0) | 3/8 | 7/6 | 17/36 |
  | (0,1) | 1/8 | 1/2 | 1/4 |
  | (1,1) | 1/8 | 5/2 | 1/4 |

* Var(Y)=3/16 and Var(Z)=1/4.
* Each of (B,C,X), (W,X), (Y(0),Y(1)), and actual Y is independent of Z. Here every independence expands to all point-mass factorizations P(f=a,g=b)=P(f=a)P(g=b), for every value a,b in the relevant codomains. The functions have finite range, so this is full independence.
* For H={W=0,X=1,Y=0}, P(H∩{Z=0})=0, P(H)=1/16, P(Z=0)=1/2, and P(H)P(Z=0)=1/32. This explicitly demonstrates the failure of independence between Z and the whole actual triple.

For the second population Ω={0,…,7}, p=1/8. Let B,C,Z be bits 0,1,2, and put X=1, W=B+C, Y=1_{C=Z}, V=B+C+Z. The statement additionally asserts:

* Every three-bit assignment has probability (1/2)^3; M,L,N hold; and every atom satisfies X=1 and W≤2.
* All cell probabilities are 1/4 and variances are 1/4. Means for (Z,Y)=(0,0),(1,0),(0,1),(1,1) are respectively 3/2,3/2,1/2,5/2.
* Var(Y)=Var(Z)=1/4, δ=0, β=2, I fails, and separately β≠1.

The docstring interprets these constructions as showing that treatment independence is a missing cause in a diagnosis of β≠1, with no false confession or list design effect. The formal assertion explicitly does NOT include I among their satisfied assumptions.

Junk-value audit: uniform laws require and supply 0<16 and 0<8, so their reciprocals are ordinary. Every cell and arm used in conditional expectations is positive. Natural division/modulo in bit extraction have positive divisors (2^k and 2), so they are genuine binary digits, with no division-by-zero behavior. Natural sums for W,V never subtract. Finite probability normalization excludes empty Ω; all bit-coordinate types have positive size. No integral, log, sqrt, real-power domain, extended-real conversion, extremum, sequence limit, or partial-function default occurs. Generated auxiliary declarations in the closure only prove positivity and numeral `AtLeastTwo` facts; they supply no substantive hypotheses.

## SAP.P019a.T8

Source: `Challenge/Part1.lean:62–65`; expanded proposition `Defs/Part5.lean:108–118`. The docstring describes the corrected baseline-composition decomposition, β=1 under the first three assumptions, and two failure diagnoses.

Quantifiers, in order: for every Ω:Type u, every finite enumeration of Ω, and every population as expanded above, assume P(D01)>0 and P(D11)>0. Conclude a conjunction of four separately conditional assertions:

1. If M and L, then β=1+E[W|D11]−E[W|D01].
2. If M, L, and I, then E[W|D11]=E[W|D01] and β=1.
3. If β≠1, then ¬M∨¬L∨¬I.
4. If M and L and β≠1, then ¬I.

Every conditional mean, cell, β, and assumption is the finite-sum formula given above. In particular L bundles no liars and no design effects; the disjunction does not treat them as separately defined predicates. N is not hypothesized, and the three structural assumptions occur inside the conclusion's implications, not as common hypotheses. Quantification is over real population contrasts, not noisy estimates or significance tests.

Junk-value audit: the only division in this closure is event conditioning. Both affirmative cell denominators are positive and their union implies q>0. There is no arbitrary completion involved. All count subtractions and the constant 1 are real, with no natural subtraction. Zero-mass atoms are harmless and normalized laws exclude empty Ω. There are no integrals, logs, roots, problematic powers, extended-real conversions, extrema, limits, or partial functions.

## SAP.P019a.T9

Source: `Challenge/Part1.lean:67–76`; complete proposition `Defs/WholeW1.lean:297–317`. This is an unconditional conjunction about a fixed 128-atom population and its iid sample laws, fixed Gaussian measures, and universally quantified completions. It is not a theorem about all five-list populations.

Let Ω={0,…,127}, p=1/128, with bit 0 equal to X, bit 1 giving sign B, and bits j+2 giving assignment signs Rj for j=0,…,4. All seven Boolean coordinates have every joint assignment of mass (1/2)^7. Let Ak=∏i<k Ri and Sj=∏j<i<5 Ri. Empty products equal 1. For list j, set

Wj=2 if B·Aj=1 and 1 otherwise (equivalently 3/2+B·Aj/2), Xj=X, Yj=X·1_{Sj=1}, Zj=1_{Rj=1}, Vj=Wj+XZj.

The theorem asserts every following clause; each indexed clause is universal over its displayed indices, independently of the others:

1. For every j, `standing` (M,L,I,N) and βj=1. For every assignment vector a∈Bool⁵, P(∀j Zj=aj)=1/32.
2. For every j and atom, Wj∈{1,2}; if another atom agrees on X,B and all assignment bits except j, then its Wj,Xj,Yj agree. Thus each list's triple omits its own assignment bit, while using other assignments.
3. Cell probabilities for j<4 are 1/8 if Y=1 and 3/8 if Y=0, regardless of Z. For j=4 all are 1/4. Control cell means are 3/2. Treated affirmative means are 5/2. Treated negative means are 11/6 for j<4 and 3/2 for j=4. Variances are 17/36 only for j<4,Z=1,Y=0 and otherwise 1/4. Each cell is explicitly positive. qj=1/4 for j<4 and 1/2 for j=4; γj=1/2, Var(Zj)=1/4, Var(Yj)=3/16 or 1/4 respectively, and E[Wj|Yj=1]=3/2.
4. The influence function in the common expansion equals, pointwise,
   ψj=2XB(Aj+1+A5) for j<4, and ψ4=2XBA5.
   Each has mean 0. E[ψjψk] is 4 if j=k<4, 2 if j=k=4, and 2 if j≠k.
5. For every j and every atom, with q=qj, γ=γj, m=E[Wj|Yj=1], the treated-minus-control influence expression
   YjZj/(qγ)(Vj−m−1)−Yj(1−Zj)/(q(1−γ))(Vj−m)
   equals ψj.
6. For every j and ε>0, the iid probability of
   |√n(β̂j(0,0)−1)−(√n)⁻¹Σi ψj(s(i))|≥ε
   tends to zero as n→∞.
7. Let E0,…,E4 be independent standard normals. Define Nj=(Ej+E4)/√2 for j<4 and N4=E4. The vector of five completed studentized statistics T(β̂j(0,0),1,v̂j(0)) converges weakly to the law of (Nj). Each Nj has law G, is integrable with integrable square, and has mean 0 and variance 1. Cross-covariances, hence correlations, are 1/2 between distinct indices below 4 and 1/√2 for pairs involving 4. Every marginal completed p-value converges weakly to Lebesgue measure restricted to [0,1]. `HasLaw` here means almost-everywhere measurability and equality of the image measure to G.
8. The Fisher statistic of those completed p-values converges weakly to Q, the image of G⁵ under e↦F((2Φ(−|Nj(e)|))j). The identity function and its square are Q-integrable; VarQ(identity)>20 and Q≠χ²10.
9. Define g(x)=−2 log(2Φ(−|x|)), h(t)=∫g((a+t)/√2)G(da). Both g,h are in L²(G), the product hg is integrable, the integrand defining h is G-integrable for G-almost every t AND separately for every real t. Q is also the image law of Σj g(Nj). Its variance is exactly
   20+12[∫h²dG−(∫hdG)²]+8[∫hg dG−(∫hdG)(∫gdG)].
   The identity and square are χ²10-integrable and Varχ²10(identity)=20.
10. Define Dn(s) to mean for every j that N11,j≥2, N01,j≥2, and v̂j(0)>0. P_iid,n(Dn)→1. Then for EVERY family Cn:(Fin n→Ω)→ℝ⁵, if for every n,s∈Dn and j, Cn(s)j equals the completed studentized statistic above, Cn converges weakly to the law of N and F((2Φ(−|Cn,j|))j) converges weakly to Q. Completion values can depend on n and the sample with no boundedness assumption.

The variance and covariance definitions for continuous laws in clauses 7–9 are exactly Bochner second moment minus squared first moment, or product moment minus product of first moments. All moment-existence clauses listed above are part of the proposition, not premises.

Junk-value audit:

* Uniform mass 1/128 has a positive denominator. All population conditional means and influence denominators are positive by the stated cell tables, qj and γj. Natural binary extraction has positive divisors.
* At n=0 the empty sample is the unique function out of the empty type, has mass 1 by the empty product, and cell counts vanish. Empty cell means are explicitly completed by 0; cell variances are 0 for count<2; v̂ is 0 on the unavailable domain. Even occupied cells can have sample variance 0, and the completed studentized statistic is explicitly 0 whenever v̂≤0. Its p-value is then 1. These are deliberate completions; Dn excludes their problematic domain and tends to probability 1.
* The remainder uses √n and its reciprocal at n=0, where both √0 and (√0)⁻¹ are 0. Its only assertion is asymptotic. The square root in actual studentization is only evaluated for strictly positive variance; √2 is strictly positive. No negative square root is used meaningfully.
* Real.log is totalized (log 0=0, with the real log extended to negative inputs), but every displayed argument is 2Φ(−|x|)>0 for finite real x; normal tails are strictly positive. Thus F in this theorem does not depend on a zero/negative-log convention, even for arbitrary real-valued C. Φ uses `toReal`, which sends ∞ to 0; G is a probability measure, so every CDF mass is finite and this convention is inactive.
* Bochner integrals default to 0 outside integrability. Weak convergence uses bounded continuous functions against probability measures, so its integrals are genuine. For Q, χ²10, g, h, and the products needed in the variance formula, the proposition explicitly asserts integrability or L² membership. In particular its universal integrability clause for h(t) rules out an undefined conditional average at exceptional real t. No variance comparison relies on a non-integrable default.
* The empty prefix and suffix sign products equal 1, as intended (notably Y4=X). Counts and natural exponents are ordinary; N−1 in sample variance and all response shifts are real subtractions. Finite Ω cannot be empty. The normal vectors and list index types have fixed positive sizes. There are no sInf/sSup, limsup/liminf, real variable powers, or partial-function defaults. The natural-sequence limits use the ordinary `atTop` filter and neighborhoods of explicitly specified finite limits.

## SAP.P019a.T10

Source: `Challenge/Part1.lean:78–84`; proposition `Defs/Part6.lean:95–108`. The docstring claims the corrected five-test limit from the full joint assignment premise, discloses omitted empirical numbers/nonrejection, and discloses its zero completions.

Quantifiers, in order: every Ω:Type u, every finite enumeration of Ω, every finite probability law P on Ω, and every five-tuple of studies Sj on Ω. Assume (i) for every j, Sj.law=P, (ii) for every j, Mj∧Lj∧Ij∧Nj, and (iii) the following full joint assignment factorization: for every real function f of three five-vectors (natural W, Boolean X, Boolean Y), and every Boolean assignment vector a,

E_P[1_{∀j Zj=aj} f((Wj)j,(Xj)j,(Yj)j)] = (∏j P(Zj=aj)) E_P[f((Wj)j,(Xj)j,(Yj)j)].

This says the assignment vector has independent coordinates AND is independent of the entire joint latent vector. It allows dependence among different lists' latent outcomes. The standalone Ij assumptions are redundant consequences of this factorization and common-law equality, but are explicitly included through `standing`.

The conclusion is the conjunction of:

1. For every j, βj=1.
2. For every distinct j,k and every atom ω, if the latent-vector fiber Hω={t:∀l,Wl(t)=Wl(ω),Xl(t)=Xl(ω),Yl(t)=Yl(ω)} has nonzero P-probability, then E_P[ψjψk|Hω]=0.
3. For every distinct j,k, E_P[ψjψk]=0.
4. The vector of T(β̂j(0,0),1,v̂j(0)) has weak limit G⁵, the product of five independent standard normal measures.
5. The vector of p(β̂j(0,0),1,v̂j(0)) has weak limit the product of five Lebesgue probability measures restricted to [0,1].
6. The Fisher transform of those five p-values has weak limit χ²10.

Each ψ, estimator, conditional expectation, product law, weak limit, p-value and χ² law is expanded in the common definitions above. No empirical statistic, empirical p-value or empirical nonrejection occurs. No sample-size lower bound is hypothesized; convergence concerns n→∞. There is no assertion of finite-sample independence of statistics or exact finite-sample Fisher calibration.

Junk-value audit: N gives all cell probabilities and conditional variances strictly positive; hence qj>0 and 0<γj<1 in every influence function. The conditional cross-moment has an explicit nonzero-probability fiber guard, so a null fiber cannot create a false zero by division. Population sums are finite and genuine. Empty-sample/cell means, unavailable variances, and nonpositive estimated variances are explicitly completed by zero as described above; p=1 at a completed statistic of zero. Positive cell masses and population variances ensure the exceptional events disappear asymptotically, although this disappearance is not separately a clause of T10. All normal p-value log arguments are strictly positive for every real completed statistic. `toReal` acts only on finite Gaussian probabilities. Weak-limit integrals are bounded continuous functions against probability laws. No standalone unguarded non-integrable moment is used. Natural-to-real embeddings are faithful, sample-variance subtraction is in ℝ, and there are no sInf/sSup, limsup/liminf, problematic real powers, or partial-function defaults. Finiteness and normalization exclude an empty Ω; the five- and ten-coordinate types are nonempty.

## Closure coverage and auxiliary constants

The definitions read are `FiniteLaw` (including its constructor and mass field), `mean`, `prob`, `ce`, `variance`, `cv`, `iid`; `Study` (constructor and all five observation fields plus law), `monotone`, `noLiarsDesign`, `treatmentIndependent`, `cell`, `nondegenerate`, `standing`, `gamma`, `listMean`, `beta`, `delta`, `cellCount`, `cellMean`, `cellVariance`, `betaHat`, `betaVarianceHat`, `betaPsi`; `bitVal`, `uniformFin`, `fairBit`, `diagnosisWitness`; `normalCDF`, `WeakLimit`, `studentized`, `normalPValue`, `jointAssignmentStable`, `latentVectorFibre`, `fisherStatistic`, `chiSquareTen`, `bitSign`, `prefixSign`, `suffixSign`, `sequentialStudy`, `sequentialPsi`, `correlatedNormals`, `sequentialFisherLimit`, `continuousVariance`; `T6Statement`, `T7Statement`, `T8Statement`, `T9Statement`, `T10Statement`; and all `whole*` definitions in the T7/T9 closures (`wholeFairBits`, `wholeIndependent`, `wholeCellTable`, `wholeDiagnosisEight`, `wholeDiagnosisPotential`, `wholeT7Sixteen`, `wholeT7Eight`, `T7WholeStatement`, `wholeFisherG`, `wholeFisherH`, `wholeGaussianFive`, `wholeCovariance`, `wholeVariance`, `wholeT9Finite`, `wholeT9Linearization`, `wholeT9Defined`, `wholeT9Margins`, `wholeT9Variance`, `wholeT9Completions`, `T9WholeStatement`).

Every line-0 auxiliary constant from `closure.json` was printed in `scratch/BlindPrint.lean`. Two `iid` proofs certify product weights nonnegative and normalized. Two `uniformFin` proofs certify uniform weights nonnegative and normalized. All remaining auxiliary types are positive-size proofs for uniform 8/16/128, numeral `AtLeastTwo` witnesses for natural arithmetic representation of real rational literals, or the `NeZero 5` instance for a coordinate of a five-vector. Those bearing `T1Statement`, `T4Statement`, `wholeT3Mass`, `wholeT3Population`, or `finiteSampleWitness` names are such shared elaborator-generated numeral/positivity proofs; their closure presence does not import any T1/T3/T4 assertion or assumption. No substantive assertion is smuggled into a definition through them.
