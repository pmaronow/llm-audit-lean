# Blind reading of the Lean statements

This file was written from `SAP/P019a/Defs.lean`, its six imported parts,
`SAP/P019a/Challenge.lean`, and `Challenge/Part1.lean`, before opening
`claims.json` or `record.json`. The theorem bodies are stubs; this is a reading
of their propositions, not an inference from their proofs or their docstrings.

## Common objects and conventions

`FiniteLaw Ω` requires a finite type Ω, real weights p(ω) ≥ 0, and
Σω p(ω) = 1. In particular there cannot be such a law on an empty type.
Write E f = Σω p(ω)f(ω), P(D) = E 1_D, and
E[f | D] = E[f 1_D]/P(D). This last definition is total: in Lean's real field
division by zero is zero. Conditional variances and covariances are exactly
E[f² | D] − E[f | D]² and E[fg | D] − E[f | D]E[g | D]; the unconditional
ones have the same formulas without conditioning. All these sums are finite.

A `Study Ω` consists of such a law and maps W,V : Ω → ℕ and
X,Y,Z : Ω → Bool. Below booleans are identified with their real indicators
0 and 1. There is no fixed upper bound on W or V in the structure.
Statements with arbitrary Ω quantify over every finite type in the indicated
universe, every `Fintype` instance, and every such study, in that order.

The four named assumptions expand as follows:

1. `monotone`: for each ω of strictly positive mass, Y(ω)=1 implies X(ω)=1.
2. `noLiarsDesign`: for each ω of strictly positive mass,
   V(ω)=W(ω)+X(ω)Z(ω), as an equality in ℝ.
3. `treatmentIndependent`: for every function f : ℕ×Bool×Bool → ℝ and then
   every z∈Bool,
   E[1_{Z=z} f(W,X,Y)] = P(Z=z) E[f(W,X,Y)]. This is independence of Z
   and the entire triple (W,X,Y), not merely pairwise independence.
4. `nondegenerate`: for every z,y∈Bool, both P(Z=z,Y=y)>0 and
   Var(V | Z=z,Y=y)>0; additionally Var(Z)>0 and Var(Y)>0.

`standing` is the conjunction of 1–4, in that order. Let
Czy={Z=z,Y=y}, mzy=E[V | Czy], σzy²=Var(V | Czy),
μ=P(X=1), τ=E[Y | X=1], γ=P(Z=1),
β=m11−m01, and δ=E[Y | Z=1]−E[Y | Z=0]. The definitions alone do not
require positive denominators; hypotheses in the individual statements do.

For n∈ℕ, the sample space is the space of ordered functions s:{0,…,n−1}→Ω.
Its law P_n gives s mass Πi p(s_i), so samples are independent with common
law P. For n=0 there is one empty sample of mass one. Define

* ybar=Σi Y(s_i)/n, set to zero for n=0 by real division;
* Nzy=Σi 1_{Czy}(s_i), Nz=Σi 1_{Z=z}(s_i), gammahat=N1/n (zero if n=0);
* Mzy(c)=c if Nzy=0, and otherwise Σi 1_{Czy}(s_i)V(s_i)/Nzy;
* O={N10>0 and N00>0}; K=N10+N00;
* muhat(c1,c0)=ybar+(1−ybar)(M10(c1)−M00(c0));
* A=1−ybar, B=M10(c1)−M00(c0)−1;
* h=σ10²/N10+σ00²/N00 (totalized by division by zero off occupied cells);
* betahat(c1,c0)=M11(c1)−M01(c0).

The sample variance vzy is zero if Nzy<2, and otherwise
Σi 1_{Czy}(s_i)(V(s_i)−Mzy(0))²/(Nzy−1), with subtraction in ℝ.
The variance estimate for muhat is cV unless N10,N00≥2, ybar<1, and
0<gammahat<1. When these conditions hold it is

    [(1−muhat)² ybar/(1−ybar)
       +(1−ybar)(v10/gammahat+v00/(1−gammahat))]/n.

The placebo variance estimate is cV unless N11,N01≥2; otherwise it is
v11/N11+v01/N01. `patternFibre s` consists of samples t with
(Y(t_i),Z(t_i))=(Y(s_i),Z(s_i)) at every index i.

For limit statements, Φ(t) is the probability of (−∞,t] under Mathlib's
`ProbabilityTheory.gaussianReal 0 1`, which is the normal probability measure
with mean zero and variance one (`Probability/Distributions/Gaussian/Real.lean`,
definition `gaussianReal`). The conversion `.toReal` converts its finite
extended nonnegative real mass to a real; it is not being applied to infinity.
q(u)=inf{x∈ℝ:u≤Φ(x)} uses the real conditionally complete order's infimum.
The use of q below has explicit nonempty and bounded-below hypotheses.

For an estimate e, null m, and variance estimate v, T(e,m,v)=(e−m)/√v
if v>0, and zero otherwise. Its normal p-value is p(e,m,v)=2Φ(−|T(e,m,v)|).
Mathlib's `Real.sqrt` is the nonnegative square root for nonnegative inputs
(zero on negative inputs). F(p)=−2Σ_{j=0}^4 log(p_j). Mathlib's real logarithm
agrees with the natural logarithm for positive arguments and is total, with
log 0=0 (`Analysis/SpecialFunctions/Log/Basic.lean`); the p-value arguments
here are normal probabilities at finite real numbers.

`WeakLimit P T Q` means: for every real-valued function f on the displayed
target space E, if f is continuous and there exists a real C such that
|f(x)|≤C for every x, then E_{P_n}[f(T_n)]→∫f dQ as n→∞.
The target spaces here are ℝ and ℝ^5 with their usual Borel structures and
usual/product topologies. The integrals are Mathlib Bochner integrals
(`MeasureTheory/Integral/Bochner/Basic.lean`); the target laws are finite
probability measures, so these bounded continuous functions are integrable.
`Measure.pi` denotes the finite product measure and `Measure.map` the
pushforward measure. All maps used here are Borel measurable. χ10² denotes
the pushforward of ten independent standard normals by x↦Σj x_j².
`Integrable f Q` asserts almost-everywhere strong measurability and finite
integral of |f| (`MeasureTheory/Function/L1Space/Integrable.lean`).
`continuousVariance Q` is ∫x² dQ−(∫x dQ)²; both integrability assertions
are separately present where it is used.

Limits `Tendsto ... atTop (nhds a)` are ordinary sequence limits along all
natural n tending to infinity. `IsBigO atTop R g` means there is a real
constant C for which |R_n|≤C|g_n| for all sufficiently large n, following
`Analysis/Asymptotics/Defs.lean`; it does not use a possibly undefined ratio.
Finite ranges, products, powers, choose coefficients, and comparisons are
the standard Mathlib ones. Natural subtraction appears in binomial exponents
only under bounds w≤4 or i≤k; the statistical differences are real differences.

## SAP.P019a.T1

There are no parameters or hypotheses. The fixed law on w∈{0,…,4} has masses
(81,216,216,96,16)/625. Define a(w)=min(w+1,4), c(w)=a(w)+1,
u(w)=w+1, and for any real-valued response r and real ρ define

    D_r(ρ)=E[(1−ρ)u(W)+ρr(W)]−E[W]

under this fixed law. The theorem is the conjunction of all of the following:

* For every w, its mass is choose(4,w)(2/5)^w(3/5)^(4−w).
* E[W]=8/5 and Var(W)=24/25.
* For every w, a(w) is the w-th entry of (1,2,3,4,4), c(w) of
  (2,3,4,5,5), and u(w) of (1,2,3,4,5).
* D_a(1/5)=3109/3125; D_c(1/5)=3734/3125;
  D_a(1/5)−1=−16/3125; D_c(1/5)−1=609/3125; and
  D_c(1/5)−D_a(1/5)=1/5.

These are assertions about a deterministic mixture of response functions;
there is no additional random affected indicator or treatment variable.

## SAP.P019a.T2

For every real ρ, assuming first 0≤ρ and then ρ≤1, the following conjunction
holds, with the same fixed law and response functions as T1:

* For every w∈{0,…,4}, c(w)=w+2 if w<4, and c(4)=5.
* For every w and then every boolean a, the selected response c(w) if a=1
  and u(w) if a=0 exceeds w by 1+1_{a=1,w<4}; the analogous selected
  printed response a(w) or u(w) exceeds w by 1−1_{a=1,w=4}.
* D_c(ρ)=1+ρ(1−P(W=4))=1+(609/625)ρ.
* D_a(ρ)=1−ρP(W=4)=1−(16/625)ρ.
* D_c(ρ)−D_a(ρ)=ρ, and if additionally ρ>0 then D_c(ρ)>1.
* D_c(1/5)=3734/3125 and D_a(1/5)=3109/3125.

The quantification over ρ covers even the response identities independent of ρ.
There is no power calculation or joint population model in this proposition.

## SAP.P019a.T3

There are no external hypotheses. Use sixteen equiprobable atoms, equivalently
independent fair bits X,C,W,Z, with Y=XC and V=W+XZ (`finiteSampleWitness`).
All four standing assumptions are asserted for this specific study.
For n=4 let P=P_4, A=1−ybar and B=M10(0)−M00(0)−1. Define
Lz(ω)=1_{Z=z,Y=0}V(ω), the one-observation subgroup mean completed by zero.
The remaining conjuncts assert:

* For every n∈ℕ and then z∈Bool,
  P_n(Nz0=0)=(5/8)^n>0.
* Cov(1−Y,L1)=5/64 and Cov(1−Y,L0)=3/64.
* P(Y=0)>0, E[1_{Z=1}|Y=0]=1/2,
  E[L1|Y=0]=5/12, and m10=5/6.
* The four numerical identities 1−(1−1/2)^k=0,1/2,3/4,15/16 for
  k=0,1,2,4 respectively. These identities have no sample conditioning.
* P(O)=1431/2048>0; Cov(A,B|O)=0;
  Cov(M10(0),M00(0)|O)=0.
* Var(muhat(0,0)|O)=141205/404496.
* E[A|O]² Var(B|O)+Var(A|O)E[B|O]²+Var(A|O)Var(B|O)
  equals 75809/202248.
* The preceding actual variance minus that product expression is
  −1157/44944.
* 4γ=2, P_4(N1=2)=3/8, and P_4(N1=0)=1/16.

## SAP.P019a.T4

For every finite Ω and every study S, assume `standing`. The conclusion has
four blocks, all for this same S:

1. For every n∈ℕ and then z∈Bool,
   P_n(Nz0=0)=(1−P(Cz0))^n and this probability is strictly positive.
2. For every n∈ℕ, assuming n≥2, and then for every real c1 and c0, use
   P=P_n, A,B,h as in the common notation, and b=m10−m00−1. Then:
   * P(O)>0.
   * For every natural k, assuming k≤n and P(K=k)≠0: for every natural i,
     assuming i≤k, P(N10=i|K=k)=choose(k,i)γ^i(1−γ)^(k−i);
     also P(N10>0|K=k)=1−(1−γ)^k and
     P(N00>0|K=k)=1−γ^k.
   * For every sample s, assuming O(s) and P(patternFibre s)≠0: for every
     boolean z, the conditional mean of Mz0(cz) on this pattern fibre is
     mz0 and its conditional variance is σz0²/Nz0(s), where ctrue=c1 and
     cfalse=c0; the conditional covariance of the two subgroup means is
     zero; E[B|patternFibre s]=b and Var(B|patternFibre s)=h(s).
   * For every real a, assuming P(O∩{A=a})≠0, and then every boolean z,
     E[Mz0(cz)|O∩{A=a}]=mz0.
   * For every boolean z, Cov(Mz0(cz),A|O)=0; also
     Cov(M10(c1),M00(c0)|O)=0.
   * Var(muhat(c1,c0)|O)=b² Var(A|O)+E[A²h|O].
   * Var(AB|O)=b² Var(A|O)+E[A²h|O].
   * E[A|O]²Var(B|O)+Var(A|O)E[B|O]²+Var(A|O)Var(B|O)
     equals b²Var(A|O)+E[A²|O]E[h|O].
   * Var(AB|O) minus that product expression equals Cov(A²,h|O).
3. Put R_n=Cov_{P_{n+2}}(A²,h|O). Then R_n=O((n+2)^−2), and

       (n+2)²R_n → −2 μτ [σ10²/γ + σ00²/(1−γ)].

4. For every natural n, assuming n>0,
   E_{P_n}N1=nγ and, for every sample s, N1(s)=n gammahat(s).

There is no separate assertion K=n(1−ybar). The conditional-count assertions
are within the n≥2 block, including the cases k=0 and k=1 at such n.

## SAP.P019a.T5

There are no external hypotheses. Use eight equiprobable atoms, equivalently
independent fair bits X,W,Z, with Y=X and V=W+XZ (`distributionWitness`).
The theorem asserts `standing` and the three conditional probabilities

    P(V=0|Z=0,Y=1)=1/2,
    P(V+1=0|Z=1,Y=1)=0,
    P(V−1=0|Z=1,Y=1)=1/2.

The additions and subtractions are in ℝ. No assertion for every threshold,
or complete conditional-law table, occurs in this proposition.

## SAP.P019a.T6

For every finite Ω and study S, assume, in order, monotonicity, the list
design identity, independence of Z from (W,X,Y), P(C01)>0, and P(C11)>0.
Then P(Y=1)≠0 and, for every real t, the following four identities hold:

    P(V=t|C01)   = P(W=t|Y=1),
    P(V−1=t|C11) = P(W=t|Y=1),
    P(V=t|C01)   = P(V−1=t|C11),
    P(V=t|C01)   = P(V=t+1|C11).

The theorem speaks of point probabilities, not cumulative probabilities.
For these finite, integer-valued variables equality at all points determines
their entire conditional distributions. No variance positivity is assumed.

## SAP.P019a.T7

There are no external hypotheses. On sixteen equiprobable atoms take independent
fair bits B,C,X,Z, and put W=B+C, Y=X 1_{C=Z}, V=W+XZ
(`diagnosisWitness`). The theorem asserts monotonicity, the design identity,
nondegeneracy as expanded above, δ=0, β=2, β≠1, and failure of independence
of Z from the whole triple (W,X,Y). It does not assert `standing` and then
negate one of its components; independence is excluded from the assumptions
it claims this witness satisfies.

## SAP.P019a.T8

For every finite Ω and study S, first assume P(C01)>0 and then P(C11)>0.
The conclusion is a conjunction of four separately conditional assertions:

1. If monotonicity and the design identity hold, then
   β=1+E[W|C11]−E[W|C01].
2. If monotonicity, the design identity, and treatment independence hold,
   then E[W|C11]=E[W|C01] and β=1.
3. If β≠1, then at least one of monotonicity, the design identity, and
   treatment independence fails.
4. If monotonicity and the design identity hold and β≠1, then treatment
   independence fails.

No assertion δ≠0 follows, and nondegenerate variances are not assumed.

## SAP.P019a.T9

There are no external hypotheses. A single sample atom is an element of
{0,…,127} with uniform mass 1/128, equivalently seven independent fair bits.
Let X be bit 0, let R be the ±1 sign of bit 1, and let Zj be bit j+2,
j=0,…,4. For each j define Pj=Π_{i<j}sign(Zi), and
Qj=Π_{j<i<5}sign(Zi), with empty products one. The j-th study has

    Wj = 2 if R Pj=1, and 1 otherwise,
    Xj = X,   Yj = X 1_{Qj=1},   Vj = Wj+XZj.

All five studies use the same uniform law. Define

    ψj = 2 X R (P_{j+1}+P5) for j<4,
    ψ4 = 2 X R P5.

For an arbitrary study the separately defined influence function is

    betaPsi = [Y/P(Y=1)] [(Z−γ)/(γ(1−γ))]
                [W−E(W|Y=1)].

The theorem asserts the following conjunction:

* For every j∈{0,…,4}, study j satisfies all standing assumptions and βj=1.
* For every assignment vector a∈Bool^5, P(∀j Zj=aj)=1/32.
* For every j and every atom ω, betaPsi_j(ω)=ψj(ω).
* For every j, Eψj=0. For every j and then k,
  Eψjψk=4 if j=k<4, =2 if j=k=4, and =2 if j≠k.
* The vector of completed studentized placebo statistics, each centered at
  one and using betahat(0,0) and its zero-completed variance estimate,
  converges weakly under iid samples from this atom law to the vector
  Gj=(ej+e4)/√2 for j<4 and G4=e4, with independent standard normal ej.
* The Fisher statistic formed from the five normal p-values of those
  studentized statistics converges weakly to the law of
  −2Σj log(2Φ(−|Gj|)). This law is `sequentialFisherLimit`.
* Both x and x² are integrable for that limiting law; its variance
  ∫x²−(∫x)² exceeds twenty; and this limiting measure is unequal to χ10².

## SAP.P019a.T10

For every finite Ω, every law P, and every family of five studies S_j on Ω,
assume in order: every S_j has law P; every S_j satisfies `standing`; and
`jointAssignmentStable P S`. The last premise expands to: for every function
f of the three complete five-dimensional latent vectors (Wj), (Xj), (Yj),
and then every assignment vector a∈Bool^5,

    E[1_{∀j Zj=aj} f((Wj),(Xj),(Yj))]
      = (Πj P(Zj=aj)) E[f((Wj),(Xj),(Yj))].

Thus the assignment vector has the product of its marginal laws and is
independent of the entire combined latent vector. These are hypotheses,
not conclusions obtained from the five individual independence assumptions.
For an atom ω, its `latentVectorFibre` is the event that all Wj,Xj,Yj
equal their values at ω. The conclusion is:

* For every j, βj=1.
* For every j,k with j≠k, and then every atom ω with positive (equivalently
  nonzero) probability of its latent fibre,
  E[betaPsi_j betaPsi_k | that fibre]=0.
* For every j,k with j≠k, E[betaPsi_j betaPsi_k]=0.
* The five completed studentized placebo statistics converge weakly to the
  product of five standard normal laws.
* Their five normal p-values converge weakly to the product of five copies
  of Lebesgue measure restricted to [0,1], i.e. independent Uniform[0,1] laws.
* Their Fisher statistic converges weakly to χ10².

All sample subgroup means and unavailable variance estimates in this statement
use zero completion. Nonpositive variance gives studentized statistic zero.

## SAP.P019a.T11

For every finite Ω and every study S, there are four conjuncts, with their
own hypotheses (there is no common `standing` premise over all four):

1. Assuming the design identity, then treatment independence, then positive
   probability of Z=0, then positive probability of Z=1, all three hold:

       E[V|Z=1]=E[W]+μ,
       E[V|Z=0]=E[W],
       E[V|Z=1]−E[V|Z=0]=μ.

2. Assuming monotonicity and then P(Y=1)>0, E[X|Y=1]=1.
3. Assuming `standing`, for every real α with first α>0 and then α<1,
   assuming the set {x:1−α/2≤Φ(x)} is nonempty and then bounded below,

       P_n(|muhat(0,0)−μ|
            ≤ q(1−α/2) sqrt(muVarianceHat(0,0,0))) → 1−α.

   The event uses the displayed finite-sample completed estimator and whole
   variance estimate at each n∈ℕ; the convergence is as n tends to infinity.
4. Assuming monotonicity, the design identity, treatment independence,
   P(C01)>0, and P(C11)>0, in that order, m11=m01+1.

This completes the blind reading of every theorem in the Challenge file.
