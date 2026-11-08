# Blind mathematical reading

Saved at stage 1, before opening `claims.json` or `record.json`. This is a reading of the actual proposition bodies, not an endorsement of their correspondence with a paper. All theorem names below have prefix `SAP.P009b.`. The challenge consists of T18 through T34, inclusive. The conjunctions defining each statement are independent universal assertions; parameters in one conjunct do not bind another conjunct.

## Common objects and conventions

For a natural number n, an assignment is a function z : {0,...,n−1} → {false,true}. Write z_i as a real 0 or 1 where arithmetic requires it. A law on a finite type Ω is a function p : Ω → ℝ with p(ω) ≥ 0 for every ω and Σω p(ω)=1. In particular Ω cannot be empty if a law is supplied. E[X]=Σω p(ω)X(ω), P(A)=E[1_A], E[X|A]=E[1_A X]/P(A), Cov(X,Y)=E[(X−EX)(Y−EY)], Var(X)=Cov(X,X), and Cov(X,Y|A)=E[(X−E[X|A])(Y−E[Y|A])|A]. These are the definitions, including when P(A)=0: real division by zero is zero in Lean. No measure-theoretic conditional-expectation operator is used here.

An experiment of size n is any such law on the entire assignment cube, together with arbitrary real functions y_i(z), defined even off the law's support. Set y_i(b;z)=y_i(z with coordinate i replaced by b), τ_i(z)=y_i(1;z)−y_i(0;z), τ(z)=n⁻¹Σi τ_i(z), EATE=Eτ, and ADSE=n⁻¹Σi(E[y_i|Z_i=1]−E[y_i|Z_i=0]). No interference means: for every i,z,z′, z_i=z′_i implies y_i(z)=y_i(z′).

Let π_i(b)=P(Z_i=b). Define μhat_b(z)=n⁻¹Σi 1_{z_i=b}y_i(z)/π_i(b), Nhat_b(z)=Σi 1_{z_i=b}/π_i(b), HT=μhat_1−μhat_0. If both Nhat_1,Nhat_0 are nonzero, Hajek=n μhat_1/Nhat_1−n μhat_0/Nhat_0; otherwise Hajek is explicitly set to zero. Also μ_b=n⁻¹Σi E[y_i(b;Z)] and μbreve_b=n⁻¹Σi E[y_i(b;Z)|Z_i=b]. All `/n` here are divisions in ℝ after casting n.

Write I_ij=1 when either i=j, or there exist two full-cube assignments differing only possibly at i on which y_j differs; otherwise I_ij=0. Thus diagonal interference is imposed even for constant outcomes. Write d_ij=1 iff some ℓ has I_ℓi=I_ℓj=1, and zero otherwise. Let d_i=Σj d_ij, dAVG=n⁻¹Σi d_i, dMAX=sup_i d_i; outgoing count c_i=Σj I_ij; incoming count c_i^in=#{j:I_ji=1}; C2=sqrt(n⁻¹Σi c_i²). Incoming counts include the diagonal.

A pairing ρ is a permutation of the n units with ρ²=id and no fixed points. Put e_ij=1 iff d_ij=0 and there exists ℓ with I_ℓi I_ρ(ℓ)j=1, and zero otherwise; eAVG=n⁻¹Σij e_ij; rSUM=Σi I_ρ(i)i.

Bernoulli means each π_i(1) lies strictly between zero and one and p(z)=Πi π_i(1)^{z_i}(1−π_i(1))^{1−z_i}. Complete(E,m) means 0<m<n and p(z)=1/binom(n,m) for assignments with exactly m treated units and zero otherwise. Paired(E,ρ) means n is even and p(z)=2^{−n/2} when z_i differs from z_ρ(i) for every i, and zero otherwise. Pairing already implies even cardinality.

Regular(E,k,q,s) means, in this order: k>0, real q≥2, real s≥1; for every i, 1/k≤π_i(1)≤1−1/k; for every i, E|y_i(Z)|^q≤k^q; for every i and Boolean b, E|y_i(b;Z)|^s≤k^s. The latter expectation is unconditional over Z; b is imposed by updating the outcome's input. Real powers use Mathlib `Real.rpow`. For nonnegative bases these are the usual real powers, with 0^0=1 and 0^r=0 for r≠0. Natural powers elsewhere are ordinary repeated multiplication.

The masked input M_i(z) keeps coordinate j exactly when I_ji=1, and puts false elsewhere. M_i^other further sets coordinate i to false. For finite-law variables X,Y taking values in arbitrary types, α(X,Y)=sup_{S,T}|P(X∈S,Y∈T)−P(X∈S)P(Y∈T)|, over all subsets S,T of their respective codomains. Define mixPower(a,θ)=0 if a=0, and a^θ otherwise. Then αEXT(θ)=n⁻¹Σij (1−d_ij)mixPower(α(M_i,M_j),θ). This explicitly differs from ordinary 0^0 at a=θ=0.

BER(z)=n⁻²Σi[1_{z_i=1}y_i(z)²/π_i(1)²+1_{z_i=0}y_i(z)²/π_i(0)²]. MSQ=n⁻¹Σi(Eτ_i)². For Boolean a, ξ_ij(a)=E[y_i(Z with i=a,j=1)−y_i(Z with i=a,j=0)], where j is updated after i. ξbreve_ij=(1−π_i(1))ξ_ij(1)+π_i(1)ξ_ij(0); ybreve_i=(1−π_i(1))E[y_i|Z_i=1]+π_i(1)E[y_i|Z_i=0].

B1=(n dAVG)⁻¹Σ_{i≠j}[ξbreve_ij ξbreve_ji+2 ybreve_j(ξ_ij(1)−ξ_ij(0))]. B2=(n dAVG)⁻¹Σ_{i≠j}Σ_{a,b∈{0,1}}(1−2a)(1−2b)Cov(y_i,y_j|Z_i=a,Z_j=b). The spectral number λMAX is sup{Σij v_i d_ij v_j : v∈ℝ^n, Σi v_i²=1}. AVG=dAVG·BER, MAX=dMAX·BER, SR=λMAX·BER, pointwise.

A Study supplies N : ℕ→ℕ, a proof that N(t)>0 for every t, a proof N(t)→∞, and an experiment E_t of size N(t). `size` is N(t) cast to ℝ. A regular sequence has the same k,q,s satisfying Regular(E_t,k,q,s) for every t. LittleO(f,g) here is exactly lim_t f(t)/g(t)=0. InProbability(X) means for every real ε>0, P_t(ε<|X_t|)→0. No common underlying probability space is required. Every limit is along t∈ℕ to infinity.

For a finite set G of units, bal_G(z)=Σ_{j∈G}(2z_j−1). The multiplier m(x) equals 2 if x>0, 1 if x=0, and 0 if x<0. A full-interference outcome with baseline b is y_i(z)=m(bal_{all units except i}(z))z_i+b_i. A one-source outcome with natural parameter h and baselines c is y_i(z)=2z_0 z_i+c_i for 0<i<h, and y_i(z)=z_i+c_i otherwise. This uses zero-based indices. `fairLaw n` assigns every assignment mass 2^{−n}; `fairExperiment n y` combines it with y.

Treated incoming count T_i(z)=Σ_{j≠i:I_ji=1}z_j. HG(n,m,r,t)=binom(m,t)binom(n−m,r−t)/binom(n,r), with all arguments natural. Thus natural subtractions truncate at zero. Relevant displayed uses below restrict t≤r, and complete-design hypotheses ensure the other subtractions in those uses are ordinary nonnegative differences. `armVariable E b a i` is 1_{Z_i=b} y_i^a, not (Z_i y_i)^a for the control arm or at a=0.

For R natural and estimates x_r, empiricalBias=R⁻¹Σ_{r<R}(x_r−1); reportedBias=|empiricalBias|. Uniform baselines are the product law of independent X_i∼Uniform[0,3] and U_i∼Uniform[0,7], all 2n coordinates independent, realized as finite products of normalized restricted Lebesgue measures and their binary product. AdjacentRanks(x,ρ) means there exists a permutation order sorting x nondecreasingly and pairing adjacent sorted positions: whenever distinct i,j have floor(i/2)=floor(j/2), ρ(order(i))=order(j). Ties may be ordered arbitrarily.

For a finite law P, approximationError(P,α,f)=|P(f=1)−α/2|+|P(f=−1)−α/2|. D(x)=min(|x+1|,|x|,|x−1|). SharpLaw(α) on three points has masses α/2,1−α,α/2 with values −1,0,1, for 0<α<1. Its specified candidate CDF H_α(x) is 0 for x<−1, α/2 for −1≤x<0, 1−α/2 for 0≤x<1, and 1 for x≥1.

Mathlib endpoints checked: `Function.update` replaces exactly one coordinate (`Logic/Function/Basic.lean`); `Nat.choose` is the ordinary binomial recurrence and vanishes when the lower argument exceeds the upper (`Data/Nat/Choose/Basic.lean`); `Real.rpow` is the real part of complex power, with its nonnegative-base formula as above (`Analysis/SpecialFunctions/Pow/Real.lean`); `Real.sqrt` is the nonnegative square root and returns zero on negative inputs (`Analysis/Real/Sqrt.lean`). `sSup` is the conditional real supremum: using it as an ordinary supremum requires a nonempty bounded-above set. The degree range is finite and nonempty for n>0; the Rayleigh-value set is nonempty and bounded for n>0; the α-value set is nonempty (choose empty sets) and bounded in [0,1]. Thus the sSup uses in the challenge's operative positive-size settings are ordinary suprema. No limsup is used. `Filter.Tendsto`, `atTop`, and `nhds` denote the ordinary eventual-tail and neighborhood limits (`Order/Filter/Defs.lean`, `Order/Filter/AtTopBot/Defs.lean`, `Topology/Defs/Filter.lean`). Sampling integrals are Bochner integrals of real functions: `Integrable` requires almost-everywhere strong measurability and finite absolute integral (`MeasureTheory/Function/L1Space/Integrable.lean`); a nonintegrable Bochner integrand otherwise has integral zero (`MeasureTheory/Integral/Bochner/Basic.lean:204`). T23 explicitly excludes that convention for its twelve integrands.

## T18

For every natural n, experiment E of size n, natural m, complete-randomization hypothesis Complete(E,m), unit i, and hypothesis c:=c_i^in≤min(m,n−m), let r=c−1 (natural subtraction). The theorem gives all the following:

1. For every natural t≤r, P(T_i=t)=HG(n,m,r,t).
2. For every natural t and Boolean b with t≤r, P(T_i=t|Z_i=b)=HG(n−1,m−b,r,t).
3. If r=0, then for every b, P(T_i=0|Z_i=b)/P(T_i=0)=1.
4. For every t,b with t≤r and r>0, the likelihood ratio minus one is
   P(T_i=t|Z_i=b)/P(T_i=t)−1 = r/[π_i(b)(n−r)]·[π_i(b)−b t/r−(1−b)(r−t)/r].
5. For every such t,b, the last bracket is strictly between −1 and 1, the absolute likelihood-ratio deviation is at most r/[π_i(b)(n−r)], and
   r/[π_i(b)(n−r)] ≤ c/[π_i(b)(n−c)] ≤ c/[π_i(b)min(m,n−m)].
6. For every full Boolean vector w and Boolean b, if P(M_i^other=w)>0, then
   |P(M_i^other=w|Z_i=b)/P(M_i^other=w)−1|≤c/[π_i(b)min(m,n−m)].

As a separately quantified conjunct under the same n,E,m,i and hypotheses, r=0 implies P(T_i=0)=1. Diagonal interference ensures c≥1; complete randomization gives n≥2 and positive marginal and combinatorial denominators. The bound on c ensures every t≤r is feasible in the conditional and unconditional count laws. No outcome moment hypothesis is present.

## T19

This is a concrete assertion, with no input hypotheses. Take n=6, the fair product law, y_0=z_0+z_2+z_4, y_1=z_1+z_3+z_5, y_j=z_j for j=2,3,4,5, and pairing (0 1)(2 3)(4 5). Then d_01=0, e_01=1, the witness sum Σℓ(1−d_01)I_ℓ0 I_ρ(ℓ)1 is 3, and 1≠3. Further, the supplied partner map is involutive; for every j its incoming influence on 0 is equivalent to j∈{0,2,4}, and on 1 to j∈{1,3,5}; for all i,j with j≠0,1, I_ij=1 iff i=j; for each ℓ the witness summand is 1 exactly for ℓ∈{0,2,4}, otherwise zero.

## T20

For every natural n>0, every experiment E of size n, and every fixed-point-free involutive pairing ρ, for all i,j:
e_ij≤Σℓ(1−d_ij)I_ℓi I_ρ(ℓ)j≤Σℓ I_ℓi I_ρ(ℓ)j;
and eAVG≤C2². This makes no hypothesis on the design beyond being a finite probability law, and no moment or randomization-design hypothesis. It does not state any intervening summed equalities or inequalities.

## T21

No input hypotheses. For the fair size-six one-source experiment with h=4, c_0=−1/4, c_i=1 for i>0, assert: Bernoulli design; dAVG=3; MSQ=1; B1=1/6; B2=1/3; 1/3≠4·3/(6+4·3); E[BER]=229/144; Var(HT)=241/144; (6/dAVG)(E[BER]−Var(HT))=−1/6; and −1/6≠(6−3−12)/18. Additional conjuncts give 6dAVG=18, MSQ/dAVG−B1−B2=−1/6, 4·3/(6+4·3)=2/3, and (6−3−12)/18=−1/2. It does not enumerate conditional covariances or assert any convergence.

## T22

The first conjunct quantifies, in order, n>0, a natural b with 1≤b≤n, and arbitrary real baselines c_i. Use the fair one-source experiment with h=b; put L=n+b(b−1), with this and the subsequent differences in ℝ. Then:

* n dAVG=L; MSQ=1; B2=(b−1)(b−2)/L; B1=(2+4c_0)(b−1)/L.
* n²(E[BER]−Var(HT))=n−2(b−1)(1+2c_0)−(b−1)(b−2).
* If c_0=−1/4, both MSQ/dAVG−B1−B2 and (n/dAVG)(E[BER]−Var(HT)) equal C=(n−(b−1)²)/L.
* 0≤2(b−1)/L≤1/sqrt(n).

The second conjunct independently quantifies natural n,b with n>0 and 1≤b≤n, and states
C−[n−(b−1)−b(b−1)]/L=2(b−1)/L.

The third conjunct quantifies a Study S; common reals k,q,s with RegularSequence(S,k,q,s); q≥4; a natural sequence b_t with 1≤b_t≤N_t; arbitrary baseline arrays c_{t,i}; c_{t,0}=−1/4 for every t; the equality of each design to fairLaw(N_t); and the equality of each outcome array to the one-source schedule with h=b_t,c=c_t. It concludes that
(N_t/dAVG_t)(BER_t−Var_t(HT_t))−[N_t−(b_t−1)²]/[N_t+b_t(b_t−1)]→0 in probability.
Neither b_t→∞ nor dAVG_t=o(N_t) is assumed. No three separate limiting-regime statements occur.

## T23

Quantifiers and hypotheses in order: natural n>0; n even; a law P on the full assignment cube; Complete((P,fullOutcome(0)),n/2); a function x↦ρ_x assigning a pairing to every x∈ℝ^n; AdjacentRanks(x,ρ_x) for every x; a function x↦Q_x assigning a finite assignment law; Paired((Q_x,fullOutcome(0)),ρ_x) for every x; and SimulationIntegrable(P,Q).

For baseline pair (X,U), define E_CR=(P,fullOutcome(X+U)), E_PAIR=(Q_X,fullOutcome(X+U)). SimulationIntegrable says that for each of the two designs and each of HT,Hajek, the following three functions of (X,U) are integrable under the independent uniforms specified above: signed design bias E(estimator)−EATE; design variance; design mean squared error E[(estimator−EATE)²]. That is twelve integrability hypotheses, not a pointwise boundedness or joint-variance definition.

For each of HT and Hajek, conclude the following integrals over (X,U): signed bias equals −1 for each design; design variance equals 58/(3n) for CR and 49/(3n)+36/[n(n+1)(n+2)] for PAIR; design MSE equals the corresponding preceding variance expression plus 1. Finally 1/[58/(3n)]=3n/58. There is no asymptotic ratio-divergence statement, no universal fixed-baseline assertion, and no joint sampling/assignment variance.

## T24

For every natural n>0 that is even, experiment E, baseline vector b∈ℝ^n, equality y=fullOutcome(b), and design hypothesis Complete(E,n/2) or existence of a pairing ρ with Paired(E,ρ):

* EATE=1.
* For every assignment z of positive design mass: for every i, y_i(z)=b_i and τ_i(z)=2(1−z_i); τ(z)=1; HT(z)=Hajek(z); HT(z)=(2/n)Σi(2z_i−1)b_i.
* EHT=EHajek=0; each signed bias relative to EATE is −1; each design MSE is the corresponding variance plus 1.

An independently quantified conjunct with exactly the same inputs and hypotheses states both absolute biases equal 1. There is no claim about other interference schedules or Monte Carlo values.

## T25

First, for every natural R>0 and every supplied array of R real estimates, reportedBias≥0, reportedBias=|empiricalBias|, |−1|=1 and −1≠1. The definitions fix the target value to 1.

Second, for every positive even n, experiment E, real baseline b, y=fullOutcome(b), and design Complete(E,n/2) or Paired(E,ρ) for some pairing, both HT and Hajek have signed bias −1 and absolute bias 1.

Third, the single estimate 0 has empiricalBias −1, the single estimate 2 has empiricalBias +1, and these two single-observation arrays have equal reportedBias. No claim of finite-sample agreement between a simulation and a population value is included.

## T26

For every Study S and real p∈(0,1), suppose every E_t has no interference and, for every t and assignment z, its mass is p at the all-true vector, 1−p at the all-false vector, and zero elsewhere. Then for every t: for every distinct i,j, α(M_i,M_j)=p(1−p); for every real θ, αEXT_t(θ)=(N_t−1)[p(1−p)]^θ; and αEXT_t(1)=(N_t−1)p(1−p). Moreover αEXT_t(1)/N_t→p(1−p), and the ratio does not tend to zero (¬LittleO(αEXT(1),N)). The outcomes are otherwise arbitrary subject to no interference. There is no regularity, potential-moment, maximal-exponent, or p=1/3 clause.

## T27

Three independently quantified assertions:

1. For every n (possibly zero), experiment E, reals k,q,s satisfying Regular, Bernoulli hypothesis, finite set G of units, and full assignment a:
   (1/k)^|G|≤P(Z_i=a_i for all i∈G)≤(1−1/k)^|G|.
2. For every finite type Ω in the theorem's universe, law P on Ω, reals δ,α, hypotheses p(ω)≤δ for every ω and 0<α<1, there exists f:Ω→ℝ with values in {−1,0,1} such that |P(f=1)−α/2|≤δ and |P(f=−1)−α/2|≤δ. δ is not separately assumed positive; that follows from existence of a normalized finite law and the bound. No minimizing property of this existential f is claimed.
3. For every Study S; common k,q,s,α; RegularSequence; Bernoulli at every t; 0<α<1; natural sequence b_t≤N_t with b_t→∞; a supplied array of functions f_t on the b_t-coordinate Boolean cube; three-point-valuedness of each f_t; and the hypothesis that for every t and every three-point-valued competing function g on that same cube, f_t has approximationError no greater than g under the pushforward law of the first b_t coordinates: the error is at most 2(1−1/k)^{b_t} for each t, and, for each Boolean a, P(f_t=1)→α/2 when a=true and P(f_t=−1)→α/2 when a=false. The embedding selects indices 0,...,b_t−1, not arbitrary data-dependent subsets. This does not assert existence of a minimizing sequence or separately state convergence of the exponential bound to zero.

## T28

Four independently quantified assertions:

1. For every finite type Ω in the theorem's universe, law P, real variable F with values in {−1,0,1}, EF=P(F=1)−P(F=−1).
2. For every such Ω,P,F, every real x≠−1,0,1, if |EF|<D(x), then P(F−EF≤x)=P(F≤x).
3. For every real sequence μ_t→0 and every fixed real x≠−1,0,1, eventually |μ_t|<D(x).
4. For every sequence of finite types Ω_t, laws P_t, three-point variables F_t, hypothesis EF_t→0, and fixed real x≠−1,0,1: D(x)>0, and eventually simultaneously |EF_t|<D(x), P_t(F_t−EF_t≤x)=P_t(F_t≤x), and not D(x)<EF_t. The threshold x is fixed before the eventual-time conclusion; uniformity over x is not asserted.

## T29

For every n (possibly zero), experiment E, reals k>0,q≥2, uniform bound E|y_ℓ|^q≤k^q for every unit ℓ, natural a satisfying 2a≤q, units i,j, and Boolean b, let X_i=1_{Z_i=b} y_i^a and X_j similarly. The theorem asserts each link of the following numerical chain and also its direct first-to-last bound:

|Cov(X_i,X_j)| ≤ sqrt(Var(X_i)Var(X_j))
≤ sqrt(E|y_i|^{2a} E|y_j|^{2a})
≤ sqrt((E|y_i|^q)^{2a/q}(E|y_j|^q)^{2a/q})
≤ sqrt((k^q)^{2a/q}(k^q)^{2a/q})
= sqrt(k^{4a}) = k^{2a}.

There is no i≠j hypothesis, Bernoulli, overlap, or potential-moment assumption. a is a natural including 0. When n=0 no units i,j can be supplied, but positive examples are within the quantifiers.

## T30

For every n>0, experiment E, hypothesis that both treatment marginals are strictly positive for every unit, and every full assignment z (not just supported ones): MAX(z)=dMAX·BER(z); SR(z)=λMAX·BER(z); AVG(z)=dMAX·BER(z) iff dAVG=dMAX or BER(z)=0; and AVG(z)=λMAX·BER(z) iff dAVG=λMAX or BER(z)=0. The first two are definitions; the other two are product-equality characterizations. No equality dAVG=dMAX or dAVG=λMAX is assumed or concluded universally.

## T31

First, for every real α∈(0,1) and every real threshold x, the CDF of SharpLaw(α) with SharpValue=−1,0,1 equals H_α(x), with the endpoint intervals specified above.

Second, for every sequence of finite types Ω_t, laws P_t, variables F_t taking values only in {−1,0,1}, every α∈(0,1), and hypotheses P_t(F_t=−1)→α/2 and P_t(F_t=1)→α/2: for every fixed real x, P_t(F_t≤x)→H_α(x). The conclusion includes x=−1,0,1, and so is stronger than CDF convergence solely at continuity points under this exact three-point-support hypothesis.

## T32

Four independently quantified assertions:

1. For every natural n, finite G⊆Fin(n), unit i, full assignment z, and Boolean b,
   bal_G(z with i=b)−bal_G(z)=2(b−z_i) if i∈G and 0 otherwise.
2. For every such n,G,i with i∈G, and assignment z with z_i=false, replacing i by true increases bal_G by 2.
3. For every integer B, m(B+2)≠m(B) iff B∈{−2,−1,0}; and m(B−2)≠m(B) iff B∈{0,1,2}. B is cast to ℝ inside m. This is an integer crossing assertion, not a real-threshold characterization for arbitrary B.
4. For every natural n, finite G, distinct units i,j, assignment z with z_i=false and z_j=true, replacing i by true and then j by false changes balance by 2·1_{i∈G}−2·1_{j∈G}. No pairing object or paired-design assumption is required for this algebraic identity.

## T33

For every n>0, natural b with 1≤b≤n, and arbitrary baselines c∈ℝ^n, use the fair one-source experiment with h=b. For every distinct i,j: ξ_ij(false)=0; ξ_ij(true)=2 exactly when 0<i<b and j=0, otherwise zero; and ξbreve_ij ξbreve_ji=0. Also ybreve_0=1/2+c_0 and B1=(2+4c_0)(b−1)/[n+b(b−1)]. There is no condition c_0=−1/4 here.

## T34

For every n>0, experiment E, pairing ρ, paired-randomization hypothesis, and reals k,q,s satisfying Regular(E,k,q,s): for every unit i and Boolean b,
|E[y_i(b;Z)|Z_i=b]−E[y_i(b;Z)]|
= (1/2)|E[y_i(b;Z)|Z_i=b]−E[y_i(b;Z)|Z_i=not b]|
≤ k.
Also k≥2, 2k≤2k², and |ADSE−EATE|≤2k² rSUM/n.

As an independently quantified conjunct with the same n,E,ρ,k,q,s hypotheses and then a unit i, the sum of the two per-arm absolute conditional-minus-unconditional potential means is at most 2k. No separate bound through the unconditional absolute first moment and no separately quantified weighted proof-chain identity is stated.
