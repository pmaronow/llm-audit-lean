# Blind reading of the Challenge statements

Saved before opening `claims.json` or `record.json`. This reads the statements, not the `sorry` proofs. All fifteen stubs assert the corresponding proposition `T1Statement`, ..., `T15Statement` in `Defs/Part5.lean` and `Defs/Part6.lean`.

## Common objects and the Mathlib meanings

All scalar quantities below are real numbers unless a measure value is explicitly mentioned. Policies on a measurable space C are functions C → R. An **admissible** policy is measurable and satisfies 0 ≤ π(x) ≤ 1 for every x, including null-set points. Write Πall for this class. Write bit(t)=1 for the Boolean true and 0 for false. For a sample of size n, N=Σ_i bit(T_i), and

- ATO(T,Y)=Σ_i Y_i bit(T_i)/N if N>0, and 0 otherwise;
- ATT(h,X,T,Y)=ATO(T,Y-h(X));
- TT(h,X,T,Y)=Σ_i (Y_i-h(X_i))bit(T_i);
- weighted TT additionally multiplies summand i by g(X_i).

An experiment E consists of a natural number n with a proof n>0; a measure P on C; functions μ0, μ1:C→R; a probability-law candidate Lπ on a fixed measurable space Ω for **every** function π:C→R; fixed functions X_i:Ω→C, Y0_i,Y1_i:Ω→R; policy-dependent Boolean Tπ_i; and hπ(ω,x), the fitted baseline. No regularity or probability properties follow merely from being an experiment. Put τ=μ1−μ0, Yπ_i=Tπ_i?Y1_i:Y0_i, and

- V(π)=∫(Yπ_0−Y0_0)dLπ (the first unit, rather than a sample sum);
- W(π)=∫π(x)τ(x)dP, q(π)=∫π dP, A(m,π)=∫mπ dP;
- h_n(q)=Σ_{j=0}^{n−1}(1−q)^j and F(m,π)=h_n(q(π))A(m,π);
- RATO, RATT, RTT, RgTT are Lπ-integrals of the respective sample rewards.

**Best(Π,f,b)** means b∈Π and f(a)≤f(b) for every a∈Π: an attained global maximum. **S(Π,f)** is the real supremum sSup{f(a):a∈Π}, and **regret(Π,V,b)** is S(Π,V)−V(b). The real sSup is only an ordinary supremum for a nonempty bounded-above set; the definition itself does not assert either property. The maximizing-policy hypotheses and/or integrable envelopes in these statements have to supply them. The positive rule is pos(m)(x)=1 if m(x)>0 and 0 otherwise. The printed average rule is top(m)(x)=1 exactly when m(x)>0 and ∀z,m(z)≤m(x), and 0 otherwise (all global maximizers, not an essential maximum).

For a unit, G_i=σ(X_i); Hπ=σ((X_i)_i,(Tπ_i)_i). These are Mathlib `MeasurableSpace.comap`, the inverse-image σ-algebras. Conditional expectation equalities below are Lπ-almost everywhere.

**OutcomeStanding(E)** means all of the following:

1. P is a probability measure, and μ0,μ1 are measurable and P-integrable.
2. For every admissible π, Lπ is a probability measure; for every i, X_i,Y0_i,Y1_i,Tπ_i are measurable and Y0_i,Y1_i are Lπ-integrable.
3. For every such π and i, X_i has distribution P. For every pair of admissible π,π′ and i, (X_i,Y0_i,Y1_i) has the same distribution under Lπ and Lπ′.
4. For each admissible π, the vectors (X_i,Y0_i,Y1_i,Tπ_i) are mutually independent across i and identically distributed across all i,j.
5. For every admissible π and i, Eπ[Y0_i|G_i]=μ0(X_i), Eπ[Y1_i|G_i]=μ1(X_i), and Eπ[bit(Tπ_i)|G_i]=π(X_i).
6. For every admissible π, i, and measurable B⊆R²,
   Eπ[bit(Tπ_i)1_B(Y0_i,Y1_i)|G_i]=π(X_i)Eπ[1_B(Y0_i,Y1_i)|G_i].

**Standing(E)** adds to precisely these conditions that hπ(ω,X_i(ω)) is integrable for every admissible π and every i, including units not treated and policies outside any subsequently chosen feasible class.

**PolicyDesign(E,π)** supplies items 1,2,3's covariate-distribution clause,5,6 for this single π. It does not assert policy invariance of the potential-outcome law, independence between units, identical unit distributions of the whole vector, integrability of the evaluated estimator, or admissibility of π itself. Those must be supplied separately when needed.

Additional estimator conditions, always with π ranging over the specified feasible set Π:

- PointwiseUnbiased: for every π∈Π and every fixed x, ω↦hπ(ω,x) is Lπ-integrable and has mean μ0(x).
- TreatedUnbiased relative to b:C→R: for every π∈Π and i, Eπ[bit(Tπ_i)(hπ(ω,X_i)−b(X_i))|G_i]=0. This predicate itself does not include integrability.
- VectorUnbiased: for every π∈Π and i, Eπ[hπ(ω,X_i)|Hπ]=μ0(X_i).
- IndependentEstimator: there exist a small type A, a measurable-space structure on A, a measurable random variable Z:Ω→A, and a function f mapping each π to A→C→R, such that, for every π∈Π, (a,x)↦fπ(a,x) is jointly measurable, hπ(ω,x)=fπ(Z(ω),x) for every ω,x, and Z is independent of the entire (X,Tπ) vector under Lπ. The witnesses A,Z,f are chosen before π; f may depend on π.

For C=X×U, **MarginalBaseline(E,b0)** says b0:X→R is measurable, c↦b0(c.1) is P-integrable, and for every admissible π and i,
Eπ[μ0(X_i)|σ((X_i).1)]=b0((X_i).1). **EstimatorUsesOnlyX** says for every π,ω,x,u,u′, hπ(ω,(x,u))=hπ(ω,(x,u′)). Put Dhet=∫|b0(c.1)−μ0(c)|dP and normalizedTT(π)=RTT(π)/n.

Mathlib conventions checked in the supplied Mathlib tree:

- `Integrable` means almost-everywhere strong measurability and finite integral of the absolute value (`Function/L1Space/Integrable.lean:59`, `HasFiniteIntegral.lean:82`). The real Bochner integral is **zero** for a nonintegrable function (`Integral/Bochner/Basic.lean:158`).
- `condExp` is zero if the conditioning σ-algebra is not below the ambient one, its trimmed measure is not σ-finite, or its argument is not integrable (`Function/ConditionalExpectation/Basic.lean:102`). Finite probability laws, measurable conditioning maps, and the stated integrability conditions are therefore material.
- `IdentDistrib` requires a.e. measurability of both functions and equality of their pushforward measures (`Probability/IdentDistrib.lean:71`). `IndepFun` and `iIndepFun` are independence of the generated inverse-image σ-algebras (`Probability/Independence/Basic.lean:136,144`), in the usual finite-intersection/product sense.
- μ≪ν means every ν-null set is μ-null (`Measure/AbsolutelyContinuous.lean:50`). `Measure.map` is pushforward for a.e. measurable maps; all maps whose pushforwards are used below are measurable. `withDensity` means integration of a nonnegative extended-real density against a measure. `rnDeriv` selects the density of the absolutely continuous part of the Lebesgue decomposition (`Measure/Decomposition/Lebesgue.lean:80`); for finite measures with μ≪ν, ν.withDensity(μ.rnDeriv ν)=μ. The derivative is finite ν-a.e. for finite μ (`Lebesgue.lean:384`), so `.toReal`, which sends infinity to zero, does not change the density a.e. here.
- Support means every open neighborhood has positive measure (`Measure/Support.lean:59`). Suprema over real sets require boundedness and nonemptiness for the usual interpretation. All subtraction in these definitions is real subtraction, not truncated natural subtraction. Finite index sets are actual finite sums.

## T1 — explicit two-unit average-reward example

Boolean covariates are fair and independent; false has treated potential outcome 9/10, true has 1, and untreated outcome is zero. A policy is a=(a0,a1)∈[0,1]²; units are treated independently conditional on their covariates with these probabilities. Let R(a) be the exact expectation of the two-unit ATO with observed outcomes and zero on an empty sample. Let RA(a) be the corresponding ATT expectation with estimator identically zero. Let V(a) be the single-unit expected observed-minus-untreated outcome.

There are no external hypotheses. The proposition asserts:

- top(effect)=(0,1) pointwise; R(0,1)=3/4, R(1,1)=19/20 and the first is strictly smaller.
- For every a∈[0,1]², R(a)≤R(17/18,1), with equality iff a=(17/18,1); R(17/18,1)=1369/1440.
- (1,1) is a welfare maximizer; V(1,1)−V(17/18,1)=1/40 and V(1,1)−V(0,1)=9/20.
- For every feasible a, RA(a)=R(a), R(a)=(9a0+10a1)(4−a0−a1)/40,
  1369/1440−R(a)=(9/40)(a0−17/18)²+(1−a1)(30−19a0−10a1)/40,
  and V(a)=(9a0+10a1)/20.
- The population treated conditional average for weights (1/2,1/2), means (9/10,1), and policy (0,1) is 1, whereas R(0,1)=3/4<1.
- V(1,1)=19/20, V(17/18,1)=37/40, V(0,1)=1/2.

Here the finite conditional average is A/q when q>0, and zero otherwise; its displayed denominator is 1/2.

## T2 — finite-sample average identities and finite-support threshold rules

Four independently universally quantified components are conjoined.

First, for every Ω,C with measurable spaces, **C countable with every singleton measurable**, every n, experiment E (hence n>0), and OutcomeStanding(E):

- For every admissible π, Pπ(N=0)=(1−q(π))^n, Pπ(N>0)=1−(1−q(π))^n, RATO(π)=F(μ1,π), and
  F(μ1,π)=[1−(1−q)^n]A(μ1,π)/q if q>0, otherwise 0.
- For every such π with q>0, the mean sample ATO conditional on N>0 is A(μ1,π)/q. Conditional event mean is literally the restricted integral divided by Pπ(N>0).
- For every policy π (not presupposed admissible), Best(Πall,RATO,π) iff Best(Πall,F(μ1,·),π).
- If also Standing(E) and VectorUnbiased(E,Πall), then, for every admissible π, RATT(π)=F(τ,π), the same piecewise nonempty-probability formula holds with τ, and for q>0 the mean sample ATT conditional on N>0 is A(τ,π)/q. For every policy π the analogous best-response equivalence holds.

Second, for every natural K>0, n>0, p,m:Fin K→R, with p_i>0, Σp_i=1, and m antitone (i≤j implies m_j≤m_i): define Q_j=Σ_{i<j}p_i and B_j=Σ_{i<j}p_i m_i. The threshold policy θ(j,q) treats i<j with probability 1, i=j with probability (q−Q_j)/p_j, and i>j with probability 0. Then:

- For every j:Fin K and real q with Q_j≤q≤Q_j+p_j, θ∈[0,1]^K, its treated mass Σp_iθ_i is q, its numerator Σp_i m_iθ_i is B_j+m_j(q−Q_j), and this numerator dominates that of every feasible π with treated mass exactly q.
- There exist j,q in such an interval for which θ(j,q) is a global maximizer on [0,1]^K of h_n(Σp_iπ_i)Σp_i m_iπ_i.
- If m_0>0, top(m) maximizes the zero-on-empty population ratio and attains m_0; otherwise the zero policy maximizes that ratio.

Third, for every K,p,m with p_i>0, every j:Fin K, and the hypothesis ∀i,m_i≤m_j (no normalization Σp=1 is required in this component): if m_j>0, top(m) maximizes the same finite population ratio and its value is m_j; otherwise zero is a maximizer. The supplied j itself ensures a nonempty type.

Fourth, for every Ω,C with the same measurable/countable/singleton conditions, every E of sample size 1, and OutcomeStanding(E), every admissible π satisfies RATO(π)=A(μ1,π); if also Standing(E) and VectorUnbiased(E,Πall), every admissible π satisfies RATT(π)=A(τ,π).

## T3 — ATT regret when withholding is feasible

For every measurable Ω,C, **C countable with measurable singletons**, n, E, Standing(E), feasible class Π all of whose members are admissible, zero policy belonging to Π, VectorUnbiased(E,Π), and policies b,s supplied with Best(Π,RATT,b) and Best(Π,V,s), conclude:

- Every π∈Π satisfies V(π)=A(τ,π), RATT(π)=h_n(q(π))V(π), and 1≤h_n(q(π)).
- RATT(0)=V(0)=0; RATT(b)≥0 and V(b)≥0.
- regret(Π,V,b)≤S(Π,V), and regret(Π,V,b)=V(s)−V(b).

Both maximizers are hypotheses preceding even the per-policy identities. There is no existence assertion for either maximizer in this theorem.

## T4 — two pointwise-unbiased but evaluation-biased estimators

Let a∈[0,1]² be a Boolean policy and let X be a fair Boolean. Estimator A is eA(s,x)=1 when x=s and −1 otherwise; estimator B is −eA. The estimator's seed is the very same observed X at evaluation. Let RA,RB be the exact one-unit TT expectations with treated outcomes respectively 1/2 and −1/2 and untreated baseline zero. Let VA(a)=(a0+a1)/4, VB(a)=−(a0+a1)/4.

Without external hypotheses:

- For every fixed x, the fair-seed means of both estimators are zero. For every x, eA(x,x)=1 and eB(x,x)=−1.
- Zero uniquely maximizes RA, (1,1) maximizes VA, its welfare regret at zero is 1/2, and RA(1,1)≠VA(1,1).
- (1,1) uniquely maximizes RB, zero maximizes VB, its welfare regret at (1,1) is 1/2, and S(VB)=0.
- For every feasible a, RA(a)=−(a0+a1)/4, VA(a)=(a0+a1)/4, RB(a)=(a0+a1)/4, VB(a)=−(a0+a1)/4.
- The fair two-point average |0−0| is zero and twice it is strictly below the first regret.
- For every feasible a the one-unit ATT expectations equal RA and RB respectively.
- The treated estimator means at all-treatment are 1 and −1; for every feasible a, RA(a)=VA(a) iff a=0; S(VA)=1/2 and VB(1,1)=−1/2.

The unique-maximizer statements quantify over every feasible policy and characterize equality to the named maximum. Treated estimator mean is a weighted mean divided by total treatment probability, here used only at a=(1,1), where the denominator is 1.

## T5 — shared-estimator rank reversal

Let Xj,Xk be independent fair Booleans and e(Xj,Xk,x)=1_{x=Xj}−1_{x=Xk}. Agent j's one-unit treated outcome is 1/4 and agent k's is 1/8; both use this same estimator. Their exact TT expectations are Sj(a),Sk(a).

Without external hypotheses, for every fixed x, E[e(Xj,Xk,x)]=0; for every Xj, averaging e(Xj,Xk,Xj) over Xk gives 1/2; for every Xk, averaging e(Xj,Xk,Xk) over Xj gives −1/2. Zero maximizes Sj, all-treatment maximizes Sk, their suprema are 0 and 5/8, and 0<5/8. For every feasible a, Sj(a)=−(a0+a1)/8 and Sk(a)=5(a0+a1)/16. The scalar inequalities 1/8≤1/4 and 0<1/8<1/4 are also asserted. This is a concrete pair of score comparisons, not a direct application of the separately defined ranking predicates.

## T6 — corrected unweighted total-treatment identity

The first component universally quantifies over measurable Ω,C, n, E, a feasible Π with every policy admissible, PolicyDesign(E,π) for every π∈Π, integrability of bit(Tπ_i)(hπ(X_i)−μ0(X_i)) for every π∈Π and i, and TreatedUnbiased(E,μ0,Π). It concludes:

- For every π∈Π, RTT(π)=nW(π) and V(π)=W(π).
- For every π:C→R, Best(Π,RTT,π) iff Best(Π,V,π).
- Every RTT maximizer has zero welfare regret.
- If Π=Πall, pos(τ) is an RTT maximizer.

The second, separately universal component quantifies over measurable Ω,C, n,E,Π; assumes PolicyDesign(E,π) and integrability of the same treated estimation error for every π∈Π,i; PointwiseUnbiased(E,Π); and IndependentEstimator(E,Π). It concludes TreatedUnbiased(E,μ0,Π). It does not separately assume the members of Π are admissible. PolicyDesign supplies the probability and design facts at those members directly.

## T7 — positive weighted total-treatment reward

For every measurable Ω,C, n,E, assume Standing of the experiment obtained by replacing h with the identically zero estimator. Choose measurable g:C→R with g(x)>0 for every x. Assume for every admissible π and i that the unweighted treated estimation error bit(Tπ_i)(hπ(X_i)−μ0(X_i)) is integrable; TreatedUnbiased(E,μ0,Πall); integrability of gτ under P; and integrability of each actual weighted summand (Yπ_i−hπ(X_i))bit(Tπ_i)g(X_i) under Lπ for every admissible π,i. No integrability of the actual h on untreated units is assumed here.

Then for every admissible π, RgTT(π)=n∫gτπ dP; pos(τ) maximizes RgTT over Πall; and, for every policy b supplied as such a maximizer, P-a.e. τ(x)>0 implies b(x)=1 and τ(x)<0 implies b(x)=0. Each such b satisfies V(b)=∫τ pos(τ)dP, is a welfare maximizer over Πall, and has zero welfare regret. No particular behavior is required at τ=0.

## T8 — private covariates and marginal-baseline bias

For every measurable Ω,X,U, n,E on C=X×U, Standing(E), b0:X→R satisfying MarginalBaseline(E,b0), EstimatorUsesOnlyX(E), and feasible Π consisting of admissible policies, assume TreatedUnbiased(E,c↦b0(c.1),Π).

For every π∈Π conclude normalizedTT(π)=∫π(c)(μ1(c)−b0(c.1))dP;
|normalizedTT(π)−V(π)|=|∫π(c)(μ0(c)−b0(c.1))dP|≤Dhet.
Furthermore, for every real γ with Dhet≤γ, and every b,s supplied with Best(Π,RTT,b) and Best(Π,V,s), regret(Π,V,b)=V(s)−V(b) and is at most 2γ. The per-policy claims precede, and do not require, these optimizer hypotheses. This theorem contains no sufficient independence implementation result.

## T9 — fitted-sample denominator and rational arithmetic

Four independent universal claims are conjoined.

1. For every n, fitted effect vector t:Fin n→R, n>0, and k=|{i:t_i>0}|>0, put S+=Σ_{t_i>0}t_i, v=S+/n, b=S+/k. Then b=v(n/k). If k<n then v<b.
2. For every real vH,bH,vS,bS with
   293907/2000000≤vH≤293909/2000000, bH=vH(255/62),
   50371/2000000≤vS≤50373/2000000, bS=vS(7264/1360),
   conclude 14989257/24800000≤bH≤14989359/24800000 and 59/400<bH;
   672601/5000000≤bS≤11434671/85000000 and 51/2000<bS.
3. For every real vH,rH,vS,rS with 0<rH≤2432/10000, vH≥14694/100000, 0<rS≤1873/10000, and vS≥2517/100000, conclude vH/rH>604/1000 and vS/rS>134/1000.
4. For every vH,bH,vS,bS under exactly the bounds and equalities in item 2, conclude
   1465/10000<vH<1475/10000, 245/10000<vS<255/10000,
   6035/10000<bH<6045/10000, and 1345/10000<bS<1355/10000.

No dataset or computation is encoded: the numeric inputs in items 2–4 are hypotheses.

## Outcome-law definitions for T10 and T11

An outcome law D is a measure on C×(R×R), with coordinates (x,(y0,y1)). **FiniteOutcomeLaw** means a probability law with y0 and y1 integrable; it does **not** mean finitely supported. Define A_D(π) by integrating the one-unit expected ATO, summing both treatment states with weights π(x),1−π(x); define V_D(π)=∫π(x)(y1−y0)dD. The treated projection is (x,y0,y1)↦(x,y1). **NondegenerateReward(Π,r)** means there exist D and π with FiniteOutcomeLaw(D), Best(Π,r_D,π), and ∫π(x)dD>0. **TreatedDataInvariant(Π,r)** means that for every two finite outcome laws with equal treated-projection pushforwards, r_D(π)=r_D′(π) for every π∈Π. This is invariance to the joint (X,Y1) law, not just a conditional law among realized treated units. The shifted law D_B is the pushforward of D under (x,y0,y1)↦(x,y1+B,y1).

## T10 — the singleton feasible class

For every real B>0, take C=Unit, D=δ_{((),(1+B,1))}, Π={1}. Then D is a finite outcome law, 1 is an A_D maximizer, ∫1dD=1, V_D(1)=−B, welfare regret at 1 is zero; indeed for every arbitrary real-valued objective f on Unit policies its regret at 1 in this singleton class is zero. Also zero is not feasible, and the scalar proposition 0≥B is false.

Independently, for every measurable C, every outcome law D, and every function π (without integrability or measurability hypotheses), A_D(π)=∫π(x)y1dD. For every two outcome laws D,D′ and every **measurable** π, equal treated-projection pushforwards imply equal A_D(π). NondegenerateReward({1},A) holds on Unit. Every arbitrary objective f has 1 as its maximizer on {1}. Finally, for every B>0 the supremum feasible welfare on the displayed point-mass law is −B.

The general algebraic identities use totalized Bochner integrals if necessary; the concrete counterexample is finite and integrable.

## T11 — unbounded regret after making zero feasible

For every measurable C, feasible Π of admissible policies with 0∈Π, every reward r, and hypotheses NondegenerateReward(Π,r) and TreatedDataInvariant(Π,r), conclude both:

- For every M>0 there exist a finite outcome law D and a policy π attaining the reward maximum such that regret(Π,V_D,π)>M. D,π may depend on M. The conclusion is existential in the maximizing policy.
- For every finite outcome law D and reward maximizer π with a=∫π(x)dD>0, and for every B>0, the shifted law D_B is finite, has the same treated projection as D, and keeps π a reward maximizer. Every π′∈Π has V_{D_B}(π′)=−B∫π′(x)dD≤0; its welfare supremum is zero, zero is a welfare maximizer, and regret at π equals Ba. For every M>0, (M+1)/a>0 and shifting by this amount gives regret greater than M.

A second independent component says that, for every B>0, the Unit point-mass law above, class Π={0,1}, and constant-zero reward satisfy finiteness, nondegeneracy and treated-data invariance; every π∈Π maximizes the reward, zero maximizes welfare and has zero regret, while 1 has regret B.

## T12 — equal support does not give the needed density

There are no input hypotheses. Let P be Lebesgue measure restricted to [0,1] and Q=(1/2)P+(1/2)δ_{1/2}. Assert P(R)=Q(R)=1; supp(P)=supp(Q)=[0,1]; P≪Q; P({1/2})=0 and Q({1/2})=1/2; Q is not absolutely continuous with respect to P; there exists no measurable f:R→[0,∞] with Q=P.withDensity(f); and for **every set** s⊆R, (1/2)P(s)≤Q(s). No treatment experiment is constructed in this proposition.

## T13 — reference-density weighted scores and rankings

For every natural K, measurable C in a universe u, family of measurable sample spaces Ω_k (k:Fin K) in a universe v, sample sizes n_k, and experiments E_k, choose a probability measure P0 on C. Assume OutcomeStanding(E_k) for every k (thus each n_k>0); μ0_j=μ0_k as functions for every j,k; P0≪P_k for each k; τ_k is P0-integrable for each k; each unweighted treated estimation error is integrable for every k, admissible π,i; TreatedUnbiased(E_k,μ0_k,Πall) for every k; and every actual reference-weighted reward summand is integrable for every k, admissible π,i.

The weight is g_k(x)=(1/n_k)(dP0/dP_k)(x), represented by `rnDeriv` and converted to real. It may be zero and need not be strictly positive everywhere. Then:

- For every k and admissible π, R_k(π)=n_k∫τ_kπg_k dP_k=∫τ_kπdP0, with both equalities separately asserted.
- For every k, pos(τ_k) attains the reward maximum over Πall and that supremum is ∫(τ_k)^+dP0, where t^+=t if t>0 and 0 otherwise (equal to max(t,0)).
- For every j,k, if τ_k(x)≤τ_j(x) for every x then ∫(τ_k)^+dP0≤∫(τ_j)^+dP0. Consequently the same pointwise comparison implies S(Πall,R_k)≤S(Πall,R_j); this is the exact `UniformRankPreservation` predicate.
- If ∀k,x,τ_k(x)≥0, then for every k the score supremum is ∫τ_kdP0, and for every j,k the inequality ∫τ_kdP0≤∫τ_jdP0 implies S(Πall,R_k)≤S(Πall,R_j); this is the exact `RelativeRankPreservation` predicate.

K need not be positive: the K=0 instance has no agents, but the statement is also universal for every positive K. No common topology or countability of C is assumed.

## T14 — positive-part integral comparison

For every measurable C, arbitrary measure P0 (not assumed a probability), and arbitrary τj,τk:C→R, assume τk(x)≤τj(x) for every x and integrability under P0 of **both** x↦max(τj(x),0) and x↦max(τk(x),0). Then ∫max(τk,0)dP0≤∫max(τj,0)dP0. Neither a score identity nor a ranking predicate is part of this proposition.

## T15 — two failures of untreated-outcome identification

Without external hypotheses:

- In a one-covariate, always-treated model with y1=1, the mass of every possible observed record (t,y) is identical for y0=0 and y0=2. Treatment probability 1 is positive, the untreated-state weight is zero, and 0≠2. The first model's observed mass is exactly 1 at (true,1) and zero elsewhere.
- In a fair Boolean covariate model with policy (1,1/2) and y1≡1, the mass of every record (x,t,y) is identical when y0≡0 and when y0(false)=2,y0(true)=0. Both treatment probabilities are positive, but the untreated probability at false is zero. Total untreated probability is 1/4. The first model's masses at (false,true,1), (true,true,1), and (true,false,0) are respectively 1/2,1/4,1/4.
- Independently, for every measurable X, every function μ0:X×Unit→R, and **every** measure P on X×Unit, the function c↦sup_{u:Unit}|μ0(c)−μ0(c.1,u)| is zero at every c and its P-integral is zero. For each existing c the supremum is over the nonempty singleton {0}, so no unbounded- or empty-supremum convention enters this assertion.

All displayed observed masses are finite sums of their explicit nonnegative fair-covariate and feasible-treatment probabilities. These assertions do not define or analyze an actual estimator computed from untreated observations.
