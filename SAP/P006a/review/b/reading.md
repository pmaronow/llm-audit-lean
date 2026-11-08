# Blind reading of the Challenge statements

This file was written from `SAP/P006a/Defs*.lean`, `Defs/Part1.lean` through `Part6.lean`, `Challenge.lean`, `Challenge/Part1.lean`, and the relevant Mathlib definitions, before opening either `claims.json` or `record.json`. Each Challenge theorem is the corresponding proposition `T<number>Statement`; there are no additional section hypotheses. The Challenge contains stubs, and no Solution or Comparator was consulted.

## Conventions and complete shared expansion

All scalars, expectations, objectives, and regrets below are real valued. Integrals are Mathlib Bochner integrals. `Integrable f μ` means almost everywhere strong measurability and finite integral of the norm. The integral is *defined to be zero* outside its integrable domain; consequently an unrestricted integral expression alone does not assert existence of an ordinary expectation. Conditional expectation `μ[f | m]` is also defined to be zero if `f` is not integrable, `m` is not a sub-sigma-algebra, or the trimmed measure is not sigma-finite. Under the stated design and moment assumptions these exceptions must be checked, not silently read as ordinary conditional expectations. These definitions were inspected in Mathlib's `MeasureTheory/Integral/Bochner/Basic.lean:158`, `Function/L1Space/Integrable.lean:59`, and `Function/ConditionalExpectation/Basic.lean:102`.

`Measurable` means inverse images of measurable sets are measurable. `comap X` is the sigma-algebra of inverse images under X. `IdentDistrib` requires both maps to be almost everywhere measurable and their pushforward measures to agree (`Probability/IdentDistrib.lean:71`). Independence of functions is independence of their generated sigma-algebras; finite intersections of measurable events have probabilities equal to products (`Probability/Independence/Basic.lean:136,144`). A probability measure has mass one on the whole space. Almost everywhere assertions use the indicated measure separately for each quantified policy or index.

An **admissible** policy on a measurable space C is a measurable function π:C→R with 0≤π(x)≤1 for every x. Write F for the set of all admissible policies. `IsBest(P,f,b)` means b∈P and, for every p∈P, f(p)≤f(b), so it asserts an attained global maximum. `bestValue(P,f)` is the real supremum of f(P), and `regret(P,V,b)` is this supremum minus V(b). This is a real conditionally complete supremum: it must not be confused with an extended-real supremum when P is empty or values are unbounded. Whenever a maximizing member is supplied, the image is nonempty and bounded above. `positiveRule(m)` is 1 where m>0 and 0 elsewhere. `printedAverageRule(m)` is 1 precisely at points x at which m(x)>0 and m(z)≤m(x) for **all** z∈C; it is zero elsewhere, including when no maximum is attained. Define h_n(q)=Σ_{r=0}^{n-1}(1-q)^r (`emptyFactor`); this is a polynomial even at q=0.

An **Experiment** consists of arbitrary measurable spaces Ω,C, a natural n together with a proof n>0, a measure P_X on C, functions μ0,μ1:C→R, a measure P_π on Ω for **every** function π:C→R, variables X_i,Y0_i,Y1_i on Ω for i∈{0,...,n-1}, Boolean T_{π,i}, and an estimator μhat_π(ω,x). At the structure level these data have no further regularity. Write τ=μ1-μ0, Y_{π,i}=Y1_i if T_{π,i} is true and Y0_i otherwise, and B_{π,i}=1 or 0 for that Boolean. The observed per-person welfare V(π) is E_{P_π}[Y_{π,0}-Y0_0]. Define mean welfare W(π)=∫π τ dP_X, q(π)=∫π dP_X, and A_m(π)=∫mπ dP_X.

For a sample, N=Σ_i B_i is its real treated count. ATO is 0 when N=0 and otherwise Σ_i Y_i B_i/N. ATT is the same expression with Y_i replaced by Y_i-μhat(X_i). Weighted TT is Σ_i(Y_i-μhat(X_i))B_i g(X_i), and TT is the case g=1. `expectedATO`, `expectedATT`, `expectedWeightedTT`, and `expectedTT` integrate these sample rewards under P_π. `averageObjective(m,π)` is h_n(q(π))A_m(π). `normalizedTT` is expectedTT/n. `eventMean(P,S,f)` is (∫_S f dP)/(P(S)).toReal; division here, as everywhere in R, is totalized with division by zero equal to zero. `ENNReal.toReal` agrees with finite nonnegative real values and sends infinity to zero.

**OutcomeStanding(E)** imposes the following for every admissible π (and the indicated further indices): P_X and P_π are probability measures; μ0,μ1 are measurable and integrable under P_X; each X_i,Y0_i,Y1_i,T_{π,i} is measurable; Y0_i,Y1_i are integrable under P_π; each X_i has law P_X; for every other admissible π' and every i the law of (X_i,Y0_i,Y1_i) agrees under P_π and P_π'; the vectors (X_i,Y0_i,Y1_i,T_{π,i}) are independent over i and identically distributed across all i,j under P_π; E[Yt_i|X_i]=μt(X_i) almost surely for t=0,1; E[B_{π,i}|X_i]=π(X_i) almost surely; and, for every measurable H⊆R²,

E[B_{π,i} 1_H(Y0_i,Y1_i)|X_i] = π(X_i) E[1_H(Y0_i,Y1_i)|X_i] almost surely.

**Standing(E)** is exactly these conditions with the added requirement that μhat_π(ω,X_i(ω)) is integrable under P_π for every admissible π and every i, even if π lies outside a subsequently chosen feasible class. It does not require estimator independence. **PolicyDesign(E,π)** has the same probability, mean, measurability, potential-outcome integrability, covariate-law, conditional-mean, Bernoulli-mean, and ignorability conditions for this single π; it has neither the independence/identical-distribution conditions across units nor the invariance condition across policies nor evaluated-estimator integrability. Both mean functions are still measurable and integrable under P_X.

For any policy set P:

- **PointwiseUnbiased(E,P)**: for every π∈P and every fixed x, μhat_π(·,x) is integrable under P_π and its integral is μ0(x).
- **TreatedUnbiased(E,b,P)**: for every π∈P and every i, E[B_{π,i}(μhat_π(ω,X_i)-b(X_i))|X_i]=0 almost surely. This predicate itself contains no integrability clause.
- **VectorUnbiased(E,P)**: for every π∈P and i, E[μhat_π(ω,X_i)|(X_0,...,X_{n-1},T_{π,0},...,T_{π,n-1})]=μ0(X_i) almost surely. This predicate itself also contains no integrability clause.
- **IndependentEstimator(E,P)**: there exist a type A in the base universe, a measurable-space structure on A, a measurable Z:Ω→A, and f(π,z,x) such that, for every π∈P, f(π,·,·) is jointly measurable on A×C, μhat_π(ω,x)=f(π,Z(ω),x) for every ω,x, and Z is independent of the full vector (X,T_π) under P_π.

For C=X×U, **MarginalBaseline(E,b0)** says b0:X→R is measurable, c↦b0(c.1) is P_X-integrable, and for every admissible π and every unit i, E[μ0(X_i)|the first coordinate of X_i]=b0(first coordinate of X_i) almost surely. **EstimatorUsesOnlyX(E)** says for every π,ω,x,u,u', μhat_π(ω,(x,u))=μhat_π(ω,(x,u')). Set Δ=∫|b0(x)-μ0(x,u)| dP_X(x,u), the marginal heterogeneity.

For the finite assertions, a binary policy is (a,b)∈R², with 0≤a,b≤1; it treats the Boolean covariate false with probability a and true with probability b. `coinMass(q,true)=q` and `coinMass(q,false)=1-q`. The finite reward sums are sums over these explicit Boolean draws with their product masses. No probability measure or Experiment is an additional premise for these closed finite sums. Binary welfare at covariate mass p=P(true) is (1-p)aτ(false)+pbτ(true). `binaryObservedWelfare` is the corresponding sum of Y(T)-Y0, and therefore the same polynomial for deterministic potential outcomes.

For K types, finitePolicies is the cube [0,1]^{Fin K}; finiteMass(p,π)=Σp_iπ_i and finiteA(p,m,π)=Σp_im_iπ_i. Let Q_j=Σ_{i<j}p_i and S_j=Σ_{i<j}p_im_i. The threshold rule t_{j,q} treats i<j with probability one, i=j with (q-Q_j)/p_j, and i>j with zero. The finite conditional average is finiteA/finiteMass if the mass is positive, otherwise zero.

## SAP.P006a.T1

This is a closed conjunction about n=2, independent fair Boolean covariates, deterministic Y0=0 and Y1(false)=9/10,Y1(true)=1, with independent policy randomization. Let R(a,b) be the explicit 16-term expectation of zero-on-empty ATO using the **observed** outcome, and V(a,b) its per-person welfare. The ATT sum uses the identically zero baseline.

For every Boolean x the printedAverageRule is the binary rule (0,1). R(0,1)=3/4<R(1,1)=19/20. For every feasible (a,b), R(a,b)≤R(17/18,1), with equality if and only if (a,b)=(17/18,1); this last value is 1369/1440. Policy (1,1) attains the maximum of V. Its welfare advantage over (17/18,1) is 1/40, and over (0,1) is 9/20.

For every feasible (a,b), the zero-baseline ATT sum equals R, R=(9a+10b)(4-a-b)/40,

1369/1440-R = (9/40)(a-17/18)² + (1-b)(30-19a-10b)/40,

and V=(9a+10b)/20. With finite masses (1/2,1/2), means (9/10,1), and rule (0,1), the conditional average is 1, whereas R=3/4<1. Finally V(1,1)=19/20, V(17/18,1)=37/40, V(0,1)=1/2. All quantifiers here are over the displayed finite types or over the explicitly feasible binary cube.

## SAP.P006a.T2

Four independently universally quantified groups are conjoined.

1. For every Ω,C with measurable spaces, **C countable and with measurable singletons**, every n and Experiment E with OutcomeStanding: for every admissible π the probabilities of N=0 and N>0 are (1-q)^n and 1-(1-q)^n; expectedATO=h_n(q)A_{μ1}; this objective equals (1-(1-q)^n)A_{μ1}/q if q>0 and zero otherwise. If q>0, the event mean of sample ATO conditional on N>0 equals A_{μ1}/q. For every policy π (without a separate admissibility premise), π is best for expectedATO on F if and only if it is best for this polynomial objective on F. **If additionally Standing(E) and VectorUnbiased(E,F) hold**, the corresponding expectedATT identities, nonempty-sample conditional mean, and best-response equivalences hold with μ1 replaced by τ. The estimator conditions are not required by the ATO branch.
2. For every natural K>0, natural n>0, strictly positive masses p_i summing to one, and real means m_i antitone in the ordinary index order: for every j∈Fin K and q∈R satisfying Q_j≤q≤Q_j+p_j, t_{j,q} is feasible, has mass q and numerator S_j+m_j(q-Q_j), and every feasible policy of that same mass has numerator at most this. There exist such j,q for which t_{j,q} is an attained maximizer of h_n(finiteMass)finiteA over the whole finite cube. If m_0>0 the printedAverageRule attains the maximum of the finite conditional-average objective and has value m_0; otherwise the identically zero policy attains that maximum.
3. Separately, for every K, every positive mass vector p (no normalization required here), every mean vector m, and every j∈Fin K with m_i≤m_j for every i: if m_j>0 the printedAverageRule maximizes the finite conditional average with value m_j; otherwise the zero rule maximizes it. Supplying j ensures this group is not using an empty Fin K.
4. For every one-unit Experiment on measurable Ω and **countable C with measurable singletons**, under OutcomeStanding, expectedATO=A_{μ1} for every admissible π. If Standing and VectorUnbiased(E,F) also hold, expectedATT=A_τ for every admissible π.

## SAP.P006a.T3

Universally, in this order: measurable Ω,C with **C countable and measurable singletons**; n; Experiment E; Standing(E); a feasible class P all of whose members are admissible and which contains the identically zero policy; VectorUnbiased(E,P); policies b,s; proofs that b maximizes expectedATT on P and s maximizes V on P. Then for every π∈P, V(π)=A_τ(π), expectedATT(π)=h_n(q(π))V(π), and h_n(q(π))≥1. The zero policy has both reward and welfare zero. The reward and welfare of b are nonnegative, regret(P,V,b)≤bestValue(P,V), and regret(P,V,b)=V(s)-V(b). Both attained maximizers are premises for the entire conjunction, including its per-policy identities.

## SAP.P006a.T4

A closed pair of fair-Boolean, one-unit finite experiments. For A take Y0=0, Y1=1/2 and estimator e_A(s,x)=1 if x=s and -1 otherwise. For B take Y0=0, Y1=-1/2 and e_B=-e_A. The random training argument s is the evaluated unit's own covariate x. For every fixed x, averaging either estimator over a fair s gives zero; on the diagonal e_A(x,x)=1 and e_B(x,x)=-1.

On the binary cube, reward A is uniquely maximized by (0,0), welfare A is maximized by (1,1), the regret of (0,0) is 1/2, and reward A at (1,1) differs from welfare there. Reward B is uniquely maximized by (1,1), welfare B by (0,0), regret at (1,1) is 1/2, and maximum welfare B is zero. For every feasible (a,b), reward A=-(a+b)/4, welfare A=(a+b)/4, reward B=(a+b)/4, welfare B=-(a+b)/4. The finite marginal heterogeneity with b0=μ0=0 is zero, and twice that is strictly less than regret A. For every feasible policy, the finite one-unit ATT rewards equal the respective TT rewards. The treated estimator means at (1,1), with denominator exactly one, are 1 and -1. Reward A equals welfare A exactly at (0,0); maximum welfare A is 1/2; welfare B(1,1)=-1/2.

## SAP.P006a.T5

A closed two-agent finite construction: x_j,x_k are independent fair Booleans; a common estimator is e(x_j,x_k,x)=1_{x=x_j}-1_{x=x_k}. Agent j's one-unit treated outcome is 1/4 and k's is 1/8, with zero baseline. Their TT scores integrate over both covariates and the respective policy randomization.

For every fixed x, the estimator's unconditional mean is zero. For every x_j its mean evaluated at x_j, averaging over x_k, is 1/2; for every x_k its mean evaluated at x_k, averaging over x_j, is -1/2. Policy (0,0) maximizes score j and (1,1) maximizes score k. Their maximum scores are respectively 0 and 5/8, with the former strictly smaller. For every feasible (a,b), score j=-(a+b)/8 and score k=5(a+b)/16. Also 0<1/8<1/4 and 1/8≤1/4. The statement asserts these scalar effect comparisons; its ranking implications are obtained from these constants, not from additional opaque ranking predicates.

## SAP.P006a.T6

Two independent universal implications are conjoined.

First, for every measurable Ω,C, positive-size Experiment E, and policy class P: assume every member is admissible, PolicyDesign(E,π) for every π∈P, integrability under P_π of B_i(μhat_π(X_i)-μ0(X_i)) for every π∈P,i, and TreatedUnbiased(E,μ0,P). Then for each π∈P, expectedTT(π)=nW(π) and V(π)=W(π); for every π, best response to TT on P is equivalent to welfare maximization on P; every such TT best response has zero regret. If P equals F, positiveRule(τ) is a TT best response. An empty P is permitted for the first implication, but its best-response premises then have no witnesses; the unrestricted-class conclusion has the explicit additional equality P=F.

Second, for every measurable Ω,C,E,P, assume PolicyDesign(E,π) and the same treated-residual integrability for each π∈P,i, PointwiseUnbiased(E,P), and IndependentEstimator(E,P). Conclude TreatedUnbiased(E,μ0,P). This second implication does not explicitly assume every π∈P is admissible, and it does not use full Standing or global evaluated-estimator integrability.

## SAP.P006a.T7

For every measurable Ω,C, positive-size E: assume Standing for the experiment with its estimator replaced by the identically zero function. Thus all design and outcome conditions hold **for every admissible policy**, but no integrability of E's original estimator alone is required. Then quantify g:C→R, measurable and strictly positive at every x; require treated-residual integrability for every admissible π,i; TreatedUnbiased(E,μ0,F); integrability of gτ under P_X; and integrability, for every admissible π,i, of the actual unit reward (Y_{π,i}-μhat_π(X_i))B_i g(X_i).

Conclude that every admissible π has expected weighted TT equal to n∫gτπ dP_X, and positiveRule(τ) is an attained maximizer over F. Every maximizing b satisfies b=1 almost surely where τ>0 and b=0 almost surely where τ<0 (nothing is imposed where τ=0), has V(b)=∫τ positiveRule(τ)dP_X, maximizes welfare over F, and has zero regret. The weight need not be bounded or bounded away from zero; the explicit product and reward integrability clauses apply.

## SAP.P006a.T8

For every measurable Ω,X,U, positive-size E on covariates X×U, Standing(E), b0 with MarginalBaseline(E,b0), EstimatorUsesOnlyX(E), feasible P consisting of admissible policies, and TreatedUnbiased(E,c↦b0(c.1),P): for every π∈P,

expectedTT(π)/n = ∫π(x,u)(μ1(x,u)-b0(x))dP_X,

|expectedTT(π)/n-V(π)| = |∫π(x,u)(μ0(x,u)-b0(x))dP_X| ≤ Δ.

Additionally, for every real γ with Δ≤γ and every b,s, if b maximizes expectedTT on P and s maximizes V on P, regret(P,V,b)=V(s)-V(b)≤2γ. The per-policy statements precede and do not require either maximizer. Standing requires original evaluated-estimator integrability for every admissible policy, including on untreated draws and for policies outside P. There is no independent-estimator implementation assertion in this proposition.

## SAP.P006a.T9

Four universal arithmetic groups are conjoined. For any positive natural n and real vector τhat on Fin n, let H={i:τhat_i>0}, k=|H|, S=Σ_{i∈H}τhat_i, fitted utility v=S/n and beneficiary mean b=S/k. If k>0 then b=v(n/k); if also k<n then v<b.

For every v_H,b_H,v_S,b_S∈R, if 293907/2000000≤v_H≤293909/2000000, b_H=v_H(255/62), 50371/2000000≤v_S≤50373/2000000, and b_S=v_S(7264/1360), then

14989257/24800000≤b_H≤14989359/24800000 and 59/400<b_H;

672601/5000000≤b_S≤11434671/85000000 and 51/2000<b_S.

Separately, for every real v_H,r_H,v_S,r_S, assumptions 0<r_H≤2432/10000, 14694/100000≤v_H, 0<r_S≤1873/10000, and 2517/100000≤v_S imply v_H/r_H>604/1000 and v_S/r_S>134/1000.

Finally, the first set of interval and scaling assumptions implies the open rounding intervals 1465/10000<v_H<1475/10000, 245/10000<v_S<255/10000, 6035/10000<b_H<6045/10000, and 1345/10000<b_S<1355/10000. These are conditional arithmetic statements; they do not assert that data or fitted estimates actually attain the assumed numbers.

## Shared outcome-law definitions for T10 and T11

An OutcomeLaw D on C is an arbitrary measure on C×R², with coordinates (x,y0,y1). FiniteOutcomeLaw means a probability measure whose y0 and y1 coordinates are integrable; it does **not** mean finite support. outcomeWelfare(D,π)=∫π(x)(y1-y0)dD. oneATOExpectation(D,π) integrates the two-Boolean-outcome finite one-unit ATO sum with coin weights π(x),1-π(x), even for nonadmissible π. NondegenerateReward(P,R) means **there exist** D,b such that D has finite moments, b is an attained R(D,·) best response on P, and ∫b(x)dD>0. TreatedDataInvariant means for every two such laws having the same pushforward under (x,y0,y1)↦(x,y1), every policy π∈P has the same reward under both laws. shiftedOutcomeLaw(D,B) is the pushforward under (x,y0,y1)↦(x,y1+B,y1).

## SAP.P006a.T10

For every real B>0, put D=δ_((),1+B,1) and P={the constant-one policy}. D has finite moments, one maximizes oneATOExpectation on P, ∫1dD=1, its welfare is -B, and its regret relative to P is zero. Indeed for **every** real functional V on policies the regret of the sole member of P is zero. The zero policy is not in P and 0≥B is false.

For every measurable C, arbitrary OutcomeLaw D and arbitrary real policy π, oneATOExpectation(D,π)=∫π(x)y1 dD. For every measurable C, arbitrary D,D' and measurable π, if their (x,y1) pushforwards agree then their oneATOExpectation scores agree. These two general identities have no integrability or admissibility hypotheses and use the total Bochner-integral convention, although the explicit counterexample has finite moments and an admissible policy. Further, NondegenerateReward({one},oneATOExpectation) holds; for every functional f, one is best on {one}; and for every B>0 the supremum of welfare over this singleton under the displayed law is -B.

## SAP.P006a.T11

For every measurable C, P consisting of admissible policies and containing zero, every reward functional R, NondegenerateReward(P,R), and TreatedDataInvariant(P,R), the following both hold:

1. For every real M>0 there **exist** a finite-moment law D and a policy π maximizing R(D,·) on P such that regret(P,outcomeWelfare(D,·),π)>M. D and π may depend on M.
2. For every D,π with finite moments, π maximizing R(D,·), and q=∫π(x)dD>0, and then for every B>0: shiftedOutcomeLaw(D,B) has finite moments, preserves the (x,y1) marginal, and preserves optimality of this same π; every π'∈P has new welfare -B∫π'(x)dD≤0; maximum welfare is zero and zero attains it; π's regret is Bq. For every M>0 the scale (M+1)/q is positive and the regret under that shifted law exceeds M.

Separately, for every B>0, with D=δ_((),1+B,1) and P={zero,one}, the zero reward R(D,π)=0 is nondegenerate and treated-data invariant, every member is reward maximizing, zero is welfare maximizing with regret zero, and one's regret is B. No assertion about **every** reward best response having large regret is made.

## SAP.P006a.T12

A closed assertion about real-line measures L=Lebesgue measure restricted to [0,1] and Q=(1/2)L+(1/2)δ_(1/2). Both have mass one and topological support [0,1]. L is absolutely continuous with respect to Q. L({1/2})=0 and Q({1/2})=1/2, Q is not absolutely continuous with respect to L, and there exists no measurable f:R→[0,∞] with Q=L.withDensity(f). For every set S⊆R (not just measurable ones), (1/2)L(S)≤Q(S).

Here Mathlib absolute continuity means every null set of the second measure is null for the first (`Measure/AbsolutelyContinuous.lean:50`); topological support means every neighborhood has positive measure (`Measure/Support.lean:59,80`); and withDensity(f)(S)=∫_S f dL on measurable S (`Measure/WithDensity.lean:39`). This assertion does not construct any agents, policies, outcomes, or estimators.

## SAP.P006a.T13

For every natural K (zero is allowed), measurable C, family of measurable Ω_k indexed by Fin K, natural sample sizes n_k, Experiments E_k (so every instantiated n_k>0), probability measure P0, and the following assumptions in order: OutcomeStanding(E_k) for every k; equality of μ0_j and μ0_k as functions for every j,k; P0 absolutely continuous with respect to P_{X,k} for every k; τ_k integrable under P0; treated-residual integrability for every k, admissible π and unit i; TreatedUnbiased(E_k,μ0_k,F) for every k; and integrability of the actual weighted unit rewards for every k, admissible π and i. The weight is

g_k(x)=(1/n_k) (dP0/dP_{X,k})(x),

where the density is the Mathlib nonnegative-extended-real rnDeriv, converted with toReal. `rnDeriv` is a chosen density in Lebesgue decomposition (`Measure/Decomposition/Lebesgue.lean:80`); probability measures and the absolute-continuity hypothesis put it in the ordinary Radon–Nikodym setting and make it finite almost everywhere under P_{X,k}.

Then for every k and admissible π, expectedWeightedTT_k(g_k,π)=n_k∫τ_kπg_k dP_{X,k}=∫τ_kπ dP0. For every k the positive-effect rule is an attained best response on F and its maximum score equals ∫(τ_k)_+dP0, where positivePart(t)=t1_{t>0}=max(t,0). For every j,k, pointwise τ_k≤τ_j implies the corresponding positive-part integral inequality. UniformRankPreservation also holds: the same pointwise dominance implies maximum score k≤maximum score j, each maximized over its own policy argument. If **all** τ_k(x)≥0 for every k,x, every maximum score is ∫τ_kdP0 and RelativeRankPreservation holds: for every j,k, ∫τ_kdP0≤∫τ_jdP0 implies maximum score k≤maximum score j. Neither ranking predicate compares agent j's score evaluated at agent k's optimizer. K=0 makes indexed assertions empty, but K≥2 is allowed with no inconsistency or empty index requirement.

## SAP.P006a.T14

For every measurable C, every measure P0 (no probability or nonzero assumption), and every two real functions τ_j,τ_k: first assume τ_k(x)≤τ_j(x) for every x, then integrability of max(τ_j,0), then integrability of max(τ_k,0), both under P0. Conclude ∫max(τ_k,0)dP0≤∫max(τ_j,0)dP0. There are no experiments, estimators, best responses, score identities, or ranking predicates in this theorem. Infinite positive-part expectations are excluded by its explicit integrability premises; τ_j and τ_k themselves are not required to be integrable.

## SAP.P006a.T15

A closed conjunction plus one universally quantified singleton-private-coordinate assertion. In the first example, treatment is always one, Y1=1, and the one-point covariate's untreated outcome is either zero or two. For every observed record (t,y), the two finite observed mass functions agree. They put mass one on (true,1) and zero elsewhere. Treatment probability one is positive, non-treatment probability is zero, and the two untreated outcomes differ.

In the second example X is a fair Boolean, treatment probabilities are (1,1/2), Y1 is constantly one, and Y0 is either constantly zero or equal to two at false and zero at true. For every record (x,t,y) the two observed mass functions agree. Every covariate's treatment probability is strictly positive, non-treatment at false has probability zero, and total non-treatment probability is 1/4. Under the zero-baseline version, the records (false,true,1), (true,true,1), and (true,false,0) have respective probabilities 1/2,1/4,1/4.

For every measurable X, arbitrary μ0:X×Unit→R, and arbitrary measure P_X on X×Unit, for every c the real supremum over u∈Unit of |μ0(c)-μ0(c.1,u)| is zero, and its integral under P_X is zero. This is `maximumDeviation`, a real sSup of a range; in this instance that range is the nonempty bounded singleton {0}. No conditional identification theorem or regression-consistency limit is itself included; the explicit identical observation laws and zero non-treatment probabilities are the asserted witnesses.
