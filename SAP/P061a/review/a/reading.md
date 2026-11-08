# Blind reading

Saved before opening `claims.json` or `record.json`. This reading uses only the Defs and Challenge files and the Mathlib definitions they invoke. There are ten theorem stubs: T1–T9 and T11. There is no T10 theorem.

## Shared definitions and conventions

An `AtomicDesign Ω` is a function p: Ω → ℝ with p(z) ≥ 0 for every z, unconditionally summable over Ω, and sum 1. Thus it is a discrete probability law, even when Ω is uncountable. Its positive support is {z: p(z)>0}. This structure excludes an empty Ω. It supplies no probability mass to a nonatomic distribution.

Write P(A) = Σ_z p(z)1_A(z), E[f] = Σ_z p(z)f(z), and M(f) for Σ_z p(z)|f(z)| being summable. All sums over Ω are Mathlib's **unconditional** sums, defined as limits over the directed finite subsets. For real families, summability is absolute summability. A nonsummable `tsum` is assigned 0 by Mathlib; a bare E[f] does not assert the existence of an ordinary expectation. `HasMean` is M(f) and does assert finite absolute first moment. Event sums are ordinary sums because they are dominated by p. Every event is an arbitrary predicate; measurability causes no issue for this atomic law.

There are N units indexed by Fin N. Responses y_i(z) and exposures g_i(z) are arbitrary real functions. Put p_i(d)=P(g_i=d). `positiveExposure d` means ∃c>0, ∀i, c≤p_i(d). With finite positive N this is equivalent to every p_i(d)>0; with N=0 it is vacuous. `targetMoment d` means M(1_{g_i=d}y_i) for every i.

The unit exposure mean is μ_i(d)=E[1_{g_i=d}y_i]/p_i(d). The separately defined conditional mean is C_i(d)=Σ_z 1_{g_i=d}(p(z)/p_i(d))y_i(z). Neither definition by itself asserts existence or positivity. Division is real division, so division by zero is totalized to 0. The population exposure mean is μ̄(d)=N⁻¹Σ_i μ_i(d); the unit contrast is τ_i(d,d′)=μ_i(d)−μ_i(d′); the population contrast is T(d,d′)=μ̄(d)−μ̄(d′). N⁻¹ also equals 0 at N=0. The HT mean estimate is μ̂(d;z)=N⁻¹Σ_i 1_{g_i(z)=d}y_i(z)/p_i(d), and τ̂(d,d′;z)=μ̂(d;z)−μ̂(d′;z).

`supportStability` means that for all i and all two positive-mass assignments z,z′, equal g_i entails equal y_i. `globalStability` makes the same assertion for all assignments, with no support qualification.

Var(X)=E[(X−E[X])²] and Cov(X,Y)=E[(X−E[X])(Y−E[Y])]. These definitions alone do not impose moments. Theorems using finite Ω have all such moments automatically.

`independent D X Y` means P(X∈E,Y∈F)=P(X∈E)P(Y∈F) for every pair of predicates E,F on their respective codomains. `mutuallyIndependent D g` means P(∀i,g_i∈E_i)=∏_i P(g_i∈E_i) for every collection of predicates E_i:ℝ→Prop.

For a real vector v, v_{−i} is its restriction to the subtype {j:j≠i}. I_i(e,w) inserts e at coordinate i and w at every other coordinate. For a feasible set S⊆ℝ^N, `coordinateExposure S` is g_i(z)=z_i. The hybrid h_i(e,z) is y_i(I_i(e,z_{−i})) when that inserted vector belongs to S, and **0 otherwise**. The direct contrast A(d,d′)=N⁻¹Σ_i E[h_i(d,Z)−h_i(d′,Z)] uses this convention unless a theorem ensures feasibility.

For varying atomic designs D_n, `probabilityLimit X a` means for every ε>0, P_n(|X_n−a|>ε)→0. `weakLimit X L` means E_n[f(X_n)]→∫f dL for every bounded continuous real f on ℝ. Mathlib's Bochner integral is 0 outside its integrability domain, but in T5 L is explicitly a probability measure, so these test integrals exist. `translatedLaw L c` is the pushforward of L by the continuous map x↦x+c. Limits use the usual neighborhood topology on ℝ and the atTop filter on ℕ; atTop as a target on ℝ means divergence to +∞.

Mathlib sources followed: `Topology/Algebra/InfiniteSum/Defs.lean` (HasSum, Summable, tsum); `Logic/Function/Basic.lean` (extend and update); `Logic/Equiv/Fin/Basic.lean` (finProdFinEquiv); `Order/Filter/Defs.lean` and `AtTopBot/Defs.lean` (Tendsto and atTop); `Topology/ContinuousMap/Bounded/Basic.lean` (bounded continuous functions); `MeasureTheory/Integral/Bochner/Basic.lean` (integral); `MeasureTheory/Measure/Typeclasses/Probability.lean` (probability measures); `MeasureTheory/Measure/Map.lean` (pushforward); `Analysis/Real/Sqrt.lean` (square root). Finite sums/products are ordinary Finset sums/products; update replaces exactly one coordinate; finProdFinEquiv enumerates pairs by 2k+b. `Function.extend` chooses a preimage on the range and the specified fallback off the range; the natural-to-real map used here is injective.

## SAP.P061a.T1

There exists a family D_N, for **every** natural N including 0, of atomic laws on {0,1,2}^N, such that every assignment has mass 3^(−N). Define g_i(z)=0 if z_i=0, and 1 otherwise; y_i(z)=z_i (as a real); and v(z)_i=0 if z_i=0, and 1 otherwise. For every N>0 the following all hold:

* The exposures g_i are mutually independent. For every i,z, 0≤y_i(z)≤2. For every i,z,z′, z_i=z′_i implies y_i(z)=y_i(z′).
* Both targets 1 and 0 satisfy uniform positivity. For every i, P(z_i=1,g_i=1)/p_i(1)=1/2 and P(z_i=2,g_i=1)/p_i(1)=1/2.
* T(1,0)=3/2. For all i,z, both y_i(update(z,i,1))−y_i(update(z,i,0)) and y_i(update(v(z),i,1))−y_i(update(v(z),i,0)) equal 1. Both corresponding averages of expected contrasts equal 1 (the raw one is asserted twice). T(1,0)−1=1/2.
* For each i, p_i(1)=2/3, p_i(0)=1/3, μ_i(1)=3/2, μ_i(0)=0 and τ_i(1,0)=3/2.
* For every z, τ̂(1,0;z)=(3/(2N))Σ_i z_i; its expectation is 3/2 and variance is 3/(2N). For **every** ε>0, P(|τ̂−3/2|≥ε)≤3/(2Nε²).

In addition, at N=2 there is **no** function H:ℝ²→ℝ with y_0(z)=H(g(z)) for **all** z∈{0,1,2}². The exposure vectors at (1,0) and (2,0) agree coordinate by coordinate, while their unit-0 responses are 1 and 2 respectively. As n→∞, T for D_{n+1} minus 1 tends to 1/2 and does not tend to 0. The existential D-family precedes all these assertions. There are no theorem hypotheses.

## SAP.P061a.T2

Let B={0,1}². Write own_i(z)=z_i and partner_i(z) for the other bit, for i=0,1, and g_i(z)=own_i(z)+2partner_i(z). The exposure vector is (g_0,g_1). `inEdgeExposureImage r` means ∃z∈B, g(z)=r. `inBitDomain r` means both coordinates of r belong to {0,1}.

There exists a law D on B with p(z)=1/4 for every z, with all of these facts:

* For every i∈{0,1} and e∈{0,1,2,3}, p_i(e)=1/4. With y_i=own_i, μ_i(1)=1, μ_i(0)=0 and T(1,0)=1. The schedule is globally stable for g, and also stable on D's support. Both targets have uniform positive exposure probability.
* For every z, the two vectors (1,g_1(z)) and (0,g_1(z)) cannot **both** belong to the exposure image; also (g_0(z),1) and (g_0(z),0) cannot both belong to it. This does not assert that both vectors individually fail.
* The probabilities that each of those two respective hybrid pairs lies wholly in {0,1}² are each 1/2. More precisely, membership of either (1,g_1(z)) or (0,g_1(z)) in the bit domain is equivalent to z_0=0, and membership of either (g_0(z),1) or (g_0(z),0) is equivalent to z_1=0.
* For every r∈ℝ², image membership is equivalent to r being one of (0,0),(2,1),(1,2),(3,3). The map takes (0,0),(0,1),(1,0),(1,1) to those respective values.

Conjoined with that existence assertion: for **every** natural K>0, there exists a law D on K copies of B with p(z)=∏_{k<K}(1/4). Units are indexed by i=2k+b via finProdFinEquiv. Own and partner refer to pair k and bit b; g_i=own_i+2partner_i and y_i=own_i. For every unit, each of its four exposure values has probability 1/4, μ_i(1)=1, μ_i(0)=0; the population contrast is 1; and global stability holds. For every i,z, replacing coordinate i of the full exposure vector by 1 and by 0 cannot give two vectors both in the paired exposure image. For every i, the probability that **both** replacements lie in the full raw bit domain {0,1}^{2K} is (1/2)(1/4)^(K−1). Here natural subtraction K−1 is harmless because K>0. The single-pair law and the laws for each K are separately existential; no theorem hypotheses.

## SAP.P061a.T3

This is a conjunction of two universal assertions.

First, for **every** N,S⊆ℝ^N, atomic D on the subtype S, response schedule y, and real d,d′, assume, in order:

1. N>0;
2. for every i, p_i(d)>0 and p_i(d′)>0, using raw coordinate exposure;
3. targetMoment at d, then targetMoment at d′;
4. for every i, Z_i is independent of the whole vector Z_{−i}.

Then: for every i and every e∈{d,d′}, for every other-coordinate vector w with P(Z_{−i}=w)>0, there exists a **positive-mass** z∈S with z=I_i(e,w). Also, for each such i,e, h_i(e,·) has finite absolute mean and μ_i(e)=E[h_i(e,Z)]. Finally T(d,d′)=A(d,d′). Feasible insertion is a conclusion on positive-mass fibers, not an assumed product structure for S.

Second, for **every** Ω,N,D,g,y,H,d,d′, where H_i:ℝ^N→ℝ is an arbitrary full exposure-vector response schedule, assume in order N>0, each unit's two target probabilities positive, both targeted moment conditions, independence of g_i(Z) from the whole other-exposure vector for each i, and, for every i,z, if z has positive mass and g_i(z)∈{d,d′}, then y_i(z)=H_i(g(z)). Then for every i,e∈{d,d′}, H_i(I_i(e,g_{−i}(Z))) has finite absolute mean and μ_i(e)=E[H_i(I_i(e,g_{−i}(Z)))]. Moreover T(d,d′)=N⁻¹Σ_i E[H_i(I_i(d,g_{−i}(Z)))−H_i(I_i(d′,g_{−i}(Z)))]. No injectivity of g or equality d≠d′ is imposed.

## SAP.P061a.T4

Define a_m=1/m for m≥2, and 0 for m=0,1; K=m^8 and N=2K. Assignments are K bit pairs. Let X_i be the own bit and W_i the partner bit. Exposures are X_i, responses y_i=1+a_m W_i, and replacing a raw own bit leaves the partner bit fixed. A_m is the average expected raw replacement contrast. Let τ̂_m be the HT contrast for exposures 1 versus 0; σ_m=√Var(τ̂_m). Define V_m=8+16/m+14/m²+2/m³−4/m⁴, with real division.

There exists a family D_m for **all** natural m, with mass at each z equal to the product over its K pairs of (1+a_m)/4 when the bits agree and (1−a_m)/4 otherwise. For every m≥2, all of the following hold:

* Every assignment has positive mass. For all i, P(X_i=1)=P(X_i=0)=1/2, and for all i,z, 1≤y_i(z)≤3/2.
* For each i, X_i is independent of the vector of entire pairs other than i's pair. For every pair k, Cov(X_{2k},X_{2k+1})=1/(4m).
* A_m=0. For all i, μ_i(1)=1+(1/m)(1+1/m)/2 and μ_i(0)=1+(1/m)(1−1/m)/2. T_m=1/m²; E[τ̂_m]=1/m²; Var(τ̂_m)=V_m/(4m^8).
* 8≤V_m<20; (m^(−2)/σ_m)²=4m^4/V_m≥m^4/5; and σ_m>0.
* P(|τ̂_m−m^(−2)|≤5σ_m)≥24/25. If m≥5, then P(|τ̂_m|≤5σ_m)≤4Var(τ̂_m)/(m^(−2))²=V_m/m^4≤20/m^4.

For the same D-family, with m=n+2 and n→∞, T_m−A_m→0, (2m^8)Var(τ̂_m)→4, ((T_m−A_m)/σ_m)²→+∞, and P(|τ̂_m−A_m|≤5σ_m)→0. The mass formula includes m=0,1 but finite inference assertions start at 2. No graph degree, outcome-neighbor predicate, unsquared divergent limit, order notation, or alternate variance polynomial occurs in the formal statement. There are no theorem hypotheses.

## SAP.P061a.T5

This is a conjunction of four universal statements, in the following order.

**InferenceTransfer.** For every sequence S_N⊆ℝ^N, D_N on S_N, y_N, real d,d′, arbitrary real estimator b_N and estimated scale r_N on S_N, deterministic scale s_N, and real Borel probability measure L, assume:

1. s_N>0 for all N;
2. r_N(z)>0 for all N and all z∈S_N;
3. for every N,i, the raw-coordinate target probabilities at d,d′ are positive;
4. for all N, the two targeted moment conditions hold;
5. for every N,i and positive-mass z, both inserted vectors I_i(d,z_{−i}) and I_i(d′,z_{−i}) belong to S_N;
6. for each N,i, both hybrid responses separately have finite absolute means;
7. (b_N−T_N)/s_N converges weakly to L;
8. r_N/s_N converges in probability to 1;
9. (T_N−A_N)/s_N→0.

Then (b_N−A_N)/r_N converges weakly to L, **and** for every q>0 with L({q})=L({−q})=0, P(|b_N−A_N|≤qr_N)→L([−q,q]), converted from ENNReal to ℝ. N runs over all naturals, including 0; there is no positive-population-size hypothesis in this sequence assertion. There is no separate interval assertion centered on T_N.

**FiniteNeighborhoodBound.** For every finite nonempty alphabet A, natural N, and injective label ℓ:A→ℝ, then every D on the full space A^N, responses y, neighborhoods H_i⊆Fin N, functions f_i:A→A^{H_i}→ℝ, and d,d′∈A, assume N>0, i∉H_i for all i, both labelled-coordinate target probabilities positive for every i, and for every i,e∈{d,d′},z, y_i(update(z,i,e))=f_i(e,z|_{H_i}). Let P_i be the unconditional law of Z|_{H_i}, and Q_{i,e} its law conditional on Z_i=e: these are the explicit finite event probabilities, with the latter divided by P(Z_i=e). Let R(f)=sup range(f)−inf range(f), and TV(Q,P)=(1/2)Σ_x|Q(x)−P(x)|. Then

|T(ℓ(d),ℓ(d′))−N⁻¹Σ_i E[y_i(update(Z,i,d))−y_i(update(Z,i,d′))]|
≤N⁻¹Σ_i [R(f_i(d,·))TV(Q_{i,d},P_i)+R(f_i(d′,·))TV(Q_{i,d′},P_i)].

Finite, nonempty neighborhood assignment spaces make the displayed suprema and infima genuine finite extrema. An empty neighborhood has a singleton assignment space, not an empty one.

**Squeeze.** For every four real sequences T,A,B,s, assume all s_N>0, |T_N−A_N|≤B_N for all N, and B_N/s_N→0. Then (T_N−A_N)/s_N→0.

**Nonzero drift.** For every varying Ω_N,D_N, estimators b_N,r_N, real deterministic T,A,s, probability measure L, and real c, assume c≠0, all s_N>0, all r_N(z)>0, weak convergence (b_N−T_N)/s_N⇒L, probability convergence r_N/s_N→1, and (T_N−A_N)/s_N→c. Then (b_N−A_N)/r_N⇒the law of X+c for X∼L. This last conjunct has no outcome, exposure, feasibility, or moment hypotheses.

## SAP.P061a.T6

First, for **every finite type** Ω, N,D,g,y and real d,d′, assume N>0, p_i(d)>0 for all i, and p_i(d′)>0 for all i. Then for every i, μ_i(d)=C_i(d) and μ_i(d′)=C_i(d′); T(d,d′)=N⁻¹Σ_i(C_i(d)−C_i(d′)); T(d,d′)=μ̄(d)−μ̄(d′); and T(d,d′)=N⁻¹Σ_i τ_i(d,d′). The population-mean difference is also the definition of T.

Second, for **every** N,D on {0,1}^N and real response schedule y, assume N>0 and positive own-bit probabilities at 1 and 0 for every i. Then the own-bit population contrast is N⁻¹Σ_i(C_i(1)−C_i(0)). No stability, independence, or moments are hypotheses; moments follow from finiteness. There is no assertion for an arbitrary infinite feasible domain.

## SAP.P061a.T7

Let p(k)=2^(−k−1) for natural k, embedded in ℝ, and p(z)=0 off those integers. Define g(k)=0 at k=0, g(k)=1 at k≥1, and g(z)=0 off the natural integers. The single response is y(0)=0, y(k)=(−1)^(k+1)2^(k+1) at k≥1, and 0 off the natural integers. These extensions use the injective natural-to-real map.

There exists an atomic D on **all ℝ**, with mass exactly p, such that positive support is exactly the embedded natural integers; both target exposures have uniform positivity; and the following all hold:

* p_0(1)=p_0(0)=1/2; μ_0(0)=0; the real family p(z)1_{g(z)=1}y(z), indexed by all ℝ, is **not** summable; the HT mean estimator for target 1 does **not** have finite absolute mean; and target 0's truncated response **does** have finite absolute mean.
* Define u_k=p(k+1)y(k+1), for every natural k. Then u_k=(−1)^k. For every natural m, sums over k<2m of max(u_k,0), max(−u_k,0), |u_k|, and u_k are respectively m,m,2m,0; the sum of u_k over k<2m+1 is 1.
* Neither nonnegative sign part of (u_k) is summable.
* For every real z, μ̂(1;z)=2y(z)1_{g(z)=1}. Define v_k=p(k+1)μ̂(1;k+1); then v_k=2(−1)^k for every k. Neither nonnegative sign part of (v_k) is summable.

The theorem does not assign an ordinary value to a divergent target-1 expectation. It does not separately assert a limit failure of ordered partial sums or nonexistence predicates for every derived population functional. There are no theorem hypotheses.

## SAP.P061a.T8

First, for **every** Ω,N,D,g,y,d, assume N>0, p_i(d)>0 for all i, and targetMoment d. Then `FirstMomentFacts` asserts all of the following:

* For every i, p(z)1_{g_i=d}y_i(z) is summable; μ_i(d)=C_i(d); 1_{g_i=d}y_i/p_i(d) has finite absolute mean; E[|1_{g_i=d}y_i/p_i(d)|]=E[|1_{g_i=d}y_i|]/p_i(d); and E[1_{g_i=d}y_i/p_i(d)]=μ_i(d).
* μ̂(d) has finite absolute mean and E[μ̂(d)]=μ̄(d).
* For every real d′, **if** p_i(d′)>0 for every i and targetMoment d′, then τ̂(d,d′) has finite absolute mean, E[τ̂(d,d′)]=T(d,d′), and T(d,d′)=N⁻¹Σ_i τ_i(d,d′).
* For every i, the conditional exposure mean formed from |y| is E[|1_{g_i=d}y_i|]/p_i(d). Also μ̄(d)=N⁻¹Σ_i C_i(d).

Second, for **every** Ω,N,D,g,y,d, assume N>0 and p_i(d)>0 for all i. Then two separate implications hold: if the positive support of D is finite, targetMoment d; and if for all i,z,z′ with positive mass and g_i(z)=g_i(z′)=d the outcomes agree, then targetMoment d and for every i there exists a real a_i such that every positive-mass target-d assignment has response a_i and E[|1_{g_i=d}y_i|]=|a_i|p_i(d). This second branch assumes stability only inside the single targeted cell, not globally.

## SAP.P061a.T9

Assignments are z∈{0,1,2}^4. For natural n, S_n means exactly one coordinate equals 2 and exactly n coordinates are nonzero. Set g_i(z)=z_i and y_i(z)=(number of nonzero coordinates)1_{z_i=2}.

There exist two designs D,D′ on the **same full assignment space**, with p_D(z)=1/12 on S_2 and 0 elsewhere, and p_D′(z)=1/12 on S_3 and 0 elsewhere. Their positive supports are exactly S_2,S_3. For each i, D gives exposure probabilities p_i(2)=1/4,p_i(1)=1/4; D′ gives p_i(2)=1/4,p_i(1)=1/2. All four displayed probabilities are separately asserted positive. The same y is support-stable for D and support-stable for D′. For every i, D's means at 2 and 1 are 2 and 0, and D′'s are 3 and 0. The two population contrasts at (2,1) are 2 and 3. Finally the common g,y schedule is **not** globally stable on {0,1,2}^4. There are no theorem hypotheses.

## SAP.P061a.T11

`positivityWellDefined` universally quantifies, in order, arbitrary types Ω, natural N, atomic D on Ω, real exposures g and responses y, and real d,d′. It asserts that N>0 and uniform positivity at both d,d′ imply the conjunction of: targetMoment d; targetMoment d′; equality μ_i(d)=C_i(d) and μ_i(d′)=C_i(d′) for every i; and T(d,d′)=N⁻¹Σ_i τ_i(d,d′).

T11 is the **negation of that entire universal implication**. Classically it asserts existence of some Ω,N,D,g,y,d,d′ with N>0 and both positivity conditions for which at least one conjunct fails. It does not assert that each identity fails, nor that any totalized real expression has no Lean value. The moment conjuncts expressly encode failure of finite ordinary means. There are no theorem hypotheses.
