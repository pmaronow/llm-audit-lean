# Blind mathematical reading

This file was written and saved before opening `claims.json` or `record.json`. The inputs for this stage were all eight `Defs/Part*.lean` files, `Defs.lean`, `Challenge/Part1.lean`, `Challenge.lean`, and the Mathlib sources cited below. The 14 Challenge theorems have no explicit parameters: theorem `SAP.P008a.Tk` asserts the entire proposition `TkStatement`, including all its internal universal quantifiers and conjunctions. The Challenge bodies are stubs, so this reading does not use their proofs.

## Common objects and conventions

* `Fin N` is the set of integers from 0 through N−1. An assignment is a function z:Fin N→Bool. Write Z_i=1 when z(i)=true and Z_i=0 otherwise (`bit`). Every displayed finite vector is indexed starting at zero. All finite sums below count each element once.
* A `FiniteLaw Q` on a finite type Ω consists of real masses Q(z)≥0 with Σ_z Q(z)=1. Its expectation is E_Q f=Σ_z Q(z)f(z); its probability of A is Σ_{z:A(z)}Q(z). Cov_Q(f,g)=E_Q[(f−E_Q f)(g−E_Q g)], and Var_Q(f)=Cov_Q(f,f). A finite law cannot exist on an empty Ω. The uniform law gives every element mass 1/|Ω| and requires Ω nonempty.
* `marginal Q F i b` is E_Q[F(z with coordinate i replaced by b)]. This is an override expectation, not the conditional expectation given z(i)=b. `commonBernoulli Q p` means Q(z)=Π_i [p if z(i)=true, otherwise 1−p]. `conditionalLaw Q A hA`, requiring Q(A)>0, gives mass Q(z)/Q(A) on A and zero off A.
* The plane is the real Euclidean plane, with the usual Euclidean distance, realized as `PiLp 2 (Fin 2→ℝ)` (Mathlib `Analysis/InnerProductSpace/PiL2.lean:114`). `lineEmbedding x` is the point (x,0), for rational x.
* A spatial model P comprises an arbitrary set F⊆ℝ², nodes x_i∈F, an arbitrary Borel measure ζ on the plane, and arbitrary real functions Y(x,z). There is no implicit compactness, positive area, distinctness of nodes, independence, measurability of F or Y, or finiteness of ζ. Such conditions must be explicit in an individual assertion.
* C_i(d)={x∈F:dist(x_i,x)=d}. Write ν_i,d=ζ restricted to C_i(d), m_i,d=(ν_i,d(ℝ²)).toReal, and A_i,d(f)=m_i,d⁻¹ ∫f dν_i,d. `M i d z` is A_i,d(Y(·,z)). `m Q i b d` is E_Q[M_i(d,z with i set to b)]. The point marginal Y and point effect are the analogous override expectation of Y(x,z), and its true-minus-false difference. The node effect is the true-minus-false difference of the M marginals. `amr` is their average (1/N)Σ_i. `risk Q b d` is (1/N)Σ_i m_i(b,d). `sharpNull` requires Y(x,z)=Y(x,all-false) for every x∈F and every z.
* `Measure.restrict` is Mathlib measure restriction, with its usual intersection formula on measurable sets (`MeasureTheory/Measure/Restrict.lean:43–78`). `.toReal` on extended nonnegative reals sends infinity to zero. The real Bochner integral is defined to be zero when its integrand is not integrable (`MeasureTheory/Integral/Bochner/Basic.lean:158,204`). `Integrable f ν` means a.e. strong measurability and finite integral of its norm (`MeasureTheory/Function/L1Space/Integrable.lean:59`). Positive finite mass and integrability hypotheses below are therefore material. In the geometric support assertion of T6, the relevant integrand vanishes on the circle.
* n₁(z)=Σ_i Z_i and n₀(z)=N−n₁(z) are **real** numbers (`nControl` does not use natural subtraction). H(M,z) (`hajek`) is Σ_i Z_i M_i(z)/n₁ − Σ_i(1−Z_i)M_i(z)/n₀. Real division by zero is totalized as zero; relevant assertions either use balanced fixed assignments or explicitly require both arms. `finiteAMR Q M`=(1/N)Σ_i(E_Q M_i(z^{i←true})−E_Q M_i(z^{i←false})).
* The inclusive two-sided tail p_Q,T(z) is Q{|T(w)|≥|T(z)|}; ties are included. `outside(lo,hi,t)` means t<lo or hi<t (strict rejection).
* For any s indexed by 0,…,n, `quantile7 s q` sets h=nq, j=min(toNat(floor h),n), g=h−j, and returns (1−g)s_j+g s_min(j+1,n). For q∈[0,1] and sorted s this is the usual finite type-7 interpolated quantile. Sorting is not performed inside the definition. All its uses here have q∈[0,1]. Samples have n+1≥1 entries.
* `countMean C f`=(Σ_{x∈C}f(x))/|C|. `lineCircle(field,node,i,d)` is the finite set {x∈field:|x−node_i|=d}, and `lineM` is its counting mean of Y(x,z). An empty counting mean is totalized to zero; the examples below identify nonempty circles.
* Let K=(1100,1010,1001,0110,0101,0011) be the six assignments on four nodes (`sixAssignment`). B=(1010,1001,0110,0101) is `blockedAssignment`. Here strings are Boolean coordinate vectors. `treatedCount` is the natural-number count of true coordinates. `contrast4(y,z)`=Σ_i Z_i y_i/2−Σ_i(1−Z_i)y_i/2. `sixComplement` sends k to 5−k; `percentileExample` is (−2,−1,0,0,1,2).
* U is the set of all 60-element subsets of {0,…,120}; V consists of unions of a 5-element subset of {0,…,9} and a 55-element subset of {10,…,120}. These are `unrestricted121` and `blocked121` (`powersetCard` has the ordinary cardinality-constrained subset meaning: Mathlib `Data/Finset/Powerset.lean:198–204`). O={0,…,4}∪{10,…,64}, and O'=(O\{10})∪{5}. `supportMass S z` equals 1/|S| for z∈S and zero otherwise, on the full type of finite subsets of ℕ.
* For fixed observed z and real node data v_i, let group means be v̄₁=Σ Z_i v_i/n₁ and v̄₀=Σ(1−Z_i)v_i/n₀. The group residual e_i=v_i−v̄_{z(i)}, contrast weight w_i=Z_i/n₁−(1−Z_i)/n₀, and regression score g_i=w_i e_i. `hac(g,D,c)`=Σ_iΣ_j g_i g_j 1{D_ij≤c}; D is an arbitrary real array unless expressly a distance. `binaryDesign` is X_i=(1,Z_i). `olsResidual` is v−X(XᵀX)⁻¹Xᵀv. `olsMeat` has entries Σ_iΣ_j 1{D_ij≤c} e_i^OLS e_j^OLS X_ia X_jb. Matrix inverse is the ordinary inverse for nonsingular matrices and zero for singular ones (Mathlib `LinearAlgebra/Matrix/NonsingularInverse.lean:168–176`); T6's two arms make X full rank.
* `archivedVariance(g,D,c,position)`=hac(g,D,c+position) if c>0, and hac(g,D,c) otherwise. `physicalVariance` always equals hac(g,D,c) and ignores the position. `bandwidthExampleDistance(i,j)`=|2i−2j| on four indices.
* The four `toyNode` points, in order, are (2028297641/2147483648,4318520789/2147483648), (7976664621/2147483648,1029755657/268435456), (1053580245/536870912,2017196647/2147483648), and (7110225301/2147483648,499145583/1073741824). These exact rational coordinates determine every toy distance used below.
* The linearization score is φ_i(z)=2Z_i(M_i(z)−m₁)−2(1−Z_i)(M_i(z)−m₀). Its constants m₁,m₀ are arbitrary unless fixed in a particular example.
* The validator spatial model has field [−1,31]×[−1,1], nodes (10i,0), outcome Y(x,z)=Σ_{i=0}³ i·1{dist(x,(10i,0))≤1}, independent of z, and measure Σ_{i=0}³Σ_{a=0}⁵ δ_(10i+a/10,0). Its five radii are r_j=(j+1)/10, j=0,…,4. Its statistic T_j(k)=H(M(·,r_j,·),K_k). A Dirac measure is the usual unit point mass; the finite sums here are counting measures with multiplicity.
* The bandwidth spatial model has whole-plane field, nodes (2i,0), assignment-independent outcome Y(x,z)=Σ_i 2i·1{dist(x,(2i,0))≤3/10}, measure Σ_{i=0}³Σ_{a=0}³ δ_(2i+a/10,0), and radii r_j=(j+1)/10, j=0,1,2. Short and long grids are (1/5,3/10) and (1/10,1/5,3/10).
* The pair counting model has field {−1,0,1,2,3}⊂ℚ, nodes 0,2, and outcome Y(x,z)=1{|x|≤1}Z₀+1{|x−2|≤1}Z₁; `pairM` is its radius-one mean. `pairAssignment` enumerates (00,01,10,11). For M replicated pairs, indices are (g,b)∈Fin M×Fin 2, nodes 6g+2b, field {6g+a−1:g∈Fin M,a∈Fin 5}, and Y(x,z)=Σ_i1{|x−node_i|≤1}Z_i. A replicated circle is the subset of this field at distance one; its mean is `replicatedCircleM`. `replicatedSpatialScore` is φ with m₁=5/4,m₀=1/4. `replicatedPairScore(g,b,z)`=(1/2)(2Z_(g,0)−1)(2Z_(g,1)−1).
* For the risk models, node i and radius j both range over Fin 4 and point k over Fin 40000. Baselines are β=(400,1000,400,1000). `riskOutcome(i,j,k,z)`=1{k<β_i−321·1{z(i)=true}}, with this threshold using **natural truncated subtraction**. All four β_i≥321, so its use here does not truncate a negative number. `riskM` is the mean over all 40000 k. The companion outcome and its counting mean use 1−Z_i. `riskSamplingProbability(Q,b)`=(1/16)Σ_iΣ_j E_Q[riskM(i,j,z^{i←b})].
* The printed grid is p_k=5k/111 for k=0,…,4; the corrected grid is c_k=k/222 for k=0,…,40. `inUgandaRange(d)` is 1/111≤d≤5/222, inclusive.

## T1 — `SAP.P008a.T1`

An unconditional conjunction:

1. |U|=choose(121,60), |V|=choose(10,5)choose(111,55), V is a proper subset of U, O∈U∩V, O'∈U\V; their listed masses are positive except V's mass at O', which is zero. Each support mass sums to one on its own support, and the two mass functions are unequal.
2. K is injective; **for every assignment z on four nodes**, treatedCount(z)=2 iff there exists k∈Fin 6 with K_k=z; K₁=1010. B is injective; **for every z**, (z₀≠z₁ and z₂≠z₃) iff there exists k∈Fin 4 with B_k=z.
3. **For every k∈Fin 6**, contrasts for y=(0,1,0,1) and y=(0,1/3,2/3,1) equal respectively (0,−1,0,0,1,0)_k and (−2/3,−1/3,0,0,1/3,2/3)_k.
4. The inclusive absolute tails at K₁ under uniform K and at B₀ under uniform B are respectively 1/3 and 1/2 for the first y, and 2/3 and 1/2 for the second y; 1/3<1/2<2/3.

## T2 — `SAP.P008a.T2`

A conjunction of five assertions, with independent quantifiers:

1. **For every finite type Ω, law Q, function T:Ω→ℝ, real δ, with 0≤δ≤1**, Q{p_Q,T≤δ}≤δ.
2. **For every finite Ω, Q, event A with Q(A)>0, T, δ with 0≤δ≤1**, the same inequality holds using Q conditioned on A both to compute tails and to measure rejection.
3. **For every natural N, law Q on assignments, real p with 0<p<1 and commonBernoulli(Q,p), natural M with M≤N**, Q{treatedCount=M}>0 and **for every z with that count**, Q(z)/Q{count=M}=1/choose(N,M).
4. **For every N, spatial P, assignment law Q, event A of positive Q-probability, finite radius set D**, assume F measurable, sharpNull(P), N>0, every evaluated circle has positive real mass and finite extended mass, every Y(·,z) is integrable on every evaluated circle for **all assignments z**, and **every z satisfying A with Q(z)>0** has n₁,n₀ nonzero. **For every δ with 0≤δ≤1**, set S(z)=Σ_{d∈D}H(M(·,d,·),z). Its conditional-law inclusive-tail test has rejection probability ≤δ; moreover **for every z in that positive-probability conditional support**, S(z)=Σ_{d∈D}H((i,w)↦M_i(d,all-false),z). D is allowed empty. Imputation is stated for S, not separately for each circle mean.
5. The four tail values and strict ordering from T1 are repeated.

## T3 — `SAP.P008a.T3`

An unconditional assertion about the fixed validator rectangle model, together with one universally quantified Bernoulli assertion:

1. K is injective, enumerates exactly all count-two assignments, and K₁=1010.
2. **For every node i**, its closed unit disk lies inside the rectangle; **for every distinct i,k**, those disks are disjoint. **For every node i and radius index j**, circle mass is positive, extended mass finite, and **for every z**, Y(·,z) is integrable there. **For every x,z**, Y(x,z)=Y(x,all-false). **For every i,j,z**, M_i(r_j,z)=i.
3. **For every j,k**, T_j(k)=(−2,−1,0,0,1,2)_k. **For every j**, its type-7 quantiles at 1/40,39/40 equal −15/8,15/8, and the uniform-six probability of falling strictly outside that interval is 1/3. For the sum over the five j, the quantiles are −75/8,75/8 and the rejection probability is 1/3; 1/20<1/3.
4. **For every law Q on four-node assignments satisfying commonBernoulli(Q,1/2)**, the count-two event has positive probability and **for every z in it**, the conditional mass is 1/6.
5. **For every j∈Fin 5 and k∈Fin 6**, single-radius rejection occurs iff k=0 or 5; Σ_r T_r(k)=(−10,−5,0,0,5,10)_k; cumulative rejection also occurs iff k=0 or 5.

## T4 — `SAP.P008a.T4`

1. **For every real y:Fin 4→ℝ and k∈Fin 6**, its complementary index differs from k, K_(5−k) is the Boolean complement of K_k, both arm counts are two, and H(y,K_k)=contrast4(y,K_k).
2. **For every natural J, real weights a:Fin J→ℝ and node arrays m:Fin J→Fin 4→ℝ**, put S(k)=Σ_j a_j contrast4(m_j,K_k). **For every k**, S(5−k)=−S(k), its inclusive uniform-six absolute tail is at least 1/3, and that tail is not ≤1/20. No positivity, normalization or nonemptiness of the weights is required.
3. **For every nonempty finite subset R of Fin 6**, its uniform probability is |R|/6≥1/6>1/20.
4. **For every finite Ω, law Q, real T and δ∈[0,1]**, the exact inclusive-tail rejection probability is ≤δ.
5. **For every finite Ω, law Q, natural B, law R on sequences Fin(B+1)→Ω, assuming R(z)=Π_k Q(z_k), real S:Ω→ℝ, and δ∈[0,1]**, the R-probability that [1+#{b∈Fin B:|S(z₀)|≤|S(z_(b+1))|}]/(B+1)≤δ is at most δ. Thus observation and all B comparisons are IID under the hypothesis; B may be zero.
6. 1.491+1.550+1.550+1.691+1.714=1999/250=7.996.

## T5 — `SAP.P008a.T5`

1. The four `pairAssignment` values enumerate all two-node assignments bijectively. Both nodes lie in the pair field. Their radius-one circles are {−1,1} and {1,3}. **For every z**, M₀(z)=Z₀+Z₁/2 and M₁(z)=Z₁+Z₀/2.
2. Under the uniform four assignments, **for each node i**, its overridden-treated and overridden-control means are 5/4 and 1/4. **For every i,k**, its linearization score equals (1/2)(2Z₀−1)(2Z₁−1). The variance of node 0's score is 1/4, covariance of the two scores is 1/4, and variance of their average is 1/4. Dropping covariance gives (1/4+1/4)/4=1/8<1/4. Explicitly, the covariance sum weighted by 1{Euclidean node distance≤1} and by (1/2)² is 1/8; the actual average-score variance is 1/4. **For each node**, score expectation is zero and variance 1/4, and the mean of its two override differences is 1.
3. **For every natural M>0**, in the replicated model: every node belongs to the field; **for all field points and z**, 0≤Y≤2; every node's circle is exactly {node−1,node+1}; **for every pair g and z**, its two means are Z_(g,0)+Z_(g,1)/2 and Z_(g,1)+Z_(g,0)/2; **for every node and z**, its spatial score equals the replicated product score. Under the uniform assignment law on all 2M nodes, the variance of (1/(2M))Σ_i φ_i is 1/[2(2M)], while (1/(2M))²Σ_i Var(φ_i)=1/[4(2M)].
4. **For every M>0, node i and Boolean b**, E[M_i(z^{i←b})]=bit(b)+1/4 under that same uniform law.
5. **For every natural M, node i and rational x**, membership in its replicated circle is equivalent to membership in the field and Euclidean distance exactly one after line embedding. **For every M and distinct nodes i,j**, their embedded distance is at least two (these statements permit M=0 but then have no node arguments).
6. **For every M>0, node i, assignments z,z' agreeing at both nodes of i's pair**, their circle means at i agree. **For every M>0**, the covariance sum truncated at embedded distance one, scaled by (1/(2M))², equals 1/[4(2M)].

## T6 — `SAP.P008a.T6`

1. **For every N, z, real node data M, real array D, real cutoff c**, assume c≥0, n₁≥1, n₀≥1, D_ii=0 for every i, and D_ij>c for every distinct i,j. Let X=(1,Z), H=(XᵀX)⁻¹. Then the Hájek contrast equals Σ_i w_i M_i; **for every i**, (HXᵀ)_(1,i)=w_i and the OLS residual equals the group residual. The (1,1) entry of H·OLSmeat·H equals hac(g,D,c), which equals Σ_i g_i², equals Σ_{treated}e_i²/n₁²+Σ_{control}e_i²/n₀², and equals hac(g,D,0).
2. **For every g:Fin 4→ℝ**, all distinct toy-node distances exceed 2/5; hac(g,toy-distance,2/5)=Σ_i g_i²=hac(g,toy-distance,0); **for every real t,critical**, the lower and upper endpoints t±critical·sqrt(hac) are identical at those two cutoffs.
3. **For every N, base:Fin N→ℝ, coefficient array a, real m₁,m₀, distinct i,j**, form M_i(z)=base_i+Σ_k a_ik Z_k and its linearization scores. Under the uniform law on assignments, Cov(φ_i,φ_j)=a_ij a_ji. No sign or locality conditions are imposed on a.
4. **For every N>0, base,a,m₁,m₀**, the variance of the average score is N⁻²[Σ_i Var(φ_i)+Σ_iΣ_{j≠i}a_ij a_ji]. **For every further D,c with c≥0, D_ii=0 and a_ij a_ji=0 whenever D_ij>c**, the covariance sum with kernel 1{D_ij≤c}, scaled by N⁻², equals that full variance.
5. **For every N, spatial P, real d,r,c, and array g_ik:ℝ²→ℝ**, assume measurable field, every radius-d circle has positive real mass and finite extended mass, g_ik(x)=0 whenever dist(node_k,x)>r **for all i,k,x in the entire plane**, and d+r≤c. Then **for every i,k with dist(node_i,node_k)>c**, A_i,d(g_ik)=0. No integrability of g is assumed separately, and no relationship of g to an additive outcome model or to the a array in the previous conjunct is imposed.

## T7 — `SAP.P008a.T7`

An unconditional conjunction concerning the two fixed labelled 40000-point models:

1. **For every i,j,k,z**, riskOutcome is 0 or 1. **For every i,j,z**, riskM=(β_i−321Z_i)/40000. **For every i,j,b**, its override mean under the uniform four-node assignment law is (β_i−321bit(b))/40000.
2. **For every j**, the node-average override difference and the observed Hájek contrast at z*=1100 both equal −321/40000. Summing four such effects gives −321/10000; 379/40000−7/400=−321/40000. Subtracting 321/10000 from 7/400 gives −73/5000<0. Four copies of −1 sum to −4, and **for every a,b∈[0,1]**, a−b≠−4.
3. The doubly averaged riskSamplingProbability under that uniform assignment law is 7/400 for false, 379/40000 for true, and their difference is −321/40000.
4. **For every i,j,k,z**, companion outcome is binary; **for every i,j,z**, its counting mean is 1−Z_i. **For every j**, its finiteAMR is −1, so their sum is −4; **for every a,b∈[0,1]**, a−b cannot equal that sum. The uniform assignment law is common Bernoulli(1/2) and gives z* mass 1/16; **for every j**, the companion's observed Hájek contrast at z* is −1, summing to −4.
5. **For every real radius weighting w:Fin 4→ℝ with each w_j≥0 and Σ_j w_j=1**, the weighted finiteAMR of the first model is −321/40000.

## T8 — `SAP.P008a.T8`

1. **For every N, spatial P, assignment law Q, real d**, assume N>0, F measurable, each radius-d circle has positive real mass and finite extended mass, **for every i,b,z with Q(z)≠0**, Y(·,z^{i←b}) is integrable on circle i, and **for every x∈F and every z**, Y(x,z) is 0 or 1. Then **for each Boolean b**, risk(Q,b,d)∈[0,1], and amr(Q,d)=risk(Q,true,d)−risk(Q,false,d).
2. **For every natural J, real arrays w,q₀,q₁**, assume w_j≥0, Σw=1, every q₀_j,q₁_j∈[0,1]. **For every real L,U such that L≤q₁_j−q₀_j≤U for every j**, both mixtures Σwq_b belong to [0,1]; their difference equals Σw(q₁−q₀), lies between L and U, and has absolute value≤1. J=0 cannot satisfy Σw=1.
3. **For every J>0 and arbitrary real q₀,q₁**, (Σq₁)/J−(Σq₀)/J=Σ(q₁−q₀)/J, and Σ(q₁−q₀)=J[Σ(q₁−q₀)/J].
4. **For every J, nonnegative w summing to one, and real t**, Σ_j t=Jt and Σ_j w_jt=t.
5. **For every natural n, monotone s:Fin(n+1)→ℝ, real q,m,x,y**, assume 0≤q≤1 and m>0. Then x≤y iff x/m≤y/m; |x|≤|y| iff |x/m|≤|y/m|; and quantile7(s/m,q)=quantile7(s,q)/m.
6. −19/625 divided by four is −19/2500; −321/10000 divided by four is −321/40000; 21/625 divided by four is 21/2500; −321/40000<−19/2500. The companion model's four finiteAMRs sum to −4 and cannot equal a−b for **any a,b∈[0,1]**.

## T9 — `SAP.P008a.T9`

1. **For every i,j**, bandwidth-model node distances are |2i−2j|. **For every node and each of its three radii**, its circle mass is exactly one, its extended mass is finite, and **for every z**, Y(·,z) is integrable there. **For every i,j,z**, its circle mean is 2i.
2. The short grid's index 0 and long grid's index 1 both equal 1/5. Assignment z*=0011 has two nodes in each arm. The circle-mean and distance identities are repeated. Its radius-1/5 Hájek contrast is four. Its regression-score archivedVariance with base cutoff 2/5 is one at position 1 and 1/2 at position 2. **For every i**, the score at node data (0,2,4,6) and z* is (1/2,−1/2,−1/2,1/2)_i.
3. **For every assignment z on the four toy nodes and every real node vector M with n₁,n₀ nonzero**, all squared toy-node distances are ≤32; archivedVariance of the regression score at cutoff 2/5 and position 6 is zero; **for every real a**, the corresponding width 2a sqrt(archivedVariance) differs from 869/250.

## T10 — `SAP.P008a.T10`

1. **For every N,z,real node vector M,real array D,real cutoff c with n₁,n₀ nonzero, and natural positions j,k**, physicalVariance at j equals hac(g,D,c) and equals physicalVariance at k, and Σ_i g_i=0. **If additionally D_il≤c for all i,l**, hac(g,D,c)=(Σ_i g_i)²=0. No positivity or metric assumptions on D or c are imposed here.
2. At the explicit score (1/2,−1/2,−1/2,1/2), D_ij=|2i−2j| and c=2/5, physicalVariance is one at positions 1 and 2.
3. **For every four-node z and real M with both arms nonempty**, hac(g,toy-distance,2/5)=Σ_i g_i²=hac(g,toy-distance,0), and archivedVariance(g,toy-distance,2/5,6)=0.

## T11 — `SAP.P008a.T11`

1. The first five numbers 1.491,1.550,1.550,1.691,1.714 sum to 7.996; adding 1.700,1.678,1.002 gives 12.376.
2. **For every real a,b,c,e,f**, respectively within 1/2000 (inclusive) of those five displayed numbers, their sum lies in [15987/2000,15997/2000]=[7.9935,7.9985], differs from 619/50=12.38 by strictly more than 1/200, and is strictly greater than 1595/200=7.975.
3. |12.376−12.38|<1/200. No rounding function is defined or quantified over.

## T12 — `SAP.P008a.T12`

1. **For every k∈Fin 5**, printedGrid(k) is outside the inclusive range. **For every f:Fin 5→ℝ**, its sum over the selected grid indices is zero. The three numbers −321/10000, −19/625 and 21/625 are all nonzero. Also 25/111>20/111.
2. **For every natural n, real array M:Fin(n+1)→Fin 5→ℝ, and q∈[0,1]**, **for every sample index z**, the sum of M(z,j) over selected printed-grid indices is zero, and the type-7 quantile at q of this resulting sample is zero. No statistical assumptions are needed because the selected set is empty.

## T13 — `SAP.P008a.T13`

The corrected index type has cardinality 41; its last grid value is 20/111. **For every k∈Fin 41**, correctedGrid(k) is in range iff 2≤k≤5. **For every real f on Fin 41**, its selected sum is f₂+f₃+f₄+f₅. **For every k∈Fin 40**, consecutive grid values differ by 1/222. Multiplying grid values 2,3,4,5 by 111 gives 1,3/2,2,5/2 respectively, and 1/222=(1/2)/111.

## T14 — `SAP.P008a.T14`

1. **For every natural N>0 and real arrays μ₁,μ₀,τ:Fin N→ℝ**, if **for every i**, τ_i=μ₁_i−μ₀_i, then (1/N)Σ_iτ_i=(1/N)Σ_i(μ₁_i−μ₀_i).
2. **For every real A**, A²=A iff A=0 or A=1.
3. [(3−0)+(7−2)]/2=4, 4·4=16, and 16≠4. There is no explicit spatial-model specialization of part 1 or explicit identification of A with that average in part 2; these are independent elementary identities.

## Blind semantic checks to carry into the comparison stage

The quantitative examples use positive-size finite types. The potentially dangerous totalizations are visible and have been recorded above: zero real denominators, extended-mass conversion, nonintegrable Bochner integrals, singular matrix inverse, empty counting circles, and the natural subtraction in the risk threshold. None is automatically ruled out by `SpatialModel` alone. Their individual theorem hypotheses, fixed examples, and relationship to the canonical claims remain to be checked in stage 2. An empty selected radius set is the explicit content of T12, rather than a hidden sample-space convention.
