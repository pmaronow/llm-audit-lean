# Blind mathematical reading

This file was written from `SAP/P045b/Defs*.lean`, `Defs/Part1`–`Part6`, and the two Challenge parts, before opening either `claims.json` or `record.json`. The Challenge contains 16 theorem stubs, each asserting its namesake `TxxStatement`; the stubs provide no proofs. Docstrings do not add hypotheses or conclusions.

## Common objects and conventions

* `Fin n` is the ordered set {0,…,n−1}; `Assignment n` is all Boolean vectors on it. True denotes treatment. Every unqualified finite sum or product runs over the entire indicated finite type. Finite sets have no repeated elements; lists can have repeats.
* A `Design Ω` is a function p:Ω→ℝ on a finite type, with p(ω)≥0 for every ω and Σω p(ω)=1. Thus a Design cannot exist on an empty Ω. No full support or independence is required. `expect p X` is Σω p(ω)X(ω), also defined algebraically over the displayed semirings. `prob p E` is Σω p(ω)1_E(ω). `condMean p E X` is Σω p(ω)1_E(ω)X(ω)/P(E). `variance p X` is E[(X−EX)²]; `momentVariance p X` is E[X²]−(EX)². These two variances agree for normalized probability masses.
* `average S x`=Σi∈S xᵢ/|S| and `mean x`=Σi xᵢ/|I|. Lean's field division is total: x/0=0. Consequently empty averages, conditional means of probability-zero events, and one-element sample variances have algebraic values unless the propositions exclude them. This convention must be checked separately at each use.
* `bit true`=1, `bit false`=0; `sign true`=1 and `sign false`=−1. `bernoulli p z`=∏ᵢ[p if zᵢ=true, otherwise 1−p]. `treatedCount z` counts true coordinates. `fixedAssignments n k` is the set having exactly k true coordinates; `crMass n k` is its uniform mass, zero off that set (identically zero if it is empty).
* For an exposure map D:{0,1}ⁿ×Fin n→Δ, `exposureProb p D i d` is P(Dᵢ=d). `observed D y z i`=yᵢ(Dᵢ(z)), so the outcome schedule factors through D by construction. Put πᵢ(d)=P(Dᵢ=d), H_d(z)=Σᵢ 1_{Dᵢ(z)=d} yᵢ(d)/πᵢ(d), and A_d(z)=Σᵢ 1_{Dᵢ(z)=d}/πᵢ(d). These are `htTotal` and the ratio denominator. `htContrast k l`=(H_k−H_l)/n. `effect y k l`=n⁻¹Σᵢyᵢ(k)−n⁻¹Σᵢyᵢ(l). `hajek d z` is the option `none` when A_d(z)=0, and `some (H_d(z)/A_d(z))` otherwise.
* For unrestricted outcomes yᵢ(z), `marginal p y i b`=E[yᵢ(Z)|Zᵢ=b]. `armMean y b z` is the sum of yᵢ(z) in arm b divided by its realized count; `armExists b z` means at least one such unit exists. `groupOverall y z`=n⁻¹Σᵢyᵢ(z). `coMembers i z`=Σ_{j≠i}bit(zⱼ).
* `withoutCoordinate i z` deletes coordinate i in the original order. Mathlib's `Fin.removeNth` is j↦z(i.succAbove j): `succAbove` skips i. `splitAssignment i` is the inverse of `Fin.insertNthEquiv`, hence z↦(zᵢ,withoutCoordinate i z).
* `InProbability p X a` means: for every real ε>0, P_{pₙ}(|Xₙ−aₙ|>ε)→0 as n→∞. The probability spaces may vary with n and are finite. This definition alone does not assert that its input masses are probability masses; the particular statements supply masses or Designs.
* `Network n` is a Boolean symmetric adjacency matrix with false diagonal. A `SimpleGraph` is an undirected loopless graph. Mathlib `SimpleGraph.edist u v : ℕ∞` is the infimum of lengths of walks from u to v: ordinary shortest-path distance when reachable, and ∞ otherwise. `pathDistance i j` is the finite natural distance |i−j|, embedded in ℕ∞.
* `neighborhood A i` is {i}∪{j:Aᵢⱼ=true}. `neighborhoodCount` counts its treated members. `badAllControl A z i` says this count is strictly less than the neighborhood size, i.e. at least one member is control, rather than every member being control.
* `separated d ε S` says d(s,t)≥ε for every distinct s,t∈S. `covers d ε S` says every v outside S has some s∈S with d(s,v)≤ε−1, where ε−1 is natural subtraction. `epsilonNet` is their conjunction. `marked d ε S` is every vertex within ε−1 of S (including centres when d(s,s)=0). `greedyRun d ε cs` says that, for each position k in the list, its entry is outside the marked set of the preceding k entries. The general graph theorem assumes ε≥1, so the subtraction has its ordinary intended meaning.
* `centreDraw d ε coded S` first forms R=V\marked(S). When `coded=true` and R={u}, it gives each v with index v≤u mass 1/(u+1), including marked vertices. Otherwise it is uniform on R and zero elsewhere. `traceMass cs` is zero unless every proper initial segment has not yet marked all vertices and the whole list has marked all vertices; otherwise it is the product of these successive draw masses. There is no `greedyRun` requirement on such a trace. `terminalCentres S` sums the masses of all finite terminating lists whose set of entries is S, including lists with repeats, over every natural list length. This is Mathlib's real `tsum`: an unconditional convergent sum, or zero if not summable. Summability is not asserted inside this definition.
* `nearestCentre d S v` sorts S by increasing distance to v, breaking ties by the vertex order, and returns the first element as an option; it is `none` for S empty. `clusterProb d S p z` is the Bernoulli(p) probability over Boolean centre-index vectors c on all n vertices that every vertex v has a nearest centre s and zᵥ=cₛ. Unused c-coordinates are summed out. `clusteredTreatment d coded p z` is Σ_S terminalCentres(d,3,coded,S) clusterProb(d,S,p,z). Thus its mixture identity is true by definition.
* For G groups of sizes n_g, `GroupAssignments n` is a vector of assignments, one per group. `firstStageSets G C` is all C-element subsets of Fin G. `selectedLaw n C q` is uniform over these subsets and independently uses group masses q_g for assignments in all groups, including unselected groups. `selectedMean C X` is C⁻¹Σ_{g∈S}X_g(z_g).
* `rawSampleVar S x`=Σ_{i∈S}(xᵢ−average(S,x))²/(|S|−1), with subtraction in ℝ. `treatedSet z` is its true coordinates. `directGroup a b z`=average(treatedSet,a)−average(complement,b). `droppedWithin a b z` adds sampleVar(treated,a)/treatedCount only if that count is ≥2, and sampleVar(control,b)/controlCount only if that count is ≥2; a smaller arm contributes zero. `directVarianceEstimate C a b` is (1−C/G)sampleVar(selected groups,directGroup)/C + Σ_{g selected}droppedWithin_g/(CG).
* For a Design S over regime vectors s∈{0,1}ᴳ, `hierarchyLaw n S ψ φ (s,z)`=S(s)∏_g Bernoulli(if s_g then ψ else φ)(z_g). `regimeGroups s high` selects groups with s_g=high. `hierarchyArm y high b` averages their arm means. `hierarchyDomain high b` requires this group set nonempty and arm b nonempty in every selected group. `hierarchyTarget y p b` averages E_p[y_gi(Z_g)|Z_gi=b], first equally within groups, then equally across all G groups. `hierarchyOverall` averages group overall means over a selected regime.
* For a schedule y_gi(own,high), `regimeMean y own high` averages first equally over each group's units and then equally over groups; `baselineMean b` is the same average of b_gi. `dilatedMarginal b` multiplies b_gi by 2 for (true,true), 5/4 for (false,true), 3/2 for (true,false), and 1 for (false,false).
* For Nc households, mediator maps m_i:{0,1}→{0,1} and schedules y_i:{0,1}×{0,1}→ℝ, `indirectHousehold`=mean_i[y_i(1,m_i(1))−y_i(0,m_i(0))], `contagion z`=mean_i[y_i(z,m_i(1))−y_i(z,m_i(0))], and `otherMechanisms z`=mean_i[y_i(1,m_i(z))−y_i(0,m_i(z))].

### General exposure-estimator definitions

These are used in T32 and T33. For a finite randomization type Ω, units i∈Fin N, exposure map f, outcome schedule y, supplied marginal weights w and joint weights q, write I_i^a(ω)=1_{f(ω,i)=a}. `exposureMarginal` is π_i^a=Σω pω I_i^a; `exposureJoint` is π_ij^{ab}=Σω pω I_i^a I_j^b. `weightedTerm` is I_i^a y_i^a/w_i^a, implemented by an if branch. `weightedMean` is N⁻¹Σ_i of these terms; `weightedContrast` T_ab is their difference. `exposureEffect` is N⁻¹Σ_i(y_i^a−y_i^b).

`totalVarianceEstimate` U_a sums over **ordered** pairs (i,j), including diagonals. If q_ij^{aa}>0 it contributes I_i^a I_j^a y_i^a y_j^a[1/(w_i^a w_j^a)−1/q_ij^{aa}]. Additionally, when i≠j and q_ij^{aa}=0 it contributes I_i^a(y_i^a)²/(2w_i^a)+I_j^a(y_j^a)²/(2w_j^a). All other contributions are zero.

`totalCovarianceEstimate` C_ab sums over ordered pairs including diagonals. If q_ij^{ab}>0 its contribution is I_i^a I_j^b y_i^a y_j^b[1/(w_i^a w_j^b)−1/q_ij^{ab}]. When q_ij^{ab}=0 it instead contributes −I_i^a(y_i^a)²/(2w_i^a)−I_j^b(y_j^b)²/(2w_j^b). A negative q would give zero, but actual q's in T32/T33 are nonnegative. `varianceEstimate` V_ab=(U_a+U_b−2C_ab)/N².

`zeroSurplus` Q_ab is N⁻² times the sum of (y_i^a+y_j^a)²/2 over ordered i≠j with π_ij^{aa}=0, plus (y_i^b+y_j^b)²/2 over ordered i≠j with π_ij^{bb}=0, plus (y_i^a−y_j^b)² over **all** ordered pairs with π_ij^{ab}=0.

For a simulation table with R rows, `exposureCount` and `jointCount` count the corresponding indicators. `smoothedWeight`=(exposureCount+1)/(R+1). `smoothedJoint aa`=(jointCount+1_{i=j})/(R+1), while `smoothedJoint ab`=jointCount/R if a≠b.

## SAP.P045b.T17

For every n>0, finite decidable exposure type Δ, Design p on assignments, map D, real schedule y, distinct k,l∈Δ, with π_i(k)>0 and π_i(l)>0 for every i, all of the following hold:

1. For every assignment z, if no unit has exposure k, then H_k(z)=0, HTcontrast(z)=−H_l(z)/n, A_k(z)=0, and the Hájek option is `none`.
2. E H_k=Σ_i y_i(k), and E HTcontrast=effect(y,k,l).
3. If P(E)>0, where E means at least one unit has exposure k, then E[H_k|E]=Σ_i y_i(k)/P(E).
4. If also P(Eᶜ)>0 and Σ_i y_i(k)≠0, that conditional mean is not Σ_i y_i(k).
5. The numerical identity 20/(20/45)=45 holds in ℝ.

The empty-cell assertions range over every assignment, even a mass-zero assignment. No design-specific empty-cell probability or numerical example is asserted beyond the scalar identity.

## SAP.P045b.T18

For every n≥0 and i∈Fin(n+1): (a) for every z and j∈Fin n, deleting i gives z_j if j<i and z_{j+1} otherwise; (b) for all z,z′ agreeing off i, their deletions agree; (c) z↦(z_i,delete_i z) is bijective onto Bool×Assignment n; (d) for every function y on full assignments, there exists a **unique** real function f on that product with f(z_i,delete_i z)=y(z) for every z. In addition, for every four-coordinate vector z, deleting zero-based coordinate 2 gives [z_0,z_1,z_3].

## SAP.P045b.T19

For every n,K∈ℕ with n≥2, every real ψ with 0<ψ<1 and K=ψn, every assignment z with exactly K treated coordinates, and every unit i: the treated peer count is K−bit(z_i); if i is treated it is ψn−1, its gap below ψ(n−1) is 1−ψ, and it is strictly smaller than ψ(n−1); if i is control it is ψn. Additionally every three-unit assignment with two treated has one treated peer per treated unit and two per control unit, and (2/3)(3−1)=4/3 in ℝ. K−bit(z_i) and ψn−1 are real subtraction.

## SAP.P045b.T20

On the path with vertices 0,…,8: no finite subset S has both d(s,t)≤3 for **all** s,t∈S (including equal pairs) and the property that every vertex outside S is within 2 of some centre. Exactly 13 subsets instead have separation ≥3 and that covering property. For every S, being such a corrected 3-net is equivalent to membership in this exact family:

{1,6}, {2,6}, {2,7}, {0,3,6}, {0,3,7}, {0,3,8}, {0,4,7}, {0,4,8}, {0,5,8}, {1,4,7}, {1,4,8}, {1,5,8}, {2,5,8}.

## SAP.P045b.T21

For every n, ε∈ℕ with ε≥1 and every simple graph on Fin n:

1. For every ε-separated S, coverage is equivalent to: for each v outside S, inserting v destroys separation.
2. For every list cs satisfying `greedyRun`, cs has no duplicates, length≤n, its set is ε-separated, and if it marks all vertices its set is an ε-net.
3. There exists such a greedy list marking every vertex, and there exists an ε-net.

It also repeats T20's exact count and complete list of the 13 corrected 3-nets on the nine-vertex path. Disconnected graphs and n=0 are allowed; ε=0 is excluded. No runtime, distribution on nets, or nearest-centre clustering guarantee is asserted.

## SAP.P045b.T22

For each n≥0 let m=n+1, let Z have independent fair Boolean coordinates on m units, let T_m=m⁻¹Σ_i sign(Z_i), let F(Z)=3/2 if Z_0=true and 1/2 otherwise, let Vhat=F²/m, and SEhat=√Vhat. For **every** n:

* ET_m=0, Var(T_m)=1/m, and for every ε>0, P(|T_m|>ε)≤1/(mε²).
* EF=1, EF²=5/4, SEhat(Z)=F(Z)/√m for every Z, and ESEhat=1/√m=√Var(T_m).
* EVhat−1/m=1/(4m)>0. For every Z, |Vhat−1/m|=|F²−1|/m≤5/(4m).
* Vhat/(1/m)=F² for every Z, takes only 1/4 and 9/4, each with probability 1/2, and P(|Vhat/(1/m)−1|>1/2)=1.

As n→∞, T_m→0 in probability, Vhat−1/m→0 in probability, but Vhat/(1/m) does **not** converge to 1 in probability. The deterministic bound 5/(4m) tends to zero. These are statements about this defined witness, not any other estimator.

## SAP.P045b.T23

The theorem is the conjunction of:

1. 3311/2660=473/380; each of 4594/4532, 1033/1045, 3407/3666, 841/838 is in [1−.071,1+.071]; .244<473/380−1<.245; and .164<2509/2155−1<.165.
2. The entire T22Statement above.
3. For every family of finite Ω_n, every sequence of Designs p_n, and every pair of real random variables T_n,Vhat_n, **assuming** Var(T_n)>0 for every n, Vhat_n≥0 pointwise, Var(T_n)→0, and E√Vhat_n−√Var(T_n)→0, one has Vhat_n−Var(T_n)→0 in probability. No relative consistency is concluded here.
4. On a fair Bool, Var(sign)=1, E√[(3/2 if true else 1/2)²]=1, and the probability that this squared factor differs from 1 by more than 1/2 is 1. The corresponding constant sequence of squared factors does not converge in probability to 1.
5. For every positive integer M and every nonnegative real vector s of length M, (mean s)²≤mean(s²).
6. Under the same hypotheses and every real sd>0, (mean(s)/sd)²≤mean(s²)/sd².

## SAP.P045b.T24

First, for every G>0, every group-size vector with each n_g>0, and every **unrestricted real** baseline vector b_gi, let B be its equally weighted average of group averages and let μ(own,high) be the averages of the four dilated schedules. Set Dψ=μ(1,1)−μ(0,1), Dφ=μ(1,0)−μ(0,0), I=μ(0,1)−μ(0,0), To=μ(1,1)−μ(0,0), and O=(2/3)μ(1,1)+(1/3)μ(0,1)−[(1/3)μ(1,0)+(2/3)μ(0,0)]. Then Dψ=3B/4, Dφ=B/2, I=B/4, To=B, O=7B/12, and To=Dψ+I. If B>0 then Dφ/Dψ=2/3 and Dφ<Dψ. If B≠0 then To−I≠Dφ.

Second, for every such group structure and **every** real schedule y_gi(own,high), μ(1,1)−μ(0,0)=[μ(1,1)−μ(0,1)]+[μ(0,1)−μ(0,0)]. Third, for every such baseline vector, the high and low weighted means are 7B/4 and 7B/6, respectively, and To−I=3B/4.

## SAP.P045b.T25

This is **the negation of a conjunction** A∧B, so it asserts that at least one of A,B fails. It does not assert ¬A∧¬B or negate every component separately.

A quantifies in order over every n>0, p∈(0,1), arbitrary real outcome schedule y_i(z), and Boolean arm b, and claims E_p[armMean_b | arm b nonempty]=n⁻¹Σ_i E_p[y_i(Z)|Z_i=b]. The conditioning event has positive probability for these parameters.

B quantifies in order over every G>0, every positive group-size vector, **every** Design S on group regimes, ψ,φ∈(0,1), and every arbitrary real group outcome schedule. With the hierarchy definitions above it conjoins:

1. For all high,b, whenever hierarchyDomain(high,b) has positive probability, the conditional expectation of hierarchyArm(high,b) equals hierarchyTarget(if high then ψ else φ,b).
2. For each high, conditioned on both arm domains for that regime (and assuming the event has positive probability), the arm-mean difference has expectation μ(p_high,1)−μ(p_high,0).
3. Conditioned on the two control-arm domains for high and low regimes, when that event is positive, the difference of their arm means has expectation μ(ψ,0)−μ(φ,0).
4. With the high treated-arm and low control-arm domains, the corresponding difference has expectation μ(ψ,1)−μ(φ,0).
5. Conditioned on both regime group sets being nonempty, when positive, the difference of hierarchyOverall means has expectation equal to the across-group average of group/unit E_ψ[y] minus its E_φ counterpart.

Here μ is hierarchyTarget. No balance or exchangeability assumption is imposed on S. The asserted negation can be witnessed by failure of A alone, regardless of B.

## SAP.P045b.T26

The theorem negates the following universal assertion: for every G,C with 2≤C≤G; every n_g,m_g with 0<m_g<n_g; and every pair of real schedules a_gi,b_gi, use `selectedLaw` with independent fixed-count uniform masses crMass(n_g,m_g). Let T be the average of selected groups' directGroup estimators and Vhat be `directVarianceEstimate` (with small-arm contributions dropped). Then (i) if there exists **one common real d** with a_gi=b_gi+d for all g,i, E Vhat=Var T; and (ii) Var T≤E Vhat. The negation only establishes a counterexample to this conjunction. Singleton treated or control arms are permitted; no support, denominator, or variance positivity assumptions are added.

## SAP.P045b.T27

It is not true that for every natural n, every symmetric loopless Boolean graph A, every assignment z, and every i∈Fin n, [at least one member of the closed neighborhood of i is control] is equivalent to [every member is control]. Equivalently some such graph, assignment, and actual vertex falsify that equivalence. The n=0 case cannot supply a vertex and cannot witness the negation.

## SAP.P045b.T29

It is not true that, for every n>0, simple graph G on Fin n, and p∈[0,1], the coded sampler at ε=3 satisfies **all three** of: total terminal-centre mass=1; terminal mass of separated-and-covering 3-nets=1; and, for every assignment z, its clusteredTreatment mass equals the defining mixture over terminal-centre sets. The third assertion is definitionally true, so the negation must arise from one of the first two. The definition includes singleton-remainder draws from marked vertices and every finite retry trace; no summability or normalization hypothesis is assumed by the proposition.

## SAP.P045b.T30

For every n>0, finite decidable Δ, Design p on Assignment n, D, y, and k with π_i(k)>0 for all i, E H_k=Σ_i y_i(k). Additionally, for **every** l∈Δ, if π_i(l)>0 for all i then E HTcontrast(k,l)=effect(y,k,l). Distinctness k≠l is not required. No simulated-probability result is asserted.

## SAP.P045b.T31

For every Nc>0, every Boolean mediator schedule m_i(z), and every real outcome schedule y_i(z,m), indirectHousehold=contagion(1)+otherMechanisms(0) and also =contagion(0)+otherMechanisms(1). Moreover for every i, if m_i(1)=m_i(0), then for **every** Boolean z, the individual contribution y_i(z,m_i(1))−y_i(z,m_i(0))=0. This is an algebraic potential-outcome statement; it imposes no randomization, identification, or disease-model assumptions.

## SAP.P045b.T32

There exist a type E, a decidable equality on E, a bijection labels:Fin 4≃E, a table f with 66 rows and 12 unit columns, rational marginal weights w indexed also by an omitted row t, and rational joint weights q indexed also by t, with all facts below. E is necessarily a four-element type; its existential quantification cannot create an empty exposure type. Put k=labels(2), l=labels(3), y_i(a)=1, and p_r=1/66. Unit i is in clique floor(i/4); `cliqueAdj` joins distinct units in the same clique. `cliquePairs r` lists all unordered pairs of distinct units in lexicographic order; `cliqueAssignments r` treats exactly that pair. `retainedAssignments t` lists every such assignment except t in inherited order. `fourExposure` labels treated with a treated peer by 0, treated without one by 1, control with one by 2, and control without one by 3. Define T_t(r) and V_t(r) as the weightedContrast and varianceEstimate with supplied w_t,q_t.

1. f is exactly this four-exposure table. Every 12-vector has treated count 2 iff it is some cliqueAssignments r; the enumeration is injective. The graph is symmetric, loopless, and every vertex has a neighbor. Each retained table is injective and excludes its omitted assignment.
2. For every t,i,a, w_t(i,a) is (count of a in the 65 retained rows+1)/66. For every t,i,j and a,b∈{k,l}, q_t(i,j,a,b) is the smoothedJoint of those 65 rows: same labels have (jointCount+1_{i=j})/66; different labels have jointCount/65. q outside {k,l}² is unconstrained. All relevant marginal weights are strictly positive. The true exposure effect is zero.
3. For every i, the full-table counts of k,l are 27,28, hence probabilities 9/22,14/33, both positive. For every distinct i,j, the joint counts (kk,ll,kl) are (17,28,0) if in the same clique and (9,6,15) otherwise.
4. Each row with a same-clique treated pair has k,l counts 2,8; a cross-clique pair gives 6,4. There are 18 same-clique rows and 48 cross-clique rows.
5. With exact full-table marginals and joints, the contrast is −220/189 on the first kind of row and 55/126 on the second. Its expectation is 0, its moment variance is 6050/11907, and the exact-weight variance estimator's expectation is also 6050/11907.
6. For each Boolean `included`, define a joint law on (t,r). If false it gives every pair mass 1/4356; if true it gives diagonal pairs zero and off-diagonal pairs 1/4290. These are nonnegative normalized laws. (`cliqueObservationMass`, although unused here, is the conditional row law: uniform over all 66 rows in the first regime and over the 65 rows unequal to t in the second.) The exact moments are:

| Law | E T_t(r) | Var T_t(r) | E V_t(r) | E V−Var T |
|---|---|---|---|---|
| included=false | −67/53592 | 113448938731/232640299584 | 1040129476423/2326402995840 | −953130413/23499020160 |
| included=true | −67/52780 | 11375808887/23342482800 | 4673362763/10414338480 | −20161943/522324075 |

For both laws, E V_t(r)<Var T_t(r) and E V_t(r)<6050/11907.

7. For **every fixed t**, with r independently uniform over all 66 rows, the moment variance, expected variance estimate, and gap are:

| omitted pair kind | Var_p T_t | E_p V_t | E_p V_t−Var_p T_t |
|---|---|---|---|
| same clique | 2810528137/5767941312 | 267260522663/634473544320 | −1551761941/23499020160 |
| cross clique | 937589375/1922647104 | 4830430961/10574559072 | −72513467/2349902016 |

Each gap is strictly negative. For every t there exists a permutation e of the 12 vertices preserving all adjacencies and satisfying cliqueAssignments(t)(e(i))=cliqueAssignments(r₀)(i) for every i, where r₀=0 for same-clique and r₀=3 for cross-clique omitted pairs.

8. Finally, for each included value, embed the rational joint mass and all weights in ℝ and recompute T,V with real outcomes identically 1. This real mass is pointwise nonnegative with total 1, and E V<Var T and E V<6050/11907 still hold.

There are no external hypotheses; this is one fully specified existential finite witness, not a universal assertion about all finite simulation procedures.

## SAP.P045b.T33

For every finite type Ω, every decidable exposure type D (not required finite), and N>0, then every Design P on Ω, map f:Ω×Fin N→D, real outcome schedule y, and distinct labels a,b with π_i^a>0 and π_i^b>0 for all i: using **exact** π_i and π_ij as the weights in the estimators defined above,

E V_ab−[E T_ab²−(E T_ab)²]=Q_ab;

Var(T_ab)≤E V_ab; and E T_ab=N⁻¹Σ_i(y_i^a−y_i^b).

The Q_ab identity includes every structural-zero joint specified above, including cross-label diagonal pairs. Positive pairwise joint probabilities are not assumed. Ω cannot be empty because P is a Design; D contains two distinct specified labels. Finite Ω ensures every variable is integrable; N and all used marginal denominators are nonzero.

## Mathlib boundary checked

The coordinate definitions were followed to `Mathlib/Data/Fin/Tuple/Basic.lean` (`removeNth`, line 846; `insertNthEquiv`, line 1066). Graph distance was followed to `Mathlib/Combinatorics/SimpleGraph/Metric.lean`, line 55. Infinite summation was followed to the `to_additive` definition/documentation of `tsum` in `Mathlib/Topology/Algebra/InfiniteSum/Defs.lean`: it is a real unconditional sum when summable, otherwise zero. The other operations used above are finite sums/products, finite filters, ordinary field arithmetic, Boolean cases, Euclidean square root, and ordinary convergence in ℝ; there is no measure-theoretic integral or limsup hidden in these SAP definitions.
