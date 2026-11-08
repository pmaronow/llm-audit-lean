# Blind reading of the Lean statements

Written before opening `claims.json` or `record.json`. Sources read: all supplied Defs and Challenge Lean files, and the relevant Mathlib definitions. This records mathematical content, not acceptance of the accompanying docstrings.

## Conventions and complete definition dictionary

`Fin n` is the set {0,...,n-1}; an assignment is a function from that set to {false,true}. All sums over finite types are over every element, including assignments of zero mass. A `Design` on a finite set Ω is a real function P with P(ω) ≥ 0 for every ω and sum P = 1. Write E_P X = sum P(ω)X(ω), P(A) = sum over A of P(ω), E_P[X | A] = (sum over A of P(ω)X(ω))/P(A), and Var_P X = E_P[(X-E_P X)^2]. `momentVariance` is E_P[X²]-(E_P X)², equal to variance for a normalized law. Definitions of expectation and moment variance are also used over the rationals.

For a finite set S, av_S x = (sum over S of x)/|S|. `mean` is the corresponding mean over the whole finite index type. These use field division, so an empty-set mean and any x/0 are 0 in Lean. Conditional means are similarly totalized when the conditioning event has zero mass. Below, statements explicitly supply positive denominators except for off-support configurations, totalized auxiliary functions, or domains described individually. `Real.sqrt` is the nonnegative real square root (and 0 on negative arguments).

For a real p, B_p(z) = product_i (p if z_i=true, else 1-p). This definition alone does not restrict p to [0,1]. `treatedCount` is the number of true coordinates; `fixedAssignments n K` is the finite set of assignments with exactly K true coordinates; `crMass n K` is uniform on that set and zero elsewhere. `bit` is 1 on true and 0 on false. The peer count `coMembers i z` is sum_{j≠i} bit(z_j), a real number.

Given an exposure map D(z,i), a schedule y(i,d), and mass P, put π_i(d)=P(D_i=d), Y_i(z)=y(i,D_i(z)), H_d(z)=sum_i 1{D_i(z)=d}Y_i(z)/π_i(d), C_{k,l}(z)=(H_k(z)-H_l(z))/n, and τ_{k,l}=n^{-1}sum_i(y(i,k)-y(i,l)). The Hajek value is `none` if sum_i 1{D_i=d}/π_i(d)=0, otherwise `some` of H_d divided by that sum. Thus `none` represents undefinedness, rather than a real zero ratio.

For unrestricted assignment-dependent outcomes y(i,z), the marginal outcome μ_i(b) is E[y(i,Z) | Z_i=b]. The arm mean A_b(z) is sum_{i:z_i=b} y(i,z) divided by the number of those i. `armExists b` is the event that this number is positive. The overall group outcome is n^{-1}sum_i y(i,z).

`withoutCoordinate i z` deletes coordinate i and preserves the order of all others: its jth coordinate is z_j for j<i, and z_{j+1} otherwise. Mathlib defines `Fin.removeNth` as composition with `Fin.succAbove`; `succAbove` inserts the missing index by that exact rule. `splitAssignment i` is the bijection z ↦ (z_i,withoutCoordinate i z), the inverse of Mathlib's coordinate insertion equivalence.

`InProbability P X a` means: for every real ε>0, P_n(|X_n-a_n|>ε) tends to 0 as n tends to infinity through natural numbers. The finite sample space may vary with n. `Filter.Tendsto ... atTop (nhds 0)` is an ordinary sequence limit, not a limsup.

A `Network n` is a symmetric, loopless Boolean adjacency relation. Its closed neighborhood N[i] consists of i and all vertices adjacent to i. `neighborhoodCount` counts treated vertices in N[i]. `badAllControl` means that this count is strictly less than |N[i]|; equivalently, at least one closed-neighborhood vertex is control, not that all are control.

For a distance d valued in the extended natural numbers ℕ∪{∞}, `separated d ε S` says every two DISTINCT members of S have distance at least ε. `covers d ε S` says each v OUTSIDE S has distance ≤ ε-1 from some member of S; ε-1 is natural-number subtraction, truncated at zero. `epsilonNet` is the conjunction. `marked d ε S` consists of ALL vertices within distance ε-1 of a member of S. A `greedyRun` is a finite ordered list whose kth entry is unmarked by the set of its preceding k entries, for every k from 0 to length-1. `pathDistance i j` is |i-j| on the labelled path. Mathlib `SimpleGraph.edist` is the infimum of lengths of walks, hence the shortest path length, with ∞ for disconnected vertices. In theorems using a variable ε, ε≥1 is explicit.

The sampler definitions are more general than a greedy run. For centre set S let R=V\marked(S). With `coded=true` and |R|=1, writing u for its unique element, `centreDraw(S,v)` is 1/(u+1) for EVERY label v≤u, and 0 otherwise. In all other cases it is 1/|R| if v∈R and 0 otherwise. The default in `head?.getD v` is irrelevant in the singleton case. A list's `traceMass` is its product of successive draw factors if every proper prefix is not fully marked and the final set is fully marked, and 0 otherwise. Repeated centres and selections of marked vertices are allowed by this trace test. `terminalCentres(S)` sums these masses over ALL finite lists with underlying set S: explicitly a real `tsum` over lengths t≥0, and a finite sum over all functions Fin t→V at each length. Mathlib's real `tsum` is the sum if summable, and 0 otherwise; summability is not a premise in T29. `nearestCentre(S,v)` sorts S by distance to v, breaking ties by smaller vertex label, and returns its first member as an Option; it returns none for empty S. `clusterProb(S,p,z)` is B_p's mass of centre-label assignments c for which every vertex v has a nearest centre s and z_v=c_s. `clusteredTreatment(d,coded,p,z)` is, BY DEFINITION, sum over all centre sets S of terminalCentres(d,3,coded,S) times clusterProb(d,S,p,z).

For two-stage fixed-count designs: there are G groups of sizes n_g. `firstStageSets G C` is all C-element subsets of the G groups. `selectedLaw` puts uniform mass on such a subset S and independently draws assignments in ALL groups with masses q_g: law(S,z)=1{|S|=C}/binom(G,C) times product_g q_g(z_g). `selectedMean C X` is C^{-1}sum_{g∈S}X_g(z_g). For a fixed group, treated set T={i:z_i=true}; `directGroup a b` is av_T a - av_{Tᶜ} b. Write s²_S(x)=sum_{i∈S}(x_i-av_S x)²/(|S|-1), where subtraction in this denominator is REAL. `droppedWithin(a,b,z)` is s²_T(a)/|T| if |T|≥2 (else 0), plus s²_{Tᶜ}(b)/|Tᶜ| if |Tᶜ|≥2 (else 0). The direct variance estimate is

    [(1-C/G)/C] s²_S(g ↦ directGroup_g(z_g))
       + [1/(CG)] sum_{g∈S} droppedWithin_g(z_g).

For hierarchical Bernoulli designs, s is a Boolean assignment of regimes to G groups with arbitrary design S. Independently conditional on s, group g has assignment mass B_ψ if s_g=true and B_φ otherwise. This joint mass is `hierarchyLaw`. For a regime h, R_h={g:s_g=h}. `hierarchyArm y h b` is av_{g∈R_h} A_{g,b}; `hierarchyDomain h b` is R_h nonempty AND every group in R_h has at least one b unit. `hierarchyTarget y p b` is G^{-1}sum_g n_g^{-1}sum_i E_{B_p}[y_g(i,Z_g)|Z_{gi}=b]. `hierarchyOverall y h` is av_{g∈R_h} n_g^{-1}sum_i y_g(i,z_g).

`regimeMean y b h` is G^{-1}sum_g n_g^{-1}sum_i y(g,i,b,h); this weights groups equally. `baselineMean b` is the same two-level mean of b(g,i). `dilatedMarginal b` is 2b for (own,high)=(true,true), (5/4)b for (false,true), (3/2)b for (true,false), and b for (false,false).

For a finite arbitrary assignment/sample space Ω, exposure labels D, N units, map f, schedule y, weights w, and joint weights q, define I_i^a(ω)=1{f(ω,i)=a}. The generic weighted mean is N^{-1}sum_i I_i^a y_i(a)/w_i(a); weighted contrast T is the a mean minus the b mean. Exact marginals m_i(a)=sum_ω P(ω)I_i^a and joints J_ij(a,b)=sum_ω P(ω)I_i^a I_j^b. `exposureEffect` is N^{-1}sum_i(y_i(a)-y_i(b)). All double sums below are ORDERED pairs, including diagonals unless excluded:

    V_a = sum_ij [ 1{q_ij(a,a)>0} I_i^a I_j^a y_i(a)y_j(a)
                            (1/(w_i(a)w_j(a))-1/q_ij(a,a))
                   + 1{i≠j and q_ij(a,a)=0}
                       (I_i^a y_i(a)²/(2w_i(a))+I_j^a y_j(a)²/(2w_j(a))) ]; 
    C_ab = sum_ij [ 1{q_ij(a,b)>0} I_i^a I_j^b y_i(a)y_j(b)
                            (1/(w_i(a)w_j(b))-1/q_ij(a,b))
                    - 1{q_ij(a,b)=0}
                       (I_i^a y_i(a)²/(2w_i(a))+I_j^b y_j(b)²/(2w_j(b))) ];
    Vhat = (V_a+V_b-2C_ab)/N².

These are branch formulas: the 1/q term is used only in the q>0 branch. `zeroSurplus` is

    [ sum_{i≠j:J_ij(a,a)=0}(y_i(a)+y_j(a))²/2
      + sum_{i≠j:J_ij(b,b)=0}(y_i(b)+y_j(b))²/2
      + sum_{ij:J_ij(a,b)=0}(y_i(a)-y_j(b))² ]/N².

For a table f of R exposure assignments, `exposureCount` counts rows with a given unit's exposure and `jointCount` counts rows with both specified exposures. `smoothedWeight` is (count+1)/(R+1). `smoothedJoint` is (joint count+1{i=j})/(R+1) if the two labels are equal, and joint count/R if they differ.

Household definitions: for Nc units, a Boolean mediator m_i(z) and real outcome y_i(z,mediator), indirectHousehold is mean_i[y_i(true,m_i(true))-y_i(false,m_i(false))]. Contagion(z) is mean_i[y_i(z,m_i(true))-y_i(z,m_i(false))]. OtherMechanisms(z) is mean_i[y_i(true,m_i(z))-y_i(false,m_i(z))].

## SAP.P045b.T17

For every natural n>0, every finite exposure type Δ with decidable equality, every design P on all n-unit assignments, every map D, every real exposure schedule y, and every ordered pair k,l of DISTINCT labels, assume π_i(k)>0 and π_i(l)>0 for EVERY unit. Then jointly:

1. For EVERY assignment z, if no unit has exposure k, H_k(z)=0, C_{k,l}(z)=-H_l(z)/n, its Hajek denominator is 0, and its Hajek result is none.
2. E H_k=sum_i y_i(k), and E C_{k,l}=τ_{k,l}.
3. If A={some unit has exposure k} has positive mass, E[H_k|A]=sum_i y_i(k)/P(A).
4. If additionally A's complement has positive mass and sum_i y_i(k)≠0, that conditional mean differs from sum_i y_i(k).
5. The real arithmetic identity 20/(20/45)=45.

The empty-cell assertion also covers zero-probability assignments; existence of an empty cell is not an unconditional premise.

## SAP.P045b.T18

For every n≥0 and every index i∈Fin(n+1), jointly: (i) for every assignment z and every j∈Fin n, deletion has the coordinate formula above; (ii) for every z,z' agreeing on all coordinates other than i, their deletions agree; (iii) z↦(z_i,delete_i z) is bijective; (iv) for EVERY real function y on assignments there exists a UNIQUE real function f on Bool×Assignment n such that for EVERY z, f(z_i,delete_i z)=y(z). Separately, for EVERY four-coordinate z, deleting coordinate 2 yields [z_0,z_1,z_3]. Zero-based indexing is used.

## SAP.P045b.T19

For every natural n,K with n≥2, every real ψ with 0<ψ<1 and K=ψn, every assignment z with exactly K treated units, and every i, peer count=K-bit(z_i). If z_i=true, peer count=ψn-1, ψ(n-1)-peer count=1-ψ, and peer count<ψ(n-1). If z_i=false, peer count=ψn. Additionally, for every three-unit assignment of treated count 2, every treated unit has one treated peer and every control unit has two; (2/3)(3-1)=4/3.

## SAP.P045b.T20

Jointly: (i) EVERY subset S of the nine labelled vertices 0,...,8 fails the conjunction of pairwise distances ≤3 (including identical pairs) and coverage of every outside vertex within distance 2; (ii) exactly 13 subsets are 3-separated and cover outside vertices within distance 2; (iii) for EVERY S, that latter property holds if and only if S belongs to the following EXACT list:

    {1,6}, {2,6}, {2,7}, {0,3,6}, {0,3,7}, {0,3,8},
    {0,4,7}, {0,4,8}, {0,5,8}, {1,4,7}, {1,4,8}, {1,5,8}, {2,5,8}.

## SAP.P045b.T21

For every natural n,ε with ε≥1, and every simple graph G on Fin n (including disconnected and empty graphs), jointly:

1. For EVERY separated S, S covers if and only if EVERY v outside S makes S∪{v} fail separation. This is maximality under addition of a single vertex.
2. For EVERY finite list cs, IF it is a greedy run, THEN it has no repeats, length≤n, its underlying set is separated, and IF its marked set is all vertices THEN its underlying set is an ε-net.
3. There EXISTS a greedy finite list with all vertices marked, and there EXISTS an ε-net.

Separately, the count 13 and exact nine-path set characterization in T20 are repeated. No random-draw probability guarantee is asserted here.

## SAP.P045b.T22

For each natural n let N=n+1, let Z consist of N independent fair bits, let T_N=N^{-1}sum_i sign(Z_i), with sign(true)=1 and sign(false)=-1, let F_N=3/2 if Z_0=true and 1/2 otherwise, Vhat_N=F_N²/N, and SEhat_N=sqrt(Vhat_N). For EVERY n, jointly:

* E T_N=0; Var(T_N)=1/N; for EVERY ε>0, P(|T_N|>ε)≤1/(Nε²).
* E F_N=1; E F_N²=5/4; for EVERY assignment, SEhat_N=F_N/sqrt(N); E SEhat_N=1/sqrt(N)=sqrt(Var(T_N)).
* E Vhat_N-1/N=1/(4N)>0.
* P(|Vhat_N/(1/N)-1|>1/2)=1.
* For EVERY assignment |Vhat_N-1/N|≤5/(4N).
* P(Vhat_N/(1/N)=1/4)=P(Vhat_N/(1/N)=9/4)=1/2.
* For EVERY assignment, Vhat_N/(1/N)=F_N², |Vhat_N-1/N|=|F_N²-1|/N, and the ratio belongs to {1/4,9/4}.

As n tends to infinity: T_N→0 in probability; Vhat_N/(1/N) does NOT tend to 1 in probability; Vhat_N-1/N→0 in probability; and the deterministic bound 5/(4N) tends to 0. There are no hypotheses identifying these random variables with a particular implemented estimator.

## SAP.P045b.T23

This is a conjunction of:

1. 3311/2660=473/380; EACH of 4594/4532,1033/1045,3407/3666,841/838 lies in [1-71/1000,1+71/1000]; 244/1000<473/380-1<245/1000; 164/1000<2509/2155-1<165/1000.
2. ALL of T22.
3. For EVERY sequence of finite sample spaces Ω_n, EVERY design P_n on each Ω_n, and EVERY pair of real statistics T_n,Vhat_n, IF for EVERY n Var_{P_n}(T_n)>0, for EVERY n,ω Vhat_n(ω)≥0, Var(T_n)→0, and E sqrt(Vhat_n)-sqrt(Var(T_n))→0, THEN Vhat_n-Var(T_n)→0 in probability. This is ABSOLUTE mean-SE agreement and ABSOLUTE variance consistency; no ratio convergence occurs in this implication.
4. On one fair Boolean sample space, sign has variance 1; E sqrt(F²)=1 for F=3/2 or 1/2 by the bit; P(|F²-1|>1/2)=1; and the sequence with this same law and statistic at every n does not converge in probability to 1.
5. For EVERY natural M>0 and every nonnegative real vector s of length M, (mean s)²≤mean(s²).
6. For EVERY such M,s, and EVERY real sd>0, (mean(s)/sd)²≤mean(s²)/sd².

## SAP.P045b.T24

For EVERY G>0, EVERY positive vector of group sizes n_g, and EVERY real baseline array b, write B for its equally group-weighted mean, and μ(b,h) for the mean of the four dilated outcomes defined above. Define Dψ=μ(true,true)-μ(false,true), Dφ=μ(true,false)-μ(false,false), I=μ(false,true)-μ(false,false), To=μ(true,true)-μ(false,false), and O=(2/3)μ(true,true)+(1/3)μ(false,true)-(1/3)μ(true,false)-(2/3)μ(false,false). Jointly:

* Dψ=3B/4, Dφ=B/2, I=B/4, To=B, O=7B/12.
* IF B>0, Dφ/Dψ=2/3 and Dφ<Dψ.
* To=Dψ+I; IF B≠0, To-I≠Dφ.
* The high-regime mixture is 7B/4, the low-regime mixture is 7B/6, and To-I=3B/4.

Separately, for EVERY G>0, positive group-size vector, and completely arbitrary real four-cell outcome schedule y, μ(true,true)-μ(false,false)=[μ(true,true)-μ(false,true)]+[μ(false,true)-μ(false,false)]. The arbitrary-outcome identity has no dilated-model premise.

## SAP.P045b.T25

The theorem is the NEGATION OF THE CONJUNCTION of the following two universal assertions, so it only requires at least one assertion to fail:

(A) For EVERY n>0, EVERY p∈(0,1), EVERY real schedule y(i,z), and EVERY Boolean arm b, E_{B_p}[A_b | arm b exists] = n^{-1}sum_i μ_i(b).

(B) For EVERY G>0, positive group-size vector n_g, arbitrary first-stage design S on group regime assignments, ψ,φ∈(0,1), and arbitrary within-group schedule y, jointly the following hold. Write L for the hierarchical joint law, M(h,b) for the hierarchical arm mean, μ(p,b) for its target, and D(h,b) for its domain.

* For EVERY h,b, IF L(D(h,b))>0, then E_L[M(h,b)|D(h,b)]=μ(ψ if h else φ,b).
* For EVERY h, on E=D(h,true)∩D(h,false), IF L(E)>0, then E_L[M(h,true)-M(h,false)|E]=μ(p_h,true)-μ(p_h,false).
* On E=D(true,false)∩D(false,false), IF L(E)>0, then E_L[M(true,false)-M(false,false)|E]=μ(ψ,false)-μ(φ,false).
* On E=D(true,true)∩D(false,false), IF L(E)>0, then E_L[M(true,true)-M(false,false)|E]=μ(ψ,true)-μ(φ,false).
* On E={both regime-group sets are nonempty}, IF L(E)>0, then the conditional expectation of hierarchyOverall(true)-hierarchyOverall(false) equals mean_g mean_i E_{B_ψ}y_g(i,Z)-mean_g mean_i E_{B_φ}y_g(i,Z).

No individual failure of (B), nor failure of all its clauses, follows just from this negated conjunction.

## SAP.P045b.T26

It is NOT true that for EVERY G,C with 2≤C≤G, EVERY vectors n_g,m_g with 0<m_g<n_g for every g, and EVERY real arrays a_g(i),b_g(i), the following conjunction holds under uniform C-group selection and independent uniform fixed-m_g assignment in every group:

1. IF there EXISTS a single real d such that for EVERY g,i a_g(i)=b_g(i)+d, THEN E[Vhat]=Var(point).
2. Var(point)≤E[Vhat].

Here point is the selected mean of directGroup and Vhat is the explicitly singleton-dropped direct variance estimate from the dictionary. Thus the formal negation only asserts existence of one failure of this conjunctive guarantee, not separately that each conjunct fails under constant effects. All selected treatment/control cells are nonempty on the design support, but arm sizes 1 are allowed.

## SAP.P045b.T27

It is NOT true that for EVERY natural n, EVERY symmetric loopless Boolean network A, EVERY assignment z, and EVERY i∈Fin n,

    [the number of treated vertices in N[i] is <|N[i]|]
      iff [EVERY j∈N[i] is control].

This is one existential failure of that equivalence. The proposition does not require every network/assignment to fail.

## SAP.P045b.T29

It is NOT true that for EVERY natural n>0, EVERY simple graph G on Fin n, and EVERY p∈[0,1], the coded=true sampler satisfies ALL of:

1. sum over all S of terminalCentres(G.edist,3,true,S)=1.
2. The terminal mass of sets satisfying the corrected separation-and-cover definition of 3-net is 1.
3. For EVERY assignment z, clusteredTreatment equals the sum of terminalCentres times clusterProb.

The third conjunct is definitional. The theorem alone identifies neither the witness graph nor which of the first two conjuncts fails. The trace sum includes arbitrary retry lengths and is not the bounded greedy process of T21.

## SAP.P045b.T30

For EVERY n>0, finite decidable exposure type Δ, probability design P on assignments, map D, real exposure schedule y, and label k, IF EVERY π_i(k)>0, THEN E H_k=sum_i y_i(k), AND for EVERY label l, IF EVERY π_i(l)>0, THEN E C_{k,l}=τ_{k,l}. In contrast to T17, k=l is allowed. The schedule is exposure-indexed, so consistency with the map is encoded by the definition Y_i(z)=y(i,D_i(z)).

## SAP.P045b.T31

For EVERY natural Nc>0, EVERY Boolean mediator schedule m, and EVERY real y_i(z,mediator), jointly:

    indirectHousehold = contagion(true)+otherMechanisms(false),
    indirectHousehold = contagion(false)+otherMechanisms(true),

and for EVERY unit i, IF m_i(true)=m_i(false), THEN for EVERY Boolean z the INDIVIDUAL difference y_i(z,m_i(true))-y_i(z,m_i(false)) is 0. No global zero-contagion conclusion is imposed unless all mediators agree.

## SAP.P045b.T32

There EXISTS a type E with decidable equality, a bijection labels:Fin 4→E, and functions f(r,i), w(t,i,a)∈ℚ, q(t,i,j,a,b)∈ℚ satisfying ALL of the facts below. The label representation is existential, not universal. Since labels is a bijection, E has exactly four elements. All assignments of two treated vertices among 12 are listed in lexicographic order r=0,...,65. Adjacency is i≠j and floor(i/4)=floor(j/4): three disjoint complete four-vertex groups. Each row's exposure is labels(0) for treated with a treated neighbor, labels(1) for treated without one, labels(2) for control with a treated neighbor, and labels(3) for control without one. Set k=labels(2), l=labels(3), y_i(a)=1, P(r)=1/66. For each omitted row t, retainedAssignments(t) is the 65-row table with t deleted in order. Put T(t,r)=weightedContrast using w_t and V(t,r)=varianceEstimate using w_t,q_t, as defined above.

1. f is EXACTLY that four-exposure map; an assignment has treated count 2 iff it occurs as a listed row; the listed assignments are injective. Adjacency is symmetric; EVERY vertex is loopless and has a neighbor. For EVERY t, its retained-row enumeration is injective and none of its rows is row t.
2. For EVERY t,i,a, w_t(i,a)=(retained exposure count+1)/66. For EVERY t,i,j,a,b with a,b∈{k,l}, q_t(i,j,a,b) is the smoothedJoint formula with R=65. No restriction on q outside those labels is asserted. For EVERY t,i, both relevant w are positive; the true effect is 0.
3. For EVERY i the full-table k,l counts are 27,28, marginals 9/22,14/33, both positive. For EVERY DISTINCT i,j the joint counts (kk,ll,kl) are (17,28,0) if in the same clique, and (9,6,15) if in different cliques.
4. For EVERY row r its (k-count,l-count) is (2,8) if the two treated vertices are in one clique, and (6,4) otherwise. Exactly 18 rows are of the first kind and 48 of the second.
5. Using exact m,J, for EVERY r the exact contrast is -220/189 for same-clique treated pairs and 55/126 otherwise; its mean is 0, moment variance is 6050/11907, and the exact variance-estimator expectation is 6050/11907.
6. For EVERY Boolean included and EVERY ordered pair x=(t,r), joint mass is nonnegative and sums to 1. For included=false it is uniform 1/4356 on all pairs; for included=true it is 0 when t=r and 1/4290 otherwise. Thus the latter draws the observed row from the retained table.
7. For included=false, jointly over (t,r): E T=-67/53592; Var T=113448938731/232640299584; E V=1040129476423/2326402995840; E V-Var T=-953130413/23499020160.
8. For included=true: E T=-67/52780; Var T=11375808887/23342482800; E V=4673362763/10414338480; E V-Var T=-20161943/522324075.
9. For EACH included value, E V<Var T and E V<6050/11907.
10. For EVERY fixed omitted row t, use the UNCONDITIONAL uniform observed-row law P, and write same for its treated pair being in one clique. Then Var_P T(t,·) is 2810528137/5767941312 if same, 937589375/1922647104 otherwise. E_P V(t,·) is 267260522663/634473544320 if same, 4830430961/10574559072 otherwise. Its difference from that variance is -1551761941/23499020160 if same, -72513467/2349902016 otherwise, and is strictly negative.
11. For EVERY t there EXISTS a permutation e of all 12 vertices preserving adjacency such that for EVERY i, assignment_t(e(i)) equals assignment_0(i) if same and assignment_3(i) otherwise.
12. For EACH included value, embed masses, weights and joints canonically from ℚ into ℝ and RECOMPUTE T,V with real unit outcomes 1. The real mass is pointwise nonnegative and sums to 1; E V<Var T and E V<6050/11907.

`cliqueObservationMass` is also defined: for fixed t it is 1/66 for independent observation and uniform 1/65 off row t for included observation. It is not used in T32's proposition. T32 is an existence theorem about this concrete finite table, not a negation of an arbitrary variance theorem and not a simulation-limit theorem.

## SAP.P045b.T33

For EVERY finite sample space Ω, EVERY exposure-label type D with decidable equality (not required finite), EVERY natural N>0, EVERY probability design P on Ω, EVERY map f:Ω×Fin N→D, EVERY real exposure schedule y, and EVERY DISTINCT a,b∈D, assume EVERY unit's exact marginal at a AND at b is positive. Then jointly:

1. With exact weights w=m and q=J, E_P[Vhat]-momentVariance_P(T)=zeroSurplus(y,J,a,b), with the full squared-outcome expression in the dictionary.
2. momentVariance_P(T)≤E_P[Vhat].
3. E_P T=N^{-1}sum_i(y_i(a)-y_i(b)).

There is no strict positivity requirement on joint probabilities: structural zeros use the explicit adjustment branches. Positivity of the marginals and N>0 prevent all active inverse-weight and population denominators from being zero. Existence of a probability design itself rules out an empty Ω.
