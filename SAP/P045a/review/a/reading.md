# Blind reading

Saved before opening `claims.json` or `record.json`. This reads the types, not the `sorry` proofs. All sixteen theorems are closed propositions `SAP.P045a.TkStatement`; their quantifiers and assumptions are inside these definitions. The following notation expands the shared definitions, so the descriptions below do not interpret a definition by its name alone.

## Shared objects and conventions

* Units are `Fin n`, namely integers 0 through n−1. An assignment is a function from these units to Bool. Write z_i=1 for true, z_i=0 for false, and K(z)=number of true entries. `bit` embeds false/true as real 0/1.
* A `Design Ω`, for a finite type Ω, consists of real masses p(w)≥0 with sum 1. `expect p X` is the finite sum Σ_w p(w)X(w); `prob p E` is Σ_w p(w)1_E(w); `condMean p E X` is Σ_w p(w)1_E(w)X(w)/prob(p,E). `variance p X` is Σ_w p(w)(X(w)−expect(p,X))². Without the `Design` wrapper these definitions also accept arbitrary real weights.
* `average S x` is Σ_{i∈S}x_i/|S| and `mean x` is Σ_i x_i/card(I). Every division is real division after casting natural denominators. Mathlib defines a/0=0. Thus these functions are total, but a conditional mean or ratio describes an ordinary statistical quantity only on its positive-denominator domain. All sums except `terminalCentres` are finite; no integrability convention is involved.
* B_p(z)=Π_i (p if z_i=1, else 1−p). The fixed-count set F(n,k) consists of all z with K(z)=k. Q(n,k)(z) is 1/|F(n,k)| on that set and 0 otherwise. `firstStageSets G C` is all C-element subsets of `Fin G` (Mathlib `Finset.powersetCard`). For group sizes n_g and local weights q_g, L(C,q)(H,w) is |firstStageSets G C|⁻¹Π_g q_g(w_g) if |H|=C, and 0 otherwise, on *all* subsets H and all group assignments w. Thus assignments for unselected groups are sampled too. The selected mean of local statistics X_g is P_C(X)(H,w)=Σ_{g∈H}X_g(w_g)/C.
* A `Network n` is a Boolean adjacency matrix symmetric everywhere and false on the diagonal. Exposure D_A(z,i) is d11 when i and at least one A-neighbor are treated, d10 when only i is treated, d01 when i is untreated with at least one treated neighbor, and d00 otherwise. For exposure outcomes y(i,d), observed outcome is y(i,D(z,i)), π_p,D(i,d)=P_p(D(z,i)=d), and H_d(z)=Σ_i 1_{D(z,i)=d} y(i,D(z,i))/π_p,D(i,d). `effect y k l` is mean_i y(i,k)−mean_i y(i,l).
* For assignment-dependent outcomes y_i(z), μ_p(i,b)=E_p[y_i(z)|z_i=b]. R_b(y,z)=Σ_{i:z_i=b}y_i(z)/#{i:z_i=b}; A_b(z) is the existence of such an i; O(y,z)=mean_i y_i(z). G_b(p,y,z)=Σ_{i:z_i=b}y_i(z)/(n·(p if b=1, else 1−p)). c_i(z)=Σ_{j≠i}z_j (`coMembers`).
* For a finite S, s²(S,x)=Σ_{i∈S}(x_i−average(S,x))²/(|S|−1), with subtraction in the real numbers; S²(x)=s²(univ,x). T(z) is the treated set. D(a,b,z)=average(T(z),a)−average(univ\T(z),b). W(a,b,z) is s²(T,a)/|T| if |T|≥2, plus s²(univ\T,b)/|univ\T| if that cardinality≥2, with either missing term replaced by zero. Vhat_C(a,b;H,w)=(1−C/G)s²(H,g↦D(a_g,b_g,w_g))/C + Σ_{g∈H}W(a_g,b_g,w_g)/(CG). `requiredDirectVariance` is `some Vhat` only if C≥2, |H|=C, and both arms in every selected group have size≥2; it is `none` otherwise.
* N_A[i]={i}∪{j:A_ij=true}, r_A(z,i)=#{j∈N_A[i]:z_j=1}. T_A is r=|N_A[i]|, C_A is r=0, and B_A is r<|N_A[i]|. `fullHT(p,A,Y,correct,z)` is mean_i of the inverse-probability-weighted T_A outcome minus the corresponding C_A outcome when `correct=true`, or B_A outcome when false. Its target is U(Y)=mean_i(Y_i(all true)−Y_i(all false)).
* The two-unit edge A² has A²_ij iff i≠j. L_i(z)=1+z_0+z_1 and F_i(z)=1+2·1_{z_0=z_1=1}, independent of i.
* U_n (`upperCells`) lists pairs i<j<n by increasing column j then increasing row i. L_n (`lowerCells`) lists j<i<n in the same column-major order. The faulty copy leaves entries i≤j unchanged; for j<i it replaces M_ij by M at the cell in U_n with the same list index as (i,j) in L_n. Missing list access defaults to (0,0), and absent `idxOf` uses the list length. The corrected copy C(M)_ij is M_ji if j<i, else M_ij. E⁴ is the matrix with ones only at (0,3),(3,0). `matrixExposure` uses positivity of Σ_j z_j M_{ji}, i.e. columns, to detect a treated neighbor. `upperInput4 u` puts the six Boolean entries u in U_4 order, reflects them symmetrically, and uses a zero diagonal (its index is reduced modulo 6; on valid four-unit off-diagonal indices there is no reduction).
* The fixed ten-unit graph A* has undirected edges 01,02,04,12,13,19,23,24,25,28,34,35,36,45,47,67,68,78,79,89 (zero-based labels). R ranges over d-element subsets of these 20 edges. A*\R removes both directions. g_R(i) is the remaining degree. b_1=5/2 and every other b_i=1. For a unique treated unit t put S={i:A*\R(t,i)}, C=univ\({t}∪S), and
  h_R(t)=[Σ_{i∈S}(5/4)b_i/g_R(i)]/[Σ_{i∈S}1/g_R(i)] − [Σ_{i∈C}b_i(1+(1/4)1_{A*(t,i)})/(9−g_R(i))]/[Σ_{i∈C}1/(9−g_R(i))].
  B(d)=average_{R:|R|=d} mean_t h_R(t)−23/80 (`deletionBias`).
* For a distance d with values in the extended naturals ℕ∞, separation at ε means d(s,t)≥ε for distinct centers. Coverage requires for every v outside S an s∈S with d(s,v)≤ε−1; subtraction is natural. An ε-net is separation and coverage. M_d,ε(S) consists of vertices within ε−1 of a center. A list cs is a `greedyRun` iff for every prefix length k<length(cs), cs[k]∉M(prefix k). In the stated instances ε=3, so the radius is exactly 2. `pathDistance` is |i−j| embedded into ℕ∞. Mathlib `SimpleGraph.edist` is the infimum of walk lengths in ℕ∞, infinite when disconnected, not the natural-valued distance that sends disconnected pairs to zero.
* The sampler from S has R=univ\M(S). For `coded=false`, the next vertex is uniform on R. For `coded=true` and |R|=1, with sole remaining index u, it is instead uniform on indices 0,…,u, including marked vertices. This is an explicit model of that special draw behavior. A list has `traceMass` zero unless every proper prefix is uncompleted and the final marked set is univ; otherwise its mass is the product of its draw probabilities. `terminalCentres(S)` is Σ'_{t∈ℕ} Σ_{z:Fin t→Fin n}1_{set(List.ofFn z)=S}traceMass(List.ofFn z). Mathlib's real `tsum` is the sum of a summable family and defaults to zero if not summable; this definition itself has no explicit summability hypothesis. Drawn center repetitions are permitted by `traceMass` in the coded case. `nearestCentre(S,v)` sorts S by distance to v and then increasing index and returns its head, or none for empty S. `clusterProb(S,p,z)` is the probability, under independent Bernoulli-p labels on all vertex indices, that every v gets the label of its nearest center. `clusteredTreatment` sums this probability against the terminal center-set masses, with ε fixed at 3.
* Pairs E consist of all i<j in `Fin 10`; z^e treats exactly the endpoints of e. π_A(i,d) is the fraction of E giving exposure d. H_A,d^e=Σ_i1_{D_A(z^e,i)=d}y(i,d)/π_A(i,d). For A*, δ_b(d11,d10,d01,d00)=(2b,3b/2,5b/4,b) and J(e)=(H_A*,11^e−H_A*,00^e)/10 with b=1. A cell is nonempty iff some unit realizes it.
* The ten-cycle joins consecutive indices modulo 10. Its outcome table is y(d11,d10,d01,d00)=(2,1,1,0). L(e)=mean_i 1_{z_i^e=1}y(D(z^e,i))/(1/5). R(e)=mean_i[1_{D=11}2/π(i,11)+1_{D=10}1/π(i,10)]. For arbitrary p,A,y, q_i=P_p(z_i=1), N(z)=mean_i1_{z_i=1}y(i,D_A(z,i))/q_i (`naiveTreated`), and Rfix(z)=mean_i[1_{D=11}y(i,11)/q_i+1_{D=10}y(i,10)/q_i].
* `pooledMean(a,b,A,B)` is none if a+b=0 and otherwise some((A+B)/(a+b)); `printedPool` is none if either count is zero and otherwise some(A/a+B/b). Counts are naturals and numerators arbitrary reals.
* The tract model has six groups of 75 units and partners 0↔1, 2↔3, 4↔5. For H⊆Fin 6 put h(H)=#{g∈H:partner(g)∈H}. The witness w* treats the first 50 units in groups 0,1,2, and the first 25 in groups 3,4,5. In a general w, k_g=K(w_g)+K(w_partner(g)); treated outcomes are 9/4 if k_g=100, 2 if k_g=75, 3/2 otherwise; control outcomes are respectively 11/8,5/4,1. r_g,b(w) is its observed within-group arm mean. A first stage picks |H|=3 uniformly; the second stage independently draws Q(75,50) for g∈H and Q(75,25) otherwise. This gives `tractTwoStageMass`. The direct estimate is mean_{g∈H}r_g,1−mean_{g∈H}r_g,0. Under `tractAllPsiMass` every group independently uses Q(75,50). Its unit-level potentials are the conditional means of the above outcomes given own assignment b. The target is the equal average of the three 150-unit tract direct contrasts (equivalently the average across the six equal groups).

## T1

Let Ω=Bool×Assignment(4)×Assignment(4). For w=(s,z,z'), high(w) is z if s=true, else z', and low(w) the other assignment. The mass is (1/2)B_{1/2}(high)B_{1/4}(low). Arm statistics are R_b(c,high/low), and their domains are A_b(high/low). Direct is high/low treated mean minus that group's control mean; indirect is high control minus low control; total is high treated minus low control; overall is O(c,high)−O(c,low). The closed conjunction asserts:

1. |Ω|=512, masses sum to 1, and, in the final conjunct, every mass is nonnegative.
2. For every real 0<p<1, then every i∈Fin 4, then b∈Bool, μ_{B_p}(i,b)=3p. For every z then i, c_i(z)=K(z)−z_i (real subtraction).
3. For every w then Boolean regime selector high, if both arms of that regime exist, its direct statistic is −1.
4. Probabilities that both high arms exist, both low arms exist, both control arms exist, high treated and low control exist, and all four arms exist are respectively 7/8, 87/128, 3825/4096, 3825/4096, 609/1024.
5. The indirect and total conditional means on their respective two-arm domains are 224/255 and 37/255. On the all-four-arm domain they are 16/29 and −13/29.
6. For every z, O(c,z)=3K(z)/4. E(overall)=3/4.
7. Single-arm conditional means, each conditional only on that arm being nonempty: at p=1/2 treated 17/15, control 28/15; at p=1/4 treated 81/175, control 84/85.
8. For each high selector, probability of its two-arm domain is 7/8 or 87/128 as appropriate and its direct conditional mean is −1.
9. For every 0<p<1, mean_i μ_{B_p}(i,true)−mean_i μ_{B_p}(i,false)=0.

There is no outer existence hypothesis and no assumed biasedness premise.

## T2

Independent conjuncts, with quantifier order as follows:

1. For every n>0, p with 0<p<1, assignment-dependent real y_i(z), and b, for every i the masked expectation equals (p or 1−p)μ(i,b), and E_{B_p}G_b=mean_i μ(i,b).
2. For every G,C with 0<C≤G, every size vector n with every n_g>0, every 0<p<1, every group-local y_g,i(z_g), then b, E_{L(C,B_p)}P_C(g↦G_b(p,y_g))=mean_g mean_i μ_{B_p}(g,i,b).
3. For every n,k with 0<k<n, every y, then b, E_{Q(n,k)}R_b=mean_i μ_{Q(n,k)}(i,b).
4. For every G,C with 0<C≤G, every n,k with 0<k_g<n_g for all g, every group-local y, then b, the analogous selected fixed-count arm mean has expectation mean_g mean_i μ_{Q(n_g,k_g)}(g,i,b).
5. For every k∈Fin 4 with k>0 (thus k=1,2,3), all units have fixed-count treated/control conditional means k−1,k; their direct contrast is −1; the Bernoulli(k/4) direct contrast is 0.
6. For every n>0, every genuine design q on its assignments, and every y, E_q O(y)=mean_i E_q y_i.
7. For every G,C with 0<C≤G, every positive size vector n, every family q_g of genuine assignment designs, then group-local y, E_{L(C,q)}P_C(O)=mean_g mean_i E_{q_g}y_g,i.
8. For every 0<p<1 then every z∈Assignment 4, G_true=K(K−1)/(4p) and G_false=K(4−K)/(4(1−p)), using real arithmetic.
9. For every 0<p<1, both these HT means have expectation 3p and their difference has expectation 0.

No joint high/low first-stage experiment, arbitrary dependent local law, or cross-group-dependent outcome function is quantified here.

## T3

Six equal groups, n_g=3, C=3; each local law is Q(3,m), with all group draws independent. Let x=(1,2,3), point=P_3(D), and variance estimate Vhat_3. Unconditionally:

* For m=1 and m=2, with a=x+1,b=x, E(point)=1, Var(point)=1/2, E(Vhat)=1/3.
* For m=2,a=2x,b=5x/4: Var(point)=9/8, E(Vhat)=43/48.
* For m=1,a=3x/2,b=x: Var(point)=8/9, E(Vhat)=19/36.
* For m=2,a=x,b=0: Var(point)=1/18, E(Vhat)=1/9.
* Separately, for each m=1,2, the single-group additive D has E=1, variance 3/2, and E(W)=1/2.

There are no outer parameters or hypotheses.

## T4

1. For all G,C with 2≤C≤G, then all size/count vectors n,m with 2≤m_g and m_g+2≤n_g for each g, then all real schedules a_g,b_g, define θ_g=mean a_g−mean b_g and V_g=S²(a_g)/m_g+S²(b_g)/(n_g−m_g)−S²(a_g−b_g)/n_g. Under L(C,Q(n_g,m_g)), each group D has mean θ_g and variance V_g; the selected point has mean mean θ and variance (1−C/G)S²(θ)/C+Σ_g V_g/(CG). E(Vhat)−Var(point)=Σ_g[S²(a_g−b_g)/n_g]/G²≥0. Equality of estimate expectation and true variance holds iff for every g, then all i,j in that group, a_gi−b_gi=a_gj−b_gj. These conditions in particular make natural n_g−m_g ordinary subtraction and all sample-variance denominators positive.
2. For all 2≤C≤G, then arbitrary a,b on G groups of 3, the singleton-dropping biases are Σ_g[S²(a_g−b_g)/3−S²(b_g)]/G² for m=2 and Σ_g[S²(a_g−b_g)/3−S²(a_g)]/G² for m=1.
3. For all 2≤C≤G, then arbitrary x on G groups of 3, those biases are −11Σ_g S²(x_g)/(8G²) for m=2,a=2x,b=5x/4 and −13Σ_g S²(x_g)/(6G²) for m=1,a=3x/2,b=x. If there exist g,i,j with x_gi≠x_gj, both biases are strictly negative.
4. For m∈{1,2}, then any six-group schedules a,b on groups of size 3, any H of size 3, then any w whose selected groups each have exactly m treated, `requiredDirectVariance 3 a b (H,w)=none`.

## T5

For the single two-unit edge, N[i] is the whole population for each i. For each i, the mixed assignment (true,false) satisfies B_A but not C_A. Under B_{1/2}, for every i, probabilities of T_A,B_A,C_A are 1/4,3/4,1/4. For L_i=1+z_0+z_1, U(L)=2 and the defective fullHT values at (00,01,10,11) are (−4/3,−8/3,−8/3,12); its expectation is 4/3 while the corrected expectation is 2. For the threshold F_i=1+2·1_{11}, U(F)=2 and both expectations are 2. No hypotheses.

## T6

1. For every n, then Network A, assignment z, and unit i, the column sum with own-unit diagonal replaced by 1 equals r_A(z,i); the analogous row sum equals |N[i]|; r≤|N[i]|. T_A iff all closed-neighborhood units are treated; C_A iff all are control; B_A iff at least one is control. C_A implies B_A; B_A and not C_A iff 0<r<|N[i]|. For this i, equivalence of C_A and B_A on *every* assignment holds iff |N[i]|=1. T_A and C_A cannot both hold, and T_A iff not B_A. No n>0 is needed here because i is quantified in Fin n.
2. For every type Ω, finite-type structure, genuine design p, event E with a decidability instance, and real random variable Y, if P(E)>0, E_p[1_EY/P(E)]=E_p[Y|E].
3. For every n>0, design p, Network A, real Y_i(z), assume for all i,z that T_A implies Y_i(z)=Y_i(all true), and C_A implies Y_i(z)=Y_i(all false), followed by positive T_A and C_A probabilities for every i. Then E(correct fullHT)=U(Y); E(defective fullHT)=mean_i[Y_i(all true)−E(Y_i|B_A,i)]. If in addition Y_i equals its all-false value on B_A for every i,z, E(defective fullHT)=U(Y).

## T7

E⁴ is symmetric and has zero diagonal on all natural indices. Faulty-copy entries (0,3),(3,0),(2,1),(1,2) are 1,0,1,0. U_4=[01,02,12,03,13,23], L_4=[10,20,30,21,31,32]. For every n≥4 their index-2 cells are respectively (1,2),(3,0). For every n≤3 and every k<length(U_n), L_n[k] is the transpose of U_n[k]. Exactly 32 of the 64 Boolean upper inputs on four vertices yield an asymmetric faulty copy. With only vertex 3 treated, unit 0 changes d01→d00 under the faulty copy; with only vertex 2 treated, unit 1 changes d00→d01. Finally for every real 0≤q<1, a Boolean draw with mass q on true and 1−q on false gives probability 1−q of obtaining the faulty E⁴ when output is zero for true and the faulty E⁴ for false.

## T8

No external parameters. A* has 20 edges and mean b/4=23/80. For every d≤2, every d-deletion mask R, then every i, 1≤g_R(i)≤6. B(0)=890121037/44498644960 lies strictly between 1/50 and 1/49; 9/1000<B(1)<1/100; −1/800<B(2)<−1/900. |B(2)|<|B(1)|<|B(0)| and B(0)≠0. Additionally, for every d∈Fin 3 and R of that size, the same degree bounds hold, and for every treated t both its measured-neighbor and measured-nonneighbor control sets are nonempty. For every such d,R, every i has g_R(i)/10>0 and (9−g_R(i))/10>0, and both sums of reciprocal weights in h_R(t) are positive for every t. The mask-family cardinalities at d=0,1,2 are 1,20,190.

## T9

1. For every natural-indexed real matrix M and i,j, C(M)_ij=C(M)_ji.
2. For every n, then matrices A,U, assume A symmetric on all natural indices and zero on its entire diagonal, A binary on i,j<n, U zero on its entire diagonal and binary above its diagonal for i<j<n. If U≤A above the diagonal, then 0≤C(U)_ij≤A_ij for all i,j<n. If A≤U above the diagonal, then A_ij≤C(U)_ij≤1 for distinct i,j<n. If U=A above the diagonal then C(U)=A on all i,j<n. Each of the three antecedents is a separate implication.
3. For every n, Networks T,S with S a subgraph of T, assignment z, and unit i, measured d01 implies true d01; measured d11 implies true d11; measured d00 implies true d00 or d01; measured d10 implies true d10 or d11.
4. For every n>0, design p, Networks T,S with S⊆T, then outcome schedule y(i,d), assume measured d00 and d01 probabilities are positive at every unit. Use outcomes generated from T and HT weights/exposures from S. Put c_i=P(true d01|measured d00). The expected measured d00 HT mean is mean_i[(1−c_i)y_i00+c_i y_i01]; the expected measured d01 HT mean is mean_i y_i01; the expected contrast minus effect(y,01,00) is −mean_i c_i(y_i01−y_i00). If all y_i00≤y_i01, this contrast expectation≤the target.
5. For the fixed A* deletion witness, B(0)≠0 and |B(1)|<|B(0)|.

## T10

On the four-path with ε=3, the coded terminal center masses at {0,1},{0,2},{0,3},{1},{2} are 1/12,1/12,1/3,1/4,1/4; the sum over all center sets is 1. The probability of a center set failing separation is 1/6. At p=1/2 its treatment-vector probabilities at 0000,1111,1100,0011,1000,0111 are 3/8,3/8,5/48,5/48,1/48,1/48. For every other four-bit assignment the probability is zero. Repaired terminal center masses at {0,3},{1},{2} are 1/2,1/4,1/4. Repaired treatment probabilities at the same six vectors are 3/8,3/8,1/8,1/8,0,0. No explicit assertion of zero repaired probability on every other vector is made. No hypotheses.

## T11

For every n>0 then every Mathlib simple graph G on Fin n (not required connected): for every center list cs satisfying the prefix admissibility rule, cs has no repeats, length≤n, and its set is 3-separated; if its marked set is univ, its set is a 3-net. For every S then every v outside its marked set, adding v strictly decreases the number of unmarked vertices. There exists some admissible completed center list. The existential is within the quantifiers over n,G, not uniform in G.

## T12

The treatment-pair set has size 45. For every cycle unit i, probabilities (d11,d10,d01,d00) are (2/45,7/45,1/3,7/15). Exactly 10 treatment pairs are adjacent. For every pair in E, L=2,R=9 when adjacent and L=1,R=9/7 otherwise; L≠R for every pair. Their unconditional pair averages are 11/9 and 3. The pair-average correct d11 HT mean is 2. Average L−mean_i y_i11=−7/9. No hypotheses.

## T13

1. For every n>0, design p, Network A, schedule y, then assumption q_i>0 for all i: q_i=π_i11+π_i10 for every i; E(N)=mean_i[(π_i11/q_i)y_i11+(π_i10/q_i)y_i10]; E(N)−mean y11=−mean_i(π_i10/q_i)(y_i11−y_i10). If all y_i10≤y_i11 then E(N)≤mean y11, with strict inequality iff there exists a unit with π_i10>0 and y_i10<y_i11. If all y_i11≤y_i10 then mean y11≤E(N). If both π_i11 and π_i10 are positive for every i then E[(H_11+H_10)/n]=mean y11+mean y10.
2. Separately, for every n>0, design p, Network A, schedule y, positive own-treatment probabilities, and then every z, N(z)=Rfix(z).
3. The two-unit edge schedule has (y_0,11,y_1,11)=(2,1), (y_0,10,y_1,10)=(1,2), and control exposures zero. Both units have unequal 11 and 10 outcomes. Under B_{1/2}, N(00),N(01),N(10),N(11) are 0,2,1,3; E(N)=3/2=mean y11.

## T14

No outer parameters. Pooled/printed treated means for counts 2,1 and numerators 9/2,2 are some(13/6),some(17/4); corresponding control means for 11/4,5/4 are some(4/3),some(21/8). Their numerical differences are 5/6 and 13/8. For every a,b>0, then every real A,B,
A/a+B/b−(A+B)/(a+b)=bA/[a(a+b)]+aB/[b(a+b)].
There are 20 three-group choices H, exactly 8 with h(H)=0, and each has h(H)=0 or 2. For every real B, printedPool(0,3,0,B)=none and pooledMean(0,3,0,B)=some(B/3).
The six-by-75 population has cardinality 450. H*={0,1,2} is allowed, with partner-in-H subclass {0,1} and partner-outside subclass {2}. For every group the specified w* has the correct count (50 for g<3 else 25) and positive Q mass. For every g<3 then every b, its observed arm mean is 9/4 or 11/8 for g<2, and 2 or 5/4 for g=2. Substituting the actual sum from groups {0,1} and the mean from group 2 into pooled/printed means gives respectively the four values above.

## T15

1. For every natural a,b and real A,B with a+b>0: pooledMean=some((A+B)/(a+b)); if separately a>0 and b>0 this is the count-weighted combination a/(a+b)·A/a+b/(a+b)·B/b; if a=0 and A=0 it is some(B/b).
2. For every H⊆Fin 6 then every real group function m, |H|=|{g∈H:partner(g)∈H}|+|{g∈H:partner(g)∉H}| and the analogous sum partition holds.
3. The specified tract two-stage mass is nonnegative everywhere, sums to 1, and is strictly positive exactly for |H|=3 and all required within-group counts. For every allowed H then every w satisfying those counts: for every g∈H then b, that arm exists and its mean is (9/4,11/8) when partner(g)∈H and (2,5/4) otherwise; the direct estimator is the average of its three group contrasts and equals (h(H)/3)(7/8)+((3−h(H))/3)(3/4), with real subtraction. For every g,i,b, under the all-50 regime, own-arm probability is 2/3 when treated and 1/3 when control, and its conditional potential is 9/4 or 11/8. Target=7/8; first-stage average h(H)/3=2/5 and average (3−h(H))/3=3/5. The two-stage direct expectation is 4/5 and its bias relative to the target is −3/40.

## T16

For every unit i of A*, let g be its degree. Pair-exposure probabilities d11,d10,d00,d01 are g/45,(9−g)/45,choose(9−g,2)/45,(36−choose(9−g,2))/45 respectively, and each is strictly positive. Here the first two 9−g operations are natural, but g≤6 for this explicit matrix, so they are not truncated in effect. On pair (5,8), the d11 cell is empty and d00 occurs exactly at units 0 or 1; H_11=0,H_00=15/2,J=−3/4. Of the 45 pairs, 20 have nonempty d11 and 19 have both d11 and d00 nonempty. Mean H_11 over all pairs is 20 and over the 20-pair restriction is 45. Mean J over all pairs, over the d11 restriction, and over the joint restriction is respectively 1,651/200,1227/380. No hypotheses.

## Mathlib endpoints checked

`Finset.powersetCard` and its membership theorem in `Mathlib/Data/Finset/Powerset.lean` give actual subsets of a prescribed cardinality. `Nat.dist` in `Mathlib/Data/Nat/Dist.lean` is n−m+(m−n), hence ordinary absolute difference. `SimpleGraph.edist` in `Mathlib/Combinatorics/SimpleGraph/Metric.lean` is the infimum of walk lengths, with self-distance zero and unreachable distance top. Real division has `div_zero` in `Mathlib/Algebra/GroupWithZero/Basic.lean`. Real infinite sum uses the additive version of `tprod` in `Mathlib/Topology/Algebra/InfiniteSum/Defs.lean`: an unsummable family's `tsum` is zero. All other shared operations are finite set/cardinality, finite sums/products, Boolean cases, list indexing/sorting, ordinary real arithmetic, and the explicitly described Option values.
