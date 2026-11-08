# Blind reading of the Challenge

Saved before opening `claims.json` or `record.json`. Sources: all eight Defs parts, the Defs import file, the Challenge import file and Challenge Part1, and the Mathlib definitions identified below. Docstrings are descriptions, not hypotheses. All eleven Challenge declarations are closed propositions of the form `TnStatement`; their proofs are `sorry` stubs and are not evidence for truth.

## Notation and definitions actually used

Units are `Fin N`, i.e. integers from 0 to N−1; assignments are all Boolean functions on these units. An adjacency is an arbitrary Boolean N by N array unless a particular theorem assumes symmetry or a zero diagonal. Put

* `k_i(z) = #{j : A_ij = true and z_j = true}` (`peerCount`). Self treatment contributes if the diagonal is true.
* `f_A(z,i)` is d11, d10, d01, d00 according as `(z_i, k_i(z)>0)` is `(true,true)`, `(true,false)`, `(false,true)`, `(false,false)`.
* A `FiniteDesign Ω` consists of a finite type Ω and real masses p_ω≥0 summing to 1. Individual masses may be zero. The separately defined `expect p T = Σ_ω p_ω T_ω` does **not** itself impose these conditions; `designVariance p T = expect p (T²) − (expect p T)²`. The finite examples use rational masses and rational outcomes instead.
* A schedule y is an arbitrary function `(i,d) ↦ y_i(d)`. `observed f y ω i = y_i(f(ω,i))`. `tau y a b = (Σ_i(y_i(a)−y_i(b)))/N`. Division is field division, including the convention 0⁻¹=0. No positivity of outcomes is implicit.
* `π_i(a)=Σ_{ω:f(ω,i)=a}p_ω` and `π_ij(a,b)=Σ_{ω:f(ω,i)=a,f(ω,j)=b}p_ω` are `marginal` and `joint`. For arbitrary supplied weights w, `H_i(a,ω)=1_{f(ω,i)=a}y_i(a)/w_i(a)` (`htTerm`), `H(a,ω)=Σ_i H_i(a,ω)/N` (`htMean`), and `T_ab=H(a)−H(b)` (`htContrast`). The indicator is implemented by an if, so a term outside the observed exposure is exactly zero without evaluating it as an ordinary statistical quotient.
* Write `I_i(a)=1_{f(ω,i)=a}`. `totalVarianceEstimate V_a` is the sum over **all ordered** i,j of
  `1_{q_ij(a,a)>0} I_i(a)I_j(a)y_i(a)y_j(a)[1/(w_i(a)w_j(a))−1/q_ij(a,a)]`
  plus, when i≠j and q_ij(a,a)=0, `[I_i(a)y_i(a)²/(2w_i(a))+I_j(a)y_j(a)²/(2w_j(a))]`.
* `totalCovarianceEstimate C_ab` sums the same first expression with exposures a,b and weights w_i(a),w_j(b), and **subtracts** `[I_i(a)y_i(a)²/(2w_i(a))+I_j(b)y_j(b)²/(2w_j(b))]` when q_ij(a,b)=0, including i=j. `varianceEstimate=(V_a+V_b−2C_ab)/N²`.
* `zeroSurplus(y,q,a,b)` is N⁻² times the sum of `(y_i(a)+y_j(a))²/2` over ordered i≠j with q_ij(a,a)=0, the analogous b sum, and `(y_i(a)−y_j(b))²` over all ordered pairs with q_ij(a,b)=0. `commonSupport` is `{i:π_i(a)>0 and π_i(b)>0}`.
* `completeProfiles N M` is the finite set of M-element subsets of `Fin N`; `completeProbability` is the number of such subsets giving an exposure divided, in ℚ, by their total number. Mathlib `Finset.powersetCard` and `Nat.choose` are the ordinary fixed-cardinality subset operation and binomial coefficients. Natural subtraction is truncated.
* For a bank f indexed by `Fin R`, let c_i(a) and c_ij(a,b) be its exposure and joint counts. `smoothedWeight=(c_i(a)+1)/(R+1)`. `smoothedJoint` is `(c_ij(a,a)+1_{i=j})/(R+1)` for a=b, and `c_ij(a,b)/R` for a≠b. These are returned weights, not assumed to form coherent probability laws.
* `degree A i` counts true entries in row i. `twoWalkDegree A i` counts **distinct endpoints j≠i** for which some k has A_ik=A_kj=true; endpoints adjacent to i are not excluded. `degreeScale a_i=d_i+s_i+d_i s_i`.
* `baseline a g e=a|g|+e`. `dilatedOutcomes B` multiplies B_i by 2, 3/2, 5/4, 1 at d11,d10,d01,d00. `normalPair` is the product of G~Normal(0,1) and E~Normal(1,1/16), independent. `baselineLaw a` is the pushforward under a|G|+E; `halfNormalLaw` is the pushforward of Normal(0,1) under absolute value. `normalPopulation N` is the product of N copies of normalPair, hence all pairs are independent. `generatedBaselines A x` has coordinates a_i|G_i|+E_i. Φ=`standardNormalCDF` is the standard normal CDF.
* Mathlib `gaussianReal μ v` takes **variance**, not standard deviation, as its nonnegative second argument (`Probability/Distributions/Gaussian/Real.lean`). `HasLaw` requires almost-everywhere measurability as well as equality of the pushforward (`Probability/HasLaw.lean`). `IndepFun` means independence of the generated sigma algebras. `bernoulliMeasure true false p` puts mass p on true; `binomial R p` is the distribution of the number of successes among R Bernoulli trials. `Measure.prod` and finite `Measure.pi` are product measures. All pushforward functions in the explicit Gaussian definitions are continuous.
* Mathlib's Bochner integral is totalized (zero when not integrable); `Integrable` means a.e. strong measurability and finite integral of the norm. `MemLp ... 2` means square integrability and a.e. strong measurability (`MeasureTheory/Function/L1Space/Integrable.lean`, `Function/LpSeminorm/Defs.lean`, `Integral/Bochner/Basic.lean`). `ProbabilityTheory.variance X μ` is `(∫⁻|X−∫X|²).toReal`, also totalized if infinite (`Probability/Moments/Variance.lean`). Here the stated L² facts make the Gaussian quantities ordinary moments. The CDF agrees with μ((−∞,x]) for probability measures (`Probability/CDF.lean`). `Measure.real` takes the real value of a set's measure.
* `blockEdgeProbability(s,t,c,i,j)=s t_i t_j 1_{c_i=c_j}`, with no implicit range constraint on s,t. For a Mathlib finite simple graph G, `G.edgeFinset` consists of unordered edges and `G.degree` is ordinary neighbor count (`Combinatorics/SimpleGraph/Finite.lean`). `withinEdges G c` filters edges for which the endpoints share a community label.
* `insertOwn i a u` sets unit i to a and the other coordinates to the Boolean function u on `{j:j≠i}`. `NoInterference y` means ∀i,a,u,v, y_i(insertOwn i a u)=y_i(insertOwn i a v). `Interference y` means ∃i,a,u,v with inequality. These definitions concern full-assignment schedules taking values in ℝ.

## SAP.P044.T1

This is an unconditional conjunction about the following fixed rational example. The graph on 12 units is three disjoint four-cliques (same integer quotient i/4, unequal vertices). `cliquePairs` lists all 66 unordered pairs in lexicographic order, and assignment r treats its two listed units. `cliqueF` computes the corresponding four exposures; y_i(d)=1 for all i,d. A bank indexed by t deletes assignment t and retains the other 65 in order (`Fin.succAbove` is the order embedding skipping t).

For this bank, weights are `(full marginal count−1_{f(t,i)=a}+1)/66`. Joint weights subtract the corresponding indicator from the full joint count, then divide by 66 for equal exposures, adding one only on the diagonal; unequal exposures divide by 65. All subtractions inside these counts are natural subtraction. Define T(t,z) and V(t,z) using these weights and exposures a=d01,b=d00. Under law J_false, all (t,z) have mass 1/4356. Under J_true, t=z has zero mass and every other pair mass 1/4290.

The proposition asserts all of the following:

1. `cliqueF` equals graph-based exposure. An assignment has exactly two treated units iff it is some listed assignment. The assignment enumeration is injective, every assignment treats two, and the graph is symmetric, loopless and has a neighbor at every vertex. Every retained enumeration is injective and excludes the deleted assignment. For every t,i the retained smoothed d01 and d00 weights are positive. The population contrast is zero.
2. At every unit the full d01,d00 counts are 27,28, giving probabilities 9/22,14/33. For distinct i,j, the full (d01,d01), (d00,d00), (d01,d00) joint counts are respectively 17,28,0 in the same clique, and 9,6,15 across cliques. The remaining full-count definition is 3 for d11 and 8 for d10, uses diagonal counts for equal units/exposures, zero for different exposures at one unit, and actual joint counts for the remaining cases.
3. A same-clique treated pair gives 2 d01 and 8 d00 units; an across-clique pair gives 6 and 4. There are 18 pairs of the first kind and 48 of the second. With exact probabilities the contrast equals −220/189 in the first kind and 55/126 in the second. Its expectation is zero, its variance is 6050/11907, and the exact-input variance estimate has expectation 6050/11907.
4. The simulated-input joint-law values are:

   | law | E T | Var T | E V | E V−Var T |
   |---|---|---|---|---|
   | J_false | −67/53592 | 113448938731/232640299584 | 1040129476423/2326402995840 | −953130413/23499020160 |
   | J_true | −67/52780 | 11375808887/23342482800 | 4673362763/10414338480 | −20161943/522324075 |

   For each Boolean law selector, E V is strictly below Var T and below 6050/11907.
5. For **every** deleted t, with z uniform on all 66 assignments, the fixed-bank values are:

   | kind of t | Var_z T(t,z) | E_z V(t,z) | difference |
   |---|---|---|---|
   | same clique | 2810528137/5767941312 | 267260522663/634473544320 | −1551761941/23499020160 |
   | across cliques | 937589375/1922647104 | 4830430961/10574559072 | −72513467/2349902016 |

   Each difference is strictly negative. The statement also repeats the displayed variance and expectation at representatives t=0 and t=3.
6. For every t,i the defined weights at d01,d00 equal the retained bank's `smoothedWeight`; for every t,i,j and a,b each belonging to {d01,d00}, the defined joint weights equal `smoothedJoint`. For every t there exists a permutation e of the 12 units preserving adjacency such that assignment t, evaluated at e(i), equals assignment 0 if t's treated units share a clique, and assignment 3 otherwise. The existential permutation is inside the universal quantifier over t.

There is no assertion about a random R=10000 bank or a limiting approximation.

## SAP.P044.T2

Two conjuncts:

1. For every finite Ω, every exposure type D with decidable equality, every N>0, every finite probability design P, exposure mapping f, real schedule y, and distinct a,b in D, **assuming** ∀i π_i(a)>0 and ∀i π_i(b)>0, using exact marginal and joint probabilities gives
   `E_P Vhat − Var_P T_ab = zeroSurplus(y,π_joint,a,b)`
   and `Var_P T_ab ≤ E_P Vhat`. Quantifier order is Ω,D,N, their instances, N>0,P,f,y,a,b,a≠b, the two positivity assumptions, then the conjunction.
2. For each Boolean selector of the two explicit T1 laws, the simulated-input expected variance estimate is strictly less than the simulated-input contrast's variance.

## SAP.P044.T3

An unconditional conjunction for a four-vertex star centered at 0, enumerating uniformly the six assignments with two treated units: 0011,0101,0110,1001,1010,1100 (coordinate order 0,1,2,3). Schedule A is identically 1; B is 5 at (0,d00) and 1 everywhere else.

* The graph has no isolated vertices, is symmetric and loopless. The six assignments are injective, have two treated units, and enumerate exactly all such assignments.
* The center's (d11,d10,d01,d00) probabilities are (1/2,0,1/2,0); every leaf's are (1/6,1/3,1/3,1/6). For every enumerated assignment and every unit both schedules' observed outcomes equal 1. Their d11−d00 population contrasts are respectively 0 and −1.
* For **every** deterministic function T taking as arguments the assignment, the entire exposure vector, and the entire real observed-outcome vector, the six-point expectations under A and B agree; they cannot simultaneously equal 0 and −1. There is no restriction on T beyond its argument and return types.
* Let f and p be this example's exposure mapping and exact probabilities. For **every proof of the additional premise** `∀r,i,a, f(r,i)=a → p_i(a)>0`, and then for every Boolean flag (true chooses A, false chooses B), the exact-weight HT d11 and d00 means have expectations 1 and 3/4, the contrast has expectation 1/4, and its bias is 1/4 under A and 5/4 under B. The positivity premise is a premise of this last conjunct only; it is positivity for actually observed terms, not positivity of every unit/exposure pair. The theorem does not explicitly assert this premise.

The theorem does not list the six individual exposure vectors.

## SAP.P044.T4

A conjunction with separately quantified components:

1. Universally over finite Ω, decidable-equality D, N>0, finite probability P, f, real y, a,b with a≠b, and positive π_i(a),π_i(b) for **every** i: every unit's exact HT term at either exposure has expectation y_i at that exposure; both HT means are unbiased for their population means; and the contrast has expectation τ_ab.
2. Universally over the same finite setting with N>0, P, any assignment map z:Ω→{0,1}^N, any f,y, distinct a,b, a specified unit j with π_j(a)=0, a real δ≠0, and any deterministic observed-data function T of assignment, exposure vector and outcome vector: change y_j(a) to y_j(a)+δ and no other entry. On every positive-mass ω every unit's observed outcome stays equal; T has equal expectations under y and y'; the population contrasts differ by δ/N; and T cannot be unbiased for both contrasts. The specified missing entry is a; swapping a,b is not a separate explicit conjunct.
3. Universally over finite Ω,D,N,P,f,y,a,b with a≠b and **nonempty** S={i:π_i(a)>0,π_i(b)>0}: the S-normalized sum of exact HT term differences is unbiased for `Σ_{i∈S}(y_i(a)−y_i(b))/|S|`. No explicit N>0 premise is present here; nonempty S implies it.
4. For the fixed star, S at (d11,d00) equals {1,2,3}. For either schedule A or B, the S-restricted population contrast and expected S-normalized exact HT contrast both equal zero (here the local flag true chooses B).
5. Universally over N,M with N>0, 1≤M≤N−1, symmetric loopless A, and unit i, write k=degree(i). Complete-randomization probabilities satisfy
   `p10=C(N−1−k,M−1)/C(N,M)`, `p00=C(N−1−k,M)/C(N,M)`, `p11=M/N−p10`, `p01=(N−M)/N−p00`.
   All four are positive iff `2≤M and 1≤k and k≤N−M−1`. The arithmetic in the binomial arguments is natural subtraction. The hypotheses and looplessness bound k≤N−1, so the displayed subtraction N−1−k has its ordinary combinatorial meaning.
6. For every symmetric loopless adjacency on 1000 units, and every unit, all four complete-randomization probabilities with M=100 are positive iff `1≤k≤899`.
7. In the star, the center's d00 and d10 probabilities are zero, every vertex has a neighbor, and the center's degree is 3.

## SAP.P044.T5

An unconditional conjunction in the ideal product Gaussian model:

1. In the loopless complete graph on 3 vertices, for every i, degree=2, twoWalkDegree=2, degreeScale=8. For vectors g=(1/64,1,−1/2) and e=(−3/4,1,5/4), baselines are B=(−5/8,9,21/4), with the first baseline strictly negative. For every i,j, the ordinary matrix-square count `Σ_k 1_{i≠k}1_{k≠j}` equals 2 on the diagonal and 1 off it; the statement also asserts the identical count written with a conjunction inside an if.
2. For this B, the d11,d10,d01,d00 outcome vectors are respectively (−5/4,18,21/2), (−15/16,27/2,63/8), (−25/32,45/4,105/16), and B.
3. For every a≥0, the normalPair event `|G|<1/[4(a+1)], −1<E<−1/2` has strictly positive measure; for every real pair x in that event, a|x₁|+x₂<−1/4. For every a≥0, `baselineLaw(a)((−∞,0))>0`, `halfNormalLaw((−∞,0))=0`, and the two laws differ.
4. The real probability of `−1/32<G<1/32, −1<E<−1/2` is exactly `[Φ(1/32)−Φ(−1/32)][Φ(−6)−Φ(−8)]`, a strictly positive number. For every g,e in these open intervals, baseline 8 g e<−1/4.
5. Let c=√(2/π), v=1−2/π. The absolute standard normal has mean c, variance v and second moment 1. For every a≥0 the baseline has mean ac+1 and variance a²v+1/16. At a=8 these are 8c+1 and 64v+1/16; their differences from half-normal moments are 7c+1 and 63v+1/16, both strictly positive.
6. For every N, adjacency A satisfying ∀i degree A i≥1, and then every unit i, the mean baseline at degreeScale A i exceeds the half-normal mean by at least 1. No symmetry or looplessness is assumed in this conjunct. For every a≥1, the mean difference equals `(a−1)c+1`.
7. For **every real a**, baseline a is in L²(normalPair); the absolute standard normal is in L² as well. Thus the moments just stated are genuine finite moments. There is no literal execution or identification of an external generator in this proposition.

## SAP.P044.T6

Conjunction:

1. For every N,B,i, dilated outcomes at d00,d11,d10,d01 are B_i,2B_i,(3/2)B_i,(5/4)B_i.
2. For every a≥0, the baseline mean is ac+1 and variance is a²(1−2/π)+1/16; the half-normal mean is c=√(2/π) and its second moment is 1. For every real a, baseline a is in L²(normalPair).
3. For every N>0 and every real B, population contrasts against d00 at d11,d10,d01 are the mean of B, one half that mean, and one quarter that mean. At B=(−5/8,9,21/4), the mean is 109/24 and these contrasts are 109/24,109/48,109/96; the mean equality is also stated separately.
4. For every N>0 and every loopless Boolean adjacency A, the normalPopulation expectation of τ_d11,d00 for generated baselines equals `1+c(Σ_i degreeScale A i)/N`. Symmetry is not a premise. With the additional hypothesis that every unit has degree at least 1, the same expectation is at least 1+c; also c<1.
5. For every measurable probability space Ω,P, N>0, and B:Ω→(Fin N→ℝ) with **each coordinate** having halfNormalLaw (in the HasLaw sense), the expected τ_d11,d00 equals c and c<1. No independence of these B_i is assumed.
6. For every N>0 and every Boolean A (no looplessness required), the generated population contrast is integrable under normalPopulation N. Under the arbitrary-space half-normal coordinate-law hypotheses of item 5, the corresponding population contrast is integrable too.

## SAP.P044.T7

Unconditional fixed rational example on the simple 8-cycle (i adjacent to j iff j=i+1 or i=j+1 modulo 8). Eight bank assignments are `z_r(i)=1_{(i+r) mod 8∈{0,1,3}}`. Outcomes, constant over units, are (2,3/2,5/4,1) at (d11,d10,d01,d00). Let f be the exposure mapping, p its exact uniform eight-assignment marginal, and q its smoothedWeight.

* Every vertex has a neighbor, the eight assignments are injective, and each treats three units. For every assignment the numbers of units at the four exposures are (2,1,3,2). For every unit its bank exposure counts are also (2,1,3,2).
* For every unit, p=(1/4,1/8,3/8,1/4), q=(1/3,2/9,4/9,1/3), and the sum of q is 4/3. All exact p entries are positive.
* For every assignment r and exposure a, the q-weighted HT means are respectively (3/2,27/32,135/128,3/4); exact-p HT means equal the corresponding constant outcomes.
* The sum over all second exposures b of `smoothedJoint f 0 1 d11 b` is 17/72, whereas q_0(d11)=1/3 and 17/72≠1/3.
* For every r, the q-weighted d11,d10,d01 contrasts against d00 are 3/4,3/32,39/128. Their true population contrasts are 1,1/2,1/4, and their differences from those targets are −1/4,−13/32,7/128. The d11 contrast's uniform expectation is separately asserted to be 3/4.
* For every r, exact-p contrasts equal 1,1/2,1/4. Some counts and target equalities are repeated conjuncts.

No individual base exposure vector, individual 0,1 joint counts, or individual returned joint entries are explicitly asserted.

## SAP.P044.T8

Two independently universally quantified conjuncts:

1. For every R>0,N>0, every finite decidable-equality exposure type D, bank f:Fin R→Fin N→D, real schedules y,w, selected a:D, and **positive supplied weights w_i(a) at every unit**, take uniform bank observation probabilities. For every i,j,b the marginal at i,a is c_i(a)/R and joint at i,j,a,b is c_ij(a,b)/R. The w-weighted HT mean expectation is `Σ_i y_i(a)π_i(a)/w_i(a) / N`. If in addition all exact selected marginals are positive, their exact-weight HT mean is unbiased. Without that extra exact-positivity premise, the smoothed-weight mean's bias equals
   `(1/N)Σ_i y_i(a) (c_i(a)−R)/[R(c_i(a)+1)]`.
   For every i, `(c_i(a)/R)/smoothedWeight_i(a)−1` is the same multiplier; it is strictly negative if c_i(a)<R. If D has at least two elements, for every i the sum over b of smoothedWeight_i(b) is `(R+|D|)/(R+1)>1`. The original positive-w hypothesis scopes over **all** these conclusions, even those that do not use w. Subtractions in the bias expression occur after casting to ℝ.
2. For every measurable probability space Ω,μ, every natural R (including 0), p∈[0,1] with **0<p<1**, Boolean random variable D and natural random variable C, assuming D has Bernoulli(p) law, C has binomial(R,p) law, and D,C are independent, the random variable `1_{D=true}/[(C+1)/(R+1)]` is integrable and has expectation `1−(1−p)^(R+1)<1`. HasLaw supplies a.e. measurability. A bank with replacement is represented by the binomial count law; no trial vector is an argument of this theorem.

## SAP.P044.T9

Conjunction of universal statements:

* For every N and real full-assignment outcome schedule y, `Interference y ↔ ¬NoInterference y`.
* For every such y, `NoInterference y` iff for every i and assignments z,z', equality z_i=z'_i implies y_i(z)=y_i(z').
* For every N,A,z,i, peerCount is exactly the cardinality of {j:A_ij=true,z_j=true}.
* For every N,A,i with A_ii=false, and every z,z' agreeing at every j≠i, their peerCounts at i agree.
* For every N,A,z,i, each of the four exposure equalities is equivalent to its defining own-treatment and positive/zero-peer-count case.
* For every N,i,z, rebuilding z by inserting its own coordinate into its restriction to all other units returns z.

N=0 is allowed in these universal identities, but there are nonempty instances. No claim about matrix-expression syntax is included.

## SAP.P044.T10

Conjunction:

1. For every N, decidable-equality community type C, real s, real unit weights t, community map c, units i,j with c_i≠c_j, the defined identity-block edge expression s t_i t_j 1_{c_i=c_j} is zero. No bounds or probability-law premise is imposed on s,t.
2. For every finite Ω, community type C with decidable equality, N, finite probability P, map G from Ω to simple graphs on N units with decidable adjacency, and potentially random community labels c(ω,i), **assume for every i,j** that the sum of P masses of samples having both edge ij and unequal communities is zero. Then for every ω with positive P mass and every edge ij in G(ω), its labels coincide. No generator or independent-edge sampling law is specified.
3. For every N>0, simple graph G on N units with decidable adjacency, community labels c (no decidable-equality instance required), assuming every vertex has strictly positive degree and every edge joins equal labels: the degree sum is 2|E|, N≤2|E|, |E|>0, the within-edge count equals |E|, its real fraction of all edges is 1, and that fraction minus 7/10 is 3/10.
4. For every finite Ω, any C, N>0, finite probability P, graph-valued G with decidable adjacencies and random labels c, **assuming every graph at every ω has positive degree at every vertex and all its edges within communities**, both `E_P[within-count/edge-count]` and `E_P[within-count]/E_P[edge-count]` equal 1, and both minus 7/10 equal 3/10. These assumptions include zero-mass ω as well as support points. The assumptions are not conclusions derived from item 1 or a rejection loop.

## SAP.P044.T13

For every natural N, every Boolean adjacency A on N units, and a proof that all diagonal entries are false, **if N>0** then it is not the case that every unit's `baselineLaw(degreeScale A i)` equals halfNormalLaw. Quantifier order: N,A,looplessness,nonemptiness,then negation of the all-unit law equality. Equivalently there is at least one unit with a different baseline law. Symmetry and absence of isolates are not assumed. The proposition concerns the specified ideal Gaussian marginal laws; it contains no external source-code predicate and does not negate a claim about whether some researcher made a description.
