# Blind reading of the P013b Challenge

This file was written after reading all Defs and Challenge sources and the relevant Mathlib definitions, before opening claims.json or record.json. The Challenge has twelve stubs, T15–T19 and T21–T27. Each asserts the corresponding `SAP.P013b.T…Statement`; none has additional binders outside that definition.

## Common objects, notation, and conventions

`Fin N` means the N-element set {0,…,N−1}. All population sums run over that entire set. Unless a clause specifies otherwise, the universally quantified data are a finite type Ω, its Fintype instance, natural numbers N,K, a law P, and a population F. A `Design Ω` is a function p:Ω→ℝ with p(z)>0 for every z and ∑z p(z)=1. Thus a design cannot exist on an empty Ω. Write E X=∑z p(z)X(z), Pr(A)=∑z∈A p(z), Cov(X,Y)=E(XY)−EX·EY and Var(X)=Cov(X,X). These are finite sums, not integrals.

A `Population P N K` consists of an exposure map D:Ω×Fin N→Fin K and arbitrary fixed real potentials y_i(d). Its observed outcome is Y_i(z)=y_i(D_i(z)); this consistency/exposure-sufficiency relation is built into the representation. Put I_i(d,z)=1 if D_i(z)=d, otherwise 0; π_i(d)=EI_i(d); π_ij(d,e)=E[I_i(d)I_j(e)]. `Positivity F d` means **every** i satisfies 0<π_i(d)<1. Some later statements explicitly require only the lower inequality.

Write T_d=∑i y_i(d), μ_d=T_d/N, τ_de=μ_d−μ_e, H_d(z)=∑i I_i(d,z)y_i(d)/π_i(d), and H_de(z)=(H_d(z)−H_e(z))/N. The library's division is real field division, so a/0=0, including 0/0. Positive-population/positive-marginal hypotheses, or the expressly defined ratio convention, determine when this matters.

For every ordered pair i,j define

  B_ij(d,e;z)=I_i(d,z)I_j(e,z)·[(π_ij(d,e)−π_i(d)π_j(e))/π_ij(d,e)]·[y_i(d)/π_i(d)]·[y_j(e)/π_j(e)].

The following estimators are literal definitions:

* V_d=∑i I_i(d)(1−π_i(d))(y_i(d)/π_i(d))²+∑i∑j≠i B_ij(d,d).
* A_d=∑i∑j≠i,π_ij(d,d)=0 [I_i(d)y_i(d)²/(2π_i(d))+I_j(d)y_j(d)²/(2π_j(d))]. The pairs are ordered.
* C_de=∑i∑j≠i B_ij(d,e)−∑i[I_i(d)y_i(d)²/(2π_i(d))+I_i(e)y_i(e)²/(2π_i(e))].
* C^A_de=∑i∑j≠i,π_ij(d,e)>0 B_ij(d,e)−∑i∑j,π_ij(d,e)=0 [I_i(d)y_i(d)²/(2π_i(d))+I_j(e)y_j(e)²/(2π_j(e))]. The second sum includes i=j.
* W_de=(V_d+A_d+V_e+A_e−2C^A_de)/N².

For fixed numerical predictions g:Fin N→ℝ, put Δ_d(g)=H_d−∑i I_i(d)g_i/π_i(d)+∑i g_i, C_d=∑i I_i(d)/π_i(d), R_d=H_d/C_d, and Δ_de(g,k)=[Δ_d(g)−Δ_e(k)]/N. In particular R_d is zero when C_d=0. Let w_di(z)=I_i(d,z)/π_i(d). Shifting F by c preserves D and replaces every y_i(a) by y_i(a)+c; a superscript c indicates this shifted population. Define L_d(h,c;z)=∑i(1−w_di(z))(h_i−c).

For arbitrary randomization potentials r:Fin N×Ω→ℝ, `Misspecified F r` means ∃i,z,z′ such that D_i(z)=D_i(z′) but r_i(z)≠r_i(z′). The corresponding randomization HT total is H^r_d(z)=∑i I_i(d,z)r_i(z)/π_i(d). The conditional target is Q_d=∑i∑z:D_i(z)=d [p(z)/π_i(D_i(z))]r_i(z).

## T15

For every finite Ω, N,K, P and F, if N>0, then for every d,e, if d≠e and both `Positivity F d` and `Positivity F e` hold, the following conjunction holds:

1. If π_ij(d,e)>0 for every i≠j, then E C_de≤Cov(H_d,H_e).
2. If π_ij(d,e)>0 for every i≠j, and then if y_i(d)=y_i(e) for every i, then E C_de=Cov(H_d,H_e).
3. E C^A_de≤Cov(H_d,H_e), with no cross-joint positivity hypothesis on this clause.
4. Var(H_de)≤E W_de.

Thus positive off-diagonal cross joints condition only the first two conjuncts. No sign restrictions on outcomes are assumed.

## T16

For every finite Ω, N,K, P,F, if N>0, then for every d with 0<π_i(d)<1 for every i, and for every fixed vector g, the conjunction is:

1. EΔ_d(g)=T_d.
2. For every z, Δ_d(g;z)=∑i I_i(d,z)[(Y_i(z)−g_i)/π_i(d)]+∑i g_i.
3. E C_d=N.
4. |E R_d−μ_d|≤sqrt[Var(C_d/N)Var(R_d)].

There is no hypothesis that any unit has exposure d in every assignment; the defined zero ratio on empty exposure samples is included. `Real.sqrt` is the nonnegative square root on nonnegative arguments and zero on negative arguments; variances here are finite-law variances.

## T17

For every finite Ω,N,K,P,F with N>0, for every r and then d,e, if d≠e, r is misspecified in the existential sense above, and both d,e have all marginals strictly between zero and one, then E H^r_d=Q_d and E[(H^r_d−H^r_e)/N]=(Q_d−Q_e)/N. The existential witness of misspecification may concern any exposure, not necessarily d or e. No bound or sign restriction on r is assumed.

## Sequence definitions used in T18 and T19

An `ExperimentSequence` S chooses, for each n≥0, a natural support size s_n, exposure size k_n, a positive normalized law on Fin s_n, and a population of size **n+1**. It also chooses d_n,e_n∈Fin k_n, proves d_n≠e_n, and proves positivity strictly between zero and one for all units at those two labels. Write N_n=n+1, X_n=H_{d_ne_n}, t_n=τ_{d_ne_n}, v_n=Var(X_n), and W_n=W_{d_ne_n} under the nth experiment.

`NestedPopulationSetup S` asserts, in order, the existence of injections ℓ_n:Fin k_n↪ℕ, fixed natural labels d≠e and one array y:ℕ×ℕ→ℝ, such that ℓ_n(d_n)=d and ℓ_n(e_n)=e for every n and the nth potential for unit i and label a equals y(i.val,ℓ_n(a)). It does not couple the assignment laws across n. `StandingPositivity` additionally requires 0<π_ni(a)<1 for every n, unit i and **every** exposure a.

`Condition3` means ∃c1,c2∈ℝ, c1≥0 and c2>0, such that for every n,i,a, |y_ni(a)|≤c1 and |1/π_ni(a)|≤c2. These constants are uniform in n,i,a.

`PairIndependent F i j` means π_ij(a,b)=π_i(a)π_j(b) for every exposure pair a,b. `Condition4` means ∃Boolean matrices g_n, with g_n(i,j)=false implying this pair independence for every n,i,j, and ∑i∑j 1{g_n(i,j)=true}/N_n²→0. Diagonal entries are counted and no symmetry is required.

For finite unit sets A,B, `VectorIndependent P D A B` means: for every pair of complete label vectors a,b:Fin N→Fin K, Pr[(∀i∈A,D_i=a_i)∧(∀j∈B,D_j=b_j)]=Pr[∀i∈A,D_i=a_i]Pr[∀j∈B,D_j=b_j]. The predicate `PrintedNoEdge h A B` literally says there do **not** exist i,j with h(i,j)=true and at least one of

  (i∈A and j∉B), (j∈A and i∉B), (i∉A and j∈B), (j∉A and i∈B).

These complements are part of the definition. `PrintedDependency` requires vector independence whenever A,B are disjoint and this literal `PrintedNoEdge` predicate holds. `RowBound h m` means ∑j 1{h(i,j)=true}≤m for every i. `Condition5Printed` means ∃natural m, then ∃Boolean matrices h_n, such that for every n both `PrintedDependency` and `RowBound h_n m` hold. There is no symmetry or irreflexivity hypothesis on h_n.

`Condition6` means ∃c>0 with N_n v_n→c. `ConvergesInProbability P X a` means for every real ε>0, Pr_n[ε<|X_n−a|]→0.

Let Φ(x)=ProbabilityTheory.cdf(ProbabilityTheory.gaussianReal 0 1)(x). Mathlib's Gaussian second parameter is the nonnegative variance, so this is the standard normal probability law; its cdf is Pr[Z≤x]. Set q_α=inf{x∈ℝ:1−α/2≤Φ(x)}. On 0<α<1 this is the usual finite normal quantile. Define coverage c_n(α)=Pr_n[W_n≥0 and |X_n−t_n|≤q_α sqrt(W_n)]. Negative W_n gives a false coverage event; it is not treated as a zero-width interval. These probabilities lie in [0,1]. Mathlib's real filter liminf along `atTop` is the supremum of eventual lower bounds; on this bounded sequence it is the usual liminf, with no unbounded-infimum convention involved.

## T18

The statement is the **negation** of the following universally quantified implication: for every S, nestedness implies standing positivity implies Condition3 implies Condition5Printed implies Condition6 implies that for every α, if 0<α and α<1 then 1−α≤liminf_n c_n(α).

Equivalently in classical mathematics, there exist S and α such that S has all five stated properties, 0<α<1, and liminf_n c_n(α)<1−α. Neither a named witness nor any additional conclusion about normal approximation is included in the theorem type.

## T19

For every S, if it is nested, has standing positivity, satisfies Condition3, and satisfies Condition4, then for every ε>0, Pr_n[ε<|(X_n−t_n)−0|]→0. There is no Condition5 or Condition6 assumption and no assertion of a rate or limiting normal law.

## T21

This is an unconditional conjunction about one fixed finite example. Ω=Fin 3, with p(0)=p(1)=1/4 and p(2)=1/2; N=3,K=2; D_i(z)=1 exactly when z=i. Let g=(2,3,5), and set y_i(0)=y_i(1)=g_i. The statement asserts all of the following (each universal quantifier has only the indicated finite domain):

* For every i, π_i(1)=p(i), π_i(0)=1−p(i), and Cov(constant g_i,I_i(1))=0; every label has positivity. For every i,d, y_i(d)=g_i. Every assignment has one unit with label 1 and two with label 0.
* For every d, T_d=10 and T^1_d=13. Both τ_10 and τ^1_10 are zero. For every z,d, Δ_d(g;z)=10, and for every z, Δ_10(g,g;z)=0.
* For every z, writing the value for z=2 first and for z=0,1 second: C_1 is 2 or 4; C_0 is 8/3 or 10/3; Δ^1_1(g) is 12 or 14; Δ^1_0(g) is 38/3 or 40/3; Δ^1_10(g,g) is −2/9 or 2/9.
* It repeats positivity, zero prediction/indicator covariances, and the one/two exposure counts; τ^1_10=τ_10. At **every** assignment, Δ^1_d(g)≠Δ_d(g)+3 for d=1 and d=0, and Δ^1_10(g,g)≠Δ_10(g,g).
* The shifted total estimators both have expectation 13; the shifted contrast has expectation 0. Both baseline total estimator variances and the baseline contrast variance are zero. Shifted variances are respectively 1, 1/9, and 4/81.
* For every z, shifting predictions too, to g+1, makes both shifted Δ totals 13 and the shifted contrast 0. For every z,i the three residuals Y_i−g_i, Y^1_i−g_i, and Y^1_i−(g_i+1) are respectively 0,1,0.
* For every z, Δ^1_d(g)=10+C_d for d=1,0. The errors Δ^1_d(g)−Δ_d(g)−3 are −1 or 1 for d=1 and −1/3 or 1/3 for d=0, with the same case order as above. The contrast change equals (C_1−C_0)/3 and the displayed ±2/9 values.

There are no external hypotheses or random predictions.

## T22

This is a conjunction of twelve separately universally quantified clauses and one fixed example. In clauses (a)–(c) the binder order is finite Ω,N,K,P,F,d,g,h,c,z, then N>0 and ∀i,π_i(d)>0. With the common definitions above, they respectively assert:

(a) Δ^c_d(g+h;z)−Δ_d(g;z)=cC_d(z)+∑i(1−w_di(z))h_i.

(b) Δ^c_d(g+h;z)−Δ_d(g;z)−cN=L_d(h,c;z).

(c) Δ^c_d(g+h;z)=Δ_d(g;z)+cN iff L_d(h,c;z)=0.

(d) Universally bind the same data without h, in order F,d,g,c,z,N>0,positive d marginals. Then Δ^c_d(g+c;z)=Δ_d(g;z)+cN.

(e) Universally bind F,N>0,d,e,g,k,c,z,positive d marginals,positive e marginals,d≠e. Both shifted difference means with predictions g+c and k+c equal their baseline difference means plus c. Each observed residual at exposure d or e is unchanged when both outcomes and the appropriate predictions shift by c. Δ^c_de(g+c,k+c)=Δ_de(g,k). Both corresponding potential totals increase by cN, and τ^c_de=τ_de.

(f) Universally bind F,N>0,d,e,g,k,h,l,c,z,positive d/e marginals,d≠e. Then Δ^c_de(g+h,k+l)−Δ_de(g,k)=[L_d(h,c)−L_e(l,c)]/N, and the contrast is unchanged iff L_d(h,c)=L_e(l,c).

(g) Universally bind F,N>0,d,e,g,k,c,z,positive d/e marginals,d≠e. With predictions fixed, Δ^c_d(g)−Δ_d(g)=cC_d; subtracting cN gives c(C_d−N); and Δ^c_de(g,k)−Δ_de(g,k)=c(C_d−C_e)/N. If c≠0, total translation equivariance is equivalent to C_d=N and contrast invariance is equivalent to C_d=C_e, all pointwise at z.

(h) For all finite Ω,N,K,P,F,d,i with π_i(d)>0, E w_di=1. No N>0 or second exposure hypothesis is present in this clause.

(i) For F,N>0,d,e,c,z,positive d/e marginals,d≠e, zero predictions give Δ_d(0)=H_d and Δ_de(0,0)=H_de. H^c_d−H_d=cC_d and H^c_de−H_de=c(C_d−C_e)/N.

(j) For F,d,g,h,c and positive d marginals, E L_d(h,c)=0; EΔ^c_d(g+h)=EΔ_d(g)+cN=T_d+cN; E C_d=N. This clause does not require N>0.

(k) For F,d,e,c,positive d/e marginals,N>0,d≠e, E[c(C_d−N)]=0 and E[c(C_d−C_e)/N]=0.

(l) For F,N>0,d,natural m,1≤m, if every assignment has ∑i I_i(d)=m and every π_i(d)=m/N, then for every fixed g,c and every z, C_d(z)=N and Δ^c_d(g;z)=Δ_d(g;z)+cN. No separate marginal-positivity hypothesis occurs here; it follows from the stated count/marginal conditions.

(m) In the fixed calibration design Ω=Fin 2 with equal weights, N=2,K=2,D_i(z)=1 iff z=i and all outcomes zero, both labels have positivity; for every assignment C_1=2 and Δ^1_1(0)=Δ_1(0)+2.

The Ω,N,K,P quantifiers are repeated independently in every general clause, not shared existential choices. All prediction/increment vectors are deterministic numerical functions of the unit index.

## Recording definitions for T23 and T24

A `Recording N K` is a fixed Boolean function R_i(d). The recorded population has the same D and potentials G_i(d)=y_i(d) if R_i(d)=true, otherwise 0. Define lost mean m_d=N^−1∑i:R_i(d)=false y_i(d). Recorded data is the **entire assignment-indexed function** (z,i)↦(D_i(z),G_i(D_i(z)),R_i(D_i(z))). This is more information than one realized record.

For fixed realized D:Fin N→Fin K, weights w_i, scores G_i and a unit set T, let A_d(T)=∑i∈T,D_i=d w_iG_i and B_d(T)=∑i∈T,D_i=d w_i. These are `recordedNumerator` and `recordedDenominator`.

## T23

This is an unconditional three-world example, indexed by world u∈Fin 3. The design is Ω=Fin 2×Fin 2, each assignment z=(z1,z2) of probability 1/4; N=2,K=2; unit 0 has exposure z1 and unit 1 has exposure z2. Unit 0 potentials (at labels 0,1) are (0,1). Unit 1 potentials are (0,0) in world 0, (0,1) in world 1, and (1,0) in world 2. Recording retains unit 0 at both exposures and discards unit 1 at both. The respondent population has only unit 0, with the same assignment law and potentials (0,1).

For every world all potentials are binary; every marginal is 1/2 and lies strictly between zero and one; every observed recorded outcome equals its indicator expansion. For every world its entire recorded-data function equals that of world 0. For every world,z the recorded HT contrast H^G_10(z)=z1 (as a real 0/1); its expectation is 1/2, variance 1/4, and recorded causal contrast 1/2. The wearing contrasts in worlds 0,1,2 are respectively 1/2,1,0. The lost means (m_0,m_1) are respectively (0,0),(0,1/2),(1/2,0). Hence the three biases E H^G_10−τ_10 are 0,−1/2,1/2.

There does not exist a single function h from entire assignment-indexed recorded-data functions to ℝ that recovers τ_10 in every world. For every world, the respondent HT contrast is pointwise 2z1 with expectation 1; the recorded full-population HT contrast is pointwise half the respondent contrast; respondent biases against the full-population wearing contrasts are 1/2,0,1 respectively. For every world,z,i the exact record is (z1,z1,true) for i=0 and (z2,0,false) for i=1. In every world the full recorded estimator bias is m_0−m_1 and the difference between respondent and full recorded estimator expectations is 1/2.

## T24

The first clause universally binds finite Ω,N,K,P,F, then recording R, N>0, d,e,d≠e, all positive d marginals, all positive e marginals. It asserts this conjunction:

* E H^G_d/N=μ^G_d, and E H^G_de=τ^G_de.
* For every exposure a, μ^G_a=μ_a−m_a; τ^G_de=τ_de−m_d+m_e; E H^G_de−τ_de=m_e−m_d.
* E H^G_de=τ_de iff m_d=m_e; E H^G_d/N=μ_d iff m_d=0.
* For every a, if every y_i(a)≥0, then m_a≥0 and m_a=0 iff every discarded unit at a has y_i(a)=0.

The second, separately quantified clause binds the same data and hypotheses in that order and additionally assumes nonnegative outcomes at d and e and that every discarded potential at each is zero. It concludes E H^G_de=τ_de. It does not separately assert that this sufficient condition is strictly stronger than equality of lost means.

The third clause universally binds N,K,realized D,w,G,S,SR, then SR⊆S, |S|>0, |SR|>0, positive w_i for i∈S, and that every i∈S with G_i≠0 lies in SR, followed by d,e. It asserts:

* For every a, A_a(SR)=A_a(S).
* A_d(S)/|S|=(|SR|/|S|)A_d(SR)/|SR|.
* [A_d(S)−A_e(S)]/|S|=(|SR|/|S|)[A_d(SR)−A_e(SR)]/|SR|.
* If B_d(SR)>0, then A_d(S)/B_d(S)=[B_d(SR)/B_d(S)]A_d(SR)/B_d(SR).

The fourth clause separately universally binds N,K,D,w,G,S,item,survey and assumes item⊆S, survey⊆S, |S|=2050, |item|=1708, |survey|=1899, positive weights on S, and that every nonzero G_i in S belongs to both retained sets, then binds d,e. It concludes that the full-set HT contrast (normalizer 2050) equals 854/1025 times the item-set contrast (normalizer 1708), and equals 1899/2050 times the survey-set contrast (normalizer 1899). These cardinalities and zero-score conditions are **hypotheses**, not facts proved about a data set. There is no asserted item⊆survey relation.

The fifth clause is one fixed example: N=3,K=2, D=(1,1,0), w=(2,2,2), G=(1,0,1), S={0,1,2},SR={0,2}. Every nonzero G belongs to SR; the retained/full Hajek denominator factors are 1/2 for exposure 1 and 1 for exposure 0; no real scalar c makes the full-set Hajek contrast equal c times the retained-set Hajek contrast (the latter is zero, the former −1/2).

The last clause asserts the arithmetic identities 2050−342=1708 and 2050−151=1899 in ℕ, 1708/2050=854/1025, 342/2050=171/1025, and 1899/2050+151/2050=1 in ℝ. Both natural subtractions have a larger minuend, so are ordinary nonnegative differences here.

## School definitions for T25 and T26

`School` is Fin 14×Fin 4 (56 schools in 14 blocks of four). The blocked assignment support B consists of all functions b↦a two-element subset of Fin 4. Mathlib `Fintype.piFinset` takes all such functions and `powersetCard` takes all subsets of exactly the specified size. Its host set is {(b,j):j∈z(b)}. The complete assignment support C is all 28-element subsets of School. Both laws below are uniform on these exact finite supports. The exceptional host set H* consists of all four schools in each of blocks 0,…,6.

For any finite set S, U_S X=∑z∈S X(z)/|S|, P_S(A)=|{z∈S:A(z)}|/|S|, and V_S X=U_S(X²)−(U_S X)². A general S is not explicitly assumed nonempty in the moment clauses of T25, but the marginal-equals-1/2 hypotheses would force it. Empty-support division is otherwise defined as zero. The two named supports have explicit positive-cardinality assertions in T26.

For distinct schools a,b define u_i=1{i=a or i=b}. The binary potential outcome is y_i(true)=u_i, y_i(false)=0; under any Boolean host map, J_i(z)=1{hosts(z,i)=true}, the observed outcome is J_i u_i. Define H_ab(z)=∑i J_i(z)u_i/(1/2) and

  V_ab(q;z)=∑i J_i(1−1/2)(u_i/(1/2))²
    +∑i∑j≠i J_iJ_j[(q−1/4)/q](u_i/(1/2))(u_j/(1/2)).

The host maps for B and C are membership in their respective host sets.

For T26's student statements, independently bind an arbitrary finite type Ξ and probability mass Q:Ξ→ℝ with Q≥0 and ∑x Q(x)=1, a student-to-school map s:Fin N→School, and a code function k:Ξ×Fin N→Fin 4. Given a host bit and a code t, exposure is 0 when not hosting and t.val+1 when hosting. Student marginal and joint probabilities are expectations of the relevant indicator(s) under the **product** of the uniform school law and Q. There is no required independence among students inside Q; independence of the student law from school assignments is built into the product formula.

## T25

This unconditional conjunction asserts:

1. H* has 28 schools, belongs to C, and equals no host set from B. Its probability under C is 1/7648690600760440>0 and under B is 0.
2. For every distinct a,b all school potentials just defined are binary, their total at true is 2, their values at false are all zero; for every type α, host map, assignment z and school i, the observed-outcome identity is J_i u_i.
3. For every type α, host map, distinct a,b,z, H_ab=2(J_a+J_b) and ∑i u_i=2.
4. For every type α, host map, distinct a,b, real q,z, if q>0 then V_ab(q)=2(J_a+J_b)+8J_aJ_b(q−1/4)/q.
5. For every α,S,host map,distinct a,b,real p,q, if P_S(J_a=1)=P_S(J_b=1)=1/2 and P_S(J_a=J_b=1)=p, and then q>0, U_S H_ab=2, V_S H_ab=8p, and U_S V_ab(q)=2+8p(q−1/4)/q.
6. For the same general data with p>0 and the stated marginals and joint p, U_S V_ab(p)=V_S H_ab.
7. Under B, a=(0,0),b=(0,1) have E H=2, Var H=4/3 and E V(27/110)=160/81. With a=(0,0),b=(1,0), Var H=2 and E V(27/110)=53/27<2. Under C the same-block pair has Var H=108/55 and E V(27/110)=108/55.
8. The same-block and different-block biases under B with input 27/110 are 52/81 and −1/27, respectively.
9. Every school under both named laws has hosting and nonhosting probabilities 1/2. The B joint hosting probabilities for the two specified pairs are 1/6 and 1/4; the specified C joint is 27/110. Finally 1/binomial(56,28)=1/7648690600760440.

## T26

This unconditional conjunction asserts:

* |B|=6^14=78364164096; |C|=binomial(56,28)=7648690600760440. Every host set induced by an element of B lies in C. H* lies in C but is induced by no element of B.
* For every school, each named law has hosting marginal 1/2. For every ordered pair of distinct schools, joint hosting under B is p=1/6 when they are in the same block and p=1/4 otherwise; under C it is 27/110. C minus B is respectively 13/165 or −1/220, and is never zero.
* For every ordered pair of distinct schools, the complete B table in order (nonhost,nonhost),(nonhost,host),(host,nonhost),(host,host) is (p,1/2−p,1/2−p,p); the C table is (27/110,14/55,14/55,27/110).
* For every finite Ξ,N>0,Q≥0 normalized to one,s,k as above, all student exposure marginals under B×Q and C×Q are equal, for every student and every d∈Fin 5. For every i,j,d,e, if s(i)=s(j), their student joint exposure probabilities also agree. The binders occur in the order N>0,Q,nonnegativity,normalization,s,k.
* For every Boolean host and code, the hosted-exposure function equals zero iff host=false.
* For every finite Ξ,N,Q≥0 normalized to one,s,k (here N>0 is absent), each student's exposure-0 marginal under both laws is 1/2. For every i,j in distinct schools, their joint exposure-(0,0) probabilities are 1/6 or 1/4 under B according to block agreement and 27/110 under C.
* It additionally asserts the exact counting/probability arithmetic binomial(4,2)=6, binomial(4,2)^14=6^14, (3·6^13)/6^14=1/2, binomial(55,27)/binomial(56,28)=28/56=1/2, 6^13/6^14=1/6, (3²·6^12)/6^14=1/4, and binomial(54,26)/binomial(56,28)=(28·27)/(56·55)=27/110.

No claim here identifies either abstract law with an actual released program.

## T27

The quantifier order is: finite Ω,N,M; a design P; N>0; an injection analysed:Fin N→Fin M; a school map Fin M→Fin 56; arbitrary host bits Ω×Fin 56→Bool; arbitrary student-assignment bits Ω×Fin M→Bool; neighbor sets on Fin M; real potentials y:Fin N×Fin 5→ℝ; binary potentials at every i,d; no self neighbors; symmetric neighbors; all neighbors in the same school; and positive marginal exposure probabilities at every analyzed i and every d∈Fin 5.

For analyzed unit i, take the host bit of its school, its own assignment bit, and the peer bit indicating that at least one member of its neighbor set is assigned. Exposure is 0 when its school is not hosting; otherwise exposure is 1 for (own=false,peer=false), 2 for (false,true), 3 for (true,false), and 4 for (true,true). The potentials are exactly y; observed outcomes are defined by selecting the potential at this exposure.

The conclusion is: for every z,i the observed outcome equals ∑d I_i(d,z)y_i(d); and for every d≠0, τ_d0=(∑i y_i(d))/N−(∑i y_i(0))/N and E H_d0=τ_d0. Because the potentials are binary, each sum divided by N is a proportion. There is no law-specific restriction on hosts or assignments, no response/recording variable, no assertion about the realized empirical outcomes, and no numerical Table 2 estimates.

## Mathlib source trail

The only non-elementary external meanings are traced to `Mathlib/Probability/Distributions/Gaussian/Real.lean` (`gaussianReal`, a Gaussian with mean μ and variance v), `Mathlib/Probability/CDF.lean` (`cdf_eq_real` for probability measures), and `Mathlib/Order/LiminfLimsup.lean` (`liminf`, dual to the supremum/infimum definitions through mapped filters). The finite combinatorial constructions are `Mathlib/Data/Fintype/Pi.lean` (`piFinset`) and `Mathlib/Data/Finset/Powerset.lean` (`powersetCard`). All other operations above are finite real arithmetic, ordinary order/topological convergence, finite sets/functions, field division, and the real square root. No SAP symbol in a theorem type is being treated as an uninterpreted predicate.
