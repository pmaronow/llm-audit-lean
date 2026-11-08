# Blind reading of the Lean statements

This file was written and saved after reading only `SAP/P025b/Defs.lean`, all seven `Defs/Part*.lean` files, the two Challenge files, and the relevant Mathlib definitions. Neither `claims.json` nor `record.json` has been opened at this stage. The mathematical assertions below come from the types, not the Challenge docstrings.

## Shared notation, fully expanded

`Fin n` is the ordered set of integers 0 through n-1. Every unqualified finite sum is over the entire indicated finite type. Real division is Lean's total field division (in particular division by zero is zero); the statements must therefore supply the conditions under which a quotient has its ordinary meaning.

For functions y,a,w on a finite set I, put

* R(y,a,w) = (sum_i a_i w_i y_i)/(sum_i a_i w_i).
* B(alpha,beta) = {w : for every i, 1/beta <= w_i <= 1/alpha}.
* A(y,a;alpha,beta) = {R(y,a,w) : w in B(alpha,beta)}.
* L(y,a;alpha,beta) = sInf A and U(y,a;alpha,beta) = sSup A, in the conditionally complete ordered real field. These are total real-valued operations; interpreting them as ordinary infimum/supremum requires nonempty bounded sets.
* A_norm(y,a;gamma) uses 1 <= w_i <= gamma instead.
* For a nonempty vector y of length n, bar(y) = (sum_i y_i)/n (`populationMean`). The definition itself does not require n>0.
* l^k_i = gamma if i<k, and 1 otherwise; u^k_i = 1 if i<k, and gamma otherwise. Here k is a natural-number prefix length; the definitions accept k=0, k=n, and even k>n.
* l_k(y,a,gamma)=R(y,a,l^k), u_k(y,a,gamma)=R(y,a,u^k).
* `lowerCut y a gamma k` means that k is the **least element** of {j in {0,...,n-1} : l_j(y,a,gamma)<=y_j}. Thus it asserts membership and absence of an earlier qualifying index. `upperCut` uses u_j<=y_j with exactly the same least-index convention. These predicates do not search the extra cut n.
* Sep(y,a,gamma) means, for every k=0,...,n-1, BOTH y_k != u_k(y,a,gamma) and y_k != l_k(y,a,gamma). There is no condition at cut n or beyond.
* b = (0,1); bL(p,gamma)=p/[gamma(1-p)+p]; bU(p,gamma)=gamma p/[(1-p)+gamma p].

Mathlib `IsLeast S x` and `IsGreatest S x` include x in S, as well as the appropriate bound on every member. `IsGLB S x` and `IsLUB S x` assert the greatest lower bound and least upper bound; they do NOT assert attainment. A monotone vector satisfies i<=j => y_i<=y_j; a strictly monotone vector satisfies i<j => y_i<y_j. Function equality is pointwise equality. `Icc x y` is the closed interval [x,y].

A finite design d consists of a finite outcome type K, a finite sample S(omega) of population units at each outcome, and real probabilities p(omega)>=0 summing to 1. Its expectation of X is sum_omega p(omega) X(omega). Its inclusion probability is pi_i=sum_omega p(omega) 1_{i in S(omega)}. For a finite population I, a class map c:I -> {0,...,J-1}, and class j, define M_j=sum_{i:c(i)=j} pi_i and C_j(omega)=sum_i 1_{c(i)=j and i in S(omega)}.

The PMF of a design has masses `ENNReal.ofReal p(omega)`; nonnegativity and total mass 1 are part of the design, so these are the original probabilities, without truncation changing them. `jointLaw d` is Mathlib `Measure.infinitePi` of the same PMF measure at all natural coordinates, on K^N with its product sigma-algebra. The finite measurable-singleton assumption in the convergence theorems makes every subset of K measurable. Mathlib's product construction has a fallback zero measure when its inputs are not probability measures, but PMF measures ARE probability measures, so this fallback does not occur here. This is the ordinary iid replication law.

For h>=0, the pooled index type is {0,...,h-1} x I, with outcome y_{c(i)} and coefficient a_{r,i}=1_{i in S(omega_r)}. Pooled L_h and U_h mean L and U for that full index type and those coefficients. Copies of a unit in distinct replications remain distinct observations. `pooledNonempty d h omega` means there exists r<h with S(omega_r) nonempty. Pooled endpoints are total even when every sample is empty. A convergence assertion PC(d,c,y,alpha,beta) means: outside a `jointLaw d` null set, there exists H (depending on the path) such that every h>=H has a nonempty pooled sample, AND L_h -> L(y,M;alpha,beta), AND U_h -> U(y,M;alpha,beta). `Tendsto` with `atTop` and `nhds` is ordinary sequential real convergence; almost-everywhere means the failure set has measure zero, not a universal-path statement.

For positive integer class sizes m_j, AC(alpha,beta,mass,m) means, for every j, m_j>0 and alpha m_j <= mass_j <= beta m_j. SC(alpha,beta,q,m) means there exists a real T>0 with AC(alpha,beta,Tq,m). Class mean mu(y,m)=(sum_j m_j y_j)/(sum_j m_j). CM(y,q;alpha,beta) is the set of these means for SC-compatible positive integer m. ACM uses AC for a fixed mass vector. KCM additionally imposes sum_j m_j=N for a fixed natural N. Class proportions are r_j(m)=m_j/(sum_k m_k). Weight proportions are r_j(q,W)=W_j q_j/(sum_k W_k q_k). PR(q,gamma) is the set of real r satisfying r_j>=0 for all j, sum_j r_j=1, and r_j q_k <= gamma r_k q_j for EVERY ordered pair j,k. A rational vector has, at each coordinate, an exactly equal rational number, coerced to R.

These expand every SAP definition used in the theorem types. The primitive Mathlib meanings were checked in `Order/Bounds/Defs.lean`, `Order/Monotone/Defs.lean`, `Order/Filter/Defs.lean`, `Order/Filter/AtTopBot/Defs.lean`, `MeasureTheory/OuterMeasure/AE.lean`, `MeasureTheory/MeasurableSpace/Defs.lean`, `Probability/ProbabilityMassFunction/{Basic,Constructions}.lean`, and `Probability/ProductMeasure.lean`.

## SAP.P025b.T12

This is one closed conjunction with no hypotheses or external parameters. Let d be the census of two units, with the sole sampling outcome having probability 1 and sample {0,1}. Then:

1. Every unit has inclusion probability 1, and b=(0,1) is nondecreasing.
2. For EVERY natural k, u^k with gamma=1 is the vector (1,1).
3. 1/1=1; u_0(b,1,1)=u_1(b,1,1)=u_2(b,1,1)=1/2; and u_1-u_0<=0.
4. It is false that u_0<=b_0.
5. The least k in {0,1} with u_k>=u_{k+1} is 0, whereas `upperCut b 1 1 1` holds: the least k in {0,1} with u_k<=b_k is 1.
6. The two explicitly written real expressions 0*0-0+1*1*(0-1) and 0-0*1+1*1*(0-1) both equal -1.
7. It is false that R(b,1,(1,1))>R(b,1,(1,1)).

There is no assertion here about the whole feasible box, L or U, or any general Proposition 1 formula.

## SAP.P025b.T13

Quantifiers, in order: for every natural N>0, every natural J>0, every finite type K equipped with a measurable space and measurable singletons, every finite design d on population Fin N and outcomes K, every surjective class map c:Fin N -> Fin J, every strictly increasing real vector y on Fin J, and all real alpha,beta satisfying 0<alpha<=beta<=1, assume EVERY population inclusion probability lies in [alpha,beta]. The conclusion is the conjunction

PC(d,c,y,alpha,beta) AND [Sep(y,M,beta/alpha) => PC(d,c,y,alpha,beta)].

Thus the first conclusion is unconditional on separation; the second repeats it under separation. It concerns the actual pooled optimization endpoints, and explicitly includes eventual pooled nonemptiness. Strictly increasing y and surjective c express distinct, inhabited outcome classes. No fixed sample size or positive lower bound on the sample size of an individual outcome is assumed.

## SAP.P025b.T14

This is a closed conjunction. The population is {(j,t):j=0,1,2; t=0,1}; sampling outcomes are all triples of zero-one choices with probability 1/8 each. Each outcome selects exactly (0,choice_0),(1,choice_1),(2,choice_2). The class map is first projection, and the class outcomes are y=(0,2,3). The statement asserts:

1. Every unit has inclusion probability 1/2. All three class totals M_j are 1. For every sampling outcome and every class, C_j=1.
2. u_1(y,1,2)=u_2(y,1,2)=2.
3. The set A(y,1;1/4,1/2) has attained minimum 5/4 and attained maximum 2.
4. For EVERY infinite sequence of choices, and EVERY natural h>0, the pooled sample is nonempty.
5. Every inclusion probability lies in [1/4,1/2], but Sep(y,M,2) is false; L(y,M;1/4,1/2)=5/4 and U(y,M;1/4,1/2)=2.
6. For EVERY infinite sequence of choices and EVERY h>0, pooled L_h=5/4 and U_h=2. For EVERY such sequence, L_h tends to 5/4 and U_h tends to 2 as h tends to infinity.

The limit assertion permits the arbitrary total-definition values at h=0. There are no polynomial identities, named optimizer vectors, or onto assertions about pooled weight sums in the type.

## SAP.P025b.T15

Quantifiers, in order: for every natural J>0, all real vectors y,q on Fin J, assume y strictly increases, every q_j>0, and sum q_j=1. For all real alpha,beta assume 0<alpha<=beta<=1, and assume there EXISTS at least one integer vector m with SC(alpha,beta,q,m). Under all these hypotheses the following entire conjunction holds:

1. For EVERY integer vector m and EVERY real mass vector mass with every mass_j>0 and AC(alpha,beta,mass,m), the vector W_j=m_j/mass_j belongs to B(alpha,beta), and R(y,mass,W)=mu(y,m).
2. For EVERY SC-compatible m, L(y,q;alpha,beta)<=mu(y,m)<=U(y,q;alpha,beta).
3. L(y,q;alpha,beta) is the GLB of CM(y,q;alpha,beta), and U is its LUB. This does not assert that either belongs to CM.
4. The set of weight proportions r(q,W) for W in B(alpha,beta) equals PR(q,beta/alpha).
5. The possible real objectives sum_j r_j y_j over PR have attained minimum L and attained maximum U.
6. For EVERY real vector r, there exists an SC-compatible integer m with r(m)=r IF AND ONLY IF r belongs to PR and every coordinate of r is rational.
7. L belongs to CM IF AND ONLY IF there exists rational r in PR with sum r_j y_j=L. The analogous equivalence holds for U.
8. For EVERY real mass vector and integer vector m, AC is equivalent to: for every j, m_j>0 and mass_j/beta<=m_j<=mass_j/alpha.
9. For EVERY strictly positive real mass vector and EVERY AC-compatible m, L(y,mass;alpha,beta)<=mu(y,m)<=U(y,mass;alpha,beta).
10. For EVERY real mass vector, natural N and real v, v belongs to KCM(y,mass;alpha,beta,N) IF AND ONLY IF there exists an integer m with every m_j>0, mass_j/beta<=m_j<=mass_j/alpha, sum m_j=N, and mu(y,m)=v.
11. For EVERY real mass vector and integer vector m, AC is equivalent to: all m_j>0, AND for EVERY class j there EXISTS a vector pi of length m_j, each pi_i in [alpha,beta], summing to mass_j. These per-class vectors need not be distinct or specify a joint sampling design.

The existence hypothesis on SC precedes and scopes all eleven conclusions, including those about separate mass vectors. No automatic-compatibility theorem for beta>alpha or ratio-one characterization of compatible q is asserted. No strict failure of sharpness for retained information is asserted.

## SAP.P025b.T16

This is a closed conjunction with two concrete examples.

First example: on population {0,1,2}, a uniformly chosen unit is omitted and the other two sampled. Classes are (0,1,1), class outcomes b=(0,1), and unit outcomes (0,1,1). Every inclusion probability is 2/3; M=(2/3,4/3); bar(y)=2/3. For EVERY integer vector m of length two,

AC(1/2,3/4,(2/3,4/3),m) iff m=(1,2).

The mean of this vector is 2/3. At gamma=3/2 and cut 1, l_1=4/7 and u_1=3/4; 2/3-4/7=2/21, 3/4-2/3=1/12, and 4/7<2/3<3/4. Sep(b,(2/3,4/3),3/2) holds. The entire ACM set is the singleton {2/3}; 4/7 is not its GLB and 3/4 is not its LUB. The entire continuous weight box A(b,(2/3,4/3);1/2,3/4) has attained minimum 4/7 and attained maximum 3/4.

Second example: for EVERY integer vector m of length two,

[AC(1/10,1/5,(50,100),m) AND m_0+m_1=1000] iff [m_0+m_1=1000 AND 500<=m_1<=750].

For EVERY natural k with 500<=k<=750, AC holds for m=(1000-k,k). The subtraction is natural truncated subtraction, but k<=750<1000 makes it ordinary subtraction here. mu(b,(250,750))=3/4; l_1(b,(50,100),2)=1/2 and u_1=4/5; 4/5-3/4=1/20 and 3/4<4/5. KCM for mass (50,100), alpha=1/10, beta=1/5, and N=1000 equals EXACTLY {k/1000: k natural, 500<=k<=750}, with attained minimum 1/2 and attained maximum 3/4. U(b,(50,100);1/10,1/5)-3/4=1/20. The full continuous box A for those masses and bounds has attained minimum 1/2 and attained maximum 4/5.

No specified endpoint weight vector or sampling design for the second example is part of this conjunction.

## SAP.P025b.T17

This is a closed numerical conjunction. For EVERY INTEGER k, independently for the three rows:

* |100 k/48 - 91.7|<=0.05 iff k=44;
* |100 k/160 - 67.5|<=0.05 iff k=108;
* |100 k/579 - 50.3|<=0.05 iff k=291.

It asserts the exact percentage values 100 bL(44/48,2)=1100/13, 100 bL(44/48,4)=220/3, 100 bU(291/579,5/4)=48500/869, 100 bL(291/579,3/2)=9700/241, 100 bU(291/579,3/2)=9700/161, and 100 bU(291/579,5/2)=48500/677.

The finite list `tableCells` consists of all 3 rows x 7 gamma values x 2 bounds. Each tuple contains (exact p, rounded p, gamma, upper?, printed t, corrected t). `cellPercent` is 100 bU for upper=true, and 100 bL otherwise. `roundsTenth(x,t)` means t/10-1/20<=x<t/10+1/20 (the lower tie is included, the upper tie excluded). For EVERY list entry, the exact-input percentage rounds to corrected t/10 and the rounded-input percentage rounds to printed t/10. The list has length 42; exactly six entries have different printed and corrected integers; for each entry the printed integer equals either the corrected integer or corrected integer+1.

The complete asserted data, written as printed lower/upper followed by corrected lower/upper percentages, are:

| exact p; rounded p | gamma | printed | corrected |
|---|---:|---|---|
| 44/48; 0.917 | 1 | 91.7 / 91.7 | 91.7 / 91.7 |
| same | 1.25 | 89.8 / 93.2 | 89.8 / 93.2 |
| same | 1.5 | 88.0 / 94.3 | 88.0 / 94.3 |
| same | 2 | 84.7 / 95.7 | 84.6 / 95.7 |
| same | 2.5 | 81.5 / 96.5 | 81.5 / 96.5 |
| same | 3 | 78.6 / 97.1 | 78.6 / 97.1 |
| same | 4 | 73.4 / 97.8 | 73.3 / 97.8 |
| 108/160; 0.675 | 1 | 67.5 / 67.5 | 67.5 / 67.5 |
| same | 1.25 | 62.4 / 72.2 | 62.4 / 72.2 |
| same | 1.5 | 58.1 / 75.7 | 58.1 / 75.7 |
| same | 2 | 50.9 / 80.6 | 50.9 / 80.6 |
| same | 2.5 | 45.4 / 83.9 | 45.4 / 83.9 |
| same | 3 | 40.9 / 86.2 | 40.9 / 86.2 |
| same | 4 | 34.2 / 89.3 | 34.2 / 89.3 |
| 291/579; 0.503 | 1 | 50.3 / 50.3 | 50.3 / 50.3 |
| same | 1.25 | 44.7 / 55.9 | 44.7 / 55.8 |
| same | 1.5 | 40.3 / 60.3 | 40.2 / 60.2 |
| same | 2 | 33.6 / 66.9 | 33.6 / 66.9 |
| same | 2.5 | 28.8 / 71.7 | 28.8 / 71.6 |
| same | 3 | 25.2 / 75.2 | 25.2 / 75.2 |
| same | 4 | 20.2 / 80.2 | 20.2 / 80.2 |

Finally bL(44/48,3)=11/14>bU(291/579,3)=291/387, while bL(44/48,4)=11/15<bU(291/579,4)=97/121. For EVERY gamma in {1,5/4,3/2,2,5/2,3}, bU(291/579,gamma)<bL(44/48,gamma) AND bU(0.503,gamma)<bL(0.917,gamma). At gamma=4, 4/5 belongs to the intersection of the two attainable closed intervals for p=44/48 and p=291/579; the same membership holds using p=0.917 and p=0.503.

## SAP.P025b.T18

Quantifiers, in order: every natural n>0, every real outcome vector y of length n, and all real alpha,beta,alpha',beta' satisfying 0<alpha<=beta<=1 and 0<alpha'<=beta'<=1. If beta/alpha=beta'/alpha', then:

1. A(y,1;alpha,beta)=A(y,1;alpha',beta').
2. A(y,1;alpha,beta)=A_norm(y,1;beta/alpha).
3. The two L values are equal, and the two U values are equal.
4. IF beta/alpha=1, then for EVERY real vector w, w belongs to B(alpha,beta) iff w is the constant vector 1/alpha; and L(y,1;alpha,beta)=bar(y) and U(y,1;alpha,beta)=bar(y).

Only coefficients identically one are quantified, rather than arbitrary a. There is no sortedness requirement on y.

## SAP.P025b.T19

Quantifiers, in order: every natural n>0; every nondecreasing real vector y of length n; every alpha,beta with 0<alpha<=beta<=1; every pair of indices kL,kH in {0,...,n-1}. Assume kL is the lower first cut for y,a=1,gamma=beta/alpha, and kH is the upper first cut. Then, for EVERY pair i,j in {0,...,n-1}, if y_i=y_j, both

(1/beta) l^{kL}_i=(1/beta) l^{kL}_j, and
(1/beta) u^{kH}_i=(1/beta) u^{kH}_j.

The conclusion equates physical inverse-probability weights, including their common 1/beta factor. The theorem assumes the two cuts satisfy the predicates; it does not explicitly assert their existence or optimality, a separate no-cut-through-ties equivalence, or recurrence/proof-step statements.

## SAP.P025b.T20

Quantifiers, in order: every natural n>0, every outcome vector y of length n with EACH coordinate equal to 0 or 1, and every alpha,beta with 0<alpha<=beta<=1. Let p=bar(y) and gamma=beta/alpha. Then:

1. A(y,1;alpha,beta) equals the ENTIRE closed interval [bL(p,gamma),bU(p,gamma)].
2. L(y,1;alpha,beta)=bL(p,gamma) and U(y,1;alpha,beta)=bU(p,gamma).
3. If p=0, both bL and bU are 0. If p=1, both are 1. If gamma=1, both are p.

No sorting or presence of both binary outcomes is assumed.

## SAP.P025b.T21

The quantifiers and hypotheses are those of T13 in exactly the same order: N>0, J>0, finite measurable-singleton outcome space K, finite design d, surjective class map c, strictly increasing real class outcomes y, and 0<alpha<=beta<=1 bounding EVERY unit inclusion probability. There is then the additional hypothesis Sep(y,M,beta/alpha), quantified over precisely k=0,...,J-1. The conclusion is PC(d,c,y,alpha,beta), meaning the almost-sure conjunction of eventual nonempty pooling and both actual pooled endpoint limits specified above. In contrast to T13 this theorem assumes separation for its sole conclusion.
