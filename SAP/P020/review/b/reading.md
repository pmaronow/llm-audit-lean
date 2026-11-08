# Blind mathematical reading

Saved before opening `claims.json` or `record.json`. Sources read at this stage:
all four `SAP/P020/Defs/Part*.lean` files, their umbrella, the Challenge files,
and the relevant Mathlib definitions. The descriptions below concern the
propositions, independently of the intentions stated in their docstrings.

## Common objects and fully expanded notation

All unqualified scalars below are real. A `FiniteLaw Ω` consists of a finite
subset S of an arbitrary type Ω, real weights p(ω), p(ω) ≥ 0 for ω in S, and
Σ(ω in S) p(ω) = 1. Values of p outside S are irrelevant and unrestricted.
Thus S cannot be empty. Write

* E_L T = Σ(ω in S) p(ω)T(ω);
* B_L(T,d) = E_L T − d;
* V_L(T) = E_L[(T − E_L T)²];
* C_L(T,U) = E_L[(T − E_L T)(U − E_L U)];
* M_L(T,d) = E_L[(T − d)²];
* q_L(T,d,ε) = Σ(ω in S, |T(ω)−d| > ε) p(ω).

There are no measure theoretic integrals. All these sums are finite. A sequence
`DesignConsistent L T d` means: for every real ε > 0,
q_(L_h)(T_h,d_h,ε) tends to zero as the natural number h tends to infinity.
The outcome type Ω_h may depend on h. Equivalently, for every ε > 0 and η > 0
there is H such that h ≥ H implies |q_(L_h)(T_h,d_h,ε)| < η.

A `ClusterPopulation` P consists, in this order, of natural numbers M and t,
proofs 0 < t and t < M, a function n : {0,…,M−1} → ℕ with n_j > 0 for every j,
and two arbitrary real functions y0 and y1 on those M clusters. In particular
M ≥ 2. Set c = M−t and N = Σ_j n_j. Here the natural subtraction defining c
is ordinary positive subtraction because t < M; c > 0 and N > 0. The y's are
cluster totals; individual outcomes are supplied only when explicitly stated.

An admissible assignment s is a subset of {0,…,M−1} of cardinality t.
Its complement sᶜ has cardinality c. The design law L_P assigns each such s
weight 1 / binomial(M,t). No other subset has positive design weight.
For a ∈ {0,1}, let s_1 = s, s_0 = sᶜ, and m_1 = t, m_0 = c. Define

* A_a(v,s) = Σ(j in s_a) v_j;
* N_a(s) = A_a(n,s), and b_a(s) = N_a(s)/m_a;
* observed totals o_j(s) = y1_j when j ∈ s, and y0_j otherwise;
* d = (Σ_j y1_j − Σ_j y0_j)/N;
* D(s) = A_1(y1,s)/N_1(s) − A_0(y0,s)/N_0(s);
* H_a(s) = (M/m_a) A_a(y_a,s), and H(s) = (H_1(s)−H_0(s))/N.

For an arbitrary real vector v on M indices put μv = (Σ_j v_j)/M,
S(v) = (Σ_j (v_j−μv)²)/M, and
C(v,w) = (Σ_j (v_j−μv)(w_j−μw))/M. These are population moments with
denominator M, not sample moments with denominator M−1. When M = 0 these
general vector definitions use Lean's real division convention; all substantive
general-vector assertions below require M > 0, and every population has M ≥ 2.
Put δ_j = n_j−μn,
R_a(k)_j = y_a,j − kδ_j,
Q_a(k,s) = (M/m_a)A_a(R_a(k),s), and
R(k,s) = (Q_1(k,s)−Q_0(k,s))/N. This R is `desRaj`.
More generally `differenced v size k` is v_j−k(size_j−μsize).

The observed fitted slope is K(s) = C(n,o(s))/S(n). Its definition is totalized
at S(n)=0, but its concrete use in T6 has S(n)=2/3. The arm coefficient is
k_a* = C(n,y_a)/S(n), and the common coefficient is
k* = (t/M)k_0* + (c/M)k_1*. The universal optimization assertions involving
these ratios explicitly assume S(n)>0.

For b0,b1 real, P' = `affinePopulation P b0 b1` keeps all sizes and counts and
sets y'_a,j = n_j b0 + b1 y_a,j. For h a natural number with h>0, P[h] =
`replicateWithin P h hh` keeps M,t and sets n'_j = h n_j and y'_a,j = h y_a,j.

For A a natural number, cluster covariates X_ℓ,j, and fixed real coefficients
ks and ka_ℓ, define
R^X_a,j = y_a,j − ks(n_j−μn) − Σ(ℓ=0,…,A−1) ka_ℓ(X_ℓ,j−μX_ℓ),
Q^X_a(s) = (M/m_a)A_a(R^X_a,s), and R^X(s) = (Q^X_1−Q^X_0)/N.
A=0 is permitted, but the claims quantify over every A, including positive A.

The named variance quantities expand as follows:

F(P) = (M²/N²)[ M/(M−1)(S(y0)/c + S(y1)/t)
                   + (2C(y0,y1)−S(y0)−S(y1))/(M−1) ].

G(P,v0,v1) = M³/[N²(M−1)] [S(v0)/c + S(v1)/t].

J(P,v0,v1,s) = (M²/N²)[
  Σ(j in sᶜ)(v0_j−A_0(v0,s)/c)² / (c(c−1))
  + Σ(j in s)(v1_j−A_1(v1,s)/t)² / (t(t−1)) ].

Z(P,s) = M⁴ S(o(s)) / [N²(M−1)ct].

W(P,k) = ((M−c)/c) S(R_0(k)) + ((M−t)/t) S(R_1(k))
         + 2 C(R_0(k),R_1(k)).

A(P) = M²/[N²(M−1)] [((M−c)/c)+((M−t)/t)+2] S(n).

J is used in theorem assertions only when t,c≥2. All denominators in F,G,Z,W
are positive for any population; A(P)>0 when S(n)>0.

An `IndividualPotentialOutcomes P` object I supplies Y0_j,i and Y1_j,i for
0≤i<n_j, with Σ_i Ya_j,i = y_a,j, for both a and every j. Its sharp null is
the pointwise assertion Y0_j,i=Y1_j,i for every j and i. Its observed individual
outcome is Y1_j,i if j∈s, and Y0_j,i otherwise.

For B blocks P_b, a block assignment is a function choosing one admissible
assignment in every block. `blockLaw` is uniform on the entire finite Cartesian
product, hence is the product of the uniform block laws. Put N_B=Σ_b N_b,
H_B(s)=Σ_b (N_b/N_B)H_b(s_b), and
d_B=[Σ_b(Σ_j y1_b,j−Σ_j y0_b,j)]/N_B. The block assertions require B>0.

For h copies of a fixed P, a copy assignment chooses an admissible assignment
s_r in each of h copies. `copyLaw P h` is uniform on the entire Cartesian
product: the h random assignments are independent and identically distributed.
`copyAverage P a v h` is h⁻¹Σ_r A_a(v,s_r).
`copiedDifferenceInMeans` is
  [Σ_r A_1(y1,s_r)]/[Σ_r N_1(s_r)]
  − [Σ_r A_0(y0,s_r)]/[Σ_r N_0(s_r)].
Every limit below uses h+1 copies and thus positive copy counts.
`WithinReplicationConsistent P` is convergence in probability of D for the
sequence P[h+1], under its own complete randomization law, to its own ATE.

The four explicitly defined populations are:

| Name | M,t | n | y0 | y1 |
| --- | --- | --- | --- | --- |
| E (`efficiencyPopulation`) | 3,1 | (1,2,4) | (0,1,1) | (0,0,0) |
| S (`slopePopulation`) | 3,1 | (1,2,3) | (0,0,0) | (0,0,3) |
| U (`subscriptPopulation`) | 2,1 | (1,2) | (0,0) | (1,2) |
| V (`bracketPopulation`) | 2,1 | (1,2) | (0,2) | (0,2) |

Finally g(x)=`logistic x`=1−1/(1+exp x), where exp is Mathlib's real
exponential; r(n)=`repairedContrast n`=2/5−9n/10000.

Mathlib checks behind this expansion: `Finset.mem_powersetCard` says exactly
subset and specified cardinality, and `card_powersetCard` gives the binomial
cardinality (`Data/Finset/Powerset.lean`, lines 198–216). `Finset.univ` on the
finite function types enumerates all functions, so the uniform laws for copies
and blocks have full product support (`Data/Fintype/Pi.lean`). `StrictMono`
means ∀x,y, x<y → g(x)<g(y) (`Order/Monotone/Defs.lean:86`). `Tendsto`
means pushforward-filter inclusion (`Order/Filter/Defs.lean:422`); `atTop`
is generated by upper intervals (`Order/Filter/AtTopBot/Defs.lean:39`), and
`nhds` is the usual neighborhood filter (`Topology/Defs/Filter.lean:130`).
Thus natural-to-real limits below are ordinary sequential limits; 7h→∞ means
∀K∈ℕ, ∃H∈ℕ, ∀h≥H, 7h≥K. No `limsup` or improper integral occurs.

## SAP.P020.T1

This is a conjunction of the following claims, with no external hypotheses.

1. For each j∈{0,1,2}, the individual control vector on n_j persons that is zero
   if j=0 and otherwise is 1 at i=0 and 0 elsewhere sums to E.y0_j; the all-zero
   treatment vector sums to E.y1_j.
2. N_E=7, d_E=−2/7. At assignments {0},{1},{2}, respectively,
   D=(−1/3,−1/5,−1/3) and H=(−3/7,−3/14,−3/14).
   E D=−13/45, B(D,d)=−1/315, M(D,d)=131/33075,
   E H=d, and M(H,d)=1/98.
3. For every real k, simultaneously:
   R(k,{0})=−3/7+6k/7, R(k,{1})=−3/14+3k/14,
   R(k,{2})=−3/14−15k/14; E R(k)=d;
   M(R(k),d)=1/98−6k/49+9k²/14=3/686+(9/14)(k−2/21)²;
   M(R(k),d)=3/686 iff k=2/21; M(R(k),d)≥3/686;
   131/33075<3/686<1/98 and M(D,d)<M(R(k),d).
4. S(n)=14/9, C(n,y0)=4/9, C(n,y1)=0, and k*=2/21 for E.
5. q(D,d,1/25)=1 for E.
6. For every natural h, then a proof h>0, then every real k: N_(E[h])=7h,
   d_(E[h])=−2/7; for every admissible assignment s of E, D,H,R(k) on E[h]
   equal their values on E; the bias of D on E[h] is −1/315; its error
   probability at ε=1/25 is 1; its MSE is strictly below that of R(k) on E[h].
7. 7h→∞; the constant-law sequence (L_E,D_E,d_E) is not consistent;
   `WithinReplicationConsistent E` is false; B_E(D,d)≠0;
   and M_E(D,d)<M_E(H,d).

## SAP.P020.T2

Independent conjuncts:

1. For every type Ω, finite law L on Ω, function T:Ω→ℝ, and real d,
   M_L(T,d)=V_L(T)+B_L(T,d)² and B_L(T,d)²≤M_L(T,d).
2. For every family of types Ω_h, family of finite laws L_h, functions T_h,U_h
   on the same Ω_h, target sequence d_h, then real b≠0, if B_(L_h)(T_h,d_h)→b
   and M_(L_h)(U_h,d_h)→0, there exists H∈ℕ such that for every h≥H,
   M_(L_h)(U_h,d_h)<M_(L_h)(T_h,d_h).
3. For every Ω,L,T,d,ε in that order, with ε>0,
   q_L(T,d,ε)≤M_L(T,d)/ε².
4. For every Ω_h,L_h,U_h,d_h, if M_(L_h)(U_h,d_h)→0, then U is design
   consistent for d, with the definition given above.
5. For every natural h>0, D on E[h] has bias −1/315 and has smaller MSE than
   R(0) on E[h]; additionally 7h→∞.

The second conjunct assumes the comparator MSE limit, not a comparison of the
two estimators as a hypothesis. The last conjunct is a concrete family.

## SAP.P020.T3

Independent conjuncts:

1. For all real x<y, g(x)<g(y).
2. For every real n with n≥1, 2/5−9n/10≤−1/2.
3. For every real base, then real n≥1,
   g(base+2/5−9n/10)−g(base)<0.
4. For every natural N>0, then arbitrary real vectors base,size on N indices,
   with size_i≥1 for all i, the arithmetic average
   N⁻¹Σ_i[g(base_i+2/5−9size_i/10)−g(base_i)] is strictly negative.
5. Under the same quantifiers and hypotheses as 4, that average is not 7/1000.

There is no cluster-design or aggregation hypothesis in the last two conjuncts;
in particular they allow N=1 and real, noninteger sizes ≥1.

## SAP.P020.T4

1. For all real alpha,block,n,t in that order,
   alpha+(2/5)t+(7/5)(n/1000)−(9/10)(n/1000)t+block
   =alpha+(2/5)t+(7/5000)n−(9/10000)nt+block.
2. For every real n, r(n)>0 iff n<4000/9, and r(n)<0 iff n>4000/9.
3. For every natural n, r(n)>0 iff n≤444, and r(n)<0 iff n≥445.
4. For every real base, then natural n, g(base)<g(base+r(n)) iff n≤444,
   and g(base+r(n))<g(base) iff n≥445.
5. For every natural N>0, real vector base, natural vector size on N indices,
   and proofs size_i≥1 for all i: if every size_i≤444, the average probability
   contrast is >0; and if every size_i≥445, the average is <0.

## SAP.P020.T5

For every population P, then every real-valued function khat on all cluster
subsets (with no independence or unbiasedness hypothesis),

E[Q_1(khat(s),s)] = Σ_j y1_j − M C_L(khat,b_1),
E[Q_0(khat(s),s)] = Σ_j y0_j − M C_L(khat,b_0), and
E[R(khat(s),s)] = d + (M/N)[C_L(khat,b_0)−C_L(khat,b_1)].

A separate universally quantified conjunct, with the same P,khat order, says
B_L(R(khat(s),s),d)=(M/N)[C_L(khat,b_0)−C_L(khat,b_1)].

## SAP.P020.T6

Without hypotheses, for the explicit population S: d=1/2;
K({0}),K({1}),K({2})=(0,0,3/2);
R(K(s),s) at those assignments equals (0,0,3/8);
E R(K)=1/8≠d and its bias is −3/8;
C_L(K,b_1)=1/2 and C_L(K,b_0)=−1/4.
Further conjuncts say N=6, S(n)=2/3,
b_1 at the three assignments is (1,2,3), b_0 is (5/2,2,3/2),
and the bias equals (M/N)[C_L(K,b_0)−C_L(K,b_1)].

## SAP.P020.T7

1. For every natural n, vector Y on n indices, and reals b0,b1,
   Σ_i(b0+b1Y_i)=n b0+b1Σ_iY_i. The case n=0 is included.
2. For every P, a∈{0,1}, reals b0,b1,k, and cluster j, in that order,
   R'_a(b0+b1k)_j=b0(N/M)+b1R_a(k)_j, where the prime means P'.
3. For every P,b0,b1,k, subset s, then proof |s|=t,
   R'(b0+b1k,s) equals
   (M/N)[ Σ(j∈s)(b0N/M+b1R_1(k)_j)/t
          −Σ(j∈sᶜ)(b0N/M+b1R_0(k)_j)/c ],
   and equals b1R(k,s).
4. Independently, for the same quantifiers and admissibility hypothesis,
   R'(b0+b1k,s) equals
   (M/N)[b1A_1(R_1(k),s)/t−b1A_0(R_0(k),s)/c],
   and this latter expression equals b1R(k,s).

No restriction on b0,b1,k, such as nonzero b1, occurs.

## SAP.P020.T8

1. For every natural M, proof M>0, real vectors v,size on M indices, then real k,
   μ(v−k(size−μsize))=μv.
2. Independently, with the same quantifier order and hypotheses,
   S(v−k(size−μsize))=S(v)+k²S(size)−2kC(v,size).
3. For every M>0, then v,w,size, then k, put δ=size−μsize and
   C'=C(v−kδ,w−kδ). All seven equalities hold:
   * C'=μ[(v−kδ)(w−kδ)]−μ(v−kδ)μ(w−kδ);
   * C'=μ[(v−kδ)(w−kδ)]−μv μw;
   * C'=μ[vw−vkδ−wkδ+k²δ²]−μv μw;
   * C'=μ[vw]−μv μw−μ[vkδ]−μ[wkδ]+μ[k²δ²];
   * C'=C(v,w)−k(C(v,size)+μv μδ)−k(C(w,size)+μw μδ)+k²S(size);
   * C'=C(v,w)−k(C(v,size)+μv·0)−k(C(w,size)+μw·0)+k²S(size);
   * C'=C(v,w)−kC(v,size)−kC(w,size)+k²S(size).

## SAP.P020.T9

No external hypotheses. The assignment {0} is admissible for U. The Des Raj
estimate on its affine transform with b0=0,b1=1,k=0 is 2/3, whereas the
expression using R_1(0) in both arm sums,
(M/N)[A_1(R_1(0),{0})/t−A_0(R_1(0),{0})/c], is −2/3; they are unequal.

The assignment {0} is admissible for V. C(y0,y1)=1 but
(μy0)y1_0−(μy0)(μy1)=−1, so these expressions are unequal.
Further explicit-vector conjuncts repeat that C((0,2),(0,2))=1, give the
misbracketed expression as −1 at j=0 and +1 at j=1, and assert inequality
at j=0. Finally R_U(0,{0})=2/3 is repeated without the affine transform.

## SAP.P020.T10

1. For every population P, individual-outcome object I with its aggregation
   certificates, proof of its pointwise sharp null, subset s, then proof |s|=t:
   for every j,i both Y0_j,i and Y1_j,i equal the observed individual outcome,
   and for every j, y0_j=y1_j.
2. Independently with the same quantifier order and hypotheses:
   for every j both y0_j and y1_j equal o_j(s);
   S(y0)=S(y1), S(y1)=S(o(s)), C(y0,y1)=S(o(s));
   V_L(H)=F(P), and F(P)=Z(P,s).

## SAP.P020.T11

1. For every type Ω, law L, real-valued functions u,v on Ω, then hypothesis
   v(ω)>0 for every ω in the support,
   E_L(u/v)=[E_L u−C_L(u/v,v)]/E_L v.
   In particular the hypothesis and normalized nonnegative weights force E_L v>0.
2. For every P,
   E_L D=d−(M/N)[C_L(A_1(y1)/N_1,N_1)/t
                    −C_L(A_0(y0)/N_0,N_0)/c],
   and B_L(D,d)=−(M/N) times the same bracket.
   The ratio functions here are evaluated at the random assignment s;
   on the support, their denominators are positive.

## SAP.P020.T12

1. For every n,Y,b0,b1, the total-transformation identity in T7(1) holds.
2. For every P, E H_0=Σ_j y0_j, E H_1=Σ_j y1_j, and E H=d.
3. For every P,b0,b1,subset s, then proof |s|=t,
   H'(s)=b0(M/N)[b_1(s)−b_0(s)]+b1H(s).
4. For every P,b0,b1,s, then proofs |s|=t, b0≠0, and b_1(s)≠b_0(s),
   H'(s)≠b1H(s).
5. There exist P,b0,b1,s, in that order, such that s is admissible and
   H'(s)≠b1H(s). This last conjunct does not specify their concrete values.

## SAP.P020.T13

1. For every P, then fixed real k,
   E Q_0(k)=Σ_j y0_j, E Q_1(k)=Σ_j y1_j, and E R(k)=d.
2. For every P, natural A, covariate array X, real ks, and real coefficient
   vector ka, in that order,
   E Q^X_0=Σ_j y0_j, E Q^X_1=Σ_j y1_j, and E R^X=d.
   All covariates and coefficients are fixed outside the random assignment.

## SAP.P020.T14

Independent universal conjuncts:

1. For every P, arm a, proof S(n)>0, then real k,
   S(R_a(k))=S(R_a(k_a*))+S(n)(k−k_a*)².
2. For every P, proof S(n)>0, arm a, then real k,
   S(R_a(k_a*))≤S(R_a(k)), with equality iff k=k_a*.
3. For every P, then real k, without a size-variance hypothesis,
   V_L(R(k))=M²/[N²(M−1)] W(P,k).
4. For every P, real k, then proof S(n)>0,
   V_L(R(k))=V_L(R(k*))+A(P)(k−k*)².
5. For every P, real k, then proof S(n)>0,
   V_L(R(k))−V_L(H)=A(P)k(k−2k*).
6. For every P, proof S(n)>0, then real k:
   V_L(R(k*))≤V_L(R(k)), with equality iff k=k*;
   V_L(R(k))<V_L(H) iff k²<2kk*;
   V_L(R(k))=V_L(H) iff k=0 or k=2k*.
7. For every pair of real numbers k,star in that order,
   k²<2k·star iff
   (star>0 and 0<k<2star) or (star<0 and 2star<k<0).

The coefficient definitions and W,A are expanded in the common notation above.
There are no derivative assertions in this proposition.

## SAP.P020.T15

1. For every P, simultaneously:
   V_L(H)=[V_L(H_0)+V_L(H_1)−2C_L(H_0,H_1)]/N²;
   V_L(H_0)=(M²/c)[(M−c)/(M−1)]S(y0);
   V_L(H_1)=(M²/t)[(M−t)/(M−1)]S(y1);
   C_L(H_0,H_1)=−M² C(y0,y1)/(M−1).
2. For every P, V_L(H)=F(P) and V_L(H)≤G(P,y0,y1).
3. For every P, 2C(y0,y1)−S(y0)−S(y1)≤0.
4. For every P, then proofs t≥2 and c≥2,
   E J(P,y0,y1,s)=G(P,y0,y1), and V_L(H)≤E J.
5. For every P, real k, then proofs t≥2 and c≥2,
   E J(P,R_0(k),R_1(k),s)=G(P,R_0(k),R_1(k)),
   and V_L(R(k))≤that expectation.
6. For every natural B, proof B>0, then family of populations P_b,
   E H_B=d_B and
   V(H_B)=Σ_b (N_b/N_B)² V_(L_b)(H_b).
7. For every B, proof B>0, family P_b, functions Vhat_b from cluster subsets
   to ℝ, then hypotheses V_(L_b)(H_b)≤E_(L_b)Vhat_b for every b,
   V(H_B)≤E_block[Σ_b(N_b/N_B)² Vhat_b(s_b)].

The last conjunct is conditional aggregation of conservativeness; it does not
assume the blocked conclusion, and block independence is built into the law.

## SAP.P020.T16

For every population P, then hypothesis
  (there exists real τ such that y1_j−y0_j=τ for every cluster j)
  OR (c=t),
V_(L_P)(H)≤E_(L_P)Z(P,s).

The first disjunct is constancy of the cluster-total treatment effect, not
constancy of an individual effect or a cluster-mean effect. The conclusion
concerns H only; it does not quantify over Des Raj coefficients.

## SAP.P020.T17

1. For every P, under the law of h+1 independent copies, all five limits hold
   in probability as h→∞:
   * (h+1)⁻¹Σ_r A_1(y1,s_r) → (t/M)Σ_j y1_j;
   * (h+1)⁻¹Σ_r A_0(y0,s_r) → (c/M)Σ_j y0_j;
   * (h+1)⁻¹Σ_r N_1(s_r) → (t/M)N;
   * (h+1)⁻¹Σ_r N_0(s_r) → (c/M)N;
   * pooled copied difference in means → d.
2. For every P, [(Σy1)(t/M)]/[N(t/M)]−[(Σy0)(c/M)]/[N(c/M)]=d.
3. For every P, natural h, then proof h>0, N_(P[h])=hN_P.
4. For every P,h,proof h>0,subset s,proof |s|=t,then real k,
   ATE,D,H,R(k) on P[h] equal those on P (the estimators at s).
5. For every P, then hypothesis B_(L_P)(D,d)≠0:
   for every h>0 the bias on P[h] equals that on P;
   and the constant-law sequence (L_P,D_P,d_P) is not design consistent.
6. The constant-law sequence for E is not design consistent; 7h→∞;
   for every h>0 the complete randomization law of E[h] equals that of E;
   `WithinReplicationConsistent E` is false;
   and for every h>0 the bias on E[h] is −1/315.

The first limit assertion is stated using the marginal laws at each h. There
is no joint probability space coupling all copy counts, nor an explicit
strict-growth certificate for both arm individual counts in the proposition.
