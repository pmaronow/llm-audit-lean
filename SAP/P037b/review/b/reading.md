# Blind reading of the Challenge statements

This file was written and saved before opening `claims.json` or `record.json`.
The only mathematical inputs to this stage were the three Defs parts, their
aggregator, the Challenge part and its aggregator, and the relevant Mathlib
definitions. There are 13 theorem stubs, each asserting the corresponding
`TxxStatement` with no additional theorem-level hypotheses.

## Common notation and fully expanded definitions

All scalar quantities below are real unless explicitly called natural numbers.
`Fin n` means the integers 0 through n−1; a sum or product over it includes every
such integer. Matrices are functions of their row and column indices. Matrix
multiplication and matrix-vector multiplication are ordinary finite sums,
`dotProduct a b = Σ_i a_i b_i`, transpose interchanges indices, `diagonal d`
has entries d_i on the diagonal and zero elsewhere, and the square-matrix `1`
is the identity. Scalar multiplication, vector subtraction, and matrix
subtraction are entrywise. In particular, `1-H` in a matrix expression is I−H.

For an n by k real matrix X, define

* A(X)=(XᵀX)⁻¹Xᵀ, H(X)=XA(X), b(X,y)=A(X)y;
* r(X,y)=y−XA(X)y;
* S(X,y)=A(X) diag(r(X,y)_i²) A(X)ᵀ;
* Q(V,l)=lᵀVl.

Mathlib's matrix inverse is the determinant ring-inverse times the adjugate;
it is the ordinary inverse for a nonsingular matrix and zero for a singular
matrix over the reals. The theorems using A(X) impose injectivity of X's
matrix-vector map when needed. For a probability measure μ on a measurable
space Ω and a vector-valued function v, m(v)_j=∫v_j dμ and
C(v)_{jl}=∫(v_j−m(v)_j)(v_l−m(v)_l)dμ. These are coordinatewise Bochner
integrals. Mathlib defines an integral to be zero for a nonintegrable function;
`Integrable` means almost-everywhere strong measurability and finite integral
of the norm. The moment assumptions in T18 explicitly cover first moments and
all pairwise products. `IsProbabilityMeasure μ` means μ(Ω)=1.

A `ProbabilityDesign Ω` consists of a finite type Ω, strictly positive real
numbers p(z) for every z, and Σ_z p(z)=1. Write
P(E)=Σ_z p(z)1_E(z) and E[F]=Σ_z p(z)F(z). Consequently a design on an empty
Ω cannot exist. For J draws, whenever used below, the space is all functions
z:{0,…,J−1}→Ω and its mass is Π_j p(z_j), expressing independent draws from
the specified finite law. Statements about an arbitrary fixed list of draws
do not impose an independence hypothesis on that list.

`powersetCard m univ` is the finite set of all m-element subsets of the
specified finite ground set. Its size is the natural binomial coefficient
choose(n,m), including zero if m>n. Real division is totalized by 1/0=0.
Natural subtraction truncates at zero; real subtraction does not. Any uses
where these distinctions matter are described below.

The following concrete definitions are shared across statements:

* The six school groups have sizes N=(14,14,7,7,7,7), treatments
  T=(0,0,1,1,1,1), compositions C=(0,0,0,0,1/5,1/5), and outcomes
  y=(0,1/5,1/10,3/10,2/5,3/5). Their rows are x_i=(1,T_i,T_i C_i).
  The proposed fit is b=(1/10,1/10,3/2). G=Σ_i N_i x_i x_iᵀ,
  g=Σ_i N_i x_i y_i, M=Σ_i N_i(y_i−x_iᵀb)²x_i x_iᵀ. The named matrices are
  K=[[1/28,−1/28,0],[−1/28,3/28,−5/14],[0,−5/14,25/7]] and
  V=[[1/2800,−1/2800,0],[−1/2800,3/2800,−1/280],[0,−1/280,1/28]].
  Centered rows are xᶜ_i=(1,T_i,T_i(C_i−1/10)), with proposed fit
  bᶜ=(1/10,1/4,3/2), inverse
  Kᶜ=[[1/28,−1/28,0],[−1/28,1/14,0],[0,0,25/7]], Gram matrix
  Gᶜ=Σ_i N_i xᶜ_i(xᶜ_i)ᵀ, and meat
  Mᶜ=Σ_i N_i(y_i−(xᶜ_i)ᵀbᶜ)²xᶜ_i(xᶜ_i)ᵀ.
* The four-school experiment uses i=0,1,2,3, potential outcomes
  Y_i(t)=3i/100+1_{t=true}3/100, and six treatment sets in this order:
  {0,1},{0,2},{0,3},{1,2},{1,3},{2,3}. Call them S_z. Observed outcome is
  Y_i(1_{i∈S_z}). Keep precisely outcomes strictly greater than 1/50. Let
  K_z be the kept set, T_z=K_z∩S_z, C_z=K_z\S_z, Δ_z the mean outcome in
  T_z minus the mean in C_z, and w_z=|T_z||C_z|/(|T_z|+|C_z|).
  For B blocks define R_B(z)=Σ_b w_{z_b}Δ_{z_b}/Σ_b w_{z_b}. For B=0 this
  definition gives 0/0=0; the asymptotic assertion uses B tending to infinity.
* Given subsets self, peers, refs, seeds of {0,…,n−1}, define L(seeds)=4
  if seeds intersects self; otherwise L=1 if seeds avoids peers; otherwise
  L=2 if seeds avoids refs; otherwise L=3. Define π⁵_0=1/2, and for k=1,…,4,
  π⁵_k=number of m-element seed subsets with L=k divided by 2 choose(n,m).
  Thus label 0 encodes a separate half-probability branch, and label 4 is a
  distinct selected-self branch. No general relation among the three input
  sets is built into the definition.
* For four real-valued probabilities π_i(k), k=0,1,2,3, define
  Pop(π)={i: for every k, 0<π_i(k)<1} and
  Cut(π,c)={i: for every k, c<π_i(k)}. For estimated probabilities e and
  assignment-dependent predicates seed, outcome, baseline, screen, define
  Analysis(e,z)={i∈Cut(e,1/100): not seed(z,i), outcome(z,i),
  baseline(z,i), screen(z,i)}.
* Avoid(n,t,m)=1/2 Π_h choose(n_h−m_h,t_h)/choose(n_h,t_h), with natural
  n_h,t_h,m_h and natural subtraction n_h−m_h. The standalone definition
  imposes no bounds. T30 uses m_h as the size of a subset of Fin(n_h), and
  explicitly assumes t_h≤n_h.
* Rare assignments are a Boolean school-treatment flag and four subsets
  s_0,…,s_3 of Fin 10, each of size 5. Every assignment has mass
  1/(2·252⁴). Its exposure is 0 if the flag is false; if true, exposure is 1
  when both s_0 and s_1 avoid {0,1,2,3,4}; otherwise exposure is 3 if
  0∈s_0, and 2 if 0∉s_0. Rareπ(k) is the finite sum of masses with that
  exposure. Blocks 2 and 3 are unrestricted in this exposure rule.
* Block(B) consists of all subsets of Fin B × Fin 4 containing exactly two
  pairs with each first coordinate. Its mass function is 6^(−B) on Block(B)
  and zero elsewhere. Unblock(n,m) consists of all m-element subsets of
  Fin n. UPr(n,m,E) is the number of its subsets satisfying E divided by
  choose(n,m). The exponent −B is an integer exponent, not truncated natural
  negation.
* A Boolean graph B has an edge i→j when B(i,j)=true. U(B)(i,j) is
  B(i,j) OR B(j,i). indeg_B(j) is the number of incoming nominations.
  Sort the n indegrees in increasing order into a. Put h=9(n−1), with
  natural subtraction, q=h div 10 and r=h mod 10. The named 90th quantile
  is ((10−r)/10)a_q+(r/10)a_(q+1), where out-of-range list entries default
  to zero. Referents Γ(B) are precisely the vertices whose indegree is
  strictly above this quantile. The concrete uses have n=10 or n=20.
* Given seeds S and referents Γ, c_B(i,S)=|{j∈S:B(i,j)}| and
  r_B(i,S,Γ)=|{j∈S:B(i,j) and j∈Γ}|. Define e(c,r)=0 if c=0, 1 if
  c≠0 and r=0, and 2 otherwise. The network label is e(c_B,r_B).
* B10 has exactly edges 1→0, 2→1, 3→1. B20 has exactly 1→0,
  0→2, 0→4, i→1 for 8≤i≤13, and i→2 for 14≤i≤19.
  Eligible seeds in B20 are (1,2,4,5,6,7); select three of these six.
  Graphπ(B,0)=1/2 and Graphπ(B,k), k=1,2,3, is the number of these
  20 seed subsets giving network label k−1 to vertex 0, divided by 40.
  The referent set in this definition is always Γ(B20), including when
  B=U(B20); it is not recomputed from the union graph.

Mathlib sources followed for these semantics include
`Data/Matrix/Mul.lean:72,698`, `Data/Matrix/Diagonal.lean:50`,
`LinearAlgebra/Matrix/Defs.lean:172`,
`LinearAlgebra/Matrix/NonsingularInverse.lean:169`,
`MeasureTheory/Integral/Bochner/Basic.lean:158`,
`MeasureTheory/Function/L1Space/Integrable.lean:59`,
`MeasureTheory/Measure/Typeclasses/Probability.lean:64`,
`Data/Finset/Powerset.lean:198`, `Data/Nat/Choose/Basic.lean:50`,
`Order/Filter/Defs.lean:422`, and `Order/Filter/AtTopBot/Defs.lean:39`.
Limits below are ordinary real neighborhood limits along natural B→∞.

## SAP.P037b.T18

This is the conjunction of four independently universally quantified assertions.

1. For every measurable Ω, probability measure μ, natural n,k, real n by k
   matrix X, response y∈Rⁿ, injectivity hypothesis on v↦Xv, and function
   v:Ω→Rⁿ, assume every v_i and v_i v_j is integrable, m(v)=0, and
   ∫v_i v_j=1 if i=j and 0 otherwise. Set b=A(X)y and
   b*(ω)=A(X)(Xb+(r(X,y)_i v_i(ω))_i). Then for every ω,
   b*(ω)=b+A(X)(r_i v_i(ω))_i, and m(b*)=b and C(b*)=S(X,y).
   Independence of the multipliers is not assumed; the stated moments suffice.
2. For every natural n,k, matrix X with injective matrix-vector map, and
   n>0: Hᵀ=H, H²=H, every H_ii lies in [0,1], Σ_i H_ii=k, and
   (Σ_i H_ii)/n=k/n.
3. For every measurable Ω, probability μ, natural n,k, full-column-rank X,
   β∈Rᵏ, nonnegative scalar σ², and u:Ω→Rⁿ, assume every u_i and u_i u_j
   is integrable, m(u)=0, and ∫u_i u_j=σ²1_{i=j}. Set y(ω)=Xβ+u(ω),
   A=A(X), H=H(X), V=C(ω↦Ay(ω)), and EV_{jl}=∫S(X,y(ω))_{jl}.
   Then, pointwise, r(X,y(ω))=(I−H)u(ω); for each i its expected square
   is σ²(1−H_ii); V=σ²AAᵀ=σ²(XᵀX)⁻¹;
   EV=σ²A diag(1−H_ii) Aᵀ; V−EV=σ²A diag(H_ii) Aᵀ; and
   tᵀ(V−EV)t≥0 for every t∈Rᵏ.
4. For every natural n and a,h∈Rⁿ, assume 0≤h_i≤1 for all i and
   Σ_i a_i²>0. Then Σ_i a_i²(1−h_i)/Σ_i a_i² equals
   1−Σ_i a_i²h_i/Σ_i a_i², is at most 1, and equals 1 exactly when
   h_i=0 at every coordinate with a_i≠0.

Only clause 2 requires n>0. Clauses 1 and 3 permit zero dimensions but
also quantify over every positive dimension satisfying the hypotheses.

## SAP.P037b.T19

This conjunction first asserts concrete facts with no premises: every school's
effect is 3/100; for every z and i, i∈K_z iff i≠0 or 0∈S_z; every T_z
has size 2; the six C_z sizes are (2,2,2,1,1,1); the six Δ_z values are
(−3/100,0,3/100,−3/200,3/100,3/40); and the six w_z values are
(1,1,1,2/3,2/3,2/3). Their equally weighted means obey EΔ=3/200≠3/100,
Ew=5/6, E(wΔ)=1/100, and E(wΔ)/Ew=3/250≠3/100.

Second, for every real ε>0, under B independent uniform six-state assignments,
the probability of |R_B−3/250|>ε tends to zero as B→∞. The statement is
the explicit finite sum over all six-to-the-B assignment lists.

Third, for all real nT,nC,yT,yC, assuming nT>0 and nC>0, it asserts
nT(1−nT/(nT+nC))²+nC(nT/(nT+nC))²=nT nC/(nT+nC), and
(1−nT/(nT+nC))yT−(nT/(nT+nC))yC
=nT nC/(nT+nC)(yT/nT−yC/nC).

Fourth, for every nonempty subset S of the four schools, the average over S
of the potential-outcome differences equals 3/100. The named block ratio
is not asserted in the formula to be a regression coefficient.

## SAP.P037b.T20

For every finite Ω and finite unit type I, every type K with decidable
equality, positive normalized finite design P, exposure map D:Ω×I→K,
assignment-varying Boolean inclusion A, real outcomes y:I×K→R, and
fixed Boolean inclusion a:I→Bool, the following three assertions hold.
Write π_i(d)=P(D_i=d).

1. For every d∈K and i∈I with π_i(d)>0,
   E[1_{a_i}1_{D_i=d}y_i(d)/π_i(d)]=y_i(d) if a_i=true and zero otherwise.
2. For every d, if all included units have π_i(d)>0 and
   N_a=|{i:a_i=true}|>0, then
   E[(Σ_i1_{a_i}1_{D_i=d}y_i(d)/π_i(d))/N_a]
   =(Σ_{i:a_i=true} y_i(d))/N_a.
   A zero denominator for an excluded unit can occur inside the sum; its
   numerator is identically zero. Every included summand has positive denominator.
3. For every d and i with π_i(d)>0,
   E[1_{A_i}1_{D_i=d}y_i(d)/π_i(d)]
   =y_i(d)P(A_i=true and D_i=d)/π_i(d).

Separately, for any types Ω,I and Y:Ω×I→R, assume that for each i either
Y(z,i)>1/50 for every z, or Y(z,i)≤1/50 for every z. Then for all z,z',i,
Y(z,i)>1/50 iff Y(z',i)>1/50. This last clause has no finiteness or probability
hypotheses.

## SAP.P037b.T21

No general input parameters or hypotheses occur. The theorem asserts all of:

* There are 924 six-element subsets of Fin 12. With self=∅,
  peers={0,1,2,3,4,5}, refs={0}, the five π⁵ values are
  (1/2,1/1848,461/1848,1/4,0); the first four lie strictly between zero
  and one and 0<1/1848<1/100.
* With self={2}, peers={0,1}, refs={0}, the five π⁵ values are
  (1/2,1/22,3/44,3/22,1/4), and each of the first four exceeds 1/100.
  The subsets {2,3,4,5,6,7} and {3,4,5,6,7,8} are both valid selections;
  their respective L labels for this second design are 4 and 1.
* There exists a list of 10000 pairs (Boolean flag, six-element seed set).
  With label zero for a false flag and L for a true flag in the first design,
  its empirical frequencies for labels 0,1,2,3 are exactly
  (1/2,1/2000,499/2000,1/4). Every seed set in this list has size six.
  This is a supported list witness, not a statement that every list or a
  randomly drawn list has these frequencies.
* The raw L histograms of the 924 seed sets are respectively
  (0,1,461,462,0) and (0,84,126,252,462). The first design's four
  probabilities sum to one; the second design's five probabilities sum to
  one. All four displayed empirical frequencies are positive and
  1/2000<1/100.

## SAP.P037b.T22

This is a conjunction of four independently quantified assertions.

1. For every finite Ω, arbitrary unit type I, positive normalized design P,
   D:Ω×I→Fin 5, natural J>0, arbitrary draws in Ω indexed by Fin J,
   four assignment-dependent predicates seed,outcome,baseline,screen, and
   actual assignment z∈Ω, set π_i(k)=P(D_i=k) for k=0,1,2,3, and
   e_i(k)=number of draws with D_i=k divided by J. Then
   Pop(π)=Cut(π,0), Cut(π,1/100)⊆Pop(π),
   Cut(e,1/100)⊆Cut(e,0)⊆Pop(π),
   Analysis(e,z)⊆Pop(π), and Analysis(e,z)⊆{i:not seed(z,i)}.
2. For every finite positive normalized P and event E with 0<P(E)<1,
   the product-law probability that at least 101 of 10000 draws fall in E
   is strictly between zero and one.
3. For every finite positive normalized P, arbitrary I, arbitrary estimated
   real array e, arbitrary four masks as above, and every i,
   P(seed_i)≤P(i∉Analysis(e,z)). There is no condition that e is obtained
   from simulation in this clause.
4. For every natural r≤10000, r/10000>1/100 iff r≥101; and if r≥101,
   then 1/(r/10000)≤10000/101<100.

## SAP.P037b.T23

All inputs are the six fixed groups defined above. It asserts Σ_i N_i=56,
Σ_i N_iT_i=28, KG=I, Gb=g, |y_i−x_iᵀb|=1/10 for every group, and
KMKᵀ=V. At rows l0=(1,0,0), l1=(1,1,1/10), d=(0,1,1/10), it asserts
l0ᵀb=1/10, l1ᵀb=7/20, Q(V,l0)=Q(V,l1)=1/2800,
Q(V,d)=1/1400, and l0ᵀVd=−1/2800. It additionally asserts the scalar
identities ((28/100)/27)/56=1/5400 and
(1/5400)/(1/2800)=14/27; the comparisons 1/1400>1/2800 and
1/5400<1/2800; and ((28/100)/27)/28≠1/2800.

For the centered groups it asserts KᶜGᶜ=I, Gᶜbᶜ=Σ_iN_ixᶜ_i y_i,
(xᶜ_i)ᵀbᶜ=x_iᵀb for every i, and (KᶜMᶜ(Kᶜ)ᵀ)_{11}=1/1400.
The expression involving 28/100 is scalar arithmetic in the statement;
there is no explicit assertion identifying it as an actual residual sum of
squares or a control sample variance.

## SAP.P037b.T24

Three independent universal assertions are conjoined.

1. For every natural p, zbar∈Rᵖ, vector b indexed by the disjoint union
   Fin 3 ⊕ Fin p, and real c, define l0=((1,0,0),zbar) and
   l1=((1,1,c),zbar). Then l0ᵀb=b_0+Σ_j zbar_j b_j,
   l1ᵀb=b_0+b_1+c b_2+Σ_jzbar_jb_j, and l1ᵀb−l0ᵀb=b_1+c b_2.
2. For every natural k, symmetric real k by k matrix V, and l0,d∈Rᵏ,
   Q(V,l0+d)=Q(V,l0)+Q(V,d)+2l0ᵀVd; and
   Q(V,l0+d)=Q(V,d) iff Q(V,l0)+2l0ᵀVd=0.
   No positive-semidefiniteness hypothesis is present or needed for this identity.
3. For every natural n,p, real vectors T,C,y on Fin n, real n by p
   covariate matrix z, and real c, form X with columns 1,T,T·C,z and
   Xc with columns 1,T,T·(C−c),z, on the same n rows. Let b=A(X)y,
   bc=A(Xc)y and V=S(X,y). If the map v↦Xv is injective, then
   Xc bc=Xb, r(Xc,y)=r(X,y), bc_1=b_1+c b_2, and
   S(Xc,y)_{11}=V_{11}+2cV_{12}+c²V_{22}.
   T need not be binary. The shifts in column indexing use natural j−3
   only on branches with j≥3, so they are ordinary subtraction there.

## SAP.P037b.T25

No hypotheses or free parameters are present. The theorem asserts:

* B10's quantile is 11/10 and Γ(B10)={1}. With seeds {1}, vertex 0 has
  label 0 under B10 and label 2 under U(B10), keeping Γ(B10) fixed.
* B20's quantile is 3/2 and Γ(B20)={1,2}. The four Graphπ values are
  (1/2,1/10,3/20,1/4) under B20 and
  (1/2,1/40,3/40,2/5) under U(B20); every coordinate of both vectors
  lies strictly between zero and one.
* The complete indegree vectors are (1,2,0,0,0,0,0,0,0,0) and
  (1,6,7,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0).
  Both graphs have false diagonals and no indegree equals its graph's
  quantile. In B10 the vertex-0 seed count and referent-seed count are
  both zero, and under U(B10) both are one.
* Vertex 0's outgoing neighbors in B20 are {2,4} and in U(B20) are
  {1,2,4}. There are 20 eligible three-of-six seed subsets; the histograms
  of shifted labels (network label plus one, counted against k=0,1,2,3)
  are (0,4,6,10) and (0,1,3,16).
* For each k=1,2,3, the two Graphπ values differ, and their reciprocals
  differ. The positive values make these genuine reciprocals.

## SAP.P037b.T26

Four independent universally quantified parts are conjoined.

1. For every natural n and Boolean graph B on Fin n with no loops,
   U(B) is symmetric, has no loops, includes every B edge, and for each
   i,j, [U(B)(i,j) and not B(i,j)] iff [B(j,i) and not B(i,j)].
2. For every natural n, Boolean graph B, Boolean seed vector z, Boolean
   referent vector γ, and vertex i, the number of union-graph seed neighbors
   equals the number of outgoing seed neighbors plus the number of
   incoming-only seed neighbors. The same decomposition holds after
   requiring γ_j=true in all three counts. No loop assumption is imposed
   in this part.
3. For all natural c,b,r,q with r≤c and q≤b,
   e(c,r)=e(c+b,r+q) iff (c>0 or b=0) and (r>0 or q=0).
   Also e(c+b,r+q)=0 implies e(c,r)=0, and e(c,r)=2 implies
   e(c+b,r+q)=2.
4. For every finite Ω, strictly positive real weights p summing to one,
   and natural functions c,b,r,q on Ω satisfying r(z)≤c(z),q(z)≤b(z)
   at every z: P(e(c+b,r+q)=0)≤P(e(c,r)=0) and
   P(e(c,r)=2)≤P(e(c+b,r+q)=2). The first inequality is strict if
   there exists a z with old label 0 and new label nonzero; the second
   is strict if there exists a z with old label not 2 and new label 2.
   These probability comparisons concern arbitrary scalar count functions;
   their instantiation by graph counts is not an additional asserted conjunct.

## SAP.P037b.T29

All statements refer to the concrete rare assignment space, with no hypotheses.
Its masses sum to one, and the four exposure probabilities are exactly
(1/2,1/127008,31751/127008,1/4); all lie strictly between zero and one.
For every natural r (not just r≤10000),
Rareπ(1)≤|r/10000−Rareπ(1)| and
Rareπ(1)/2<|r/10000−Rareπ(1)|.

For 10000 independent rare-design assignments let H be the number of label-1
hits and weight each list by the product mass. The theorem asserts
E[H]=625/7938, P(H=0)=(127007/127008)^10000, and
E[(H/10000−1/127008)²]=127007/161310320640000.
The zero-hit probability is strictly between 9/10 and 19/20.

It separately repeats the universal grid-error inequalities with explicit
constants 1/127008 and 1/254016, and asserts
10000/127008=625/7938,
(1/127008)(1−1/127008)/10000=127007/161310320640000,
that quantity divided by (1/127008)² equals 127007/10000,
(1/2)(1−1/2)/10000=1/40000, and (1/200)²=1/40000.
There is no explicit square-root or relative-standard-error assertion.

## SAP.P037b.T30

The theorem conjoins these five groups of assertions.

1. For every finite positive normalized design P on Ω, event E, and
   natural J>0, put p=P(E), H(z)=number of E hits in J draws,
   e(z)=H(z)/J, and use the product law. For every natural r≤J,
   P(H=r)=choose(J,r)p^r(1−p)^(J−r). Also E[e]=p,
   E[(e−p)²]=p(1−p)/J, and P(H=0)=(1−p)^J. For every ε>0,
   P(|e−p|≥ε)≤p(1−p)/(Jε²)≤1/(4Jε²). For every ε,δ>0,
   if J≥1/(4δε²), then P(|e−p|≥ε)≤δ. If p=0, then every draw
   list has H=0. If 0<p<1, both (1−p)^J and p(1−p)/J are positive.
   Here J−r is natural subtraction with r≤J, and p=0,1 are allowed
   in the identities (including the conventional exponent-zero value one).
2. For every such P, natural m,J with J>0, m events E_k indexed by
   Fin m, and ε>0, the product-law probability that at least one
   empirical event frequency differs from its true probability by at least
   ε is at most m/(4Jε²). No independence among the m events is required.
3. For every natural b, size and sample-count vectors n,t:Fin b→N,
   peer subsets peers_h⊆Fin(n_h), and t_h≤n_h for every h, take all
   lists of size-t_h subsets independently with mass
   Π_h1/choose(n_h,t_h). One half times the probability that every
   selected subset avoids its peer set is
   Avoid(n,t,(|peers_h|)_h). The peer-set representation ensures
   |peers_h|≤n_h; the denominators are nonzero under the stated t bounds.
4. For four blocks all with n_h=10,t_h=5, Avoid takes values 8/6561,
   1/6048, 0, and 1/127008 at peer-count vectors (2,2,2,2),
   (5,3,0,0), (6,2,0,0), and (5,5,0,0), respectively.
5. For every such P,E,J>0 and every fixed supported draw list, its
   frequency is r/J for some natural r≤J; if 0<p<1/(2J), its absolute
   error is at least p; if p=0, the frequency is zero. For every finite
   positive normalized P, arbitrary unit type I, D:Ω×I→Fin 5,
   J>0 and draw list, Cut(empirical first-four frequencies,0) is
   contained in Pop(true first-four probabilities). Finally all four
   Rareπ values lie strictly between zero and one, and there exists a
   10000-draw rare-assignment list for which at least one of the four
   empirical exposure frequencies is not positive.

## SAP.P037b.T31

First, without hypotheses: |Block(14)|=78364164096,
|Unblock(56,28)|=7648690600760440, |Unblock(8,4)|=70,
|Block(2)|=36. The subset {0,1,2,3} is in Unblock(8,4), while the
subset {(0,0),(0,1),(0,2),(0,3)} is not in Block(2).
UPr(56,28,{0 and 1 selected})=27/110 and
UPr(4,2,{0 and 1 selected})=1/6.

For y on eight schools, define U2(y) as the uniform mean over the 70
four-of-eight assignments of ((Σ_i(2·1_{i selected}−1)y_i)/4)².
Define B2(y) as the corresponding uniform mean over the 36 assignments
in two blocks of four. Then U2(1,1,1,1,0,0,0,0)=1/7 and
B2(y_{(b,j)}=1_{b=0})=0; also U2(2,0,1,1,1,1,1,1)=1/7 and
B2(y_{(0,0)}=2,y_{(0,1)}=0,all others=1)=1/6. These are explicitly
uncentered second moments; zero means of these four concrete laws are
not separate concrete conjuncts here.

Second, for every finite Ω, natural n, nonnegative real p(z) summing to
one, Boolean selection array S(z,i), half-marginal hypotheses
Σ_zp(z)1_{S(z,i)}=1/2 for every i, arbitrary y∈Rⁿ, and natural m>0,
put T(z)=Σ_i(2·1_{S(z,i)}−1)y_i/m. Then E[T]=0 and
E[T²]=(1/m²)Σ_iΣ_j y_i y_j a_ij, where a_ii=1 and, for i≠j,
a_ij=4P(S_i=true and S_j=true)−1. No balanced-cardinality requirement
on S, nor any relation n=2m, is assumed in this algebraic assertion.

## SAP.P037b.T32

First, for every natural B,n,m, assuming n≥2 and m≤n:
|Block(B)|=6^B; Σ_{s∈Block(B)} mass(s)=1;
|Unblock(n,m)|=choose(n,m); for every h∈Fin n,
UPr(n,m,h selected)=m/n; and for every distinct h,j∈Fin n,
UPr(n,m,h and j selected)=m(m−1)/(n(n−1)). The subtractions in
this last real-valued fraction are real subtractions after coercion,
and n≥2 ensures a positive denominator. The blocked assertions have
the same n,m hypotheses in scope even though they do not depend on them.
B=0 and m=0 are allowed; Block(0) has one empty assignment.

Second, for every finite Ω,U, type K with decidable equality, real
functions p on Ω and q on U, Boolean S:Ω→Bool, hypotheses
Σ_zp(z)1_{S(z)}=1/2, Σ_zp(z)=1, arbitrary f:Bool×U→K and k∈K,
and hypotheses p(z)≥0,q(u)≥0,Σ_uq(u)=1, it asserts
Σ_zΣ_u p(z)q(u)1_{f(S(z),u)=k}
=1/2 Σ_uq(u)1_{f(false,u)=k}+1/2 Σ_uq(u)1_{f(true,u)=k}.
Thus it is a mixture identity for the explicitly independent product law;
f has access only to the local Boolean S(z), not the entire z.
