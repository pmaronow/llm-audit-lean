# Blind reading of the Challenge statements

This file was written after reading only `Defs.lean`, all six `Defs/Part*.lean`,
`Challenge.lean`, `Challenge/Part1.lean`, and the relevant Mathlib definitions.
Neither `claims.json` nor `record.json` has been opened. The descriptions below
read the actual propositions; the Challenge docstrings do not supply hypotheses.

## Common mathematical conventions traced to Mathlib

`Fin n` is the set of integers from 0 through n−1. `Fintype` supplies a finite
enumeration, without assuming nonemptiness. Every unqualified sum or product is
over that entire finite type. A sum `∑ i ∈ E` is over the finite subset E.
`powersetCard n` is exactly the collection of n-element subsets, and `Nat.choose`
is the ordinary binomial coefficient. `Finset.univ \\ z` is set complement in
the specified finite universe. `image` takes the set image, discarding duplicates.
Bool negation exchanges false and true; Bool equality has its usual meaning.

A matrix is an array; `Matrix.mulVec X b` has coordinate
Σ_j X_ij b_j, and `dotProduct` is Σ_j u_j v_j
(`Mathlib/Data/Matrix/Mul.lean`, definitions at lines 72 and 698).
`Function.Injective (Matrix.mulVec X)` means full column rank over the reals.
`castAdd p`, `castSucc`, and the explicit `Fin` constructors preserve the
integer index. Thus the first four pooled columns are the four group indicators,
followed by the covariates; the first separate column is an intercept.

For weights w, X, response Y, and coefficient b,
`regressionMinimum w X Y b` means
**for every coefficient c**, Σ_i w_i(Y_i−(Xb)_i)² ≤ Σ_i w_i(Y_i−(Xc)_i)².
It is a global minimizer condition, not a definition by a chosen optimizer.
`regressionMap w X` is (Xᵀ diag(w) X)⁻¹ Xᵀ diag(w).
The Mathlib matrix inverse is the ordinary inverse when nonsingular, and the
zero matrix when singular (`LinearAlgebra/Matrix/NonsingularInverse.lean:168–178`).
Real division is totalized (division by zero gives zero). Any use below must be
read with precisely the stated positivity/rank assumptions or certified facts,
not with an implicit nonzero-denominator convention.

All expectations and variances below are explicit finite real sums, not
measure-theoretic integrals or limits. Variance means Σ q f²−(Σ q f)².

## SAP.P037c.T35

This is a closed proposition with no parameters or hypotheses.

Let U={0,…,4}×{false,true}, let P(b,s)=(b,not s), let S be **all** five-element
subsets of U, and let O={(b,false):b=0,…,4}. For **any** subset z of U put
Y_z(i)=1 if i∈z and 0 otherwise, and for any real outcome vector Y put

    F(z,Y) = (Σ_{i∈z} Y(Pi))/5 − (Σ_{i∈U\z} Y(Pi))/5.
    q(z) = #{z'∈S : |F(z',Y_z)| ≥ |F(z,Y_z)|}/252.

There is no requirement that z∈S in these definitions; the closed assertions
specify support membership when needed. A subset is split if for every b,
(b,false)∈z iff (b,true)∉z (exactly one member of each pair).

The theorem is the conjunction of every following assertion:

1. |S|=252; O∈S; F(O,Y_O)=−1.
2. For every integer k=0,…,5, exactly binom(5,k)² assignments z∈S satisfy
   F(z,Y_O)=(2k−5)/5.
3. q(O)=1/126 and 1/126<1/100.
4. For every z∈S, if z is split then q(z)=1/126; if z is not split then
   q(z)≥13/63.
5. #{z∈S:q(z)<1/100}/252=8/63.
6. For every z,z'⊆U and every i∈U, if i∈z iff i∈z', then Y_z(i)=Y_z'(i).
7. For k=0,…,5, binom(5,k)² is the k-th entry of [1,25,100,100,25,1].
8. Exactly 32 supported subsets are split.
9. For every z∈S,
   F(z,Y_O)=(2|z∩P(O)|−5)/5, with real rather than natural subtraction.
10. For every b, Y_O(b,false)=1 and Y_O(b,true)=0.
11. The two separate means Σ_{i∈O}Y_O(Pi)/5 and
    Σ_{i∈U\O}Y_O(Pi)/5 are respectively 0 and 1.
12. P(O)=U\O and P(U\O)=O.
13. q(O)=2/252 and 2⁵=32 as a natural-number equality.

There is no four-block population, assignment space, or conclusion in this
proposition.

## SAP.P037c.T36

For **every finite type Ω and every finite type I**, including types which are
empty before the following hypotheses are supplied, the theorem asserts three
conjuncts. Define the nomination statistic, for E⊆I and real arrays A,M,z,Y, by

    H(E,A,M,z,Y)
      = [Σ_{i∈E,j∈I} A_ij M_j z_i Y_j]/[Σ_{i∈E,j∈I} A_ij M_j z_i]
        −[Σ_{i∈E,j∈I} A_ij M_j (1−z_i) Y_j]/[Σ_{i∈E,j∈I} A_ij M_j (1−z_i)].

First conjunct: **for every**, in order, E⊆I, A:I×I→R, M:I→R,
Z:Ω×I→R, p:Ω→R, Y:Ω×I→R, z0∈Ω, and α∈R, assume:

* every A_ij≥0;
* every M_i is either 0 or 1;
* every Z(ω,i) is either 0 or 1;
* for every ω,i with i∉E, Z(ω,i)=0;
* for every ω, each of the two denominators in H(E,A,M,Z_ω,Y) is positive;
* every p(ω)>0 and Σ_ω p(ω)=1;
* for every ω,ω',i, Y(ω,i)=Y(ω',i) (global sharp null);
* 0≤α≤1.

Define

    q(ω)=Σ_{ω'∈Ω} p(ω') 1{|H(E,A,M,Z_ω',Y_z0)| ≥ |H(E,A,M,Z_ω,Y_z0)|}.

Then Σ_ω p(ω)1{q(ω)≤α}≤α. The outcome vector is fixed at the arbitrarily
quantified z0 in both statistics, and ties are included in the upper tail.

Second conjunct: **for every**, in order, E,A,M,z,baseline,δ, with the same
nonnegative A, binary M,z, z=0 off E, and both denominators strictly positive,

    H(E,A,M,z,baseline+δz) = H(E,A,M,z,baseline)+δ H(E,A,M,z,z).

Third conjunct is a **closed** ten-unit witness, independent of Ω,I. Use U,P,S,O,
Y_z,F,q from T35 and put A_ij=1{j=P(i)}. It says:

* for every z∈S and every Y:U→R,
  H(U,A,1,Y_z,Y)=F(z,Y);
* for all subsets z,z' and i, identical own membership implies Y_z(i)=Y_z'(i);
* it is **not** the case that for every z,z'∈S and every i, Y_z(i)=Y_z'(i);
* H(U,A,1,Y_O,Y_O)=−1, q(O)=1/126, and
  #{z∈S:q(z)<1/100}/252=8/63.

Thus the actual witness has no dependence of an individual's outcome on anyone
else's treatment, but violates the global sharp null. No conditional test of a
no-social-influence null is asserted to be valid.

## SAP.P037c.T27

This is a closed conjunction with no hypotheses.

### All definitions used in the conjunction

There are twelve analysis units i=(k,j)∈{0,1,2,3}×{0,1,2}, with x_i=k+j,
potential response Y_i(h)=(2 if h=3, otherwise 1)x_i, observed D_i=k,
and observed Y_i=Y_i(k).

For a four-vector v of weights set

    β(v)=(v0+v1+v2+2v3)/(v0+v1+v2+v3),
    B(v)=[1−β,2−2β,3−3β,8−4β,β],
    M(B,h)=B_h+(5/2)B_4.

The theorem only uses v=[4,4,4,4] and [2,8,8,4]; no nonzero claim is made here
for arbitrary v. The separate augmented mean is

    S(v,h)=(1/12)Σ_i [1{D_i=h} v_{D_i}(Y_i−f_h(i))+f_h(i)],
    f_h(i)=(2 if h=3, otherwise 1)x_i.

There are six schools s=0,…,5 with size n_s=7 for s<3 and 9 otherwise,
and a total student population of all pairs (s,a), 0≤a<n_s. The twelve focal
students are: i=(0,j) maps to school j, student 6; i=(k,j) with k>0 maps to
school k+2, student 6+j. Directed nomination a→b in school s holds exactly when

    (a≥6 and (b=0 or b=2)) or ((a=4 or a=5) and b=0).

Indegree is the number of nominators. Sort all n_s indegrees increasingly, set
h=9(n_s−1), q=floor(h/10), r=h mod 10, and define the threshold
Q_s=(10−r)/10 times sorted[q]+r/10 times sorted[q+1]. List access defaults to
0 if out of range, exactly as `List.getD`; these sizes use valid indices.

An assignment consists of a three-element subset H of the six schools and a
pair of Boolean choices b_s=(u_s,v_s) for **every** school. The seed set in s is
{0 if u_s else 1, 2 if v_s else 3}. For any student, assign exposure:

* 0 if its school is outside H;
* otherwise 4 if it belongs to the seed set;
* otherwise 3 if it has an outgoing or incoming nomination with a selected seed
  whose indegree is **strictly** greater than Q_s;
* otherwise 2 if it has an outgoing or incoming nomination with any selected seed;
* otherwise 1.

The focal hierarchical exposure is 0 if its school is outside H, otherwise 3 if
u_s is true, otherwise 2 if v_s is true, otherwise 1. The probability π_a(h)
is the explicit sum of 1/(20·4⁶) times the exposure indicator, over every H of
size three and every one of the 4⁶ school-choice functions. There are no
independent four-category assignments to individual analysis units in this theorem.

### Exact assertions

1. For every s,a, indegree is n_s−4 at a=0, n_s−6 at a=2, and zero otherwise.
   Every Q_s equals 9/5 for s<3 and 17/5 otherwise. For every s,a,
   indegree(a)>Q_s iff a=0.
2. For every school and Boolean seed choice the seed set has size two, exactly
   one seed has index <2, and exactly one has index in [2,4).
3. The focal-student map is injective. For every H, every full function of seed
   choices, and every focal i, its student exposure equals its hierarchical
   exposure (embedded from four into five categories).
4. For every focal i and h=0,…,3, π_i(h)=[1/2,1/8,1/8,1/4]_h.
5. For every student a, all four π_a(h) lie strictly between 0 and 1 iff a is
   one of the twelve focal students. (This does not require positivity for h=4.)
6. Summing 1/(20·4⁶) over seed functions that produce the observed focal
   exposures D_i=i.first when H={3,4,5} gives 1/640.
7. Σ_i x_i/12=5/2.
8. For each of the two specified weight vectors v and every h, [0,2 if h=3
   else 1] globally minimizes Σ_{i:D_i=h}v_h(Y_i−c0−c1 x_i)².
9. For each such v and **every** five-vector c, c is a global minimizer of the
   pooled objective with four group indicators and common covariate x iff c=B(v).
10. B([4,4,4,4])=[−1/4,−1/2,−3/4,3,5/4];
    B([2,8,8,4])=[−2/11,−4/11,−6/11,36/11,13/11].
11. For every h, M(B([4,4,4,4]),h)=[23/8,21/8,19/8,49/8]_h and
    M(B([2,8,8,4]),h)=[61/22,57/22,53/22,137/22]_h.
12. 15/4≠5/2 and 42/11≠5/2.
13. For each specified v and h, the group weighted sum of pooled residuals
    Σ_{j=0}² v_h(Y_(h,j)−B(v)_h−x_(h,j)B(v)_4) is zero; the corresponding
    all-unit weighted sum of x_i times the pooled residual is also zero.
14. For each specified v and h, S(v,h)=5 if h=3, and 5/2 otherwise.
15. The pooled 3-minus-2 contrasts are 15/4 and 42/11 respectively.
    Their differences from 5/2 are respectively 5/4 and 29/22.
16. For every h, Σ_i Y_i(h)/12 equals 5 if h=3 and 5/2 otherwise.
    Every observed separate residual Y_i−(2 if D_i=3 else 1)x_i is zero.
17. For each specified v, S(v,3)−S(v,2)=5/2.
18. For every focal i, 1/π_i(D_i)=[2,8,8,4]_{D_i}.

## SAP.P037c.T28

For **every finite type I**, this asserts five general groups of identities and
two numerical equalities. There is no outer nonemptiness assumption: each
identity involving population averages separately assumes n=|I|>0.

Define X^P(D,x) with row (four group indicators for D_i∈{0,1,2,3}, followed
by x_i∈R^p), and X^S(x) with row (1,x_i). For predictions f and group h define

    A(D,w,Y,f,h)=(1/n)Σ_i [1{D_i=h}w_i(Y_i−f_i)+f_i].

First: **for every**, in order, natural p, proof n>0, D:I→Fin 4, w,Y:I→R,
proof every w_i>0, x:I→R^p, b∈R^(4+p), and separate coefficient vectors
s_h∈R^(1+p), assume:

* X^P(D,x) has full column rank;
* for every h, the map c↦(X^S(x)c)|_{D=h} is injective;
* b is a global WLS minimizer for X^P, w, Y;
* for every h, s_h is a global WLS minimizer for X^S with weights w_i1{D_i=h}.

Put f^P_h(i)=b_h+Σ_j x_ij b_(4+j) and
f^S_h(i)=s_h,0+Σ_j x_ij s_h,(1+j). Then, for every h:

* Σ_{D_i=h}w_i(Y_i−f^P_h(i))=0 and Σ_{D_i=h}w_i(Y_i−f^S_h(i))=0;
* A(D,w,Y,f^P_h,h)=Σ_i f^P_h(i)/n, and similarly for f^S_h.

For every h,l the difference of the two pooled prediction averages is b_h−b_l.

Second: **for every**, in order, proof n>0, D:I→Fin 4, w,x,Y:I→R, and
proof every w_i>0, define for h=0,…,3

    W_h=Σ_{D_i=h}w_i,
    xb_h=Σ_{D_i=h}w_i x_i/W_h,   yb_h=Σ_{D_i=h}w_i Y_i/W_h,
    Sxx_h=Σ_{D_i=h}w_i(x_i−xb_h)²,
    Sxy_h=Σ_{D_i=h}w_i(x_i−xb_h)(Y_i−yb_h),
    b_h=Sxy_h/Sxx_h,   β=Σ_h Sxy_h/Σ_h Sxx_h,   xbar=Σ_i x_i/n.

**If every Sxx_h>0**, all the following hold:

* for every h and every c∈R², c is a separate global WLS minimizer iff
  c=[yb_h−b_h xb_h,b_h];
* for every c∈R⁵, c is a pooled global WLS minimizer iff
  c=[yb_0−βxb_0,…,yb_3−βxb_3,β];
* for every h, (yb_h−b_h xb_h+b_h xbar)−(yb_h−βxb_h+βxbar)
  =(b_h−β)(xbar−xb_h).

Third: **for all real** yb,bk,β,xb,xbar, the last algebraic factorization holds
with these scalar values, without design hypotheses.

Fourth: **for every**, in order, p∈N, proof n>0, α:Fin 4→R, β:Fin p→R,
x:I→R^p, and h∈Fin 4,

    (1/n)Σ_i(α_h+Σ_j x_ij β_j)=α_h+Σ_j[(1/n)Σ_i x_ij]β_j.

Fifth: **for all real** yb,bk,β,xb,xbar,

    yb−bk xb+bk xbar = yb−βxb+βxbar  iff  bk=β or xbar=xb.

Finally (2−5/4)(5/2−4)=−9/8 and 5−49/8=−9/8.

## SAP.P037c.T33

This is a closed statement about eight units i=(j,a), 0≤j<4, 0≤a<2,
and 96 assignments z=(H,b). Here H is one of the six two-element subsets of
{0,1,2,3}, enumerated in lexicographic order, and b is any Boolean function
on the four pairs. Put r=[1/10,1/5,3/10,2/5]. The mass of (H,b) is

    q(H,b)=(1/6)Π_j [ r_j if b_j=true else 1−r_j, if j∈H;
                      1/2, otherwise ].

Exposure D_z(j,a) is 3 if j∈H and b_j=(a=0), 2 if j∈H and this equality
fails, 0 if j∉H and the equality holds, and 1 otherwise. Define

    πI(j,a)=(1/2)(r_j if a=0 else 1−r_j),
    π_i(0)=π_i(1)=1/4, π_i(2)=1/2−πI_i, π_i(3)=πI_i.

For **any** exposure function D on these units, w(D)_i=1/π_i(D_i),
X(D) has four indicator columns followed by the fixed covariate πI_i, and
R(D)=(X(D)ᵀ diag(w(D)) X(D))⁻¹X(D)ᵀdiag(w(D)).
The observed exposure D0 equals 3,2 for the two members of pairs 0,1,
and 0,1 for the two members of pairs 2,3. The response array is
[[0,2],[1,0],[3,1],[2,4]]. Put b0=R(D0)Y, m_h=b0_h+b0_4/4,
e=Y−X(D0)b0, and Y*_z(i)=Y_i+m_(D_z(i))−m_(D0(i)).

The full contrast F_z(V) is coefficient 3 minus coefficient 2 in R(D_z)V.
The collapsed contrast G_z(V) is the same coefficient difference with the
covariate removed and the same assignment-specific inverse-probability weights.
Var(f)=Σ_z q_z f_z²−(Σ_z q_z f_z)². Define the two exact constants

    VF = 1574066925743604937750798623088231315086040632174801225920729815316988109390788379330079414475192929
         /171796363313262196427951740421954806512514436622177625713808591915692887084446808987770465290240000,
    VG = 1453114769225810453/621302156766720000.

The conjunction asserts all of the following:

1. The assignment type has size 96, Σ_z q_z=1, and every q_z>0.
2. For every z,h, exactly two units have exposure h. For every unit and h,
   Σ_z q_z 1{D_z(i)=h}=π_i(h).
3. For every z, X(D_z) has full column rank.
4. b0=[1/13,−2,−14/3,−23/39,180/13], and for every h,
   m_h=[46/13,19/13,−47/39,112/39]_h.
5. For every z, F_z(Y*_z)=F_z(e)+m_3−m_2.
6. Var(z↦F_z(e))=VF, Var(z↦G_z(e))=VG,
   9<VF<37/4, and 2<VG<5/2.
7. Var(G(e))≠Var(F(e)).
8. e=[[-4/39,17/39],[8/39,-34/39],[11/13,-24/13],[-11/13,24/13]].
9. Var(z↦F_z(Y*_z))=VF.
10. For every i, π_i(2)+π_i(3)=1/2; for **every exposure function D** and
    every i, w(D)_i>0; X(D0) has full column rank; and for every z, the
    four-indicator collapsed design has full column rank.

There is no conclusion about the shift in each of the four refitted exposure
means individually, and no asserted graph or seed construction for this design.

## SAP.P037c.T34

For **every finite type Ω**, the theorem conjoins two universally quantified
statements with the same premises. In each statement quantify, in order,
natural n,p, a proof n>0, D0:Fin n→Fin 4, D:Ω→Fin n→Fin 4,
a fixed real n-by-p control matrix C, w0:Fin n→R,
w:Ω→Fin n→R, proofs w0_i>0 and w_ωi>0, proofs that X0=X^P(D0,C)
and every X_ω=X^P(D_ω,C) have full column rank,
y:Fin n→R, prob:Ω→R, a proof prob_ω≥0 for every ω,
and a proof Σ_ω prob_ω=1.

Define R0=(X0ᵀW0X0)⁻¹X0ᵀW0, b0=R0y,
cbar_j=(1/n)Σ_i C_ij, row_h=(four indicators for h,cbar),
m_h=row_h·b0, e=y−X0b0,
y*_ω(i)=y_i+m_(D_ωi)−m_(D0_i),
L_ω=(X_ωᵀW_ωX_ω)⁻¹X_ωᵀW_ω.

The first statement concludes:

1. For all h,l, m_h−m_l=b0_h−b0_l.
2. For every ω, L_ω X_ω is the identity matrix and
   L_ω y*_ω=L_ω e+b0.
3. For every ω,h,
   row_h·L_ω y*_ω=row_h·L_ω e+m_h.
4. For every h,l, the finite-probability variance of
   ω↦(row_h−row_l)·L_ω y*_ω equals the variance of
   ω↦(row_h−row_l)·L_ω e.

The second statement (with a fresh universal quantification of the same
objects and hypotheses) concludes:

1. For every ω,i, y*_ω(i)=y_i−b0_(D0_i)+b0_(D_ωi).
2. For every ω, y*_ω=e+X_ω b0.
3. For every h, Var(ω↦row_h·L_ω y*_ω)=Var(ω↦row_h·L_ω e).

There is no statement about any refit with a different or smaller control
matrix, nor any explicit numerical counterexample here.

## SAP.P037c.T43

For **every finite type Ω and every finite control-index type K**, the theorem
conjoins two statements. A `FiniteDesign Ω` is exactly a function q:Ω→R with
every q_ω≥0 and Σ_ω q_ω=1. Define E f=Σ_ω q_ω f_ω,
⟨u,v⟩=Σ_i u_i v_i, and [u,v]=E⟨u,v⟩.

For a natural B the unit index is Fin B×Fin 4. For any vector x define
(Mx)_(b,j)=x_(b,j)−(1/4)Σ_l x_(b,l). Thus demeaning is over complete
four-unit blocks. Given T,C:Ω→(Fin B×Fin 4)→R and X:K→(Fin B×Fin 4)→R,
write t_ω=MT_ω, z_ω=M(T_ω C_ω), V_k=MX_k, and

    π=[z,t]/[t,t],   r_ω=z_ω−πt_ω−p Σ_k λ_k V_k.

The first statement quantifies **for every**, in order: B∈N, finite design q,
T,C,Y, fixed vectors X,a,η,μ, fixed λ:K→R, real p,τ0,β,τ,b,
and g:K→R. It then assumes:

* for every i, E T_i=p;
* for every i, E(T_i C_i)=p μ_i;
* for every i, (Mμ)_i=Σ_k λ_k (MX_k)_i;
* for every ω,i, Y_ωi=a_i+T_ωi(τ0+η_i+β C_ωi);
* [t,t]≠0;
* [r,r]>0;
* the specified coefficients (τ,g,b) satisfy the expected normal equations:
  with ε_ω=MY_ω−τt_ω−Σ_k g_k V_k−b z_ω,
  [t,ε]=0, [V_k,ε]=0 for every k, and [z,ε]=0.

The conclusion is

    b−β = [r,(ω,i↦T_ωi η_i)]/[r,r].

The second statement separately quantifies B,q,T,C,Y,X,a,μ,λ,p,τ0,β,τ,b,g
in the corresponding order, with exactly the same hypotheses except that η
is absent and the response model is Y_ωi=a_i+T_ωi(τ0+β C_ωi).
Its conclusion is b=β.

In particular, these are implications for **any supplied normal-equation
solution**. Existence of such a solution is not a conclusion. There is no
binary-treatment, range-of-p, treatment-count, control-rank, or independence
hypothesis beyond the moment, span, and nondegeneracy conditions explicitly
listed. There is also no separate residual-moment conclusion or explicit
nondegenerate example in this theorem. Although B=0, empty Ω, or degenerate
design choices exist as types/data before hypotheses, the probability and
positive-second-moment premises exclude them from an applicable instance.
