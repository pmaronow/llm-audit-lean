# Blind reading

Saved before opening `claims.json` or `record.json`. Sources read: every entry of
`closure.json`, Challenge/Part1, Defs/Part1, Part2, Part5, Part6, and WholeW1.
The two generated declarations in the closures were also printed in
`scratch/Inspect.lean`: both prove that the natural numeral `1+1` is at least two,
solely to synthesize a real numeral instance; neither adds a statistical axiom.

## Fully unfolded notation used below

This dictionary is part of each of the five readings. All sums are ordinary
finite real sums. Let I={0,...,n-1}, J={0,...,d-1}. A Population is exactly three
arbitrary functions x:I→(J→R), yT:I→R, yC:I→R, with no fields of assumptions.
Write x_i for the vector x(i), u·v=Σ_{k∈J}u_k v_k,
A_S(f)=(Σ_{i∈S}f_i)/|S|, A(f)=A_I(f), and C=I\S.
Write c_S(f,g)=A_S(fg)-A_S(f)A_S(g) and c(f,g)=c_I(f,g).
Let D(n,m) be the finite set of **all** subsets S⊆I with |S|=m.
E_m(F)=Σ_{S∈D(n,m)}F(S)/|D(n,m)| and
Pr_m(B)=|{S∈D(n,m):B(S)}|/|D(n,m)|. Thus this is uniform complete
randomization, without any auxiliary random variables or replicate coupling.

Define z_S=(A_S(x_k))_{k∈J}, G=(A(x_k x_l))_{k,l∈J},
h_i=Σ_k x_{ik}², H(y)=A(hy)-A(h)A(y), τ=A(yT)-A(yC),
p=m/n, q=(n-m)/n (real subtraction), and b(y)=(A(y x_k))_k.
`standardized` means **both** z_I=0 and G=identity matrix.
Define V_S=(A_S(x_k x_l)-z_{S,k}z_{S,l})_{kl} and
w_S(y)=(A_S(y x_k)-A_S(y)z_{S,k})_k.
Then L_S=Id-p z_S z_Sᵀ-q z_C z_Cᵀ,
W_S=p w_S(yT)+q w_C(yC), B_S=L_S^{-1}W_S,
B_S(y)=V_S^{-1}w_S(y), and N=p b(yT)+q b(yC).
`noninteractedRegular` means det(L_S)≠0 for **every** S∈D(n,m).
`interactedRegular` means det(V_S)≠0 and det(V_C)≠0 for **every** such S.

For any y:I→R, let y°_i=y_i-A(y), and set
u1_S(y)=(A_S(y° x_k)-A(y° x_k))_k,
u2_S(y)=(V_S^{-1}-Id)w_S(y),
u3_S(y)=(-z_{S,k}A_S(y°))_k.
Set v1_S=p u1_S(yT)+q u1_C(yC),
v2_S=(L_S^{-1}-Id)W_S, and
v3_S=p u3_S(yT)+q u3_C(yC).
These are exactly `armNu1/2/3` and `nu1/2/3`, respectively.

The noninteracted and interacted estimates are, respectively,
T_S=A_S(yT)-A_C(yC)-(z_S-z_C)·B_S and
TI_S=A_S(yT)-A_C(yC)-z_S·B_S(yT)+z_C·B_C(yC).
Write
K_S=[c_C(h,yC)-c_S(h,yT)]/(n-2)+(z_C-z_S)·v2_S,
KI_S=m/[(n-2)(n-m)] c_C(h,yC)+z_C·u2_C(yC)
      -(n-m)/[(n-2)m] c_S(h,yT)-z_S·u2_S(yT).
The debiased estimates are T_S-K_S and TI_S-KI_S.
The inverse-free arm expression is
D_S(y)=A_S(y)-z_S·w_S(y)+(n-|S|)/[(n-2)|S|] c_S(h,y).

The numerical coefficients are
a(n,m)=(n-m)(n-2m)/[(n-1)(n-2)m²],
aC(n,m)=a(n,n-m), where this **argument** n-m is natural subtraction,
and aTC(n,m)=-(n-2m)/[(n-1)(n-2)m].
These unfold `NTTT`, `NCCC`, and `NTTC`.

Common conventions: real division is total, with a/0=0. A_S and E_m therefore
return zero on an empty averaging set; the same holds for Pr_m on an empty
design. In the finite assertions n≥2 or n≥3 and 0<m<n ensure nonempty population,
both nonempty arms, and nonempty design. Factors n-1, n-2, m, n-m in displayed
real denominators are guarded where used (n-2 occurs only when n≥3). In T21's
(11)/(12) block the additional arm-size bounds guard m-1 and n-m-1. The casts
inside `(n-2 : R)`, `(n-1 : R)`, `(n-2*m : R)`, and the scalar formulas above
are real arithmetic, not natural truncated subtraction; natural subtraction is
used in the argument a(n,n-m), the tests 2≤n-m and m=n-m, and finite complements.
Under m<n those natural differences equal the corresponding nonnegative integer
differences.

Mathlib's square matrix inverse is the ordinary inverse when the real determinant
is nonzero, and the zero matrix when it is zero. All inverse-dependent conclusions
here are guarded on the whole assignment design. Inverse-free expressions require
no inverse convention. If d=0, vectors and matrices are empty, all vector dot
products are zero, and the empty determinant is 1. This is a legitimate regression
without covariates, not an inconsistent hypothesis. If n=0 all population means
would be zero by total division, but no finite quantified hypothesis permits it.
There are no Bochner integrals, extended real conversions, partial functions,
integer casts, infima, limsups, liminfs, or real powers in these closures.

## SAP.P005b.T20

The docstring calls two universal assertions false (a third-component sign
identity and an asymptotic expansion under a literal logarithm condition), while
asserting the exact slopes, bias decomposition, and first-component moments.
The statement is a conjunction of three independently quantified propositions:

1. All of T24 as spelled out in its section below, with n≥2, not n≥3.
2. It is **not** true that for every natural n,d,m and every population P,
   n≥3, 0<m<n, z_I=0, G=Id, and interacted regularity imply
   E_m[z_C·u3_C(yC)]-E_m[z_S·u3_S(yT)]
   =aC(n,m)H(yC)-a(n,m)H(yT).
   Equivalently, there exist n,d,m,P satisfying every one of those conditions
   for which that equality fails. The witness may have d=0 syntactically,
   although d=0 itself cannot break this zero-valued identity.
3. It is **not** true that for every pair of natural sequences d_n,m_n and
   populations P_n on Fin n with d_n covariates, the following assumptions imply
   the stated stochastic order. The assumptions, in order, are:
   (a) for all n≥3, 1≤d_n≤n and 0<m_n<n;
   (b) there exists one real K≥0 such that for every n≥3,
   A(yT_n²)≤K, A(yC_n²)≤K, and for every coordinate k, A(x_{n,k}²)≤K;
   (c) z_{I_n}=0 and G_n=Id eventually as n→∞;
   (d) there exist real lo,hi with 0<lo<hi<1 such that
   lo<m_n/n<hi for all n≥3;
   (e) interacted regularity eventually;
   (f) κ_n log(d_n)→0, where κ_n=sup_{i∈Fin n}(h_{n,i}/n).
   Define eT_i=yT_i-A(yT)-x_i·b(yT) and similarly eC;
   R_n(S)=TI_{n,S}-τ_n-[A_S(eT)-A_C(eC)],
   r_n=sqrt(κ_n d_n/n). The conclusion being denied is:
   for every real ε>0 there exist real M>0 and natural n0 such that
   for every n≥n0, Pr_{m_n}(|R_n(S)|>M r_n)<ε.
   Thus the third conjunct existentially asserts sequences meeting all these
   assumptions but failing this ε,M,n0 probability criterion.

In addition to the common conventions: real sSup on an empty or unbounded set
is totalized; here the set is finite and nonempty for n≥3, so κ is an ordinary
maximum there. Real.log 0=0 and log of a negative argument is log of its absolute
value; eventual d_n≥1 excludes both cases. log 1=0 is an ordinary in-domain value
and makes the logarithm condition automatic in dimension one. Real.sqrt of a
nonpositive value is zero; the argument is nonnegative for n≥3. With positive
dimension and standardization, κ_n>0 eventually, so the asymptotic rate is
positive. Arbitrary values at n=0,1,2 are immaterial to convergence and stochastic
order; the uniform moment and sampling-fraction clauses explicitly start at 3.
There is no stochastic bound hidden in the definitions: the probability is the
cardinality ratio specified above.

## SAP.P005b.T21

The theorem is T21WholeStatement. Its two conjuncts repeat the same universal
quantifiers and hypotheses independently: for **every** natural n,d,m and every
population P, if n≥3, 0<m<n, z_I=0, G=Id, and det(L_S)≠0 for every S∈D(n,m),
the following conclusions hold.

From T21Statement:

* E_m(K)=E_m(T)-τ, and E_m(T-K)=τ.
* For every S∈D(n,m),
  T_S-K_S=A_S(yT)-A_C(yC)-(z_S-z_C)·W_S
          +c_S(h,yT)/(n-2)-c_C(h,yC)/(n-2).
* E_m(T)-τ=E_m[(z_C-z_S)·(v1_S+v2_S+v3_S)].
* For every S∈D(n,m), (z_C-z_S)·v2_S
  =(z_C-z_S)·[(L_S^{-1}-Id)W_S]. This last clause is definitional.
* **If additionally** m≥2 and n-m≥2, define
  J11_S=1/(n-1){(n-m)(n-1)/[(n-m-1)n] c_C(h,yC)
                    -m(n-1)/[(m-1)n] c_S(h,yT)} and
  J12_S=a(n,m)m²(n-1)/[(n-m)(m-1)n] c_S(h,yT)
                    -aTC(n,m)m(n-1)/[(n-m-1)n] c_C(h,yC).
  Then E_m(J11)=[H(yC)-H(yT)]/(n-1),
  E_m(J12)=(p/q)a(n,m)H(yT)-(p/q)aTC(n,m)H(yC),
  E_m(J12)=(n-2m)/[(n-1)(n-2)m]H(yT)
              -(2m-n)/[(n-1)(n-2)(n-m)]H(yC),
  and for every S, J11_S+J12_S=[c_C(h,yC)-c_S(h,yT)]/(n-2).

From the second WholeW1 conjunct:

* For every S∈D(n,m), set Y_i=yT_i if i∈S and yC_i otherwise,
  loss(a,t,b)=Σ_i[Y_i-a-t 1_{i∈S}-x_i·b]², and
  a0=A_C(yC)-z_C·B_S. For **every** real a,t and vector b:J→R,
  loss(a0,T_S,B_S)≤loss(a,t,b); if equality of these losses holds, then
  a=a0, t=T_S, and b=B_S. This is precisely uniqueness of the least-squares
  minimizer with intercept, treatment indicator, and common covariate slope.
* E_m[(z_C-z_S)·v1_S]=[H(yC)-H(yT)]/(n-1).
* E_m[(z_C-z_S)·v3_S]=(p/q)a(n,m)H(yT)-(p/q)aTC(n,m)H(yC).

All SAP symbols used here have been unfolded in the dictionary or this section,
including indicator (0 or 1 according to membership), observed outcome, fitted
value, loss, intercept, and unique-minimizer predicate. The docstring asserts
exact unbiasedness and these identities, and distinguishes the extra nonzero
denominators of J11,J12. The common junk-convention analysis applies; q>0 and
n≥3 additionally guard p/q and n-2. There are no logarithms, square roots,
suprema, or asymptotic notions in this target. Empty covariate dimension remains
permitted, with an ordinary unique intercept/treatment regression.

## SAP.P005b.T22

The statement has three independently quantified conjuncts:

1. For every natural n,d,m and P, if n≥3, 0<m<n, z_I=0, G=Id, and both
   V_S,V_C are invertible for every S∈D(n,m), then
   E_m(KI)=E_m(TI)-τ, E_m(TI-KI)=τ,
   E_m[D_S(yT)]=A(yT), E_m[D_C(yC)]=A(yC), and for every S∈D(n,m),
   TI_S-KI_S=
   {A_S(yT)-z_S·w_S(yT)+(n-m)/[(n-2)m] c_S(h,yT)}
   -{A_C(yC)-z_C·w_C(yC)+m/[(n-2)(n-m)] c_C(h,yC)}.
2. For every natural n,d,m and P, if n≥3, m≥2, m<n, and z_I=0 (without
   standardization of G or regularity), then E_m[D_S(yT)]=A(yT).
3. For every natural n,d,m and P, if n≥3, 0<m<n, n-m≥2, and z_I=0
   (without standardization of G or regularity), then E_m[D_C(yC)]=A(yC).

The docstring describes exact unbiasedness, the inverse-free identity, both
armwise expectations, and the two weaker centered-covariate hypotheses. In D_C
the size parameter is |C|, exactly n-m on the design, not the sampling size m.
All SAP notions are explicitly expanded above. Common total division, finite
sums, empty vectors, and singular inverse conventions apply; the inverse-free
two extra assertions are genuinely free of inverse hypotheses. Here n-2>0 and
both arms are nonempty, so no junk division is used. There are no other
potentially partial analytic operations in this target.

## SAP.P005b.T23

For every natural n,d,m and P, if n≥3, 0<m<n, z_I=0, G=Id, and all L_S
for S∈D(n,m) have nonzero determinants, the following conjunction holds:

* For every S∈D(n,m), B_S=N+v1_S+v2_S+v3_S.
* E_m(T)-τ=E_m[(z_C-z_S)·(v1_S+v2_S+v3_S)].
* E_m[(z_C-z_S)·v1_S]=[H(yC)-H(yT)]/(n-1).
* [H(yC)-H(yT)]/(n-1)
  =-1/(n-1) A_i[(h_i-A(h))(yT_i-yC_i)].
* E_m[(z_C-z_S)·v3_S]
  =(n-2m)/[(n-1)(n-2)m]H(yT)
   -(2m-n)/[(n-1)(n-2)(n-m)]H(yC).
* If there exists a real c such that yT_i-yC_i=c for every i, then
  E_m[(z_C-z_S)·v1_S]=0.
* If m=n-m (natural subtraction), then E_m[(z_C-z_S)·v3_S]=0.

The existential c is inside the antecedent of the sixth conjunct, after the
population is fixed. The balanced-design antecedent is similarly conditional;
neither is a global hypothesis. The docstring attributes these exact identities
and vanishing consequences to Theorem 3.1 and Remark 1. All definitions are
expanded above, including N and the two covariance notions. Every real
denominator in this target is nonzero under the main hypotheses. Dimension zero
is allowed and has the legitimate empty-matrix interpretation described above.
There are no logs, roots, suprema, limiting operations, or integration conventions.

## SAP.P005b.T24

For every natural n,d,m and P, if n≥2, 0<m<n, z_I=0, G=Id, and for every
S∈D(n,m) the two arm covariance matrices V_S,V_C are invertible, then:

* For every such S, both equalities hold:
  B_S(yT)=b(yT)+u1_S(yT)+u2_S(yT)+u3_S(yT), and
  B_C(yC)=b(yC)+u1_C(yC)+u2_C(yC)+u3_C(yC).
* E_m(TI-τ)=E_m[z_C·(u1_C(yC)+u2_C(yC)+u3_C(yC))]
             -E_m[z_S·(u1_S(yT)+u2_S(yT)+u3_S(yT))].
* E_m[z_S·u1_S(yT)]=(n-m)/[(n-1)m] H(yT).
* E_m[z_C·u1_C(yC)]=m/[(n-1)(n-m)] H(yC).
* E_m[z_C·u1_C(yC)]-E_m[z_S·u1_S(yT)]
  =m/[(n-1)(n-m)] H(yC)-(n-m)/[(n-1)m] H(yT).

There is no third-component sign identity and no asymptotic expansion in this
statement. The docstring calls it Theorem 4.1's valid exact part and describes
exactly these slope, bias, and first-component formulas. All SAP symbols are
unfolded in the dictionary and this section. The only real scalar denominators
are population/design/arm sizes and (n-1)m, (n-1)(n-m), all nonzero under these
hypotheses. The real inverse is guarded on every assignment. In particular n=2
is allowed only with zero covariate dimension, since positive-dimensional
singleton arm covariances are singular; this is a legitimate nonempty case.

## Library-convention addendum (checked after the claim and record stages)

Mathlib's `Real.sSup_empty` gives sSup(empty subset of R)=0;
`csSup_of_not_bddAbove` gives the same zero value for an unbounded-above subset
of R. Thus T20's κ at n=0 is zero. These conventions do not affect any of the
readings or the claim-stage conclusions: for all n≥3 the leverage range is
finite and nonempty and its supremum is an actual maximum.
