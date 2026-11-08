# Blind reading of the Challenge

This file was written after reading only SAP/P005b/Defs.lean, its seven
parts, SAP/P005b/Challenge.lean, its Part1, and the relevant Mathlib
definitions. Neither claims.json nor record.json has been read.
The Challenge has thirteen theorem stubs, T15 through T27. Each asserts
the proposition defined by the correspondingly named Statement.

## Common mathematical objects and conventions

All population sizes, dimensions, and arm sizes are natural numbers.
The individuals are \(I_n=\{0,\ldots,n-1\}\). A population \(P\) consists
of arbitrary real vectors \(x_i\in\mathbb R^d\) and two arbitrary real
outcome arrays \(y_{Ti},y_{Ci}\), for \(i\in I_n\).
There is no randomness in these arrays.

For a subset \(S\subseteq I_n\), write \(C=I_n\setminus S\),
\(\bar a_S=|S|^{-1}\sum_{i\in S}a_i\), and
\(\bar a=n^{-1}\sum_i a_i\). Means of vectors are coordinatewise.
Write
\[
 c_S(a,b)=\overline{ab}_S-\bar a_S\bar b_S,\qquad
 c(a,b)=\overline{ab}-\bar a\bar b.
\]
These covariances use the divisor \(|S|\), not \(|S|-1\).
\(\widetilde a_i=a_i-\bar a\).
The design \(\mathcal D_{n,m}\) is the finite set of all \(m\)-element
subsets of \(I_n\). For a real function \(f\) of subsets,
\[
 E_m f={1\over|\mathcal D_{n,m}|}\sum_{S\in\mathcal D_{n,m}} f(S),
 \quad V_m f=E_m[(f-E_m f)^2],
 \quad \Pr_m(A)={|\{S\in\mathcal D_{n,m}:A(S)\}|\over
                         |\mathcal D_{n,m}|}.
\]
Thus the probability is uniform complete randomization. It is a ratio
of finite cardinalities coerced to reals, not natural-number division.
Mathlib powersetCard membership is precisely subset membership plus the
specified cardinality. In all finite statistical assertions below,
\(0<m<n\) or positive explicitly specified arm sizes ensure the design
and both arms are nonempty.

Dot products, matrix-vector products, outer products, and the identity
matrix have their usual finite-coordinate meanings, including dimension
zero. Put
\[
 G=\overline{xx^\mathsf T},\quad h_i=x_i^\mathsf T x_i,\quad
 \kappa=\sup_{i\in I_n}h_i/n,\quad \tau=\bar y_T-\bar y_C,
 \quad p=m/n,\quad q=(n-m)/n.
\]
For positive \(n\), the supremum is a maximum of a finite nonempty set.
There is no unbounded supremum in such uses. Standardization means
exactly \(\bar x=0\) and \(G=I_d\).
Define
\[
 b(y)=\overline{yx},\quad b=pb(y_T)+qb(y_C),
 \quad L_S=\overline{xx^\mathsf T}_S-\bar x_S\bar x_S^\mathsf T,
 \quad A_S(y)=\overline{yx}_S-\bar y_S\bar x_S,
\]
\[
 \widehat L=I_d-p\bar x_S\bar x_S^\mathsf T
                 -q\bar x_C\bar x_C^\mathsf T,\qquad
 \widehat N=pA_S(y_T)+qA_C(y_C),
 \quad \widehat b=\widehat L^{-1}\widehat N,\quad
 \widehat b_S(y)=L_S^{-1}A_S(y).
\]
Noninteracted regularity means \(\det\widehat L(S)\ne0\) for EVERY
\(S\in\mathcal D_{n,m}\). Interacted regularity means
\(\det L_S\ne0\) AND \(\det L_C\ne0\) for EVERY such \(S\).
These are deterministic conditions on the entire randomization design,
not just the realized sample.

The three arm slope errors and their common-slope counterparts are
\[
 u_{1S}(y)=\overline{\widetilde yx}_S-\overline{\widetilde yx},
 \quad u_{2S}(y)=(L_S^{-1}-I_d)A_S(y),
 \quad u_{3S}(y)=-\bar x_S\,\overline{\widetilde y}_S,
\]
\[
 v_1=pu_{1S}(y_T)+qu_{1C}(y_C),\quad
 v_2=(\widehat L^{-1}-I_d)\widehat N,\quad
 v_3=pu_{3S}(y_T)+qu_{3C}(y_C).
\]
The regression estimates are the explicit formulas
\[
 \widehat\tau=\bar y_{TS}-\bar y_{CC}
                    -(\bar x_S-\bar x_C)^\mathsf T\widehat b,
 \quad
 \widehat\tau_I=\bar y_{TS}-\bar y_{CC}
        -\bar x_S^\mathsf T\widehat b_S(y_T)
        +\bar x_C^\mathsf T\widehat b_C(y_C).
\]
Define the two bias estimates and corrected estimates by
\[
 \widehat B={c_C(h,y_C)-c_S(h,y_T)\over n-2}
                    +(\bar x_C-\bar x_S)^\mathsf T v_2,
 \quad \widehat\tau_D=\widehat\tau-\widehat B,
\]
\[
 \widehat B_I={m\over(n-2)(n-m)}c_C(h,y_C)
        +\bar x_C^\mathsf T u_{2C}(y_C)
        -{n-m\over(n-2)m}c_S(h,y_T)
        -\bar x_S^\mathsf T u_{2S}(y_T),
 \quad \widehat\tau_{ID}=\widehat\tau_I-\widehat B_I.
\]
Here \(H(y)=c(h,y)\). Common residuals and arm residuals are
\[
 e_i(y)=y_i-\bar y-x_i^\mathsf T b,\qquad
 e_i^A(y)=y_i-\bar y-x_i^\mathsf T b(y).
\]
Write
\[
 \ell=\overline{e(y_T)}_S-\overline{e(y_C)}_C,\qquad
 \ell_I=\overline{e^A(y_T)}_S-\overline{e^A(y_C)}_C .
\]
The armwise inverse-free corrected mean is
\[
 D_S(y)=\bar y_S-\bar x_S^\mathsf T A_S(y)
                +{n-|S|\over(n-2)|S|}c_S(h,y).
\]
For any two arrays \(e_T,e_C\), put
\[
 e_i^{obs}(S)=
 \begin{cases}e_{Ti}&i\in S,\\e_{Ci}&i\notin S,\end{cases}
 \quad
 F(S;e_T,e_C)=(\bar x_S-\bar x_C)^\mathsf T
                    \overline{x e^{obs}(S)}.
\]
Finally the third-moment coefficients are
\[
 a_{TTT}(n,m)={(n-m)(n-2m)\over(n-1)(n-2)m^2},
 \quad a_{CCC}(n,m)=a_{TTT}(n,n-m),\qquad
 a_{TTC}(n,m)=-{n-2m\over(n-1)(n-2)m}.
\]

These definitions are total Lean expressions: real division by zero is
zero; the Mathlib matrix inverse is the ordinary inverse when the
determinant is nonzero and the zero matrix otherwise. Natural subtraction
occurs in armSize, NCCC's argument \(n-m\), and dimension/size arithmetic;
the displayed statistical denominators \(n-1,n-2,m-1\) are real
subtractions. In the uses with \(m<n\), natural \(n-m\) has the usual
positive integer meaning. Empty finite sums are zero. The statements do
not posit positive dimension unless explicitly specified below.

For sequences, all limits are as natural \(n\to\infty\). Define
\(\mathcal H(d,m,P)\) (standingAssumptions) to be the conjunction:

1. For every \(n\ge3\), \(1\le d_n\le n\) and \(0<m_n<n\).
2. There exists a single real \(K\ge0\) such that, for every \(n\ge3\),
   \(\overline{y_{Tn}^2}\le K\), \(\overline{y_{Cn}^2}\le K\), and,
   for every coordinate \(k\in I_{d_n}\),
   \(\overline{x_{nk}^2}\le K\).
3. There exists a threshold after which every \(P_n\) is standardized.
4. There exist real constants \(0<l<u<1\) such that, for every
   \(n\ge3\), \(l<p_n<u\).

The variant \(\mathcal H_0\) used in T17 replaces \(1\le d_n\le n\)
by \(d_n\le n\); all other clauses are identical.
No conditions are imposed at \(n=0,1,2\) by clauses 1, 2, or 4.

The package's \(R_n=O_p(r_n)\) means, in this exact quantifier order:
for every real \(\epsilon>0\), there exist real \(M>0\) and natural
\(n_0\) such that, for every \(n\ge n_0\),
\(\Pr_{m_n}(|R_n(S)|>Mr_n)<\epsilon\).
Its \(R_n=o_p(r_n)\) means: for every real \(\delta>0\),
\(\Pr_{m_n}(|R_n(S)|>\delta r_n)\to0\).
Deterministic Mathlib \(f=O(g)\) means there exists a real constant \(C\)
and a threshold after which \(|f_n|\le C|g_n|\).
These definitions do not themselves require a strictly positive rate.
Square root is Mathlib's nonnegative real square root (zero on
nonpositive arguments). Real.log is the natural logarithm on positive
arguments, extended by log(0)=0 and log(x)=log(|x|) for negative x;
in particular log(1)=0.

Mathlib sources followed: Data/Finset/Powerset.lean (powersetCard);
Data/Matrix/Mul.lean (vecMulVec, mulVec);
LinearAlgebra/Matrix/NonsingularInverse.lean (Inv instance);
Order/ConditionallyCompleteLattice/Defs.lean, Basic.lean, Finset.lean
(finite, bounded nonempty sSup);
Order/Filter/Defs.lean and AtTopBot/Defs.lean, Basic.lean (Tendsto,
eventually atTop);
Analysis/Asymptotics/Defs.lean (IsBigOWith and IsBigO);
Analysis/SpecialFunctions/Log/Basic.lean and Sqrt.lean.

## T15

Universally quantify first natural \(t,c\), with \(t\ge2,c\ge2\).
Let \(n=t+c\), \(a=a_{TTT}(n,t)\), \(b_*=a_{TTC}(n,t)\), and define
\[
 Q_C={1\over n-1}{c(n-1)\over(c-1)n}
                   -b_*{t(n-1)\over(c-1)n},
 \quad
 Q_T=-{1\over n-1}{t(n-1)\over(t-1)n}
                   +a{t^2(n-1)\over c(t-1)n}.
\]
Then the conjunction of the following holds:
\[
 Q_C={1\over n-2},\qquad
 Q_T={n-tn\over(n-2)(t-1)n},\qquad
 {n-tn\over(n-2)(t-1)n}=-{1\over n-2}.
\]
In addition, for EVERY dimension \(d\), population \(P\) of size \(n\),
and subset \(S\) with \(|S|=t\), set \(A=c_S(h,y_T)\),
\(B=c_C(h,y_C)\). Then
\[
 {1\over n-1}\left({c(n-1)\over(c-1)n}B
                 -{t(n-1)\over(t-1)n}A\right)
 +a{t^2(n-1)\over c(t-1)n}A
 -b_*{t(n-1)\over(c-1)n}B
 ={B\over n-2}-{A\over n-2}.
\]
No standardization, outcome bound, or regularity is assumed.

## T16

For EVERY natural \(n,m\), then proofs/assumptions \(n\ge3\),
\(0<m<n\), then real arrays \(a,b,c\) on \(I_n\), then assumptions
\(\sum_i a_i=\sum_i b_i=\sum_i c_i=0\), the following fifteen
clauses all hold. Put \(Z_i(S)=1\) if \(i\in S\), otherwise zero,
\(J=\sum_i a_i b_i c_i\),
\(\pi_2=m(m-1)/(n(n-1))\),
\(\pi_3=m(m-1)(m-2)/(n(n-1)(n-2))\), and
\[
 R(S)=\sum_{i\ne j}Z_iZ_j a_i b_i c_j,\qquad
 T(S)=\sum_{\substack{i,j,k\\\text{pairwise distinct}}}
                       Z_iZ_jZ_k a_i b_j c_k .
\]
Both sums are ordered sums.

1. For every \(i\ne j\), \(E_m Z_iZ_j=\pi_2\).
2. For every pairwise distinct \(i,j,k\), \(E_m Z_iZ_jZ_k=\pi_3\).
3. \(E_m R=\sum_{i\ne j}(E_m Z_iZ_j)a_i b_i c_j\).
4. \(E_m R=-\pi_2 J\).
5. \(E_m T=2\pi_3 J\).
6. \(E_m(\bar a_S\bar b_S\bar c_S)\) equals \(m^{-3}\) times
   the sum of \(E_m\sum_i Z_i a_i b_i c_i\),
   \(E_m\sum_{i\ne j}Z_iZ_j(a_i b_i c_j+a_i b_j c_i+a_j b_i c_i)\),
   and \(E_m T\).
7. \(E_m(\bar a_S\bar b_S\bar c_S)
          =m^{-3}(m/n-3\pi_2+2\pi_3)J\).
8. \(E_m(\bar a_S\bar b_S\bar c_S)
          =a_{TTT}(n,m)\overline{abc}\).
9. \(E_m(\bar a_S\bar b_S\bar c_C)
          =a_{TTC}(n,m)\overline{abc}\).
10. \(m^{-3}(m/n-3\pi_2+2\pi_3)=a_{TTT}(n,m)/n\).
11. \(E_m R=\pi_2\sum_{i\ne j}a_i b_i c_j\).
12. \(\pi_2\sum_{i\ne j}a_i b_i c_j
          =\pi_2(\sum_{i,j}a_i b_i c_j-J)\).
13. \(a_{TTT}(n,m)/n=(n-m)(n-2m)/(nm^2(n-1)(n-2))\).
14. For every \(S\in\mathcal D_{n,m}\),
    \(\bar c_C=-m/(n-m)\bar c_S\).
15. \(a_{TTC}(n,m)=-m/(n-m)a_{TTT}(n,m)\).

## T17

This is a conjunction of four independently universally quantified groups.

First, for every \(n,d,m,P\) with \(n\ge2\), \(0<m<n\), \(G=I_d\),
and then EVERY real array \(\delta\), let
\(\mu=\overline{x\delta}\), \(v=m(n-m)/(n(n-1))\), and
\(A=(1/(qmn))^2v\). Then:

1. For every individual \(i\),
   \(\sum_j[x_i^\mathsf T(x_j\delta_j-\mu)]^2
          \le\sum_j(x_i^\mathsf T x_j\delta_j)^2\).
2. \(A\sum_{i,j}(x_i^\mathsf T x_j\delta_j)^2
          =(1/(qmn))^2 n^2v\sum_j h_j\delta_j^2/n\).
3. The same left side equals
   \(\overline{h\delta^2}/(pqn(n-1))\).
4. \(\overline{h\delta^2}/(pqn(n-1))
          \le\kappa\,\overline{\delta^2}/(pq(n-1))\).

Second, for every \(n,d,P\), if \(n>0\) and \(G=I_d\), then for every
real array \(a\), both
\[
 \sum_{i,j}(x_i^\mathsf T x_j a_j)^2
 =\sum_j a_j^2 x_j^\mathsf T\left(\sum_i x_ix_i^\mathsf T\right)x_j
 =n\sum_j a_j^2h_j
\]
hold as two separate equalities.

Third, for every \(n,d,m,P\), if \(n>0\), then for every real \(K\)
such that \(\overline{y_T^2}\le K\) and \(\overline{y_C^2}\le K\),
\[
 \overline{(e(y_T)-e(y_C))^2}\le4K.
\]
There is NO standardization, arm-size, dimension, or sign assumption
on \(K\) in this third group.

Fourth, for every dimension sequence \(d\), arm-size sequence \(m\),
and population sequence \(P_n\), assuming exactly \(\mathcal H_0\),
both deterministic bounds hold:
\[
 {\overline{h_n(e_n(y_T)-e_n(y_C))^2}\over
                     p_nq_nn(n-1)}
        =O(\kappa_n/n),\qquad
 \overline{(e_n(y_T)-e_n(y_C))^2}=O(1).
\]

## T18

This is a conjunction of two universal assertions.
First, for every \(n,d,m,P\) with \(n>0,0<m<n\), then subset \(S\)
with \(|S|=m\), then arrays \(e_T,e_C\), assume
\(p\,b(e_T)+q\,b(e_C)=0\). Define
\[
 A=\overline{x(e_T-e_C)},\quad B=\overline{xe_C},
 \quad U={1\over n}\sum_{i\in S}x_i(e_{Ti}-e_{Ci}).
\]
The four conclusions are
\[
 B=-pA,\quad
 U+B={1\over n}\sum_{i\in S}[x_i(e_{Ti}-e_{Ci})+B/p],
 \quad U+B={1\over n}\sum_{i\in S}[x_i(e_{Ti}-e_{Ci})-A],
\]
and equality of the scalar products of the last two equal vectors with
\(\bar x_S/q\). No standardization or regression definition of the
arrays is assumed in this first assertion.

Second, for every \(n,d,m,P\) with \(n>0,0<m<n\), standardization,
and then every \(S\in\mathcal D_{n,m}\), let
\(e_T=e(y_T),e_C=e(y_C)\), and \(U,B\) as above. Then
\[
 \bar x_S-\bar x_C=\bar x_S/q,\quad
 p\,b(e_T)+q\,b(e_C)=0,\quad
 F(S;e_T,e_C)=\bar x_S^\mathsf T(U+B)/q.
\]

## T19

This theorem is a NEGATION, with no external hypotheses.
It asserts that the following universal conjunction is NOT true:
for every \(n,m\) with \(n\ge4,0<m<n\), every arm
\(t\in\{T,C\}\), and every pair of arbitrary real arrays \(a,b\),
letting \(r=m\) for the treated arm and \(r=n-m\) for the control arm,
\[
 E_m c_{S_t}(a,b)={(r-1)n\over r(n-1)}c(a,b)
\]
AND
\[
 V_m c_{S_t}(a,b)\le
 {2(n-r)\over r(n-1)}\overline{(ab-\overline{ab})^2}
 +{2(n-r)n\over r^3(n-1)}\overline{a^2}\,\overline{b^2}.
\]
Equivalently, there exists such \(n,m,t,a,b\) for which at least one
of those two assertions fails. It does not separately assert the
expectation identity or give a named witness, and it does not assume
that either input array is centered.

## T20

This is a conjunction of three propositions with independent quantifiers.

1. The entire universal assertion T24 below holds.
2. It is NOT the case that, for every \(n,d,m,P\) with \(n\ge3\),
   \(0<m<n\), standardization, and interacted regularity,
   \[
   E_m[\bar x_C^\mathsf T u_{3C}(y_C)]
    -E_m[\bar x_S^\mathsf T u_{3S}(y_T)]
        =a_{CCC}(n,m)H(y_C)-a_{TTT}(n,m)H(y_T).
   \]
3. It is NOT the case that, for every \(d,m,P\) satisfying
   \(\mathcal H\), eventual interacted regularity, and
   \(\kappa_n\log(d_n)\to0\),
   \[
   \widehat\tau_{In}-\tau_n-\ell_{In}
                    =O_p(\sqrt{\kappa_nd_n/n}).
   \]

Thus clauses 2 and 3 assert existence of finite and sequential
counterexamples, respectively, within the stated hypotheses.

## T21

For every \(n,d,m,P\), with \(n\ge3,0<m<n\), standardization, and
noninteracted regularity, all the following hold:

1. \(E_m\widehat B=E_m\widehat\tau-\tau\).
2. \(E_m\widehat\tau_D=\tau\).
3. For every \(S\in\mathcal D_{n,m}\),
   \[
   \widehat\tau_D=\bar y_{TS}-\bar y_{CC}
       -(\bar x_S-\bar x_C)^\mathsf T\widehat N
       +c_S(h,y_T)/(n-2)-c_C(h,y_C)/(n-2).
   \]
4. \(E_m\widehat\tau-\tau
           =E_m[(\bar x_C-\bar x_S)^\mathsf T(v_1+v_2+v_3)]\).
5. For every design subset, the inner product involving \(v_2\) equals
   that involving \((\widehat L^{-1}-I_d)\widehat N\); this expands its
   definition.
6. IF ADDITIONALLY \(m\ge2\) and \(n-m\ge2\), define
   \[
   B_{11}(S)={1\over n-1}
      \left[{(n-m)(n-1)\over(n-m-1)n}c_C(h,y_C)
            -{m(n-1)\over(m-1)n}c_S(h,y_T)\right],
   \]
   \[
   B_{12}(S)=a_{TTT}{m^2(n-1)\over(n-m)(m-1)n}c_S(h,y_T)
          -a_{TTC}{m(n-1)\over(n-m-1)n}c_C(h,y_C).
   \]
   Then the following four conclusions hold:
   \[
   E_m B_{11}={H(y_C)-H(y_T)\over n-1},
   \]
   \[
   E_m B_{12}=(p/q)a_{TTT}H(y_T)-(p/q)a_{TTC}H(y_C),
   \]
   \[
   E_m B_{12}={n-2m\over(n-1)(n-2)m}H(y_T)
             -{2m-n\over(n-1)(n-2)(n-m)}H(y_C),
   \]
   and, for every design subset,
   \(B_{11}(S)+B_{12}(S)=c_C(h,y_C)/(n-2)-c_S(h,y_T)/(n-2)\).

The additional arm-size assumptions in clause 6 do not govern clauses
1 through 5.

## T22

This is a conjunction of a main assertion and two weaker-hypothesis
armwise assertions.

The main assertion universally quantifies \(n,d,m,P\) with \(n\ge3\),
\(0<m<n\), standardization, and interacted regularity. It concludes
\[
 E_m\widehat B_I=E_m\widehat\tau_I-\tau,\quad
 E_m\widehat\tau_{ID}=\tau,\quad
 E_mD_S(y_T)=\bar y_T,\quad E_mD_C(y_C)=\bar y_C,
\]
and, for every design subset,
\[
 \widehat\tau_{ID}
 =\left[\bar y_{TS}-\bar x_S^\mathsf T A_S(y_T)
                   +{n-m\over(n-2)m}c_S(h,y_T)\right]
 -\left[\bar y_{CC}-\bar x_C^\mathsf T A_C(y_C)
                   +{m\over(n-2)(n-m)}c_C(h,y_C)\right].
\]
The other two assertions independently quantify all \(n,d,m,P\):

* If \(n\ge3\), \(m\ge2\), \(m<n\), and \(\bar x=0\),
  then \(E_mD_S(y_T)=\bar y_T\).
* If \(n\ge3\), \(0<m<n\), \(n-m\ge2\), and \(\bar x=0\),
  then \(E_mD_C(y_C)=\bar y_C\).

These last two assertions require neither Gram standardization nor
regularity, and impose no outcome bounds.

## T23

For every \(n,d,m,P\) with \(n\ge3,0<m<n\), standardization and
noninteracted regularity, the following seven assertions hold:

1. For every design subset, \(\widehat b=b+v_1+v_2+v_3\).
2. \(E_m\widehat\tau-\tau
      =E_m[(\bar x_C-\bar x_S)^\mathsf T(v_1+v_2+v_3)]\).
3. \(E_m[(\bar x_C-\bar x_S)^\mathsf T v_1]
      =[H(y_C)-H(y_T)]/(n-1)\).
4. \([H(y_C)-H(y_T)]/(n-1)
      =-\overline{(h-\bar h)(y_T-y_C)}/(n-1)\).
5. \(E_m[(\bar x_C-\bar x_S)^\mathsf T v_3]
      ={n-2m\over(n-1)(n-2)m}H(y_T)
       -{2m-n\over(n-1)(n-2)(n-m)}H(y_C)\).
6. If there exists real \(c\) with \(y_{Ti}-y_{Ci}=c\) for every
   individual, then the expectation in clause 3 is zero.
7. If \(m=n-m\), then the expectation in clause 5 is zero.

## T24

For every \(n,d,m,P\) with \(n\ge2,0<m<n\), standardization and
interacted regularity, the following five assertions hold:

1. For every design subset, both arm slope decompositions hold:
   \(\widehat b_S(y_T)=b(y_T)+u_{1S}(y_T)+u_{2S}(y_T)+u_{3S}(y_T)\)
   and the identical formula with \(C,y_C\).
2. \(E_m(\widehat\tau_I-\tau)\) equals
   \(E_m[\bar x_C^\mathsf T(u_{1C}+u_{2C}+u_{3C})(y_C)]
    -E_m[\bar x_S^\mathsf T(u_{1S}+u_{2S}+u_{3S})(y_T)]\).
3. \(E_m[\bar x_S^\mathsf T u_{1S}(y_T)]
             =(n-m)H(y_T)/((n-1)m)\).
4. \(E_m[\bar x_C^\mathsf T u_{1C}(y_C)]
             =mH(y_C)/((n-1)(n-m))\).
5. The difference of the expectations in clauses 4 and 3 equals the
   difference of their displayed right sides.

No third-component moment or stochastic remainder bound is a clause
of T24.

## T25

For every dimension sequence \(d:\mathbb N\to\mathbb N\), then
allocation sequence \(m:\mathbb N\to\mathbb N\), then population
sequence \(P_n\), assume \(\mathcal H(d,m,P)\), eventual
noninteracted regularity, and \(d_n/n\to0\). Then
\[
 \widehat\tau_n-\tau_n-\ell_n=O_p(\sqrt{\kappa_nd_n/n}).
\]
The stochastic bound has exactly the quantifiers given in the common
dictionary. There is no separate assumption \(\kappa_n\to0\).

## T26

For every \(d,m,P\) in that order, assume \(\mathcal H(d,m,P)\),
eventual noninteracted regularity, and \(\kappa_n\to0\). Then
\[
 \widehat\tau_{Dn}-\tau_n-\ell_n=o_p(\sqrt{1/n}).
\]
There is no conclusion giving a rate when leverage does not decay,
nor any identity of this remainder with a separately named expression.

## T27

For every \(d,m,P\) in that order, assume \(\mathcal H(d,m,P)\),
eventual interacted regularity, and \(\kappa_n\to0\). Then
\[
 \widehat\tau_{IDn}-\tau_n-\ell_{In}=o_p(\sqrt{1/n}).
\]
There is no conclusion giving a rate without leverage decay.
