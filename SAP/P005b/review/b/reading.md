# Blind reading

This file was written after reading only `SAP/P005b/Defs*.lean`,
`SAP/P005b/Defs/*.lean`, and `SAP/P005b/Challenge*.lean` and its parts, together
with the relevant Mathlib definitions. Neither `claims.json` nor `record.json`
has been opened at this stage. The readings below concern the types of the
theorems, including every conjunct; the docstrings are not additional hypotheses.

## Dictionary used throughout

All populations and outcomes are fixed real arrays. Write
`I_n = {0,...,n-1}` (Lean `Fin n`), `D(n,m) = {S subset I_n : |S|=m}`,
and `C = I_n \\ S`. Mathlib `Finset.powersetCard` has precisely this membership
condition and cardinality `choose(n,m)`. A sum over a finite set counts each
member once. For an array `a`, write

* `M_S a = sum_{i in S} a_i / |S|`, and `M a = sum_i a_i/n`;
* `E_m f = sum_{S in D(n,m)} f(S) / choose(n,m)`;
* `V_m f = E_m[(f-E_m f)^2]`;
* `Pr_m A = |{S in D(n,m): A(S)}| / choose(n,m)`;
* `C_S(a,b) = M_S(ab) - M_S a M_S b`, and `C(a,b) = M(ab)-Ma Mb`;
* `a^o_i = a_i-Ma`.

Thus these are uniform complete randomization, variance, and covariance with
divisor the sample size, not sample size minus one. Lean real division is
totalized (`a/0=0`). Empty finite sums are zero. There is no measure-theoretic
integral anywhere in these definitions. Under `0<m<n`, the design, treatment,
and control sets are nonempty. Natural subtraction in arm sizes and in the
argument `n-m` of `NCCC` is truncated; their applications with `m<n` agree
with ordinary subtraction. Subtractions in displayed real scalar coefficients
are real subtraction, including `(n-2 : ℝ)`.

A `Population n d` consists of vectors `x_i in R^d` and two arrays `yT_i,yC_i`.
The dot product is `u.v=sum_{k=0}^{d-1}u_k v_k`. Define

* `xbar_S = M_S x`, `G=M(xx')`;
* standardized: `M x=0` and `G=I_d`;
* `h_i=x_i.x_i`, `kappa=max_i h_i/n` when `n>0`;
* `tau=M yT-M yC`, `p=m/n`, `q=(n-m)/n`;
* `b(y)=M(yx)`, `b=p b(yT)+q b(yC)`;
* `L_S=M_S(xx')-xbar_S xbar_S'`;
* `v_S(y)=M_S(yx)-M_S y xbar_S`;
* `Lhat=I_d-p xbar_S xbar_S'-q xbar_C xbar_C'`;
* `vhat=p v_S(yT)+q v_C(yC)`;
* `bhat=Lhat^{-1} vhat`, `bhat_S(y)=L_S^{-1}v_S(y)`.

`kappa` is implemented as the real supremum of the range of `i -> h_i/n`.
For positive finite `n` the range is nonempty and bounded, so this is the
ordinary maximum. Matrix products, outer products, and identity matrices are
the ordinary coordinate operations (`Matrix.mulVec`, `vecMulVec`, and `1`).
Mathlib's matrix inverse is `det(A)^{-1} adj(A)` over the reals and equals
zero for singular matrices; it is an ordinary inverse when `det(A) != 0`.
For `d=0`, vectors and matrices have no entries, dot products are zero,
and the determinant of the empty identity matrix is one.

Write `RegNI(P,m)` for: **for every** `S in D(n,m)`, `det(Lhat)!=0`.
Write `RegI(P,m)` for: **for every** such `S`, both `det(L_S)!=0` and
`det(L_C)!=0`. These are assumptions about the entire randomization support,
not just the observed allocation.

The estimators and decompositions are the following fixed formulas:

* `That = M_S yT-M_C yC-(xbar_S-xbar_C).bhat`;
* `TIhat = M_S yT-M_C yC-xbar_S.bhat_S(yT)+xbar_C.bhat_C(yC)`;
* `u1_S(y)=M_S(y^o x)-M(y^o x)`;
* `u2_S(y)=(L_S^{-1}-I)v_S(y)`;
* `u3_S(y)=-xbar_S M_S(y^o)`;
* `u1=p u1_S(yT)+q u1_C(yC)`;
* `u2=(Lhat^{-1}-I)vhat`;
* `u3=p u3_S(yT)+q u3_C(yC)`;
* `Bhat=[C_C(h,yC)-C_S(h,yT)]/(n-2)+(xbar_C-xbar_S).u2`;
* `Tdb=That-Bhat`;
* `BIhat=m/[(n-2)(n-m)] C_C(h,yC)+xbar_C.u2_C(yC)
  -(n-m)/[(n-2)m] C_S(h,yT)-xbar_S.u2_S(yT)`;
* `TIdb=TIhat-BIhat`;
* `H(y)=C(h,y)`;
* `A=NTTT(n,m)=(n-m)(n-2m)/[(n-1)(n-2)m^2]`;
* `Ac=NCCC(n,m)=NTTT(n,n-m)`;
* `B=NTTC(n,m)=-(n-2m)/[(n-1)(n-2)m]`.

In sections using `A,B` for other local variables, `NTTT,NTTC` are written
out by name to avoid shadowing. Residuals and leading terms mean

* `e_y(i)=y_i-My-x_i.b(y)` (arm-specific residual);
* `r_y(i)=y_i-My-x_i.b` (common-slope residual);
* `LeadNI=M_S r_yT-M_C r_yC`;
* `LeadI=M_S e_yT-M_C e_yC`;
* `D_S(y)=M_S y-xbar_S.v_S(y)
  +(n-|S|)/[(n-2)|S|] C_S(h,y)` (`armDebiased`).

For arrays `a,b,c`, let `Z_i=1` if `i in S`, zero otherwise, and put
`RP(S)=sum_{i != j} Z_i Z_j a_i b_i c_j`,
`DT(S)=sum_{i,j,k pairwise distinct} Z_i Z_j Z_k a_i b_j c_k`.
These are ordered index sums. `observedResidual(S,eT,eC)_i` is `eT_i` in S
and `eC_i` outside S. `Star=(xbar_S-xbar_C).M(x observedResidual)`.

For a sequence `d_n,m_n,P_n` define `SA+` to be the entire conjunction:

1. For **every** `n>=3`, `1<=d_n<=n` and `0<m_n<n`.
2. There exists a single real `K>=0` such that for **every** `n>=3`,
   `M(yT_n^2)<=K`, `M(yC_n^2)<=K`, and for **every** coordinate `k<d_n`,
   `M(x_{n,k}^2)<=K`.
3. There exists a threshold after which **every** `P_n` is standardized.
4. There exist real `lo,hi` with `0<lo<hi<1` such that for **every**
   `n>=3`, `lo<m_n/n<hi`.

Write `SA0` for exactly these clauses with the lower bound `1<=d_n`
removed from clause 1. There are no conditions on `n<3` beyond typing,
except any separately quantified eventual conditions. No independent
randomness across different `n` is specified or needed.

`R_n=O_p(r_n)` here means: for every real `epsilon>0`, there exist real
`M>0` and natural `n0` such that for every `n>=n0`,
`Pr_{m_n}(|R_n(S)|>M r_n)<epsilon`.
`R_n=o_p(r_n)` means: for every real `delta>0`, the probabilities
`Pr_{m_n}(|R_n(S)|>delta r_n)` converge to zero. In particular, the scale
is not replaced by its absolute value in these two definitions. All scales
actually used are real square roots and are nonnegative. A zero scale asks
for the probability of nonzero remainder to vanish.

Mathlib deterministic `f=O(g)` along natural `n -> infinity` means there
exists a real constant `C` and a threshold such that eventually
`|f_n|<=C |g_n|` (equivalently one may take `C>0`). `Tendsto ... atTop
(nhds 0)` is the usual limit to zero. Real `sqrt` is the nonnegative square
root on nonnegative arguments, zero on negative arguments; real `log` is
the usual natural logarithm on positive arguments, with `log 1=0` and
the totalized value `log 0=0`.

## SAP.P005b.T15

There are no external hypotheses. Universally quantify natural `t,c`, then
assume `t>=2`, then `c>=2`; let `n=t+c`. Define

`cC=1/(n-1)*[c(n-1)/((c-1)n)]
     -NTTC(n,t)*[t(n-1)/((c-1)n)]`,

`cT=-1/(n-1)*[t(n-1)/((t-1)n)]
     +NTTT(n,t)*[t^2(n-1)/(c(t-1)n)]`.

The conclusion is the conjunction:

1. `cC=1/(n-2)`.
2. `cT=[n-tn]/[(n-2)(t-1)n]`.
3. The fraction in item 2 equals `-1/(n-2)`.
4. For every natural `d`, every `P:Population n d`, and every subset `S`
   with `|S|=t`, the following holds. With `U=C_S(h,yT)`, `V=C_C(h,yC)`,
   `1/(n-1)*[c(n-1)/((c-1)n)*V-t(n-1)/((t-1)n)*U]
   +NTTT(n,t)*t^2(n-1)/(c(t-1)n)*U
   -NTTC(n,t)*t(n-1)/((c-1)n)*V = V/(n-2)-U/(n-2)`.

No centering, standardization, regression regularity, or outcome assumptions
are made for this coefficient identity.

## SAP.P005b.T16

For every natural `n,m`, assuming `n>=3`, `m>0`, `m<n`, for every three
real arrays `a,b,c` on `I_n`, assuming in order `sum a=0`, `sum b=0`,
`sum c=0`, all of the following hold. Put
`Q=sum_i a_i b_i c_i`, `f2=m(m-1)/[n(n-1)]`,
`f3=m(m-1)(m-2)/[n(n-1)(n-2)]`,
`K=(1/m^3)[m/n-3f2+2f3]` (all factors in real arithmetic).

1. For every distinct `i,j`, `E_m Z_i Z_j=f2`.
2. For every pairwise distinct `i,j,k`, `E_m Z_i Z_j Z_k=f3`.
3. `E_m RP=sum_{i != j} E_m(Z_i Z_j) a_i b_i c_j`.
4. `E_m RP=-f2 Q`.
5. `E_m DT=2 f3 Q`.
6. `E_m(M_S a M_S b M_S c)` is `1/m^3` times the sum of three expectations:
   `E_m sum_i Z_i a_i b_i c_i`,
   `E_m sum_{i != j} Z_i Z_j(a_i b_i c_j+a_i b_j c_i+a_j b_i c_i)`,
   and `E_m DT`.
7. `E_m(M_S a M_S b M_S c)=K Q`.
8. The same third moment equals `NTTT(n,m) M(abc)`.
9. `E_m(M_S a M_S b M_C c)=NTTC(n,m) M(abc)`.
10. `K=NTTT(n,m)/n`.
11. `E_m RP=f2 sum_{i != j}a_i b_i c_j`.
12. The right side in item 11 equals
    `f2[(sum_{i,j}a_i b_i c_j)-Q]`.
13. `NTTT(n,m)/n=(n-m)(n-2m)/[n m^2(n-1)(n-2)]`.
14. For every `S` with `|S|=m`, `M_C c=-m/(n-m) M_S c`.
15. `NTTC(n,m)=-m/(n-m) NTTT(n,m)`.

## SAP.P005b.T17

This theorem is a conjunction of four independently quantified assertions.

1. For every natural `n,d,m`, every population `P`, assuming `n>=2`,
   `0<m<n`, and `G=I_d`, for every real array `delta`, let
   `mu=M(x delta)`, `W=sum_{i,j}[(x_i.x_j)delta_j]^2`,
   `F=[1/(q m n)]^2 m(n-m)/[n(n-1)]`. Then:
   * for every `i`, `sum_j[x_i.(x_j delta_j-mu)]^2
     <=sum_j[(x_i.x_j)delta_j]^2`;
   * `F W=[1/(q m n)]^2 n^2 m(n-m)/[n(n-1)]
     *sum_j (1/n)h_j delta_j^2`;
   * `F W=1/[p q n(n-1)] M(h delta^2)`;
   * this last expression is at most `kappa/[p q(n-1)] M(delta^2)`.
2. For every natural `n,d`, every population `P`, assuming `n>0` and
   `G=I_d`, for every real array `a`,
   `sum_{i,j}[(x_i.x_j)a_j]^2
    =sum_j a_j^2 x_j.[(sum_i x_i x_i')x_j]
    =n sum_j a_j^2 h_j` (two asserted equalities).
3. For every natural `n,d,m`, every population `P`, assuming `n>0`,
   for every real `K`, assuming `M(yT^2)<=K` and `M(yC^2)<=K`,
   `M[(r_yT-r_yC)^2]<=4K`. No standardization or allocation-size
   assumption appears in this particular conjunct. The common fitted
   slopes cancel in the residual difference.
4. For every sequences `d,m,P`, assuming `SA0`, both
   `1/[p_n q_n n(n-1)] M[h_n(r_yT-r_yC)^2]=O(kappa_n/n)`
   and `M[(r_yT-r_yC)^2]=O(1)` hold. No regularity or dimension-decay
   assumption appears here.

## SAP.P005b.T18

This theorem has two independently quantified conjuncts.

1. For every natural `n,d,m`, population `P`, assuming `n>0`, `m>0`,
   `m<n`, for every subset `S`, assuming `|S|=m`, for every arrays
   `eT,eC`, assuming `p b(eT)+q b(eC)=0`, define
   `A=b(eT-eC)`, `B=b(eC)`,
   `U=(1/n)sum_{i in S}x_i(eT_i-eC_i)`. Then
   * `B=-p A`;
   * `U+B=(1/n)sum_{i in S}[x_i(eT_i-eC_i)+(1/p)B]`;
   * `U+B=(1/n)sum_{i in S}[x_i(eT_i-eC_i)-A]`;
   * `(1/q)xbar_S.(U+B)` equals `(1/q)xbar_S` dotted with the vector
     on the right in the previous item.
2. For every natural `n,d,m`, population `P`, assuming `n>0`, `m>0`,
   `m<n`, and standardization, for every `S in D(n,m)`, take
   `eT=r_yT`, `eC=r_yC`, `U,B` as above. Then
   `xbar_S-xbar_C=(1/q)xbar_S`,
   `p b(eT)+q b(eC)=0`, and
   `Star=(1/q)xbar_S.(U+B)`.

## SAP.P005b.T19

There are no hypotheses. The theorem asserts the **negation** of this
universal conjunction: for every natural `n,m`, if `n>=4`, `0<m<n`,
then for every choice of arm `t` (treated or control), and every real arrays
`a,b`, putting `s=m` for treatment and `s=n-m` for control,

`E_m C_arm(a,b)=(s-1)n/[s(n-1)] C(a,b)`

and

`V_m C_arm(a,b) <= 2(n-s)/[s(n-1)] M[(ab-M(ab))^2]
 +2(n-s)n/[s^3(n-1)] M(a^2)M(b^2)`.

Equivalently, some `n>=4`, `0<m<n`, arm, and arrays violate at least one
of these two assertions. The arrays are not required to be centered. The
theorem does not assert either universal positive assertion by itself.

## SAP.P005b.T24 (also the first conjunct of T20)

For every natural `n,d,m` and population `P`, assume in order `n>=2`,
`m>0`, `m<n`, standardization, and `RegI(P,m)`. The conclusion is:

1. For every `S in D(n,m)`, both
   `bhat_S(yT)=b(yT)+u1_S(yT)+u2_S(yT)+u3_S(yT)` and
   `bhat_C(yC)=b(yC)+u1_C(yC)+u2_C(yC)+u3_C(yC)`.
2. `E_m(TIhat-tau)
   =E_m[xbar_C.(u1_C(yC)+u2_C(yC)+u3_C(yC))]
    -E_m[xbar_S.(u1_S(yT)+u2_S(yT)+u3_S(yT))]`.
3. `E_m[xbar_S.u1_S(yT)]=(n-m)/[(n-1)m] H(yT)`.
4. `E_m[xbar_C.u1_C(yC)]=m/[(n-1)(n-m)] H(yC)`.
5. The control expectation in item 4 minus the treatment expectation in
   item 3 equals `m/[(n-1)(n-m)]H(yC)-(n-m)/[(n-1)m]H(yT)`.

## SAP.P005b.T20

This is the conjunction of the complete T24 assertion just read, and the
following two **separate negations**:

1. It is not true that for every natural `n,d,m`, every population `P`,
   `n>=3`, `0<m<n`, standardization, and `RegI(P,m)` imply
   `E_m[xbar_C.u3_C(yC)]-E_m[xbar_S.u3_S(yT)]
    =NCCC(n,m)H(yC)-NTTT(n,m)H(yT)`.
2. It is not true that for every sequences `d,m,P`, `SA+`, eventual
   `RegI(P_n,m_n)`, and `kappa_n log(d_n)->0` imply
   `TIhat_n-tau_n-LeadI_n=O_p(sqrt(kappa_n d_n/n))`.

Thus it asserts failure of a universal third-component identity and failure
of a universal sequence expansion under this literal logarithm condition;
the two counterexamples need not be the same population or sequence.

## SAP.P005b.T21

For every natural `n,d,m`, every population `P`, assume in order `n>=3`,
`m>0`, `m<n`, standardization, and `RegNI(P,m)`. All these hold:

1. `E_m Bhat=E_m That-tau`.
2. `E_m Tdb=tau`.
3. For every `S in D(n,m)`,
   `Tdb=M_S yT-M_C yC-(xbar_S-xbar_C).vhat
          +C_S(h,yT)/(n-2)-C_C(h,yC)/(n-2)`.
4. `E_m That-tau=E_m[(xbar_C-xbar_S).(u1+u2+u3)]`.
5. For every `S in D(n,m)`,
   `(xbar_C-xbar_S).u2=(xbar_C-xbar_S).[(Lhat^{-1}-I)vhat]`.
6. **If additionally** `m>=2` and `n-m>=2`, define
   `B11=1/(n-1)*[(n-m)(n-1)/((n-m-1)n) C_C(h,yC)
                 -m(n-1)/((m-1)n) C_S(h,yT)]` and
   `B12=NTTT(n,m)m^2(n-1)/[(n-m)(m-1)n] C_S(h,yT)
          -NTTC(n,m)m(n-1)/[(n-m-1)n] C_C(h,yC)`.
   Then all four assertions hold:
   * `E_m B11=[H(yC)-H(yT)]/(n-1)`;
   * `E_m B12=(p/q)NTTT(n,m)H(yT)-(p/q)NTTC(n,m)H(yC)`;
   * `E_m B12=(n-2m)/[(n-1)(n-2)m]H(yT)
                  -(2m-n)/[(n-1)(n-2)(n-m)]H(yC)`;
   * for every `S in D(n,m)`,
     `B11+B12=C_C(h,yC)/(n-2)-C_S(h,yT)/(n-2)`.

The extra two size hypotheses apply only to item 6, including its alternative
third-bias expression. They do not apply to items 1--5.

## SAP.P005b.T22

This is a conjunction of three independently quantified assertions.

1. For every natural `n,d,m` and population `P`, assume `n>=3`,
   `m>0`, `m<n`, standardization, and `RegI(P,m)`. Then
   * `E_m BIhat=E_m TIhat-tau`;
   * `E_m TIdb=tau`;
   * `E_m D_S(yT)=M yT`;
   * `E_m D_C(yC)=M yC`;
   * for every `S in D(n,m)`,
     `TIdb=[M_S yT-xbar_S.v_S(yT)+(n-m)/((n-2)m) C_S(h,yT)]
            -[M_C yC-xbar_C.v_C(yC)+m/((n-2)(n-m)) C_C(h,yC)]`.
2. For every natural `n,d,m` and population `P`, assuming `n>=3`,
   `m>=2`, `m<n`, and **only** `M x=0`,
   `E_m D_S(yT)=M yT`.
3. For every natural `n,d,m` and population `P`, assuming `n>=3`,
   `m>0`, `m<n`, `n-m>=2`, and **only** `M x=0`,
   `E_m D_C(yC)=M yC`.

Items 2--3 have neither unit-Gram nor invertibility assumptions.

## SAP.P005b.T23

For every natural `n,d,m` and population `P`, assume `n>=3`, `m>0`,
`m<n`, standardization, and `RegNI(P,m)`. The conclusion is:

1. For every `S in D(n,m)`, `bhat=b+u1+u2+u3`.
2. `E_m That-tau=E_m[(xbar_C-xbar_S).(u1+u2+u3)]`.
3. `E_m[(xbar_C-xbar_S).u1]=[H(yC)-H(yT)]/(n-1)`.
4. This last deterministic expression equals
   `-1/(n-1) M[(h-Mh)(yT-yC)]`.
5. `E_m[(xbar_C-xbar_S).u3]
   =(n-2m)/[(n-1)(n-2)m]H(yT)
     -(2m-n)/[(n-1)(n-2)(n-m)]H(yC)`.
6. If there exists a real `c` such that **every** unit has
   `yT_i-yC_i=c`, then the expectation in item 3 is zero.
7. If `m=n-m`, the expectation in item 5 is zero.

There is no stochastic-order assertion in T23 itself.

## SAP.P005b.T25

For every dimension sequence `d:N->N`, allocation sequence `m:N->N`,
and population sequence `P_n:Population n d_n`, assume in order `SA+`,
eventual `RegNI(P_n,m_n)`, and `d_n/n -> 0`. Then

`That_n-tau_n-LeadNI_n=O_p(sqrt(kappa_n d_n/n))`.

The constants and thresholds in this order may depend on the whole input
sequence and on epsilon, but not on n or the realized allocation.

## SAP.P005b.T26

For every sequences `d,m,P`, assume `SA+`, eventual `RegNI(P_n,m_n)`,
and `kappa_n->0`. Then

`Tdb_n-tau_n-LeadNI_n=o_p(sqrt(1/n))`.

There is no assertion here of an order bound without leverage decay or an
exact identity of this remainder with a particular finite-sample term.

## SAP.P005b.T27

For every sequences `d,m,P`, assume `SA+`, eventual `RegI(P_n,m_n)`,
and `kappa_n->0`. Then

`TIdb_n-tau_n-LeadI_n=o_p(sqrt(1/n))`.

The leading residuals use the separate population slopes `b(yT),b(yC)`.
There is no stochastic order bound here without leverage decay.

## Mathlib checks supporting the dictionary

The source definitions inspected were `Data/Finset/Powerset.lean`
(`powersetCard`, `mem_powersetCard`, `card_powersetCard`),
`Data/Matrix/Mul.lean` (dot product, outer product, matrix-vector product),
`LinearAlgebra/Matrix/NonsingularInverse.lean` (inverse and singular case),
and `Analysis/Asymptotics/Defs.lean` (`IsBigOWith`, `IsBigO`,
`isBigO_iff`). The real logarithm's values at zero and one are explicit in
`Analysis/SpecialFunctions/Log/Basic.lean`. The real supremum here is
always of a finite nonempty range whenever used in the positive-size
conclusions; it is not an unbounded supremum or a limsup.
