# Blind reading of P016a

Saved before opening either `claims.json` or `record.json`. This reading uses the
five Challenge docstrings, all their closure entries, and their source definitions.
The 74 distinct auxiliary `_proof_` declarations were also printed with Lean;
they supply natural-number numeral/finite-index instances, nonemptiness of the
displayed finite types, or the positivity and normalization proofs for a uniform
probability law. They introduce no additional mathematical assumptions. The
generated option matchers implement exactly the `some`/missing cases below.

## Mathematical notation used after unfolding

All unit indices are `Fin n`, meaning integers `0,...,n-1`. An outcome vector is
a function from those indices to the real numbers. An assignment is a function
to `Bool`; identify `true` with 1 (treated), `false` with 0 (control). Write
`z_i` for this real indicator when it occurs in arithmetic.

For an assignment and group `g`, let `I_g={i:z_i=g}` and `n_g=|I_g|`. Then

- `groupSum` is the finite sum over `I_g`;
- `groupMean` is `mu_g=(sum_{i in I_g} u_i)/n_g`;
- `pooledMean` is `mu=(sum_i u_i)/n`;
- `meanDifference` is `Delta=mu_1-mu_0`;
- `rss` is `R(u,z)=sum_i (u_i-mu_{z_i})^2`;
- `tss` is `Q(u)=sum_i (u_i-mu)^2`;
- `ecdf` is `F_g(t)=|{i in I_g:u_i<=t}|/n_g`;
- `ks` is `D(u,z)=max({0} union {|F_1(u_i)-F_0(u_i)|:i<n})`;
- `signedKS` is `K(u,z)=max({0} union {F_1(u_i)-F_0(u_i):i<n})`.

These maxima are list folds with `max` and initial value 0, not unexplained
suprema. `groupValues` is the multiset of outcomes in a group, including
multiplicities; `sameMargins` means equality of these multisets for both labels.

A `FiniteLaw` on a finite type `Omega` consists of real weights `p_w>=0` with
`sum_w p_w=1`. Its constructor requires these two proofs; its `weight` projection
returns these weights. For this law, `mass(E)=sum_w p_w 1_E(w)`,
`expectation(f)=sum_w p_w f(w)`,
`covariance(f,g)=sum_w p_w f(w)g(w)-(sum_w p_w f(w))(sum_w p_w g(w))`, and
`variance(f)=covariance(f,f)`. A uniform law on a finite nonempty type has every
weight `1/|Omega|`. Separately, `uniformMass(Omega,E)=|E|/|Omega|`, without a
nonempty type requirement in that definition.

For any real matrix with `n` rows and `k` columns, set
`L(u,X,b)=sum_i (u_i-sum_j X_ij b_j)^2` and
`M(u,X)=inf {L(u,X,b):b in R^k}` using the real `sInf`. The simple design matrix
has row `(1,z_i)`; the application matrix has row `(1,z_i,e_i)`. The column sum
`degree(S)_i` is `sum_j S_ji`.

For any real matrix `S`, `x(S,z)_i=sum_j S_ij z_j`. A bank is a function from a
finite index type to assignments; repeated assignments count with multiplicity.
For each unit and Boolean `a`,
`c(S,bank,i,a)=sum_{b:bank(b)_i=a} x(S,bank(b))_i / |{b:bank(b)_i=a}|`.
Its centered exposure is
`h(S,bank,z)_i=x(S,z)_i-z_i c(S,bank,i,1)-(1-z_i)c(S,bank,i,0)`.
For a real vector `v`, set
`V(v)=sum_i (v_i-mean(v))^2/(n-1)`, `sd(v)=sqrt(V(v))`, and
`std(v)_i=(v_i-mean(v))/sd(v)`. The coded exposure is `std(h(S,bank,z))`.

For optional real scores, similarity is 0 on the diagonal, is
`1-|s_i-s_j|/2` off the diagonal when both scores are present, and is 0 if either
score is missing. No range condition on scores is built into this definition.
The distance matrix is `d(s)_ij=|s_i-s_j|`, including its zero diagonal.
`applicationAdjust(Y,z,e,b1,b2)_i=Y_i-z_i b1-b2 e_i`.
`additiveGenerate(y,z,t)_i=y_i+z_i t` and
`additiveAdjust(Y,z,t)_i=Y_i-z_i t`.

For a reference list `r_0,...,r_{B-1}`, the counts are
`l(r,o)=|{b:r_b<=o}|` and `u(r,o)=|{b:o<=r_b}|`, both inclusive.
The raw p-value is `p(r,o)=min(1,2 min(l(r,o)/B,u(r,o)/B))`.
`codedReject(p)` means `p<=1/20`; `printedReject(p)` means `p<1/20`.

The fixed four-outcome vector is `a=(0,1,2,3)`. In the following order the complete
bank `C`, indexed by `Fin 6`, is
`(1100,1010,1001,0110,0101,0011)`. The blocked bank `B`, indexed by `Fin 4`, is
`(1100,1001,0110,0011)`. The matched bank `H4` is
`(0101,0110,1001,1010)`. The matched bank `H6`, indexed by all eight Boolean
triples `(b0,b1,b2)`, gives assignment
`(b0,1-b0,b1,1-b1,b2,1-b2)`.

## SAP.P016a.T1

Challenge location: `SAP/P016a/Challenge/Part1.lean:8-10`; statement definition:
`SAP/P016a/Defs/Part3.lean:11-31`. There are no external hypotheses. The theorem
is the conjunction of these finite assertions, with each quantifier local to
its indicated clause:

1. `C` is injective, and for every Boolean assignment `z` on four units,
   `|I_1(z)|=2` if and only if there exists `k in Fin 6` with `C_k=z`.
2. `B` is injective, and for every assignment `z` on four units,
   `(z_0!=z_2 and z_1!=z_3)` if and only if there exists `k in Fin 4` with `B_k=z`.
3. Define the paired population covariance of two length-two vectors `t,c` as
   `[(t0-(t0+t1)/2)(c0-(c0+c1)/2)+(t1-(t0+t1)/2)(c1-(c0+c1)/2)]/2`.
   It is 1 for `t=(0,2),c=(1,3)` and -1 for `t=(0,2),c=(3,1)`.
   For `z=C_0=1100`, the two four-vectors `(0,2,1,3)` and `(0,2,3,1)` both
   have `R=4` and `D=1/2`.
4. For every `k in Fin 6`, the values of `R(a,C_k)` are
   `(1,4,5,5,4,1)_k`, and the values of `D(a,C_k)` are
   `(1,1/2,1/2,1/2,1/2,1)_k`. For every `k in Fin 4`, the values of
   `R(a,B_k)` are `(1,5,5,1)_k`, and `D(a,B_k)` are `(1,1/2,1/2,1)_k`.
5. Under the uniform distribution on the six complete assignments,
   `Pr[R(a,C_k)<=R(a,C_0)]=1/3`,
   `Pr[D(a,C_0)<=D(a,C_k)]=1/3`, and the covariance of the treated and control
   group means of `a` is `-5/12`. Under the uniform distribution on the four
   blocked assignments the corresponding two inclusive probabilities are
   `1/2` and `1/2`, and the group-mean covariance is `-1/2`.

The order of universal and existential quantifiers in clauses 1 and 2 is
`for every assignment, ... iff there exists a bank index`. There is no claim
that a covariance of paired unit outcomes equals either design covariance.

Junk conventions: real division at zero gives 0, so general group means and
empirical cdfs of empty groups are defined as 0. Here every displayed
assignment has two units in each group. All probability denominators are 6 or
4, and the paired covariance denominators are 2. Finite indexing is bounded,
with no out-of-range/default vector entries. The `max` initial value 0 is
mathematically harmless for nonnegative absolute cdf differences. No square
root, log, real power, truncated subtraction, integral, extended-real
conversion, infimum, supremum, or asymptotic limit occurs in this closure.
All casts of natural counts are exact casts to real numbers.

## SAP.P016a.T2

Challenge location: `SAP/P016a/Challenge/Part1.lean:12-14`; statement definition:
`SAP/P016a/Defs/Part3.lean:33-90`. Each numbered assertion below is a separate
conjunct, so data quantified for one do not constrain another.

1. For every natural `n`, proof `n>=2`, real vector `u` of length `n`, Boolean
   assignment `z`, and proofs `n_0(z)>0,n_1(z)>0`,
   `M(u,rows(1,z))=R(u,z)`;
   for every pair of real coefficients `(a,b)`,
   `L(u,rows(1,z),(a,b))=R(u,z)` if and only if
   `a=mu_0` and `b=mu_1-mu_0`;
   and `R(u,z)=sum_i u_i^2-n_0 mu_0^2-n_1 mu_1^2`.
2. For every `n>=2,u,z` with both groups positive,
   `R(u,z)=Q(u)-(n_0 n_1/n)Delta(u,z)^2`.
3. For every `n>=2,u,z,w` with both groups of `z` positive and
   `n_1(w)=n_1(z)`,
   `R(u,w)<=R(u,z)` if and only if `|Delta(u,z)|<=|Delta(u,w)|`.
4. For every `n`, finite type `Omega`, normalized nonnegative weights `P`,
   proof `n>=2`, vector `u`, observed assignment `zobs`, assignment map
   `assign:Omega -> {0,1}^n`, positive group sizes for `zobs`, and proof that
   `n_1(assign(w))=n_1(zobs)` for every `w`,
   `sum_w p_w 1_{R(u,assign(w))<=R(u,zobs)}` equals
   `sum_w p_w 1_{|Delta(u,zobs)|<=|Delta(u,assign(w))|}`.
5. For every `n>=2,u,z` with positive groups,
   `R(u,z)=n_0(mean_0(u^2)-mu_0^2)+n_1(mean_1(u^2)-mu_1^2)`.
6. For every `n>=2`, vectors `u,v`, assignments `z,w`, proofs that both groups
   of `z` are positive, and equality of the treated and control multisets of
   `(u,z)` and `(v,w)`, both `R(u,z)=R(v,w)` and `D(u,z)=D(v,w)`.
7. For every `n`, finite type `Omega`, law `P`, proof `n>=2`, vector `u`,
   assignment map, positive natural numbers `n0,n1`, and proof that every
   assignment has exactly `n0` controls and `n1` treated units:
   for every `w`, `n1 mu_1(w)+n0 mu_0(w)=n mean(u)`;
   `Cov_P(mu_1,mu_0)=-(n1/n0) Var_P(mu_1)`;
   and for every real threshold `x`, for every `w`,
   `n1 F_1(w,x)+n0 F_0(w,x)=sum_i 1_{u_i<=x}`, and
   `Cov_P(F_1(.,x),F_0(.,x))=-(n1/n0) Var_P(F_1(.,x))`.
   Thus `x` is chosen after the assignment data, but before the pointwise
   assertion over `w`; the covariance is over the same fixed threshold.
8. Fix `z=C_1=1010` and
   `S=[[0,0,1,0],[0,0,0,1],[1,0,0,1],[0,1,1,0]]`.
   Let `v=(2,1,0,3)`, `d_i=sum_j S_ji`, and `X_i=(1,z_i,d_i)`.
   The group multisets of `(a,z)` and `(v,z)` agree; both have `R=4,D=1/2`;
   `d=(1,1,2,2)`;
   `L(a,X,(-1,-1,2))=M(a,X)=0`; and
   `L(v,X,(2,-1,0))=M(v,X)=4`.
9. `D(a,C_1)=D(a,C_2)=1/2`, but `R(a,C_1)=4` and `R(a,C_2)=5`.
10. For every natural `n`, vector `u`, and assignment `z`, if both groups are
    positive, `R(u,z)=sum_{i in I_0}(u_i-mu_0)^2+sum_{i in I_1}(u_i-mu_1)^2`.
11. For every natural `n`, vector `u`, and assignment `z`, if both groups are
    positive, there exists a real coefficient vector of length two attaining
    `M(u,rows(1,z))`.

Junk conventions: group-size, total-size, and ratio denominators are nonzero
under the stated positive-group/fixed-size conditions. In clauses 3, 4, and 6,
the other assignments' positive group sizes follow from their equal counts
or equal multisets and the common total `n`. The last two clauses do not state
`n>=2`, but positive sizes of both disjoint groups imply it. Although `Omega`
is not explicitly nonempty, its probability law's sum-one condition rules out
an empty finite type. Zero individual weights and constant statistics are
allowed and do not change the covariance identities into strict inequalities.
The real infimum of an empty or unbounded-below set defaults to 0; here the
objective range is nonempty (use zero coefficients, even if `k=0`) and is
bounded below by 0 (a finite sum of squares). Thus no infimum junk value is
used. All subtractions in these formulas are real, not truncated natural
subtractions. The maxima and finite natural casts have the meanings above.
There are no integrals, extended-real values, logs, roots, powers with real
exponents, limit operations, or partial functions.

## SAP.P016a.T3

Challenge location: `SAP/P016a/Challenge/Part1.lean:16-18`; statement definition:
`SAP/P016a/Defs/Part4.lean:11-66`. There are no external hypotheses. This is a
conjunction of the following fixed witnesses. The finite unit quantifiers in
each clause range over precisely the displayed length.

1. On four units take scores `s=(-1,-1/2,1/2,1)`, all present. Their similarity
   matrix is
   `S=[[0,3/4,1/4,0],[3/4,0,1/2,1/4],[1/4,1/2,0,3/4],[0,1/4,3/4,0]]`.
   For every unit, the bank-conditional exposure means under `H4` are
   `c(.,0)=(7/8,9/8,9/8,7/8)` and `c(.,1)=(1/8,3/8,3/8,1/8)`.
   With `z=C_1=1010`,
   `x(S,z)=(1/4,5/4,1/4,3/4)`,
   `x(d(s),z)=(3/2,3/2,3/2,5/2)`, and
   `h(S,H4,z)=(1/8,1/8,-1/8,-1/8)`.
   There do not exist real `A,B,C` such that for every unit
   `h_i=A+B z_i+C x(S,z)_i`. Separately, there do not exist such coefficients
   expressing `h_i=A+B z_i+C x(d(s),z)_i`.
2. On six units take scores `s=(-1,-3/4,-1/2,0,1/4,1)`, all present,
   `z=101010`, bank `H6`, and outcomes `y=(0,1,0,1,1,0)`.
   The similarity matrix is `1/8` times
   `[[0,7,6,4,3,0],[7,0,7,5,4,1],[6,7,0,6,5,2],`
   `[4,5,6,0,7,4],[3,4,5,7,0,5],[0,1,2,4,5,0]]`.
   For every unit, the raw exposure `x`, conditional mean at the observed
   label `c_i=c(S,H6,i,z_i)`, centered exposure `h`, and degree `d` satisfy
   `x=(9/8,9/4,11/8,17/8,1,7/8)`,
   `c=(13/16,31/16,5/4,2,19/16,17/16)`,
   `h=(5/16,5/16,1/8,1/8,-3/16,-3/16)`, and
   `d=(5/2,3,13/4,13/4,3,3/2)`.
   `mean(h)=1/12`, `V(h)=49/960`, and, for every unit,
   `std(h)=(sqrt(15)/42)*(11,11,2,2,-13,-13)`.
   Neither real coefficients `A,C` with `h_i=A+C x_i` for every unit nor
   real coefficients `A,B,C` with `h_i=A+B z_i+C x_i` for every unit exist.
   `M(y,rows(1,z,h))=M(y,rows(1,z,std(h)))=4/3`,
   `M(y,rows(1,z,x))=655/708`, and
   `M(y,rows(1,z,x,d))=515/859`.
3. The determinant of rows
   `(1,1,1/4,1/8),(1,0,5/4,1/8),(1,1,1/4,-1/8),(1,0,3/4,-1/8)` is `1/8`.
   Set
   `r=(216630956840236,191947426509578,208676713418681,225467332911212)/10^13`
   and
   `q=(370753999962044,240866262449021,286925998351727,-193126413625389)/10^15`.
   The determinant with row `i` equal to `(1,(0,0,1,1)_i,r_i,q_i)` is
   `-14030283848669586515272953541/10^28`.
4. For those exact rational vectors `r,q`, there do not exist real `A,B,C`
   such that `q_i=A+B(0,0,1,1)_i+C r_i` for every `i in Fin 4`.
5. For the 1,000-element reference vector `r_b=b+1`, `b=0,...,999`:
   at observed value 25, `l=25,u=976,p=1/20`, so `p<=1/20` and not `p<1/20`;
   at observed value 40, `l=40,p=2/25`, with `l/1000<=1/20` but not
   `p<=1/20`; at observed value 980, `l=980,p=21/500`, with not
   `l/1000<=1/20` but `p<=1/20`.

In every negative-existence assertion, coefficients are quantified before the
universal unit equality: it rules out one coefficient tuple fitting all units,
not independently chosen coefficients for each unit. The recorded rational
table is supplied literally; no assertion here derives it from a larger data
set or bounds floating-point approximation error.

Junk conventions: conditional means for unrepresented unit-label cells would
be 0 by division-by-zero, but every unit takes both labels in `H4` (twice each)
and `H6` (four times each). All scores are present and lie in `[-1,1]`, so
neither missing-score defaults nor negative out-of-range similarities are used.
`sampleVariance` divides by the real number `n-1`, namely 5 in the six-unit
calculation, not by natural truncated subtraction. Its square root is the
nonnegative real square root, with value 0 for nonpositive arguments in general.
The six-unit variance is strictly positive and the displayed root has argument
15, so standardization has a nonzero denominator. The four-unit part does not
standardize. All regression objective ranges are nonempty and bounded below
by 0. The reference denominator is 1000 and all other denominators are
positive integers. Finite counts cast exactly to reals; no asymptotic operations,
integrals, extended-real conversions, log, real-exponent power, empty type, or
partial-function choice occurs.

## SAP.P016a.T4

Challenge location: `SAP/P016a/Challenge/Part1.lean:20-23`; statement definition:
`SAP/P016a/Defs/Part4.lean:68-100`. Its conjunction consists of:

1. For all natural numbers `n,N`, proof `n>=2`, real `n` by `n` matrix `S`,
   proofs `S_ij=S_ji` and `S_ii=0`, bank `bank:Fin N -> {0,1}^n`, and proof
   that for every unit `i` and Boolean `a` there exists an index `b` with
   `bank(b)_i=a`; for every finite set `Omega` of assignments with proof
   `sd(h(S,bank,z))>0` for every `z in Omega`; for every baseline vector `y0`,
   map `y:{0,1}^n -> R^n`, and real coefficients `b1,b2`, if
   for every `z in Omega` and every unit
   `y(z)_i=y0_i+z_i b1+b2 std(h(S,bank,z))_i`, then for every `z in Omega`
   the vector whose entries are `y(z)_i-z_i b1-b2 std(h(S,bank,z))_i`
   equals `y0`.
   No probability weights or requirement that `Omega` be nonempty appear.
2. For every `n>=2`, vectors `h,u`, assignment `z`, and proof `sd(h)>0`,
   `sum_i std(h)_i=0`, `sum_i std(h)_i^2/(n-1)=1`, and
   `M(u,rows(1,z,std(h)))=M(u,rows(1,z,h))`.
3. For every `n,N`, proof `n>=2`, arbitrary real score vector `s`, bank that
   represents both labels at every unit, current assignment `z`, natural `m`,
   proof `|I_1(z)|=m`, and proof `|I_1(bank(b))|=m` for every bank index:
   put `S_ii=0`, `S_ij=1-|s_i-s_j|/2` for `i!=j` and `D_ij=|s_i-s_j|`.
   For every unit,
   `x(S,z)_i=m-z_i-(1/2)x(D,z)_i` and
   `h(S,bank,z)_i=-(1/2)h(D,bank,z)_i`.
   If `sd(h(D,bank,z))>0` and also `sd(h(S,bank,z))>0`, then
   `std(h(S,bank,z))_i=-std(h(D,bank,z))_i` for every unit.
   In quantifier order both positive-SD conditions come after the two
   unstandardized identities and constrain only the standardized conclusion.
4. For the four-unit scores, matched bank, and `z=C_1` described in T3,
   `h=(1/8,1/8,-1/8,-1/8)` has positive sample SD; no single real tuple
   `(A,B,C)` represents `h_i=A+B z_i+C x(S,z)_i` at every unit; and no such
   tuple represents `std(h)_i=A+B z_i+C x(S,z)_i` at every unit.
5. For every positive natural `B`, reference vector `r:Fin B -> R`, and
   observed real `o`, `l(r,o)/B+u(r,o)/B>=1`.
6. For all real `p,alpha`, `(p<=alpha and not p<alpha) iff p=alpha`.
7. Every clause of T3 as expanded in the preceding section, with all of its
   exact finite vectors, matrices, rational determinant, regression infima,
   negative-existence quantifiers, and 1,000-reference cutoff examples.

This is cancellation under an assumed exact generation model; it does not
assert estimation, identification, testing calibration, confidence bounds,
sampled-bank accuracy, or a numerical experiment. The docstring expressly
omits the complete application and simulation procedures and lists several
such omissions. It expressly mentions common treated counts for the raw
orientation formula and two positive SDs for the standardized sign formula.

Junk conventions: `hbank` guarantees every conditional-mean denominator is
positive. Because `n>=2`, it also excludes `N=0`. `Omega` may be empty, in which
case only that instance of clause 1 is vacuous; the other conjuncts and
nonempty instances remain substantive. Every standardization used in a general
conclusion is protected by positive SD, and the finite witness has positive SD.
`n-1` is real subtraction with positive value. Unrestricted scores in clause 3
can give negative values of `1-|s_i-s_j|/2`; the formula is used algebraically,
with no stated assertion that it is a nonnegative similarity for all real
scores. There is no missing score in any application of the similarity
definition. `B>0` protects reference proportions. The real `sInf` objectives
are always nonempty and bounded below by 0. All T3 convention checks also
apply to its included conjunct. No integrals, extended-real conversions,
logs, real-exponent powers, limiting values, or partial-function defaults
occur. Natural casts are exact. The broad helpers have zero-division defaults,
but the theorem's substantive standardization and conditional-mean assertions
do not rely on them.

## SAP.P016a.T7

Challenge location: `SAP/P016a/Challenge/Part1.lean:30-32`; statement definition:
`SAP/P016a/Defs/Part5.lean:22-66`. There are no external hypotheses. The
conjunction asserts:

1. `C` is injective and, for every four-unit assignment `z`, treated size 2
   is equivalent to existence of `k in Fin 6` with `C_k=z`.
2. For every `k in Fin 6`,
   `Delta(a,C_k)=(-2,-1,0,0,1,2)_k` and
   `Delta(a+10 C_k,C_k)=(8,9,10,10,11,12)_k`.
   Over uniform `j in Fin 6`, each of
   `Pr[|Delta(a,C_j)|>=|Delta(a+10 C_k,C_k)|]` and
   `Pr[Delta(a,C_j)>=Delta(a+10 C_k,C_k)]` is 0.
   The corrected absolute-reference probability
   `Pr[|Delta(a,C_j)|>=|Delta(a,C_k)|]` is
   `(1/3,2/3,1,1,2/3,1/3)_k`.
3. For every real `alpha>0`, the uniform mass over `k` for which the first
   (absolute) mismatched probability in clause 2 is strictly less than `alpha`
   is 1. Separately, for every real `alpha>0`, the same assertion holds for
   the one-sided mismatched probability. There is no upper bound on `alpha`.
4. For every `k`, subtracting `10 C_k` from `a+10 C_k` gives exactly `a`.
5. Let `y_i=i` for `i in Fin 8`. Let `Z` be the subtype of all Boolean
   eight-unit assignments having exactly four treated units (this unfolds
   `Balanced 8 4`). Define `s(z)=K(y,z)` and `d(z)=D(y,z)`.
   Then `|Z|=70`. For every `z in Z`, subtracting `-100 z` from `y-100 z`
   recovers `y`, and `K(y-100 z,z)=D(y-100 z,z)=1`.
   In the uniform measure `U(E)=|E|/70` on `Z`,
   `U{s>=1}=1/70` and `U{d>=1}=1/35`;
   `U{z:U{w:s(z)<=s(w)}<1/20}=1/70` and
   `U{z:U{w:d(z)<=d(w)}<1/20}=1/35`;
   `U{z:U{w:K(y-100 z,z)<=s(w)}<1/20}=1` and
   `U{z:U{w:D(y-100 z,z)<=d(w)}<1/20}=1`.
   Each inner reference assignment `w` is quantified after the observed `z`;
   the raw observed outcome vector depends on `z`, whereas the reference
   vector is the same recovered baseline `y`.
6. For every `z in Z`, units `i,j`, proof `z_i=1`, and proof `z_j=0`,
   `(y-100 z)_i<(y-100 z)_j`. Thus the treated raw outcomes all lie strictly
   below all the control raw outcomes in every assignment.
7. The real inequalities `1/70<1/20` and `1/35<1/20` hold.

The assertion is about literal comparison of the raw observed statistic with
the reference law of an adjusted baseline, and supplies exact witnesses. It
does not quantify over all outcome vectors, all additive effects, or all
statistics. Its additive hypotheses are true by the displayed generation and
recovery identities, rather than by an assumed equality of unmatched laws.

Junk conventions: every four-unit assignment here has group sizes 2 and 2,
and every eight-unit subtype member has group sizes 4 and 4. The uniform finite
law on six indices has nonzero cardinality. Although `uniformMass` generally
returns 0 on an empty index type through `0/0=0`, `Z` has 70 members and admits
the explicit assignment `11110000`, so that convention is not used. The signed
KS fold includes 0, agreeing with the zero cdf difference outside the data;
the two-sided fold is an absolute maximum. Values of `i.val` cast to real
numbers are exactly 0 through 7. Subtraction is real throughout, so `-100`
and the adjusted outcomes have their usual meanings. No infimum, supremum,
root, log, real-exponent power, integral, extended-real conversion, limit,
or partial-function default occurs.
