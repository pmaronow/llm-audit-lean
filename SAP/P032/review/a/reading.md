# Blind reading of the P032 Challenge

This file was written and saved before opening `claims.json` or `record.json`.
It reads the theorem types, not their docstrings as additional hypotheses. All
indices below start at zero. Every theorem is universally quantified over its
displayed type parameters and typeclass instances. No displayed finite type is
required to be nonempty unless a later condition forces that.

## Shared definitions, expanded

All matrices and vectors have real entries. R, M, P are finite types with
decidable equality. A dyad d(r) is a finite subset of M of cardinality exactly
two, so its two members are distinct and unordered. Put k = |M| and define

* D(r,s) = 1 if d(r) and d(s) intersect, and 0 otherwise.
* E(r,s) = 1 if their member sets are equal, and 0 otherwise. Repeated rows of
  the same dyad are permitted.
* I(r,s) = 1 if r=s, and 0 otherwise.
* C_i(r,s) = 1_{i in d(r) and i in d(s)} +
  1_{r=s and i not in d(r)}. Thus the rows incident to member i form one
  cluster, while every nonincident row forms its own singleton cluster.
* S_g(r,s) = 1_{g(r)=g(s)}, and T_g(r,s) = 1_{r != s and g(r)=g(s)}.
  The codomain G of g only needs decidable equality; it need not be finite.

For scores z_r in R^P, K(H,z)_{ij} = sum_{r,s} H(r,s) z_{ri} z_{sj}.
For a square matrix A and vector h, q(A,h) = sum_{r,s} h_r h_s A_{rs}.
The restriction A_D has entries D(r,s) A_{rs}. The omitted sum is
O(d,A,h) = sum over all ordered nonincident pairs (r,s) of h_r h_s A_{rs}.
Diagonal pairs cannot be nonincident when d is supplied.

For an R by P design X, B_X = (X^T X)^(-1), betaHat_X(Y) = B_X X^T Y,
e_X(Y) = Y-X betaHat_X(Y), S_X(A) = B_X X^T A X B_X, and
V_X(u,H) = S_X((H(r,s) u_r u_s)_{rs}). Matrix multiplication and dot products
are the ordinary finite sums. Mathlib's matrix inverse is the adjugate times
the inverse determinant; it is zero for singular real matrices. No determinant
condition is built into these definitions.

For a measure mu and real errors u_r, A_{rs} = integral u_r u_s dmu.
These are Bochner integrals. Mathlib defines a nonintegrable real integral to
be zero. `MemLp f 2 mu` says f is almost everywhere strongly measurable and
square integrable. Under that condition on a probability space, all means,
products and variances used here have their usual finite meanings.
Mathlib's covariance is integral (f-Ef)(g-Eg) dmu; its real variance is the
extended integral of |f-Ef|^2 converted to a real (infinity converts to zero).
`IsProbabilityMeasure` means mu(universe)=1.

For a finite law w, w_a >= 0 and sum w_a=1, E_w f = sum w_a f(a) and
Var_w f = sum w_a (f(a)-E_w f)^2. Its measure is sum_a ofReal(w_a) delta_a.
The finite spaces occurring here have the usual discrete measurable structure,
and finite products have the product structure. An IID realization of w means
there exist a type Omega, a measurable structure, a probability measure mu,
and measurable functions block_b: Omega -> S for every natural b, mutually
independent, with mu{block_b=a}=ofReal(w_a) for every b,a.
`iIndepFun` is independence of the sigma algebras pulled back by the functions.
Convergence in measure to a real constant L means, for every epsilon>0, the
measure of {|f_m-L|>=epsilon} tends to zero. An almost sure limit means the
ordinary real sequential limit holds outside a null set. All sequence limits
are as the natural index tends to infinity.

For a real symmetric V, its Mathlib Hermitian structure is V^T=V. Its
eigenvector unitary Q has an orthonormal eigenbasis in its columns and matching
real eigenvalues lambda. Define clip(Q,lambda) = Q diag(max(lambda_j,0)) Q^T,
V_+ = clip(Q,lambda), and gate(V) = V_+ if some V_{ii}<0, otherwise V.
The structure proof of symmetry is an argument to V_+ and gate.
`PosSemidef` means symmetric with nonnegative quadratic form for every vector;
`PosDef` means symmetric with positive quadratic form on every nonzero vector.
Mathlib initially uses finitely supported vectors for these definitions, which
is equivalent to every vector on the finite types here. Matrix rank is the
real dimension of the range of its multiplication map.

For scalar row influences z, the record covariance is sum_r z_r^2, the g-cluster
covariance is sum_g (sum_{r:g(r)=g} z_r)^2, and the member covariance is
(sum_{r:i in d(r)} z_r)^2 + sum_{r:i not in d(r)} z_r^2.

For any finite R, bar(u)=|R|^(-1) sum_r u_r. The intercept design has one
column of ones. The residual intercept estimate is
Vhat_D(d,u)=|R|^(-2) q(D,u-bar(u)). Negative powers here are integer powers
of a real number. The intercept-fit assertion says betaHat(u)=bar(u),
e(u)_r=u_r-bar(u), and X B_X 1 is the constant vector |R|^(-1).

For m estimates b_t in R^P, define bar(b)=m^(-1) sum_t b_t,
B(b)_{ij}=(m-1)^(-1) sum_t (b_{ti}-bar(b)_i)(b_{tj}-bar(b)_j),
and R(b)=(1+1/m) B(b). For component matrices U_{jt}, bar(U)_j=m^(-1)sum_t U_{jt}.
For real weights s_j and factors a_j define
poolFirst = sum_j s_j a_j [a_j^(-1) bar(U)_j + R(b)], and
combineFirst = m^(-1)sum_t sum_j s_j U_{jt} + R(b).
Subtraction in all real scalar formulas below is real subtraction, even where
k or m was originally natural.

Mathlib definitions followed: `Probability/Moments/{Variance,Covariance}.lean`,
`MeasureTheory/Function/LpSeminorm/Defs.lean`,
`MeasureTheory/Integral/Bochner/Basic.lean`,
`MeasureTheory/Function/ConvergenceInMeasure.lean`,
`Probability/Independence/Basic.lean`,
`LinearAlgebra/Matrix/{Hermitian,PosDef,NonsingularInverse,Rank}.lean`,
and `Analysis/Matrix/Spectrum.lean`.

## SAP.P032.T1

For every measurable type Omega, the following conjunction holds. The finite
assertions and existential IID realizations are unconditional; the replication
assertions quantify over probability measures and block functions on the
specified Omega and then impose the IID hypotheses stated below.

**Two-row data.** The dyads are {0,1} and {2,3}. Four possible error vectors,
in order, are (-1,-1), (-1,1), (1,-1), (1,1). The negative law has weights
(1,3,3,1)/8 and the positive law (3,1,1,3)/8. Write
A_- = [[1,-1/2],[-1/2,1]] and A_+ = [[1,1/2],[1/2,1]].
Both laws have zero means in every coordinate and second moments equal to
their respective A matrices. Every error has absolute value at most one.
Both A matrices are positive definite. Both the one-column intercept design
(1,1) and one-column slope design (-1,1) have nonzero Gram determinant.
The negative-law intercept variance is 1/4, the positive-law slope variance
is 1/4, and the positive-law intercept variance is 3/4.
With H=[[1,1],[1,-1]], A_- H=H diag(1/2,3/2),
A_+ H=H diag(3/2,1/2), and H((1/2)H)=identity.

For the intercept, the contrast vector c=1 induces h=(1/2,1/2);
q(A_-,h)=1/4, q((A_-)_D,h)=1/2, and the former is strictly smaller.
For the slope, c=1 induces h=(-1/2,1/2); q(A_+,h)=1/4 and
q((A_+)_D,h)=1/2. For the intercept weights and A_+, the corresponding
values are 3/4 and 1/2. The fit statements again include the Gram determinant.

**Four-row data.** Dyads in order are {0,1},{0,2},{3,4},{3,5}. Errors range
over all 16 sign vectors, in lexicographic order with -1 before +1. Each
has probability 3/64, with an additional 1/8 on (-1,-1,1,1) and
(1,1,-1,-1). Means vanish and the second moment matrix is

    A4 = [[1,1/4,-1/4,-1/4], [1/4,1,-1/4,-1/4],
          [-1/4,-1/4,1,1/4], [-1/4,-1/4,1/4,1]].

A4 is positive definite. With

    H4 = [[1,1,0,1], [1,-1,0,1], [-1,0,1,1], [-1,0,-1,1]],
    J4 = [[1/4,1/4,-1/4,-1/4], [1/2,-1/2,0,0],
          [0,0,1/2,-1/2], [1/4,1/4,1/4,1/4]],

J4 H4=identity and A4 H4=H4 diag(7/4,3/4,3/4,3/4).
For h=(1/4,1/4,1/4,1/4), q(A4,h)=3/16 and q((A4)_D,h)=5/16.
The finite-law variance of the mean is 3/16. The intercept-fit assertion
holds for each of the 16 possible error vectors.

**Six-row data.** The six dyads are the edges of the complete graph on
four members, ordered {0,1},{0,2},{0,3},{1,2},{1,3},{2,3}. Let 13 signs
xi_0,...,xi_12 be uniform on all 8192 sign assignments. A sign is -1 for
the corresponding Fin 2 value 0 and +1 for value 1. For edge r set

    u_r = (sqrt(2)/4) sum_{i in edge r} xi_i
          + eta_r (sqrt(2)/2) xi_{4+ell_r} + (1/2) xi_{7+r},
    ell = (0,1,2,2,1,0), eta = (1,1,1,-1,-1,-1).

All means vanish and the second moment matrix A6 has diagonal 1, entries
-1/2 on the three ordered disjoint edge pairs, and 1/8 on all other
off-diagonal pairs. A6 is positive definite. With

    H6 = [[1,1,1,1,0,0], [-1,0,1,0,1,0], [0,-1,1,0,0,1],
          [0,-1,1,0,0,-1], [-1,0,1,0,-1,0], [1,1,1,-1,0,0]],
    J6 = [[1/6,-2/6,1/6,1/6,-2/6,1/6],
          [1/6,1/6,-2/6,-2/6,1/6,1/6],
          [1/6,1/6,1/6,1/6,1/6,1/6],
          [1/2,0,0,0,0,-1/2], [0,1/2,0,0,-1/2,0],
          [0,0,1/2,-1/2,0,0]],

J6 H6=identity and A6 H6=H6 diag(1/4,1/4,1,3/2,3/2,3/2).
Each row sum of A6 is 1, each row sum of (A6)_D is 3/2, and each row
sum of D is 5. For constant h=1/6, q(A6,h)=1/6,
q((A6)_D,h)=1/4, and the diagonal-only value is 1/6.
Every |u_r| <= sqrt(2)+1/2. The intercept-fit assertion holds for every
sign assignment. The measure of the uniform 8192 assignments equals the
product of 13 fair two-point measures.

There exist an infinite IID realization of the four-row law and an infinite
IID realization of the six-row sign law, each on some measurable probability
space (the two existential spaces need not be the parameter Omega).

**Four-row replication.** For every probability measure mu on Omega, then
every block: N -> Omega -> Fin 16, if all block functions are measurable,
mutually independent, and every block has the four-row law, the following
hold. For each natural m>=1 take rows (b,r) in Fin m x Fin 4, members
(b,i) in Fin m x Fin 6, copy the four dyads into each block (so distinct
blocks have disjoint members), and take u_{br}(omega)=u_r(block_b(omega)).
The intercept-fit assertion holds for every omega. Write bar(u) for the
mean over the 4m rows. For every omega,

    (4m)^2 Vhat_D = sum_{b<m} [(u_b0+u_b1)^2+(u_b2+u_b3)^2]
                         - 8m bar(u)^2.

Var_mu(bar(u))=3/(16m), E_mu Vhat_D=(10m-3)/(32m^2), and
E_mu Vhat_D-Var_mu(bar(u))=(4m-3)/(32m^2)>0.
The random ratio Vhat_D/Var_mu(bar(u)), evaluated using m+1 blocks,
converges in measure to 5/3.

**Six-row replication.** For every probability measure mu on Omega, then
every measurable mutually independent block: N -> Omega -> (Fin 13 -> Fin 2),
if mu{block_b=a}=1/8192 for every b,a, take m copies of the six dyads and
their errors on disjoint sets of members as above. For every m>=1 the
intercept-fit assertion holds for all omega. Every block has zero means,
second moments A6, and E_mu q(D6,u_b)=9. For every omega,

    6m Vhat_D = (sum_{b<m} q(D6,u_b))/(6m) - 5 bar(u)^2.

The sampling variance of bar(u) is 1/(6m). The true second-moment matrix
restricted to incident pairs gives q(A_D,constant 1/(6m))=3/(2(6m));
retaining only its diagonal gives 1/(6m). Also
E_mu Vhat_D=3/(2(6m))-5/(6m)^2, and
(Var_mu(bar(u)) < E_mu Vhat_D) iff m>=2.
For m=1, E_mu Vhat_D=1/9 < Var_mu(bar(u)). Almost surely,
6(m+1) Vhat_D for m+1 blocks tends to 3/2.

## SAP.P032.T2

For every finite R,M,P and every measurable Omega, there is a conjunction
of the following universal assertion and the fixed finite pair assertions.

For every probability measure mu on Omega, every dyad assignment d, every
design X with det(X^T X)!=0, then every beta in R^P and errors u_r on Omega,
if every u_r is square integrable and has mean zero, put A_{rs}=E u_r u_s,
A_D=D*A entrywise, and V(c)=Var_mu(c dot betaHat_X(X beta+u)). For every
contrast c, with h=X B_X c, all of the following hold:

* For every omega, c dot betaHat_X(X beta+u(omega))-c dot beta=h dot u(omega).
* V(c)=q(A,h)=q(S_X(A),c).
* q(A,h)-q(A_D,h)=O(d,A,h).
* q(A_D,h)<=V(c) iff O>=0; q(A_D,h)<V(c) iff O>0;
  V(c)<q(A_D,h) iff O<0.

For the same data, domination q(A_D,X B_X c)<=V(c) for every c is equivalent
to S_X(A-A_D) being PSD, and this is equivalent to X^T(A-A_D)X being PSD.
No sign restriction on individual covariances is assumed.

The theorem also asserts the pair moment, boundedness, positive definiteness,
Gram invertibility, sampling variances, intercept comparison and slope
comparison stated under T1. Additionally the omitted sums for (A_-,intercept),
(A_+,intercept), and (A_+,slope) are respectively -1/4, 1/4, and -1/4;
both off-diagonal entries of A_+ are strictly positive. These finite assertions
do not depend on the generic R,M,P,Omega.

## SAP.P032.T3

This is a closed conjunction about the following ten survival records. The
columns are (subject id, unordered dyad, start, stop, covariate, status):

    0: (0,{0,1},0,1, 1,1)    1: (1,{2,3},0,1,-1,1)
    2: (2,{0,2},0,1, 1,0)    3: (2,{0,2},1,2, 3,1)
    4: (3,{1,3},0,1,-1,0)    5: (3,{1,3},1,2,-3,1)
    6: (4,{0,3},0,1, 1,0)    7: (4,{0,3},1,3, 1,2)
    8: (5,{1,2},0,1,-1,0)    9: (5,{1,2},1,3,-1,2).

A row is at risk at integer time t iff start<t<=stop and is an event at t
iff status=1 and stop=t. Only t=1,2 enter the likelihood, scores and
information. Let n_t and d_t be risk/event counts, and xbar_t the risk-set
mean. The log likelihood at real beta is
sum_{t=1,2} [sum_{events at t} beta*x_r - d_t log(sum_{risk at t} exp(beta*x_r))].
The efficient row score is sum_{t=1,2:r at risk}
(1_{event at t}-d_t/n_t)(x_r-xbar_t); information is
sum_{t=1,2} d_t [sum_{risk}x_r^2/n_t-xbar_t^2].

The risk sets are {0,1,2,4,6,8} and {3,5,7,9}; their counts are 6 and 4,
the event counts are 2 and 2, and both risk means are zero. Information is
12, the score vector is
(2/3,-2/3,-1/3,3/2,1/3,-3/2,-1/3,-1/2,1/3,1/2), and its sum is zero.
Subject totals are (2/3,-2/3,7/6,-7/6,-5/6,5/6).
The influence vector is this explicitly defined score vector divided by 12.
Its record covariance is 19/432, subject-cluster covariance 5/144, and the
four member covariances are (25/864,59/2592,89/2592,185/2592), summing
to 17/108. The direct dyadic quadratic form is 5/144.

The scalar identities asserted are

    17/108-5/144-2(19/432) = 5/144,
    17/108-5/144-2(5/144) = 23/432,
    23/432-5/144 = 8/432,
    ((10-1)/10)(6/(6-1)) = 27/25,
    17/108-5/144-2((27/25)(5/144)) = 103/2160.

The correct value differs from each of the latter two values and all three
are positive. For every real beta the log likelihood equals
-2 log(6 cosh(beta))-2 log(2 cosh(3 beta)+2 cosh(beta)); for every beta!=0
it is strictly smaller than its value at zero. The subject-equality mask
equals the repeated-dyad mask. Taking max(value,0) leaves each of 5/144,
23/432 and 103/2160 unchanged.

## SAP.P032.T4

For every finite R,M,P and every G with decidable equality, the following
conjunction holds, with no design or probability assumptions.

For every d and every score array z,

    sum_i K(C_i,z) - K(E,z) - (k-2) K(I,z) = K(D,z).

For every d and every ordered pair r,s, let
c(r,s)=sum_i C_i(r,s)-E(r,s)-(k-2)I(r,s). Then c(r,s)=D(r,s), and:
if r=s, c=k-1-(k-2); if r!=s and d(r)=d(s), c=2-1-0;
if d(r)!=d(s) and their intersection has size 1, c=1-0-0;
if their intersection is empty, c=0.
For every two dyads a,b on M, either their member sets agree and their
intersection has size two, or the sets differ and their intersection has
size at most one.

For every d,z and g:R->G, let V0=K(I,z), Vi=K(S_g,z), Vr=K(D,z),
C=sum_i K(C_i,z)-K(E,z). Then

    Vi=V0+K(T_g,z),
    C-(k-2)Vi=Vr+(k-2)(V0-Vi)=Vr-(k-2)K(T_g,z).

If g is injective, Vi=V0 and C-(k-2)Vi=Vr. For every real alpha,
C-(k-2)(alpha Vi)=Vr+(k-2)(V0-alpha Vi).
Finally all the scalar assertions of T3's discrepancy paragraph (including
the direct dyadic value, positivity and unequal values) are conjoined.

## SAP.P032.T5

This is the conjunction of the negations of four universal propositions.
It is not phrased as a conditional theorem about one dataset.

1. The population weak bound universally quantifies, in order, naturals
   n,p,k, d:Fin n->two-subsets(Fin k), design X, contrast c, and matrix A.
   Its hypotheses are det(X^T X)!=0, A PSD, and existence of a nonincident
   pair r,s with A_{rs}!=0. Its conclusion is
   q(A_D,X B_X c)<=q(A,X B_X c). T5 says this universal assertion is false.
2. The strict proposition has exactly the same quantifiers and hypotheses,
   with a strict inequality as its conclusion. T5 says it too is false.
3. The expectation proposition quantifies over a small type Omega and
   measurable structure, probability measure mu, naturals n,p,k, d,X,
   coefficients beta and contrast c, then real error functions u_r.
   Its hypotheses are nonzero Gram determinant, every u_r square integrable,
   every E u_r=0, and some nonincident pair with E u_r u_s!=0.
   Its conclusion is E_mu q(V_X(e_X(X beta+u),D),c)
   <= Var_mu(c dot betaHat_X(X beta+u)). T5 negates this universal assertion.
4. The limit proposition quantifies over a small measurable Omega and
   probability measure mu, natural p, sequences of small finite row/member
   types R_m,M_m (with decidable equality), then d_m, designs X_m, beta,c,
   and triangular-array error functions u_{mr} on that common Omega.
   Hypotheses are |R_m| tends to infinity, every Gram determinant is nonzero,
   every error is square integrable and mean zero, eventually there is a
   nonincident pair with nonzero second moment, and eventually the contrast's
   sampling variance is strictly positive. Then for every real L, if the
   random ratio of the actual residual dyadic sandwich contrast variance
   to its sampling variance converges in measure to L, the conclusion is
   L<=1. T5 says this entire universal proposition is false.

## SAP.P032.T6

This is a closed assertion about all ten dyads on five members, in order
{0,1},{0,2},{1,2},{0,3},{1,3},{2,3},{0,4},{1,4},{2,4},{3,4}.
The covariate is (3,0,2,1,-1,1,-3,-2,3,-2), response
(3,-2,-2,1,1,0,0,2,1,0), and X has intercept and covariate columns.
It asserts X^T X=[[10,2],[2,42]], B=(1/208)[[21,-1],[-1,5]] satisfies
B X^T X=identity and is B_X; X^T Y=(4,4); betaHat=(5/13,1/13);
e=(31,-31,-33,7,9,-6,-2,23,5,-3)/13; and X^T e=0.
Scores are z_{ri}=e_r X_{ri}. Their dyadic meat is
(1/169)[[1984,-1108],[-1108,50]], their record meat is
(1/169)[[3744,4052],[4052,15584]], and the covariance V=B K(D,z) B is
(1/3655808)[[460765,-79681],[-79681,7157]].
The member sum minus the record meat minus three times the record meat is
the dyadic meat (there are no repeated dyads). V is symmetric; both diagonal
entries are strictly positive; det V=-70529/308915776;
q(V,(1,6))=-237755/3655808; V is not PSD. For every proof of its symmetry
gate(V)=V. Finally q((5/4)V,(1,6))=-1188775/14623232.

## SAP.P032.T7

For every finite P with decidable equality, a conjunction asserts:

* For every real P by P matrix Q and eigenvalue vector lambda, if Q^T Q=I
  and Q Q^T=I, then clip(Q,lambda) is symmetric and PSD; for every c,
  q(clip,c)=sum_j max(lambda_j,0)(sum_i Q_{ij}c_i)^2; every such quadratic
  form is nonnegative; and clip(Q,lambda)=Q diag(lambda)Q^T iff that
  unclipped matrix is PSD.
* For every symmetric real V and every supplied proof hV of symmetry,
  V_+ is PSD, V_+=V iff V is PSD, and gate(V) is PSD iff
  (some diagonal entry of V is negative) or V itself is PSD.
* For every real a,b,d, if a>=0 and d>=0, the real two by two matrix
  [[a,b],[b,d]] is PSD iff b^2<=ad.
* The fixed T6 matrix has both diagonal entries positive and is not PSD;
  its trace is t=467922/3655808 and determinant delta=-70529/308915776.
  Put lambda_+=(t+sqrt(t^2-4delta))/2 and
  lambda_-=(t-sqrt(t^2-4delta))/2. There exists a proof hV of symmetry
  for which the two Mathlib eigenvalues are lambda_+,lambda_- in either
  order, lambda_-<0<lambda_+, and there exists a vector q in R^2 with
  q dot q=1, Vq=lambda_+ q and V_+=lambda_+ q q^T. For this hV, V_+
  has rank one, is PSD and differs from V.

The fixed two-dimensional clauses are independent of the arbitrary type P.

## SAP.P032.T8

This closed assertion defines two completed binary datasets, labelled false
and true, each with four records for each of the six edges on four members
ordered as under T1. The numbers of successes per edge are
(4,2,2,2,2,0) for false and (4,3,3,3,3,2) for true. Record (edge r,j)
has outcome 1 iff j is less than its edge's success count, otherwise 0.
For each dataset p is the mean of its 24 outcomes,
beta=log(p/(1-p)), information H=24p(1-p), score=y-p,
V0=H^(-2) times the record covariance of these scores,
VD=H^(-2) times their edge-cluster covariance, and
Vi=H^(-2) times the member covariance (including nonincident singletons).

For false/true respectively it asserts p=1/2,3/4; beta=0,log 3;
H=6,9/2; VD=2/9,8/81; V0=1/6,2/9. All four false member values are
7/36; the true values are (5/27,5/27,11/81,11/81). The decomposition
sum_i Vi-VD-2V0 equals 2/9 and 8/81 respectively. There are 24 rows
and each member is incident to exactly 12.

The five estimates are (0,0,0,log 3,log 3), in one dimension. Their average
is (2/5)log 3, B=(3/10)(log 3)^2 and R=(9/25)(log 3)^2.
Let bar(Vi),bar(VD),bar(V0) average three false and two true copies.
Define Vcorrect=sum_i bar(Vi)-bar(VD)-2bar(V0)+R, and

    Vcode = sum_{i<4} (12/13)[bar(Vi)/(12/13)+R]
            -(5/6)[bar(VD)/(5/6)+R]
            -2(23/24)[bar(V0)/(23/24)+R].

It asserts the average decomposed within variance is 14/81,
Vcorrect=14/81+(9/25)(log 3)^2,
Vcode=14/81+(441/1300)(log 3)^2=14/81+(49/52)R,
Vcode-Vcorrect=-(27/1300)(log 3)^2=((49/52)-1)R<0,
and both totals are positive. It also asserts
4(12/13)-5/6-2(23/24)=49/52. Each completed-data decomposed value is
positive and unchanged by max(value,0); the same holds for both pooled totals.
There is no assertion equating a completed-data decomposed value to a direct
ordered-pair dyadic sum.

## SAP.P032.T9

For every finite P with decidable equality and every finite J, a conjunction
asserts the following statements.

For every natural m>=2, then every real arrays s,a on J with every a_j!=0,
then every array of symmetric real P by P matrices U_{jt}, then every
estimate array b_t, one has

    poolFirst = sum_j s_j bar(U)_j + c R(b),
    combineFirst = sum_j s_j bar(U)_j + R(b),
    poolFirst-combineFirst = (c-1) R(b),
    poolFirst+(1-c)R(b) = combineFirst,
    c = sum_j s_j a_j.

For every natural k the weights on J_k=Fin k disjoint-union Fin 2 given by
s_i=1 for members and s_D=-1, s_0=-(k-2) have sum one. For every k,
m>=2, symmetric component matrices indexed by J_k and b_t, poolFirst with
these weights and all a_j=1 equals combineFirst.

For every natural k, real member counts Gi_i (i in Fin k), and real GD,n,
if every Gi_i!=0, GD!=0 and n!=0, take member factors 1-1/Gi_i,
dyad factor 1-1/GD and record factor 1-1/n. Then

    sum_j s_j a_j - 1 = -sum_i 1/Gi_i + 1/GD + (k-2)/n.

There is no integrality, positivity, >1 or combinatorial feasibility
hypothesis on these real counts in this last clause. Finally the fixed
numerical identity (4(12/13)-5/6-2(23/24))-1=-3/52 holds.

## SAP.P032.T10

This closed assertion concerns the following 22 rows (n,loss,lossMilli,serMilli):

    (6,1,167,2739), (173,43,249,2187), (29,6,207,2200),
    (8,3,375,1099), (9,8,889,3269), (24,0,0,1526),
    (45,5,111,898), (36,5,139,1511), (4,2,500,4158),
    (1,1,1000,1691), (170,7,41,955), (3,0,0,1895),
    (6,0,0,1301), (41,8,195,1432), (16,0,0,908),
    (18,4,222,1426), (20,1,50,1291), (18,0,0,999),
    (9,0,0,1071), (15,0,0,1212), (28,17,607,3268), (12,2,167,1311).

Every n is positive. For every row i, then every natural ell,
(ell<=n_i and |ell/n_i-lossMilli_i/1000|<=1/2000) iff ell=loss_i,
where all division and absolute values in this recovery formula are rational.
The rows with n<=2loss are exactly {4,8,9,20} and number four;
the rows with n<2loss are exactly {4,9,20} and number three. The rows
with lossMilli>=500 are exactly {4,8,9,20}. Row 8 has n=4 and loss=2.
There are 22 rows, total n=691, seven loss=0 rows, and 18 rows with
serMilli>1000. Every serMilli lies between 898 and 4158 inclusive;
row 6 has 898 and row 8 has 4158. These are assertions about the supplied
finite data, with the displayed thousandth scaling.

## SAP.P032.T11

For every finite R,M,P with decidable equality, then every dyad assignment
d and real design X, if det(X^T X)!=0 and every member i in M is in some
observed dyad d(r), then for every response Y,

    V_X(e_X(Y),D) = sum_i V_X(e_X(Y),C_i)
                    - V_X(e_X(Y),E) - (|M|-2) V_X(e_X(Y),I).

All component covariances use the same OLS fit, same residuals and same
bread, with no finite sample factors. No distributional hypotheses occur.
The only conclusion is this matrix equality.

## SAP.P032.T12

For every measurable Omega, then every probability measure mu, a conjunction
asserts the following two universal statements.

First, for every real Y1,Y2 on Omega, if both are square integrable, then

    Var((Y1+Y2)/2) = (Var(Y1)+Var(Y2))/4 + Cov(Y1,Y2)/2.

Second, for every family Z0,...,Z4 of real square integrable functions on
Omega, if Cov(Zi,Zj)=0 for every i!=j, then for every real a,b,c,d put
Y1=aZ0+bZ1+Z3, Y2=cZ0+dZ2+Z4,
Vn=(Var(Y1)+Var(Y2))/4 and V=Var((Y1+Y2)/2). Then

    Cov(Y1,Y2)=ac Var(Z0),
    V=Vn+(ac/2)Var(Z0).

If ac>0 and Var(Z0)>0, Vn<V; if ac<0 and Var(Z0)>0, V<Vn;
if ac=0 or Var(Z0)=0, V=Vn. No centering, unit variance or independence
hypothesis is present; pairwise zero covariances and square integrability
are the hypotheses.
