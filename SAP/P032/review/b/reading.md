# Blind mathematical reading

This file was written from `SAP/P032/Defs*.lean`, `SAP/P032/Defs/*.lean`, and
`SAP/P032/Challenge*.lean` before opening either `claims.json` or `record.json`.
The Challenge has twelve theorem constants, `SAP.P032.T1` through `T12`.
Their proofs are `sorry`; this reading concerns their propositions only.

## Shared definitions and Mathlib meanings

All unspecified scalars, vectors and matrices below are real. Finite index types
need not be nonempty. Labels in `Fin n` run from 0 to n−1. Decidable equality is
assumed on R, M, P where used, and on the subject-label type G. G need not be
finite. Each dyad d(r) is a **set of exactly two distinct members** of M. Repeated
records and repeated dyads are allowed. There are no loops, orientations, or
requirement that every member appears, except the explicit coverage hypothesis
in T11. All double sums are over ordered record pairs, including the diagonal.

Write N=|R| and K=|M|. Define the following real-valued masks:

* D(r,s)=1 if d(r) and d(s) intersect, and 0 otherwise.
* H(r,s)=1 if d(r)=d(s), and 0 otherwise (including r=s).
* I(r,s)=1 if r=s, and 0 otherwise.
* A_i(r,s)=1 if both records contain i, plus 1 if r=s and r does not contain i.
  Thus a record outside member i's incident cluster is its own singleton cluster.
* S_g(r,s)=1 if g(r)=g(s), and 0 otherwise.
* S_g^off(r,s)=1 if r≠s and g(r)=g(s), and 0 otherwise.

For scores z_r in R^P, write C(W,z)=sum_(r,s) W(r,s) z_r z_s^T.
For a record matrix B and vector h, q(B,h)=sum_(r,s) h_r h_s B_rs.
The dyadic restriction of B is B_D=D elementwise-multiplied by B.
O(B,h)=sum_(r,s):d(r)∩d(s)=empty h_r h_s B_rs.
For a design X, B_X=(X^T X)^−1, betaHat_X(Y)=B_X X^T Y,
e_X(Y)=Y−X betaHat_X(Y), and V_X(B)=B_X X^T B X B_X.
The plug-in covariance is V_X(W elementwise-multiplied by uu^T).
Mathlib's matrix inverse is the ordinary inverse for nonsingular real matrices,
and zero for singular matrices. Statements using general OLS below explicitly
assume det(X^T X)≠0; the concrete designs have nonsingularity assertions.

`errorMoments μ u` means the uncentered product integral E[u_r u_s]. It is a
covariance when the stated means are zero. `MemLp f 2 μ` means f is almost
everywhere strongly measurable and square integrable. `IsProbabilityMeasure μ`
means μ(univ)=1. Mathlib variance is the extended integral of |f−E f|² followed
by `ENNReal.toReal`; infinite variance would become zero. Covariance is the
Bochner integral E[(f−E f)(g−E g)]. Bochner integrals are defined as zero outside
the integrable case. The L² or bounded-finite-distribution assumptions in the
statements below are therefore mathematically significant.

For a finite distribution w, weights are real, nonnegative, and sum to 1;
E_w f=sum w(a)f(a), Var_w f=E_w[(f−E_w f)²]. Its measure is
sum_a ENNReal.ofReal(w(a)) times the Dirac measure at a. The concrete finite
spaces have their standard discrete measurable spaces.
`iIndepFun block μ` is joint independence of all finite subfamilies of the
coordinate random variables. Convergence in measure to L means that for every
epsilon>0 the measure of {|f_m−L|≥epsilon} tends to zero. Almost-sure convergence
means that for μ-almost every outcome the real sequence converges ordinarily.

For real matrices `IsHermitian` means V^T=V. `PosSemidef` includes symmetry and
nonnegativity of every finitely supported quadratic form; on finite indices this
is ordinary positive semidefiniteness. `PosDef` includes symmetry and strict
positivity for every nonzero vector. Rank is the real dimension of the image.
For orthogonal Q and real eigenvalue list lambda, Clip(Q,lambda)=
Q diag(max(lambda_j,0)) Q^T. For symmetric V, V_+ uses Mathlib's actual
orthonormal eigenbasis and actual real eigenvalues of V, rather than arbitrary
claimed eigenvalues. Gate(V) equals V_+ if any diagonal entry of V is negative,
and V otherwise. Eigenvalue indexing is not assumed sorted on an arbitrary P.

Sources followed: Mathlib `Probability/Moments/{Variance,Covariance}.lean`,
`MeasureTheory/Function/LpSeminorm/Defs.lean`,
`MeasureTheory/Function/ConvergenceInMeasure.lean`,
`MeasureTheory/Integral/Bochner/Basic.lean`,
`Probability/Independence/Basic.lean`,
`LinearAlgebra/Matrix/{NonsingularInverse,Hermitian,PosDef,Rank}.lean`, and
`Analysis/Matrix/Spectrum.lean`.

## T1

For **every type Ω with a measurable space**, the following conjunction holds.
The initial finite-data clauses do not depend on Ω. The final two replication
clauses quantify over every probability measure μ on that Ω and every block
sequence on it satisfying the hypotheses described below. Two separate existence
clauses choose their own probability spaces; they do not assert existence of
the required block sequence on every prescribed Ω.

Pair example: the records are {0,1} and {2,3}, with errors taking
(−1,−1),(−1,1),(1,−1),(1,1). The negative law gives these weights
(1,3,3,1)/8 and the positive law (3,1,1,3)/8. Under each law every error mean is
zero and the product-moment matrix is A_− or A_+, where
A_s=[[1,s/2],[s/2,1]]. Every error value has absolute value at most 1; both
matrices are positive definite. For the intercept design X=(1,1)^T and slope
design X=(−1,1)^T, both Gram determinants are nonzero. The intercept sampling
variance under the negative law is 1/4; the slope sampling variance under the
positive law is 1/4; the intercept sampling variance under the positive law is
3/4. With Q=[[1,1],[1,−1]], A_− Q=Q diag(1/2,3/2),
A_+ Q=Q diag(3/2,1/2), and Q(Q/2)=identity. For intercept contrast 1,
h=(1/2,1/2), q(A_−,h)=1/4<q((A_−)_D,h)=1/2. For slope contrast 1,
h=(−1/2,1/2), q(A_+,h)=1/4 and q((A_+)_D,h)=1/2. With intercept weights,
q(A_+,(1/2,1/2))=3/4 and q((A_+)_D,(1/2,1/2))=1/2.

Four-record example: dyads are (01,02,34,35). The error support is all sixteen
sign vectors in lexicographic order (−1 before 1), each of weight 3/64, plus
1/8 extra at (−1,−1,1,1) and (1,1,−1,−1). Every mean is zero; the moment
matrix A4 has diagonal 1, within-pair off-diagonals 1/4 at (0,1) and (2,3),
and all cross-pair entries −1/4. A4 is positive definite. The matrices

```
Q4 = [ 1  1  0  1;  1 -1  0  1; -1  0  1  1; -1  0 -1  1 ]
L4 = [ 1/4 1/4 -1/4 -1/4; 1/2 -1/2 0 0;
       0 0 1/2 -1/2; 1/4 1/4 1/4 1/4 ]
```

satisfy L4 Q4=identity and A4 Q4=Q4 diag(7/4,3/4,3/4,3/4).
The true variance at weights 1/4 is 3/16, the dyad-restricted quadratic form is
5/16, and the finite-law variance of the error average is 3/16. For every
support point the intercept OLS fit equals the record mean, the residuals are
errors minus that mean, and the contrast weights are the constant 1/4.

Six-record example: dyads are (01,02,03,12,13,23). A6 has diagonal 1,
entry −1/2 for disjoint dyads, and entry 1/8 for distinct incident dyads.
It is positive definite. The matrices

```
Q6 = [1 1 1 1 0 0; -1 0 1 0 1 0; 0 -1 1 0 0 1;
      0 -1 1 0 0 -1; -1 0 1 0 -1 0; 1 1 1 -1 0 0]
L6 = [1/6 -2/6 1/6 1/6 -2/6 1/6;
      1/6 1/6 -2/6 -2/6 1/6 1/6;
      1/6 1/6 1/6 1/6 1/6 1/6;
      1/2 0 0 0 0 -1/2; 0 1/2 0 0 -1/2 0; 0 0 1/2 -1/2 0 0]
```

satisfy L6 Q6=identity and A6 Q6=Q6 diag(1/4,1/4,1,3/2,3/2,3/2).
There are thirteen independent fair signs: four member signs F_i, three
opposite-edge-pair signs G_j, and six record signs E_r. The uniform law on
all 8192 assignments is explicitly used. For record r with endpoints i,j,
u_r=(sqrt(2)/4)(F_i+F_j)+epsilon_r(sqrt(2)/2)G_p(r)+(1/2)E_r,
where p=(0,1,2,2,1,0) and epsilon=(1,1,1,−1,−1,−1).
Every mean is zero, the moment matrix is A6, and |u_r|≤sqrt(2)+1/2 at every
assignment. Every row sum of A6 is 1, every row sum of (A6)_D is 3/2, and
every row sum of D is 5. At weights 1/6 the full, dyadic, and diagonal-only
quadratic forms are 1/6, 1/4, and 1/6. At every assignment the intercept
fit/residual/weight identities hold with weights 1/6. The uniform atomic
measure on the thirteen signs equals the finite product of thirteen fair-sign
measures.

For each of the four- and six-record laws there **exists** a type Ω', a
measurable space on Ω', a probability measure μ', and an infinite sequence of
measurable, jointly independent blocks with exactly the specified atom weights.

Four-record replication: for every μ on the prescribed Ω, then every
block:Nat→Ω→Fin 16, assume μ is a probability measure, every block map is
measurable, blocks are jointly independent, and each block has the four-record
atom probabilities above. For m blocks use disjoint copies of the six members
(labels (b,i)), four records per block, and the corresponding block errors.
Write bar(u) for the mean of all 4m errors and
Vhat_m=(4m)^−2 q(D,u−bar(u)). For every natural m≥1 and every outcome the
intercept fit/residual/contrast identities hold. For every outcome,
(4m)² Vhat_m=sum_b[(u_b0+u_b1)²+(u_b2+u_b3)²]−8m bar(u)².
The sampling variance is 3/(16m), E Vhat_m=(10m−3)/(32m²), their difference is
(4m−3)/(32m²), and E Vhat_m is strictly larger. As m tends to infinity,
Vhat_(m+1)/Var(bar(u)_(m+1)) converges in measure to 5/3. The use of m+1
keeps all denominators positive.

Six-record replication: for every probability μ and every measurable independent
block:Nat→Ω→(Fin 13→Fin 2) whose atom probabilities are 1/8192, use disjoint
copies of the four members with six records each. Write N=6m,
bar(u) for the overall mean, Q_b=q(D6,u_b), and
Vhat_m=N^−2 q(D,u−bar(u)). For every m≥1 the intercept fit/residual/weight
identities hold pointwise; for every b,r,s, E u_br=0,
E[u_br u_bs]=(A6)_rs, and E Q_b=9. Pointwise,
N Vhat_m=(sum_b Q_b)/N−5 bar(u)². Var(bar(u))=1/N, the dyadic population
quadratic form is 3/(2N), the record-diagonal population form is 1/N, and
E Vhat_m=3/(2N)−5/N². The inequality Var(bar(u))<E Vhat_m holds exactly
when m≥2. With one block E Vhat=1/9<Var(bar(u)). Almost surely,
6(m+1)Vhat_(m+1) tends to 3/2. No separate six-block ratio-in-measure clause
is present.

## T2

For every finite R,M,P and every measurable Ω, first universally quantify over
a probability μ on Ω, a dyad assignment d, and a real design X. Assume
det(X^T X)≠0. Then quantify over beta and record errors u, assume each u_r is
L² and E u_r=0. Put A_rs=E[u_r u_s], AD=D elementwise-multiplied by A,
and V(c)=Var(c^T betaHat_X(X beta+u)). For **every contrast c**, put
h=X B_X c. For every outcome, c^T betaHat−c^T beta=h^T u. Also
V(c)=q(A,h)=q(V_X(A),c), q(A,h)−q(AD,h)=O(A,h), and

* q(AD,h)≤V(c) iff O(A,h)≥0;
* q(AD,h)<V(c) iff O(A,h)>0;
* V(c)<q(AD,h) iff O(A,h)<0.

For these same μ,d,X,beta,u, the ordering q(AD,X B_X c)≤V(c) for **all c**
is equivalent to V_X(A−AD) being PSD. That PSD condition is in turn equivalent
to X^T(A−AD)X being PSD. No sign assumption on individual omitted covariances,
independence, or asymptotic limit is imposed.

Conjoined are all the pair mean, moment, boundedness, positive-definiteness,
nonsingularity, finite sampling variance, intercept and slope comparisons stated
for T1. In addition O(A_−,(1/2,1/2))=−1/4,
O(A_+,(1/2,1/2))=1/4, O(A_+,(−1/2,1/2))=−1/4, and both off-diagonal
entries of A_+ are strictly positive.

## T3

This is a closed conjunction about the following ten fixed survival records;
there are no external hypotheses or free data. Each row lists
(subject id, dyad, start, stop, covariate, status):

```
(0,01,0,1, 1,1)  (1,23,0,1,-1,1)
(2,02,0,1, 1,0)  (2,02,1,2, 3,1)
(3,13,0,1,-1,0)  (3,13,1,2,-3,1)
(4,03,0,1, 1,0)  (4,03,1,3, 1,2)
(5,12,0,1,-1,0)  (5,12,1,3,-1,2)
```

At risk at t means start<t≤stop; an event means status=1 and stop=t.
Risk sets at t=1,2 are {0,1,2,4,6,8} and {3,5,7,9}. Their sizes are 6,4,
both event counts are 2, and both unweighted risk-set covariate means are 0.
The defined Breslow log likelihood sums, at these two times, beta times the
event covariates minus event count times log(sum_at_risk exp(beta x)). For
every real beta it equals
−2 log(6 cosh beta)−2 log(2 cosh(3 beta)+2 cosh beta); for every beta≠0 it is
strictly below its value at zero. Thus zero is its unique global maximizer.
Information is defined as the sum of event counts times the risk-set covariate
variance at zero and equals 12. The row score is the sum over t=1,2 of
1_at_risk (1_event−eventCount/riskCount)(x−riskMean). For every row this equals
s=(2/3,−2/3,−1/3,3/2,1/3,−3/2,−1/3,−1/2,1/3,1/2), whose sum is zero.
Subject score totals are (2/3,−2/3,7/6,−7/6,−5/6,5/6).

Use row influences z=s/12. Record covariance sum z_r²=19/432; subject-cluster
covariance sum_g(sum_(r:g_r=g) z_r)²=5/144. Member covariance means the
square of the incident-score sum plus the sum of squares of nonincident rows;
its four values are (25/864,59/2592,89/2592,185/2592), totaling 17/108.
The direct dyadic ordered-pair covariance is 5/144. Subject equality is
identically the same pair mask as repeated-dyad equality for these records.
The correct combination is 17/108−5/144−2(19/432)=5/144. Substituting the
subject covariance in the last term gives 23/432, exceeding the correct value
by 8/432. Multiplying that substituted covariance by
((10−1)/10)(6/(6−1))=27/25 instead gives 103/2160. Both incorrect answers
differ from the correct one; all three answers are positive, and taking
max(answer,0) leaves each unchanged. No general software execution theorem,
likelihood derivative identity, or arbitrary-data Cox theorem is included.

## T4

For every finite R,M,P and every type G with decidable equality:

1. For every dyad assignment d and score array z,
   sum_i C(A_i,z)−C(H,z)−(K−2)C(I,z)=C(D,z).
2. For every d,r,s, the coefficient
   a_rs=sum_i A_i(r,s)−H(r,s)−(K−2)I(r,s) equals D(r,s).
   If r=s it also equals K−1−(K−2); if distinct records have equal dyads it
   equals 2−1−0; if unequal dyads share exactly one member it equals 1−0−0;
   if dyads are disjoint it equals 0. Subtractions here are real subtractions.
3. For every two dyads a,b, either their sets agree and intersection size is 2,
   or they disagree and intersection size is at most 1.
4. For every d,z,g, put V0=C(I,z), Vi=C(S_g,z), Vr=C(D,z),
   C=sum_i C(A_i,z)−C(H,z), and k=K−2. Then
   Vi=V0+C(S_g^off,z), C−k Vi=Vr+k(V0−Vi)=Vr−k C(S_g^off,z).
   If g is injective, Vi=V0 and C−k Vi=Vr. For every real alpha,
   C−k(alpha Vi)=Vr+k(V0−alpha Vi).
5. All numerical equalities, inequalities and non-equalities in T3's
   `survivalDiscrepancyStatement` are also conjoined, including its direct
   ordered-pair covariance and 27/25 multiplier. Other Cox-fit clauses are not.

There is no full-rank, coverage, stochastic, or nonempty-type hypothesis.

## T5

This closed theorem is the conjunction of **four negated universally quantified
propositions**. It claims that each of the following four universal assertions
fails; the counterexamples for different assertions need not be identical.

1. For every natural n,p,k, assignment d:Fin n→two-element subsets of Fin k,
   design X, contrast c, and real square record matrix A, if det(X^T X)≠0,
   A is PSD, and there exist disjoint records r,s with A_rs≠0, then
   q(AD,X B_X c)≤q(A,X B_X c).
2. The identical universal assertion with a strict < conclusion.
3. For every type Ω in Type, measurable structure, probability μ, natural
   n,p,k, dyads d, design X, beta, c, and errors u, assume det(X^T X)≠0,
   every u_r is L² and mean zero, and some disjoint pair has nonzero product
   moment. Then E[q(plugInCovariance(X,e_X(X beta+u),D),c)]
   ≤Var(c^T betaHat_X(X beta+u)).
4. For every such Ω, probability μ, natural p, sequences of finite types
   R_m,M_m with decidable equality, dyads d_m, designs X_m, fixed beta,c in
   R^p, and errors u_m, assume |R_m|→infinity, all Gram determinants are
   nonzero, all errors are L² and mean zero, eventually some disjoint pair
   has nonzero product moment, and eventually the sampling contrast variance
   is positive. Then for every real L, if the residual plug-in contrast
   variance divided by the true sampling contrast variance converges in
   measure to the constant L, L≤1.

The fourth assertion concerns a ratio limit, not an unscaled difference or an
unbounded limsup. The theorem itself says no one of these universal assertions
is valid. It does not quantify over a paper or a printed-language interpretation.

## T6

A closed statement about all ten unordered dyads on five members in order
(01,02,12,03,13,23,04,14,24,34). The design has an intercept and covariate
x=(3,0,2,1,−1,1,−3,−2,3,−2); response Y=(3,−2,−2,1,1,0,0,2,1,0).
It asserts X^T X=[[10,2],[2,42]],
B=(1/208)[[21,−1],[−1,5]], B(X^T X)=identity, B=B_X,
X^T Y=(4,4), betaHat=(5/13,1/13), and
e=(31,−31,−33,7,9,−6,−2,23,5,−3)/13, with X^T e=0.
With scores z_r=e_r(1,x_r), the dyadic meat is
(1/169)[[1984,−1108],[−1108,50]]; the record meat is
(1/169)[[3744,4052],[4052,15584]]. Member-score covariance minus the record
covariance minus three times that same record covariance equals the dyadic
meat. The covariance V=B meat B is symmetric and equals
(1/3655808)[[460765,−79681],[−79681,7157]]. Both diagonal entries are
positive; det V=−70529/308915776, q(V,(1,6))=−237755/3655808,
and V is not PSD. For every proof of V's symmetry Gate(V)=V. Finally
q((5/4)V,(1,6))=−1188775/14623232. No stochastic errors are needed.

## T7

For every finite P with decidable equality, for every real square Q and list
lambda:P→R, assume Q^T Q=identity and Q Q^T=identity. Then Clip is symmetric
and PSD, and for every c,
q(Clip,c)=sum_j max(lambda_j,0)(sum_i Q_ij c_i)²≥0.
Clip equals Q diag(lambda) Q^T exactly when that original matrix is PSD.
For every symmetric real V (and its supplied symmetry proof), V_+ is PSD,
V_+=V iff V is PSD, and Gate(V) is PSD iff either a negative diagonal entry
exists or V itself is PSD. For all real a,b,d with a,d≥0,
[[a,b],[b,d]] is PSD iff b²≤ad.

The fixed V from T6 has positive diagonal, is not PSD, has trace
t=467922/3655808 and determinant delta=−70529/308915776. There exists a
symmetry proof such that its two actual eigenvalues, in either order, are
lambdaPlus=(t+sqrt(t²−4 delta))/2 and
lambdaMinus=(t−sqrt(t²−4 delta))/2, with lambdaMinus<0<lambdaPlus.
There exists q in R² with q^Tq=1, Vq=lambdaPlus q, and
V_+=lambdaPlus q q^T. This V_+ has rank 1, is PSD, and differs from V.

## T8

A closed scalar example uses 24 binary records: four ordered records for each
of the six dyads (01,02,03,12,13,23). For completed dataset B=false the
success counts by dyad are (4,2,2,2,2,0); for B=true they are (4,3,3,3,3,2).
Within each dyad the first that-many records have response 1 and the rest 0.
The success probability is the empirical mean p, the estimate is
log(p/(1−p)), information is 24p(1−p), and record scores are Y−p.
All record, dyad-cluster and member-plus-singleton covariances use the same
scores and are multiplied by information^−2. It asserts p=(1/2,3/4),
estimates=(0,log 3), information=(6,9/2), dyad covariances=(2/9,8/81),
record covariances=(1/6,2/9), member covariances all 7/36 for false and
(5/27,5/27,11/81,11/81) for true. Their member-minus-dyad-minus-twice-record
combinations are respectively 2/9 and 8/81. There are 24 records and each
member's incident set has 12 records.

Five estimates are (0,0,0,log 3,log 3). For m estimates b_t, bar(b)=sum b_t/m,
between covariance is sum_t(b_t−bar(b))(b_t−bar(b))^T/(m−1), and the full
Rubin contribution is R=(1+1/m) times that between covariance. Here
bar(b)=(2/5)log 3, between variance=(3/10)(log 3)² and R=(9/25)(log 3)².
Average completed component covariances give weight 3/5 to false and 2/5 to
true. Define Correct as their member-minus-dyad-minus-twice-record combination
plus R, and Code as
sum_i (12/13)(averageMember_i/(12/13)+R)
−(5/6)(averageDyad/(5/6)+R)
−2(23/24)(averageRecord/(23/24)+R).
Then the completed decomposition average is 14/81,
Correct=14/81+(9/25)(log 3)², Code=14/81+(441/1300)(log 3)²,
Code−Correct=−(27/1300)(log 3)²<0, and both are positive.
The factor sum is 4(12/13)−5/6−2(23/24)=49/52;
Code=14/81+(49/52)R and Code−Correct=(49/52−1)R.
For each B, the completed decomposition is positive and unchanged by max(.,0);
so are Code and Correct. There is no equality of either completed decomposition
with a direct D-masked ordered-pair covariance. There is no general logit
likelihood maximization theorem here: the estimates are defined by the formula.

## T9

For every finite P with decidable equality and every finite component type J:
first quantify over natural m≥2, then real weight and factor functions s,a on
J with every a_j≠0, then component covariance matrices U_jt that are symmetric
for every j,t, then arbitrary estimates b_t. Let Ubar_j=sum_t U_jt/m,
R=(1+1/m) betweenCovariance(b), and c=sum_j s_j a_j. Define
Before=sum_j(s_j a_j)(a_j^−1 Ubar_j+R) and
After=sum_t sum_j s_j U_jt/m+R. Then
Before=sum_j s_j Ubar_j+cR, After=sum_j s_j Ubar_j+R,
Before−After=(c−1)R, and Before+(1−c)R=After.
Symmetry is a hypothesis; PSD of U_jt is not.

For every natural k, on the finite component index Fin k plus Fin 2 the weights
are k member weights 1, a dyad weight −1, and a record weight −(k−2),
where k−2 is a real subtraction. These weights sum to 1. For every k and m≥2,
every such symmetric U_jt and every b_t, the Before and After operations with
all a_j=1 agree.

For every natural k, real list Gi:Fin k→R and reals GD,n, assume
every Gi_i≠0, GD≠0, n≠0. Use member a_i=1−1/Gi_i, dyad a_D=1−1/GD,
and record a_0=1−1/n. Then
sum_j s_j a_j−1=−sum_i 1/Gi_i+1/GD+(k−2)/n.
This separate coefficient identity does **not** assume these a_j are nonzero,
does not require the numbers to be integer counts, and does not instantiate
the first identity when an a_j=0. Finally the closed example gives
4(12/13)−5/6−2(23/24)−1=−3/52.

## T10

This closed statement uses the following fixed table, rows indexed 0 through 21.
Each row is (number n, integer loss l, loss proportion in thousandths, standard
error ratio in thousandths):

```
(6,1,167,2739) (173,43,249,2187) (29,6,207,2200)
(8,3,375,1099) (9,8,889,3269) (24,0,0,1526)
(45,5,111,898) (36,5,139,1511) (4,2,500,4158)
(1,1,1000,1691) (170,7,41,955) (3,0,0,1895)
(6,0,0,1301) (41,8,195,1432) (16,0,0,908)
(18,4,222,1426) (20,1,50,1291) (18,0,0,999)
(9,0,0,1071) (15,0,0,1212) (28,17,607,3268) (12,2,167,1311)
```

Every n is positive. For every row i, then **every natural integer k**,
[k≤n_i and |k/n_i−lossMilli_i/1000|≤1/2000] iff k=l_i; these divisions and
absolute values are in the rationals. The rows n≤2l are exactly {4,8,9,20},
and rows n<2l exactly {4,9,20}, of cardinalities 4 and 3 respectively. Rows
with lossMilli≥500 are also exactly {4,8,9,20}. Row 8 has n=4 and l=2.
There are 22 rows, sum n=691, exactly 7 rows have l=0, and exactly 18 have
serMilli>1000. Every serMilli lies from 898 to 4158 inclusive, with values
898 at row 6 and 4158 at row 8. This is arithmetic on the encoded table;
the theorem has no external table-transcription hypothesis.

## T11

For every finite R,M,P with decidable equality, for every dyad assignment d
and real design X, assume det(X^T X)≠0, then assume every member i of M
appears in at least one record. For **every response Y**, set u=e_X(Y).
The D-masked plug-in OLS covariance equals the sum of member-plus-singleton
plug-in covariances minus the repeated-dyad plug-in covariance minus (K−2)
times the record plug-in covariance. Every component uses the same design,
bread and residual vector. No probability space, covariance sparsity, finite
sample factors, pointwise coefficient assertion, conventional multiway-cluster
comparison, computation claim, square-root SE rule, or clipping assertion occurs.

## T12

For every measurable Ω, then every probability measure μ on it, a conjunction:

1. For every two real random variables Y1,Y2, assuming each is L²,
   Var((Y1+Y2)/2)=(Var(Y1)+Var(Y2))/4+Cov(Y1,Y2)/2.
2. For every list Z_0,...,Z_4 of L² real random variables, assume every pair
   of distinct list positions has zero covariance. Then for **every real
   a,b,c,d**, set Y1=a Z0+b Z1+Z3 and Y2=c Z0+d Z2,
   Vn=(Var(Y1)+Var(Y2))/4 and V=Var((Y1+Y2)/2). Then
   Cov(Y1,Y2)=ac Var(Z0), V=Vn+(ac/2)Var(Z0);
   if ac>0 and Var(Z0)>0 then Vn<V;
   if ac<0 and Var(Z0)>0 then V<Vn;
   if ac=0 or Var(Z0)=0 then V=Vn.

The primitives need not be independent or centered; zero cross-covariances and
L² membership are the actual hypotheses. There is no assumption on the signs
of b or d and no extra restriction on the contrast variables.
