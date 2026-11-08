# Blind reading, saved before opening claims.json or record.json

Only the Challenge sources, their statement closures, Mathlib definitions, and
scratch elaboration checks have been used at this stage. The five fingerprints
and the full lists in closure.json were read. Every source declaration in those
lists was read, including enclosing definitions of generated helpers. All 96
distinct `._proof_` helpers were additionally printed in
scratch/ClosureHelpers.log. They are numeral/typeclass facts, finite-index
bounds, graph symmetry/diagonal proofs, probability-instance proofs, and proofs
of positivity and growth of the explicitly given sizes. They add no premises to
the mathematical statements. Structure constructors and projections have their
ordinary field meanings below.

## Common notation, fully expanded

Indices are `Fin n`, the natural numbers strictly below n. A graph is a symmetric
Boolean function on pairs of these indices, false on the diagonal. Write A for
its real 0/1 adjacency matrix, g_i for its degree (the finite sum of incident
Boolean indicators), and B=I+A. An observed graph R and natural caps d permit a
graph exactly when it contains every edge of R and g_i <= d_i for every i.
`Maximizes` means that feasibility condition AND comparison with every feasible
graph; it is not an independently postulated optimum value.

A model consists of a probability measure P on the Borel space R^n, deterministic
real weights theta_i, a true graph G, an observed graph R, and natural caps d_i.
Write X_i(y)=theta_i*y_i, bar(x)=(sum_i x_i)/n,
r_i(x)=x_i-bar(x), s2(x)=sum_i r_i(x)^2/n, and
q(M,x)=sum_i sum_j M_ij*x_i*x_j. All sums are finite Mathlib sums.
Expectation is the real Bochner integral against P;
Var(f)=E[(f-E[f])^2], betaHat=bar(X), beta=E[betaHat],
mu_i=E[X_i], C_ij=E[(X_i-mu_i)(X_j-mu_j)],
delta_i=mu_i-beta, b=q(B,delta)/n,
meanSpread=sum_i delta_i^2/n, meanVariance=sum_i C_ii/n.
Homoskedastic means all diagonal entries of C are equal.

Dependency means: for EVERY two disjoint finite sets S,T of vertices with no
edge between them, the random vectors (y_i)_(i in S) and (y_j)_(j in T) are
independent (`IndepFun` for their restricted-coordinate functions and P).
This is full independence of separated sets, not just pairwise zero covariance.
It also gives this independence for their deterministic weighted coordinates.

A family has sizes n_k>0, with n_k tending to infinity in the natural-number
atTop filter, and one model on R^(n_k) for every natural k. Models in different
rows are not required to live on one probability space. Validity means the true
graph is feasible in every row. Nestedness means sizes are monotone and, for
each k, there EXISTS an injection from that row's vertices into the next row's
vertices preserving BOTH edges and nonedges of G.

`Scaling(F,c1,c2,c3,c4)` is the conjunction of nestedness, c1,c2,c3,c4>0,
dependency in every row, almost surely |X_i-beta|<=c1 for every vertex in every
row, g_i<=c2 in every row, n_k Var(betaHat_k) -> c3, and |theta_i|<c4 everywhere.
`RowScaling` and `WholeScaling_W3` have EXACTLY the same clauses except for the
omission of nestedness. Positive sizes and growth still come from the family.
These definitions do not assume common means, independence along true edges,
uniformly bounded supplied caps, or observed-graph nesting.

The original oracle variance estimate is
V1(G,x)=[sum_i r_i(x)^2+q(A,r(x))]/n^2=q(B,r(x))/n^2.
For general M, V(M,x)=q(M,r(x))/n^2. The scaled true variance is
v_k=n_k Var(betaHat_k), and scaledOracle_k(y)=n_k V1(G_k,X(y)).
`InProbability(F,T,a)` means: for every real epsilon>0,
P_k(|T_k-a_k|>epsilon) -> 0 as k->infinity.
`Conservative(F,V)` means: for every epsilon>0,
P_k(n_k(Var(betaHat_k)-V_k)>epsilon) -> 0.
Probability is `P.real E`, i.e. `(P E).toReal`.

Phi(t) is the cdf of Mathlib's real Gaussian with mean 0 and variance 1.
z_alpha=inf{t in R : 1-alpha/2 <= Phi(t)}.
Coverage(V,alpha)=P(|betaHat-beta| <= z_alpha*sqrt(max(V,0))).
All coverage assertions below quantify 0<alpha<1, unless a fixed alpha is
explicitly specified. PSD(M) means M is symmetric AND q(M,z)>=0 for every real
vector z. The operator norm is the norm of the associated continuous linear map
on Euclidean R^n, hence the Euclidean spectral norm. Matrix multiplication,
trace, diagonal matrices, transpose, and identity have their Mathlib meanings.
An upper sum means sum over i<j, counting an undirected edge once.

For the corrected estimates, put h_i=min(d_i,n-1), a_i=0 if h_i=0 and
a_i=1-1/h_i otherwise, D_G=diag(g_i), and D_h=diag(h_i). Then
Mplus=B+diag(a_i*g_i),
Vplus(G,d,x)=V1(G,x)+sum_i a_i*g_i*r_i(x)^2/n^2,
VYoung(d,x)=sum_i(1+h_i)*r_i(x)^2/n^2, and
V2prime(d,x)=s2(x)/n*[1+sum_i h_i/n].
The corrected edge objective is
w(G)=sum_(i<j) A_ij*[r_i*r_j+(a_i*r_i^2+a_j*r_j^2)/2].

## SAP.P011a.T1

Location: Challenge/Part1.lean:9-17; principal definitions:
Defs/WholeW2.lean:216-231, Defs/Part5.lean:229-236,
Defs/Part3.lean:41-78, and the common definitions above.

This is an unconditional conjunction about explicitly specified laws, NOT an
implication from assumed counterexample facts. In row k let K=k+1 and n=4K.
Choose all 4K Boolean entries independently and uniformly; replace false by -1
and true by 1. In each block set
x=(a+u0+u3,-a+u0+u1,a+u1+u2,-a+u2+u3).
The law is the image of the uniform PMF on all Boolean arrays, converted to a
measure; thus atoms with several preimages receive their combined mass.
Weights are all 1; G and R are disjoint copies of the four-cycle
0--1--2--3--0, and every supplied cap is 2. Local indices are i mod 4 and block
indices are floor(i/4). These laws are the specified objects, not arbitrary
dependent-sign arrays.

For a=3/2 the conjunction asserts:

* Scaling with constants (7/2,2,4,2), validity, and, for every k,
  homoskedasticity, means repeating (3/2,-3/2,3/2,-3/2), and full covariance
  C=2I+A, including zero cross-block covariances.
* For every k: beta=0, v_k=4, b_k=-9/4; for EVERY graph H, H is feasible iff
  H=G_k; E[scaledOracle]=7/4-12/n;
  Var(scaledOracle)=44/n-96/n^2-288/n^3.
* scaledOracle -> 7/4 in probability. For EVERY epsilon with 0<epsilon<9/4,
  both P(|scaledOracle-4|>epsilon) and P(4-scaledOracle>epsilon) tend to 1.
* For EVERY real t, P(sqrt(n)*betaHat<=t) -> Phi(t/2).
* For EVERY 0<alpha<1, coverage tends to
  2 Phi(z_alpha sqrt(7/16))-1, and that number is strictly below 1-alpha.
  At alpha=1/20 this number lies strictly between 8045/10000 and 8055/10000.
* P(V1(G_k,X)>0) -> 1.

For a=3 it asserts Scaling with constants (5,2,4,2), validity,
homoskedasticity, beta=0 and v_k=4 for every k, and scaledOracle -> -5 in
probability. For the one-block law the vector (5,-1,5,-1) has probability 1/16,
its sample average is 2, and its V1 estimate is -9/4.

In addition, for EVERY real a the matrix
H=[[1,0,0,1],[1,1,0,0],[0,1,1,0],[0,0,1,1]] satisfies
HH^T=2I+A_cycle, q(B_cycle,(a,-a,a,-a))=-4a^2, and the entries of 2I+A_cycle
sum to 16. For EVERY a,k,i, the diagonal covariance of the corresponding cycle
law equals 2. The universal quantifier over a also scopes the constant matrix
facts; it is harmless redundancy.

The docstring describes these as refutations of quoted printed assertions. The
Lean proposition itself states the explicit model facts and limiting failures;
whether those contradict a particular external assertion remains to be checked.

Junk-value audit: n=4(k+1) is always positive; all other denominators are
nonzero numerical constants. Modulus/division in the block functions use the
proved positive divisor 4, with Fin bounds certified. The sample mean never
uses 0/0. Every random variable integrated here has finite support, so no
nonintegrable-Bochner default is used. The probability measures have mass 1,
so `toReal infinity=0` is irrelevant. Square-root inputs n, 7/16, and max(V,0)
are nonnegative; clipping is an intentional convention for negative V and is
material to interval coverage. For 0<alpha<1 the quantile set is nonempty and
bounded below, so its real infimum is not an empty/unbounded-set default.
The fixed alpha=1/20 is in that interval. No logarithm, real power, limit
inferior, empty vertex set, or partial matrix inverse is used in this target.

## SAP.P011a.T2

Location: Challenge/Part1.lean:19-28; principal definitions:
Defs/WholeW2.lean:233-276, Defs/Part5.lean:223-227,238,
Defs/Part3.lean:80-128, and the common definitions above.

This is another unconditional conjunction. Its main quantifier is FOR EVERY
real t satisfying t=1 OR t=2 (not an existential selection of whichever case
works). With K=k+1 and n=3K, each block has independent fair signs U,V and
x=(t+U,-2t+(3/5)U+(4/5)V,t+V).
All 2K signs are independent. The law is the uniform-PMF image on Boolean
arrays. All weights are 1. G=R is the disjoint union of paths 0--1--2; supplied
caps repeat (1,2,1). Indices are i mod 3 and floor(i/3).

For each permitted t it asserts Scaling with constants (6,2,29/15,2), validity,
and homoskedasticity in every row. For every k, beta=0, v_k=29/15, feasibility
of ANY graph H is equivalent to H=G_k, and
E[scaledOracle]=(29-10t^2)/15-217/[135(k+1)]. Also
scaledOracle -> (29-10t^2)/15 in probability.

If t=1, for EVERY 0<epsilon<2/3 both
P(|scaledOracle-29/15|>epsilon) and P(29/15-scaledOracle>epsilon) tend to 1.
For EVERY 0<alpha<1 coverage tends to
2 Phi(z_alpha sqrt(19/29))-1 < 1-alpha. At alpha=1/20 this limit is strictly
between 8873623230/10000000000 and 8873623231/10000000000.
If t=2, P(V1<0)->1 and, for EVERY 0<alpha<1, clipped coverage tends to zero.
No exact zero coverage at every finite sample size is asserted.

Finite moments, for EVERY permitted t:

* For each of the three coordinates, the four-sign average AND the expectation
  under the one-block probability law equal the respective entry of (t,-2t,t).
* C=[[1,3/5,0],[3/5,1,4/5],[0,4/5,1]] for one block,
  q(B,(t,-2t,t))=-2t^2, and q(B,1)=7.
* Writing S=sum_i x_i, L=sum_ij B_ij*x_j, Q=q(B,x), the four-sign
  averages give E[S]=0, E[S^2]=29/5, E[Q]=29/5-2t^2,
  E[(Q-(29/5-2t^2))^2]=8t^2+8836/625, and E[S L]=14.
  Here the four-sign average explicitly sums over (U,V) in {-1,1}^2 and divides
  by 4, so this is a genuine finite-law mean.

For EVERY permitted t and EVERY natural K>0, it further asserts |y_i|<=27/5
almost surely, the means repeat (t,-2t,t), and C is block diagonal with the
displayed 3x3 block (zero for different blocks). For EVERY real data vector y,
put y_b(r)=y_(3b+r). Then

    n V1(G,y) = sum_b Q(y_b)/n
                -(2/3) bar(y) * [sum_b L(y_b)/K]
                +(7/3) bar(y)^2.

For EVERY real t (without restricting to 1 or 2) and EVERY Boolean u,v, with
U=sign(u), V=sign(v), the single-block polynomials are
S=(8/5)U+(9/5)V,
L=-2t+(19/5)U+(22/5)V,
Q=29/5-2t^2-2t(U+V)+(94/25)UV.

Finally, for EVERY permitted t and EVERY K>0, define the 3K by 2 deterministic
design with first column all 1 and second column repeating (t,-2t,t).
Every coordinate y_i is integrable and its expectation equals that design row
times gamma=(0,1). For EVERY data vector y,
[(D^T D)^(-1) D^T y]_0=bar(y). Thus the average statistic is the ordinary
least-squares intercept of a correctly specified model.

Junk-value audit: all n,K divisions use K>0 or K=k+1. Fin reindexing has an
explicit proof 3b+r<3K, and block divisions have positive divisor 3. All
integrals have finite support. The matrix inverse in OLS is Mathlib's total
square-matrix inverse (singular matrices would give the totalized inverse);
here the two design columns are orthogonal, with squared norms 3K and 6Kt^2,
so K>0 and t in {1,2} make the Gram matrix invertible. Quantile, clipping,
probability-toReal, and square-root safety are as for T1, with 19/29 replacing
7/16. No liminf, logarithm, rpow, truncated natural subtraction, or empty
sample is used in the asserted cases.

## SAP.P011a.T3

Location: Challenge/Part1.lean:30-38; principal definitions:
Defs/WholeW2.lean:14-60,278-290; Defs/Part3.lean:161-167.

The statement conjoins five universally quantified propositions plus an
additional universal bound. In EACH of the first four propositions it
quantifies over EVERY family F and EVERY four real constants c1,c2,c3,c4,
THEN assumes RowScaling with those constants. Thus the family, all laws,
graphs, weights, caps, and constants are arbitrary subject to precisely the
row assumptions written in the common expansion. The conclusions are:

1. scaledOracle_k-v_k-b_k -> 0 in probability.
2. For EVERY natural k,
   |E[scaledOracle_k]-v_k-b_k| <= 3(1+c2)^2*c1^2/n_k.
3. s2(X_k)-meanVariance_k-meanSpread_k -> 0 in probability.
4. Both equivalences hold: scaledOracle_k-v_k ->0 in probability IFF
   b_k->0 as a real deterministic sequence; and V1 is conservative IFF
   0<=liminf_k b_k. Additionally, if delta_i=0 for EVERY k,i then the oracle
   is scaled consistent; if B_k is PSD for EVERY k then it is conservative.

The fifth proposition is separately quantified over EVERY natural n>0 and
EVERY graph G on n vertices. B is PSD IFF the relation i=j OR G(i,j) is
transitive (equivalently, G is a disjoint union of complete graphs). Moreover,
for EVERY map label:Fin n -> N such that G(i,j) iff i!=j AND label(i)=label(j),
and EVERY real vector x,

    V1(G,x)=sum_(c in image(label)) [sum_(i:label(i)=c) r_i(x)]^2/n^2.

There is no assumption that such a label has been supplied for arbitrary G;
the formula is conditional on the displayed representation.

The final conjunct again universally quantifies F and the four constants,
assumes RowScaling, THEN for EVERY k concludes sum_i delta_i=0 and
|b_k| <= (1+c2)c1^2. No validity, common means, or nesting is a prerequisite
for the four general results or these two bounds.

Junk-value audit: family sizes and finite-graph formula sizes are positive.
The weighted coordinate functions are continuous; boundedness of X_i-beta
implies boundedness around a finite real number and hence all their moments
are integrable under a probability measure. Thus beta, covariance, and
quadratic expectations do not exploit Bochner's zero default. All relevant
events are measurable and probability-toReal never sees infinity. Real
liminf is total even for pathological unbounded sequences, but b_k is
uniformly bounded above AND below by the explicitly asserted bound (also
obtained directly from bounded means and degree). Thus its occurrence is the
ordinary finite real liminf. The finite image of labels is nonempty for n>0;
empty clique-label terms would in any event be zero finite sums. No quantile,
square root, log, rpow, partial inverse, or natural truncated subtraction
occurs in this target's substantive definitions.

## SAP.P011a.T4

Location: Challenge/Part1.lean:40-50; principal definitions:
Defs/WholeW3.lean:13-134; Defs/Part3.lean:161-167,197-204.

This is an unconditional conjunction of the following assertions.

First, for EVERY family F, four real constants satisfying WholeScaling_W3,
EVERY k, and EVERY deterministic symmetric real n_k by n_k matrix M, put
H=I-11^T/n. Both exact identities hold:

    E[q(M,r(X))]=tr(H M H C)+q(M,delta)
               =tr(M C)+q(M,delta)-(2/n)sum_ij(M C)_ij
                 +q(M,1) Var(betaHat).

Second, for EVERY family, EVERY c1,c2,c3,c4,K satisfying the row scaling
assumptions, and EVERY deterministic sequence of symmetric matrices M_k with
Euclidean operator norm <=K for EVERY k, the following conjunction holds:

* There EXISTS a real B>=0 (allowed to depend on the preceding data) such that
  for EVERY k, Var(q(M_k,r(X_k)))<=B n_k. This is a bound on the unnormalized
  quadratic form, in every row.
* The difference between n_k V(M_k,X)-v_k and
  [tr((M_k-B_k)C_k)+q(M_k,delta_k)]/n_k tends to zero in probability (F1).
* IF for EVERY k both M_k and M_k-B_k are PSD, THEN for EVERY k the mean
  quadratic and covariance trace just displayed are individually nonnegative,
  AND V(M_k,X) is conservative.

Third, under the same universal family/constant/matrix quantifiers and norm
and symmetry assumptions, assume each M_k is PSD. Two sufficient conditions
are each asserted separately:

* If tr((M_k-B_k)C_k)>=0 for EVERY k, then every q(M_k,delta_k)>=0 and the
  estimator is conservative.
* If, for EVERY k and EVERY admissible covariance C,
  tr((M_k-B_k)C)>=0, then the actual covariance traces and mean quadratics
  are nonnegative for every k, and the estimator is conservative.

Admissibility is unfolded as follows: there EXISTS a probability model m on
R^n with true graph G, full disjoint-set dependency, each weighted coordinate
in Mathlib MemLp exponent 2, and covariance exactly C. The auxiliary model's
weights, observed graph, caps, and law may all be chosen. This ranges over
square-integrable laws with G as a dependency graph, without bounding means.

Fourth, for EVERY n (including zero), graph G, admissible C, and symmetric
matrix N,

    tr(N C)=sum_i N_ii C_ii+2 sum_(i<j) A_ij N_ij C_ij.

Fifth, for EVERY n,G, B-(I+A)=0. This one conjunct merely records the definition
of B; it does not replace any of the nontrivial conclusions. The full clique
characterization and formula from T3 are also included, with their independent
universal n>0, graph, label, vector quantifiers.

Finally, the data-dependent failure uses n=k+1, independent uniform signs
y_i in {-1,1}, all weights 1, G=R empty, and caps zero. Its law is the uniform
PMF image on all Boolean vectors. For EVERY n>0 and EVERY deterministic sign
vector x, define M(x)=xx^T/n. Then
||M||=1, tr(M)=1, and n V(M(x),x)=(1-bar(x)^2)^2.
For the specified sign family the theorem asserts:

* WholeScaling_W3 with constants (1,1,1,2), validity, and for EVERY k:
  v_k=1, beta=0, dependency, C=I, delta=0, and each marginal assigns mass 1/2
  to each sign; almost surely tr(M(y)-I)/n=(1-n)/n.
* n V(M(y),y)-1 ->0 in probability; tr(M(y)-I)/n ->-1 in probability;
  n V(M(y),y)->1 and n V(M(y),y)-v_k->0 in probability;
  the deterministic sequence (1-n)/n tends to -1.
* The residual n V(M(y),y)-v_k-tr(M(y)-I)/n tends to 1 in probability,
  and does NOT tend to zero in probability.

This counterexample addresses extending F1 to random matrices. It is not a
counterexample to the deterministic F1 result in the same conjunction.

Junk-value audit: scaling gives positive n and all moments, as in T3. The
independent-sign law is finite, so every displayed witness quantity exists.
An admissible covariance explicitly supplies MemLp 2 for each weighted
coordinate, enough for its covariance and trace. All finite-sign formulas
require n>0. The support identity and B-(I+A)=0 allow n=0 but contain no
division and use the ordinary empty sums/matrices; they are genuine zero
dimensional identities. Operator norm is the Euclidean operator norm, not
the norm on the unconverted sup-norm function space. No sInf, sSup, liminf,
log, rpow, sqrt, partial inverse, or truncated subtraction affects T4.

## SAP.P011a.T5

Location: Challenge/Part1.lean:52-62; principal definitions:
Defs/Part3.lean:206-240, Defs/Part4.lean:35-39,
Defs/Part5.lean:142-150, Defs/WholeW3.lean:136-185.

This conjunction first makes universal finite assertions. FOR EVERY natural
n>0, EVERY observed graph R, feasible graph G, cap vector d, and real vector x,
with h,a,D_G,D_h,Mplus,Vplus,VYoung,w defined in the common expansion:

* g_i<=h_i for every i, and
  Mplus=D_G+A+diag(1-(if h_i=0 then 0 else g_i/h_i)).
* For EVERY z, q(D_G+A,z)=sum_(i<j) A_ij(z_i+z_j)^2, and
  q(D_G-A,z)=sum_(i<j) A_ij(z_i-z_j)^2.
* Each of Mplus, Mplus-B, I+D_h, D_h-A, D_h-D_G, and D_G-A is PSD;
  Vplus>=0; and (I+D_h)-B=(D_h-D_G)+(D_G-A).
* V1(G,x)<=VYoung(d,x), and n^2 Vplus=sum_i r_i^2+2w(G).
* For EVERY natural D, IF all h_i=D, THEN
  VYoung=V2prime=s2(x)(1+D)/n.
* For EVERY naturals g0,D with D>=1, IF all graph degrees equal g0 AND all
  h_i=D, THEN Vplus=V1+g0(1-1/D)sum_i r_i^2/n^2.
* For EVERY natural g0>=1, IF all graph degrees and h_i equal g0, THEN
  Vplus=V1+(g0-1)sum_i r_i^2/n^2. IF every graph degree is zero, Vplus=V1.

An additional separately universal finite proposition explicitly states
PSD(Mplus), PSD(Mplus-B), Vplus=V(Mplus,x), and Vplus>=0.

The finite optimization proposition has quantifiers EVERY n>0,R,G,d,x;
IF G is feasible and Vplus(G,d,x) dominates Vplus of EVERY feasible graph,
THEN w(G) dominates w of EVERY feasible graph and
n^2 Vplus(G,d,x)=sum_i r_i^2+2w(G).

The finite supplement instead quantifies EVERY n>0,R,G,d with G feasible,
and asserts Mplus-B=diag(a_i*g_i). For EVERY vector x,
VYoung=V(I+D_h,x)>=0, there EXISTS a feasible graph maximizing Vplus,
and EVERY such maximizing graph H satisfies Vplus(G,d,x)<=Vplus(H,d,x).
For EVERY real c2>=0 bounding all degrees of G,
||Mplus||<=1+2c2. The existence claim is not conditioned on an empty feasible
set: the supplied G is already a member.

The asymptotic proposition quantifies EVERY family F and real c1,c2,c3,c4,
assumes WholeScaling_W3 AND validity, THEN quantifies EVERY sample-dependent
graph selection H_k(y) which maximizes Vplus over the row's feasible graphs
for EVERY k and EVERY y. It concludes:

* For every k, ||Mplus(d_k,G_k)||<=1+2c2, and for every k,y the true-graph
  corrected estimate is no larger than the selected maximum.
* Each of the following estimates is conservative, in the exact one-sided
  scaled probability sense defined above: Vplus on the true graph; Vplus on
  the selected graph; VYoung; min(selected Vplus,VYoung).
* IF for EVERY k there EXISTS a natural D_k such that h_i=D_k for EVERY
  vertex in that row, THEN V2prime is also conservative.

No bound on the supplied d_i, their truncated h_i, or the rowwise common D_k
is assumed; only the true graph degrees obey c2. There is no nesting or size
monotonicity premise, homoskedasticity premise, common-mean premise, or
independence of the selected graph from the sample. Pointwise maximizer
values are measurable because they equal the maximum of finitely many
continuous functions (even without measurable tie breaking of H itself).

Junk-value audit: n>0 throughout finite assertions and family sizes are
positive. Natural subtraction n-1 is truncated, but n>=1 makes it the usual
nonnegative number; g0-1 in the displayed formula is REAL subtraction after
casting and the premise g0>=1 removes any boundary concern. The definition
a_i=0 when h_i=0 is an explicit substantive convention, so it does not use
the spurious real inverse 1/0=0 to set a_i=1. Feasibility forces g_i=0 at
such vertices. The alternative diagonal formula also branches at h_i=0;
it correctly leaves residual diagonal entry 1 there. All other cap divisions
occur in the positive branch or with D>=1. Finite sums over zero edges and
isolated vertices are intentional. Maxima are attained in a finite nonempty
set; no supremum of an empty or unbounded set is used. Scaling yields the
moment existence and finite probabilities described for T3. There is no
liminf, quantile, sqrt, log, rpow, or partial inverse in T5's closure.
