# Blind reading

Saved before opening either `claims.json` or `record.json`. This reading uses only
the Defs and Challenge sources and the Mathlib definitions they invoke. Source
docstrings are not treated as additional hypotheses.

## Common objects and definitions

* `Graph n` is a Boolean symmetric, loopless adjacency function on the **labelled**
  vertex set `Fin n`. Write its real adjacency matrix as A: entries are 1 on
  edges, 0 elsewhere. Its degree at i is the number of adjacent vertices. Every
  double sum below is over **ordered** vertex pairs. `oracleMatrix G` is I+A,
  where Mathlib's matrix 1 is the identity matrix, not the all-ones matrix.
* `Compatible R d G` means every edge of R belongs to G and, separately, each
  degree of G is at most the supplied natural-number cap d_i. It imposes no bound
  on d_i itself. `Maximizes R d f G` means G is compatible and, for **every**
  compatible graph B, f(B) <= f(G). This is a global maximum, with ties allowed.
* For a real vector x on n vertices, bar(x) = (sum_i x_i)/n,
  z_i = x_i-bar(x), s²(x) = (sum_i z_i²)/n, and
  Q(M,x) = sum_i sum_j M_ij x_i x_j. Thus
  V1(G,x) = [sum_i z_i² + Q(A,z)]/n²,
  V2(G,x) = [s²(x)/n][1 + (sum_ij A_ij)/n], and
  V2prime(d,x) = [s²(x)/n][1 + (sum_i min(d_i,n-1))/n].
  `n-1` in the cap is natural subtraction. All statistical uses below have n>0.
* A `Model n` consists of a probability measure mu on R^n with its coordinate
  product Borel sigma algebra, a fixed real weight vector theta, and fixed graphs
  G,R and natural caps d. There is no compatibility, independence, integrability,
  or mean-model condition in the structure itself. Put X_i(y)=theta_i y_i,
  bhat(y)=n^{-1} sum_i X_i(y), b=E[bhat], and
  v=E[(bhat-E[bhat])²]. These are the SAP `weighted`, `betaHat`, `beta`, and `var`.
  E is the Mathlib Bochner integral against mu. Off its integrable domain that
  integral is defined to be zero; the finite-moment/boundedness hypotheses below
  must therefore be retained in interpreting these as ordinary moments.
* `covariance m i j` = E[(X_i-E X_i)(X_j-E X_j)]. `Homoskedastic m`
  says these diagonal entries are equal for **all** i,j: it concerns the weighted
  coordinates, not necessarily the raw coordinates, and does not require equal
  coordinate means or positive coordinate variances. `covOf m f g` is instead
  E[fg]-E[f]E[g], used below for raw coordinate covariances under finite moments.
* `VariableDependency mu G X` says that for every two finite vertex sets S,T,
  **if** they are disjoint and every G-edge between them is absent, **then** the
  random vectors (X_i)_{i in S} and (X_j)_{j in T} are independent under mu.
  Mathlib `IndepFun` is independence of the two inverse-image sigma algebras;
  here the coordinate vectors are measurable. `Dependency m` applies this to
  **raw** coordinates y_i, hence also gives the corresponding independence for
  their fixed scalar multiples. It is stronger than pairwise independence alone.
* A `Family F` gives positive sizes n_k, n_k -> infinity, and a separate model
  m_k on R^{n_k} for every natural k. `Nested F` additionally requires n_k to be
  nondecreasing and, for every k, the existence of an injection of the k-th
  vertex set into the (k+1)-st that preserves and reflects G-adjacency. There is
  no common probability space, consistency of laws between rows, compatibility
  of those injections, or preservation of weights, R, or d in this definition.
* `Scaling F c1 c2 c3 c4` is the conjunction, in order, of: Nested F;
  c1>0, c2>0, c3>0, c4>0; Dependency m_k for every k;
  for every k, almost surely **all** i satisfy |X_{ki}-b_k|<=c1;
  deg(G_k,i)<=c2 for every k,i; n_k v_k -> c3;
  and |theta_{ki}|<c4 for every k,i. The bound is about b_k, the single
  expectation of the row average, rather than about each E[X_{ki}]. Because
  coordinates are Borel measurable and b_k is a real number, the bound makes
  each weighted coordinate essentially bounded and therefore square integrable.
  It does not force each raw coordinate to be integrable when its weight is zero.
  `Valid F` separately says Compatible R_k d_k G_k for every k.
* P_k(E) = mu_k(E).toReal. Mathlib measures apply to all sets by the associated
  outer measure, so no measurability is implicit in this notation. Probability
  finiteness implies 0<=P_k(E)<=1 for every E; `toReal` is not taking infinity to
  zero in these uses. Thus all coverage liminfs below are bounded real liminfs.
* `InProbability F T a` means: for **every real epsilon>0**,
  P_k(|T_k-a_k|>epsilon) -> 0 as k->infinity.
  `Conservative F V` means: for **every real epsilon>0**,
  P_k(n_k(v_k-V_k)>epsilon) -> 0. It controls only underestimation, scaled by n_k.
  `scaledTrue_k=n_k v_k` and `scaledOracle_k(y)=n_k V1(G_k,X_k(y))`.
* Phi is the cdf of Mathlib's real Gaussian measure with mean 0 and variance 1.
  q_alpha = inf{t in R : 1-alpha/2 <= Phi(t)}. Every coverage assertion below
  restricts 0<alpha<1, where this is the ordinary finite positive normal critical
  value. `coverage m V alpha` is P(|bhat-b|<=q_alpha sqrt(max(V,0))).
  `printedCoverage` is P(0<=V AND |bhat-b|<=q_alpha sqrt(V)). In Mathlib real sqrt
  is zero on nonpositive inputs; the explicit nonnegativity conjunct in printed
  coverage prevents negative values from being silently treated as valid radii.
  `ConservativeCoverage F V` says for every 0<alpha<1 that
  liminf_k coverage_k >= 1-alpha; `PrintedConservativeCoverage` uses the printed
  event instead. The order liminf is supremum of eventual lower bounds.
* `standardized m(y)=(bhat(y)-b)/sqrt(v)`. Zero division is totalized in R, but
  T38 explicitly includes eventual v>0.
* `MeanModel m D bvec` says every raw coordinate y_i is integrable and
  E[y_i]=(D bvec)_i for every i. For a real n-by-p matrix D,
  ols(D,y)=(D^T D)^{-1}D^T y and
  olsTheta(D)=n[(D^T D)^{-1}D^T]. Matrix multiplication, transpose, and scalar
  multiplication have their ordinary meanings. Mathlib's square-matrix inverse
  is zero for singular real matrices; every OLS assertion below explicitly
  requires det(D^T D) != 0, excluding that convention.
* gFactor(m)=1+(sum_ij A(G)_ij)/n.
  `PSD M` means both M_ij=M_ji for all i,j and Q(M,x)>=0 for **every** real vector x.
  The capacity matrix C(R,h)=I+A(R)+diag(h_i-deg_R(i)); its subtraction is in R,
  not truncated natural subtraction. Its diagonal is 1+h_i-deg_R(i).

## Each theorem

### SAP.P011c.T29

A conjunction of two independent universal assertions:

1. For every natural n,p, if n>0, then for every Model m on n vertices, real
   n-by-p design D, and real p-vector bvec, if det(D^T D)!=0 and MeanModel m D
   bvec, then (a) for every coefficient j and **every raw outcome vector y**,
   ols(D,y)_j = (sum_i olsTheta(D)_{ji} y_i)/n, and (b) for every j,
   E[ols(D,y)_j]=bvec_j. Model m's own theta,G,R,d are unrestricted here.
2. For every n>0 and every Model m on n vertices, if every raw coordinate belongs
   to Mathlib MemLp 2 (measurable up to null sets and finite second moment), then
   v = [sum_i sum_j theta_i theta_j
   (E[y_i y_j]-E[y_i]E[y_j])]/n².

The p=0 case of the first assertion has no coefficient j; the second assertion
is still independent and unrestricted in p.

### SAP.P011c.T31

The **negation** of this universal statement: for every Family F and then every
four real constants c1,c2,c3,c4, Scaling F c1 c2 c3 c4 implies
InProbability F scaledOracle scaledTrue. Classically it asserts that there
exist such F and constants satisfying all Scaling hypotheses for which some
epsilon>0 has P_k(|n_k V1(G_k,X_k)-n_k v_k|>epsilon) failing to converge to zero.
There is no Valid or homoskedasticity hypothesis.

### SAP.P011c.T32

The **negation** of the following universal implication, with quantifiers in
this order: every F; every c1,c2,c3,c4; Scaling F c1 c2 c3 c4; Valid F; every
selector A_k(y) of a graph for each row and **every** raw y; if for all k,y the
selected graph globally maximizes B -> V1(B,X_k(y)) subject to R_k,d_k, then
Conservative F [V1(A_k(y),X_k(y))], **and**, if every m_k is homoskedastic, that
same conservativeness conclusion. Thus the final conjunction is logically
equivalent to its first component. A witness must satisfy Scaling and Valid,
provide a maximizer for every raw y, and fail conservativeness. A need not be
assumed measurable; its optimal objective value is determined by finitely many
continuous functions. The assertion does not demand a homoskedastic witness.

### SAP.P011c.T33

The **negation** of the universal assertion: for every F and four constants,
Scaling and Valid imply that for every selector A_k(y) which, for all k,y,
maximizes V1 under R_k,d_k, PrintedConservativeCoverage holds for
V_k(y)=V1(A_k(y),X_k(y)). Equivalently there are such data and a maximizing
selector for which some alpha in (0,1) has printed coverage liminf strictly
less than 1-alpha. Negative V realizations are excluded from the coverage event.

### SAP.P011c.T34

For every Family F and then every four real constants, if Scaling holds, then
for **every** natural row k,
1 <= 1 + (sum_ij A(G_k)_ij)/n_k <= 1+c2.
It does not assume homoskedasticity or Valid, and asserts no estimator
consistency, convergence in mean square, correlation bound, or domination.

### SAP.P011c.T35

The **negation** of this universal assertion: for every F and four constants,
Scaling and Valid imply that for every natural p, coefficient j in Fin p,
sequence of real n_k-by-p matrices D_k, and fixed real p-vector bvec, if
every Gram matrix is nonsingular, every row has MeanModel m_k D_k bvec,
and theta_{ki}=olsTheta(D_k)_{ji} for every k,i, then for every graph selector
A_k(y) which globally maximizes V1 for every k,y subject to R_k,d_k, both
Conservative F [V1(A_k(y),X_k(y))] and PrintedConservativeCoverage for this
same variance estimator hold. An existential counterexample therefore must
have p>0 (because j is supplied), the specified OLS weights and a fixed correct
integrable mean model; it may fail either of the two final conclusions or both.

### SAP.P011c.T36

For every F and then every four constants, Scaling and homoskedasticity of
**every** row imply Conservative F [V2(G_k,X_k(y))]. There is no Valid condition,
no estimated graph, and no assertion that this oracle estimator is inconsistent
in any example or in general.

### SAP.P011c.T37

For every F and four constants, if Scaling holds, every row is homoskedastic,
and Valid holds, then for **every** selector A_k(y), if it globally maximizes
B -> V2(B,X_k(y)) over compatible graphs for all k,y, both
Conservative F [V2(A_k(y),X_k(y))] and
Conservative F [V2prime(d_k,X_k(y))] hold. There is no upper bound on supplied
caps d; each cap is reduced to min(d_i,n_k-1) inside V2prime. The selector has
no separate measurability hypothesis.

### SAP.P011c.T38

For every F and four constants, Scaling implies the conjunction of (1) v_k>0
for all sufficiently large k, and (2) for **every** real threshold t,
P_k((bhat_k-b_k)/sqrt(v_k)<=t) -> Phi(t). The quantifier over thresholds follows
the entire Scaling antecedent. No graph-constraint validity or homoskedasticity
is assumed. This is a cdf version of a standard normal central limit theorem.

### SAP.P011c.T39

For every F and four constants, if Scaling holds, then for **every** sequence
of statistics V_k:R^{n_k}->R, if **every V_k is Borel measurable**, the following
two implications both hold:

1. InProbability of n_k V_k to n_k v_k implies: for **every** real alpha with
   0<alpha<1, clipped coverage_k -> 1-alpha.
2. Conservative F V implies: for **every** 0<alpha<1, the liminf of clipped
   coverage_k is at least 1-alpha.

Measurability is with respect to the fixed raw Borel space, not merely its
completion under the row law. No nonnegativity of V is assumed: clipping is
part of the defined coverage event. No maximization, Valid, or homoskedasticity
is required. Neither implication assumes its coverage conclusion.

### SAP.P011c.T40

For every F and four constants, if Scaling holds, every row is homoskedastic,
and Valid holds, then for every selector A_k(y) globally maximizing V2 under
R_k,d_k for **all** k,y, PrintedConservativeCoverage holds **both** for
V2(A_k(y),X_k(y)) and for V2prime(d_k,X_k(y)). These are un-clipped events with
an explicit nonnegativity requirement; both formulae are in fact nonnegative
for all raw outcomes. No extra measurability of A is assumed.

### SAP.P011c.T41

A conjunction of two independent universal assertions:

1. For every natural n (including zero), every Graph R on n vertices, and every
   natural-valued vector h, if 2 deg_R(i)-1 <= h_i in **real** arithmetic for
   every vertex i, then C(R,h) is symmetric with nonnegative quadratic form on
   every real vector, and, **if n>0**, for every real vector delta,
   Q(C(R,h),delta)/n >= 0. There is no requirement h_i>=deg_R(i) except what
   the displayed capacity condition entails, and no matrix decomposition is
   asserted. At n=0 PSD is the ordinary empty-matrix assertion; normalization
   is only claimed for n>0.
2. For every natural n, Graph R, natural cap vector d, **arbitrary** real-valued
   graph objective f, real c, and Graph A, A globally maximizes B -> f(B)+c
   over Compatible R d if and only if it globally maximizes f there. The same
   c is used for every candidate B; no nonempty feasible-set hypothesis is
   required for the equivalence.

## Mathlib definitions checked

The concrete definitions inspected were matrix identity/diagonal and nonsingular
inverse; Bochner integral's nonintegrable-zero convention; MemLp; probability
measure normalization and real-valued measure; independence via inverse-image
sigma algebras; GaussianReal and its cdf; coordinate measurability; real square
root; and the order definition of filter liminf. The probability bound [0,1],
finite moments, positive sizes, and explicit Gram invertibility above are
mathematically relevant safeguards, not implicit extra assumptions.
