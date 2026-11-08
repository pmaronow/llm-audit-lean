# Blind reading of the Challenge statements

Saved at stage 1, before opening `claims.json` or `record.json`. This reads the
types of the 13 Challenge theorems, including their definitions; it does not
infer a stronger assertion from their names or comments. Each Challenge theorem
has no explicit arguments and asserts the entire proposition `TxxStatement`
described below. Universally quantified arguments inside each proposition are
listed in their order. Separate conjuncts have independent quantifiers.

## Common objects and conventions

* `Assignment N` is the set of all Boolean vectors indexed by `Fin N`, hence
  exactly the (2^N) assignments, including the unique empty vector if (N=0).
  `bit true=1` and `bit false=0`, as real numbers. `update z i b` replaces just
  coordinate (i) by (b).
* A `FiniteLaw Ω` requires a finite enumerated type Ω, real masses (q_z\ge0),
  and (\sum_{z\in\Omega}q_z=1). It cannot exist on an empty Ω. Its expectation,
  event probability, covariance and variance are respectively
  (E_Q f=\sum_z q_z f(z)), (Q(A)=\sum_{z\in A}q_z),
  (\operatorname{Cov}_Q(f,g)=E_Q[(f-E_Qf)(g-E_Qg)]), and
  (\operatorname{Var}_Q f=\operatorname{Cov}_Q(f,f)).
  `uniformLaw Ω` additionally requires Ω nonempty and gives every point mass
  (1/|\Omega|).
* `marginal Q F i b` means (E_Q[F(Z^{i\leftarrow b})]). Thus it averages over
  the unconditional marginal law of all coordinates other than (i), obtained
  by overwriting (i) in each full vector. It is not defined as a conditional
  expectation given (Z_i=b), and it does not by definition assert independence.
* `Plane` is Mathlib's `EuclideanSpace ℝ (Fin 2)`, i.e. the two-coordinate
  (\ell^2) space, with its usual Euclidean distance and Borel measurable
  structure. `WithLp.toLp 2 ![u,v]` is the point with coordinates ((u,v)).
  A `SpatialModel N` consists of an arbitrary set (F\subseteq\mathbb R^2),
  locations (s_i\in F) for every (i<N), an arbitrary nonnegative measure ζ
  on the plane, and real potential outcomes (Y(x,z)). Distinctness of node
  locations, whole-field measurability, finite ζ, and independent assignment are
  not built into this structure.
* For a spatial model, write (C_i(d)=\{x\in F:|x-s_i|=d\}),
  (\mu_{i,d}=\zeta\mathbin{|}_{C_i(d)}), (c_{i,d}=\mu_{i,d}(\mathbb R^2))
  converted from extended nonnegative reals to reals, and
  (A_{i,d}(f)=c_{i,d}^{-1}\int f\,d\mu_{i,d}). These are exactly `circle`,
  `circleMeasure`, `circleMass`, and `average`. Write
  (M_i(d,z)=A_{i,d}(Y(\cdot,z))),
  (y_{i,b}(x)=E_QY(x,Z^{i\leftarrow b})),
  (\tau_i(x)=y_{i,1}(x)-y_{i,0}(x)),
  (m_{i,b}(d)=E_QM_i(d,Z^{i\leftarrow b})),
  (\tau_i(d)=m_{i,1}(d)-m_{i,0}(d)), and
  (\operatorname{AMR}(d)=N^{-1}\sum_{i<N}\tau_i(d)).
  These names expand `M`, `marginalY`, `pointEffect`, `m`, `nodeEffect`, `amr`.
* `validCircle i d` means, in order: (0<c_{i,d}),
  (\mu_{i,d}(\mathbb R^2)\ne\infty), and, for every assignment (z),
  (Y(\cdot,z)) is integrable with respect to this restricted measure. Mathlib
  integrability means almost-everywhere strong measurability and finite integral
  of the norm. The first two conditions give a genuine positive finite
  normalizing mass. They do not select arclength or a particular ζ.
* The band is (B_i(d,k)=\{x\in F:d-k\le |x-s_i|\le d+k\});
  its `bandAverage` is the integral under ζ restricted to this set, divided by
  that restriction's total real mass. The disk is
  (D_i(d)=\{x\in F:|x-s_i|\le d\}).
* For any finite set (S), `countMean S f` is (\sum_{x\in S}f(x)/|S|).
  For outcome summaries (M_i(z)), put (n_1(z)=\sum_i\operatorname{bit}(z_i))
  and (n_0(z)=N-n_1(z)). This subtraction is in ℝ, not truncated natural
  subtraction. `hajek M z` is
  (\widehat\tau_M(z)=\sum_i z_iM_i(z)/n_1(z)-\sum_i(1-z_i)M_i(z)/n_0(z)).
  `finiteAMR Q M` is
  (N^{-1}\sum_i(E_QM_i(Z^{i\leftarrow1})-E_QM_i(Z^{i\leftarrow0}))).
* All real divisions are total: (1/0=0). `ENNReal.toReal` sends infinity to
  zero. Mathlib's Bochner integral is zero for a nonintegrable real integrand.
  Mathlib's `Metric.infDist x S` is the ordinary infimum distance when (S)
  is nonempty but is zero when (S=\varnothing). These are conventions of the
  underlying definitions, not additional hypotheses. The conditions in the
  individual propositions below must be checked before reading an expression
  as a genuine average or a distance to a nonempty set.

The Mathlib definitions were followed at
`Analysis/InnerProductSpace/PiL2.lean:114`,
`MeasureTheory/Measure/Restrict.lean:43–51`,
`MeasureTheory/Function/L1Space/Integrable.lean:59`,
`MeasureTheory/Integral/Bochner/Basic.lean:158–164,204`,
`Topology/MetricSpace/HausdorffDistance.lean:76,463–477`,
`Topology/Defs/Basic.lean:122–131`, and `Order/Filter/Defs.lean:422`.
SAP's finite sums, probabilities and covariances are its own definitions, not
invocations of a different Mathlib probability or covariance convention.

## SAP.P008b.T15

For every natural (N), spatial model (P), node (i\in\mathrm{Fin}(N)),
and real (d,k), assume first (d\ge0) and then (k\ge0). The conclusion is
the conjunction of:

1. For every assignment (z), if the band restriction has positive real total
   mass, has extended total mass different from infinity, and (Y(\cdot,z))
   is integrable under it, in that order, then its `bandAverage` equals the
   explicitly written normalized integral over
   (\{x\in F:d-k\le |x-s_i|\le d+k\}). This equality unfolds the definition;
   it asserts neither convergence of a circle approximation nor an estimator
   identity. Integrability is assumed separately for each (z) in this branch.
2. If (0<d-k), and then every other node (j\ne i) satisfies
   (d+k<|s_i-s_j|), the set of node indices whose locations belong to the
   band is empty. This branch has no mass or integrability assumption.

There is no field-measurability hypothesis. The existence of (i\in\mathrm{Fin}(N))
already forces (N>0); separation is imposed only in the second branch.

## SAP.P008b.T16

This is an unconditional conjunction about explicit objects, not a universal
claim about all polygon configurations. There are rectangles

\[P_i=[100i,100i+1]\times[-1,1],\quad i=0,1.\]

`donutPolygonBoundary` explicitly describes their four sides, including
corners. The eight cell locations are

\[x_{i,c}=(100i+1+r_c,0),\quad
  (r_0,r_1,r_2,r_3)=(0,19/8,27/8,35/8),\]

with outcomes (Y_{0,c}(z)=z_0v_c), (Y_{1,c}(z)=0),

\[(v_0,v_1,v_2,v_3)=(4,2,0,8).\]

Let (\rho_i(j,c)=\inf_{y\in\partial P_i}|x_{j,c}-y|).
`donutSpatialBuffer i r` selects all eight cell indices with (\rho_i\le r),
and `donutSpatialCentered i` selects those with (3\le\rho_i\le5).
The three summaries `donutSpatialMeans mode` use, respectively, the set
difference (B_i(4)\setminus B_i(2)), the centered set, and (B_i(4)), with
equal-weight arithmetic means. For the assignment (z=(1,0)) the proposition
asserts all of the following:

* For every (i,c), (\rho_i(i,c)=r_c); for every (i,j,c), if (i\ne j)
  then (\rho_i(j,c)>5).
* (B_0(2)) has one cell and outcome sum 4; (B_0(4)) has three cells and
  outcome sum 6.
* For every mode the summary for polygon 1 is zero. The three Hájek contrasts
  are 1, 4, and 2, and the first and second are unequal.
* Independently, selecting directly from the four numbers (r_c), the mean
  of (v_c) on (2<r_c\le4) is 1, on (3\le r_c\le5) is 4, and on
  (r_c\le4) is 2.

No assignment law is quantified or used; (z=(1,0)) has one treated and one
control node. The full-buffer mode is a boundary-distance buffer, including its
zero-distance cells, rather than a formally identified whole polygon.

## SAP.P008b.T17

This is a conjunction of six independent blocks:

1. For all plane points (p,x) and real (d>0),
   (\operatorname{dist}(x,\{q:|q-p|=d\})=\big||x-p|-d\big|).
2. For all (p,x,d,k), if (d>0) and (k\ge0), distance at most (k) from
   that circle is equivalent to
   (\max(0,d-k)\le|x-p|\le d+k). Under these same hypotheses, if also
   (k\le d), the difference of the two *unclipped* radial endpoints is
   ((d+k)-(d-k)=2k). No assertion that the clipped interval has width (2k)
   when (k>d) is made.
3. The real numerical identities (4-1=3), (4+1=5), (5-3=2).
4. For every (N,P,i,d\in\mathbb R) (with (N) natural and (i<N)),
   `P.disk i d` equals (\{x\in F:|x-s_i|\le d\}), without a radius-sign
   hypothesis. This unfolds a definition.
5. For every type (X) with decidable equality, sequence (B_j) of finite
   subsets of (X), and real function (Y\) on (X), let `bufferRule` at
   index zero be the mean on (B_0), and at (j>0) be
   
   \[\frac{\sum_{x\in B_j}Y(x)-\sum_{x\in B_{j-1}}Y(x)}
           {|B_j|-|B_{j-1}|}.\]
   
   If (B_0\ne\varnothing), the zero-index rule equals that full-buffer
   mean. For every (j>0), if (B_{j-1}\subseteq B_j) and then
   (|B_{j-1}|<|B_j|), the rule equals the mean on
   (B_j\setminus B_{j-1}). The denominator subtraction is in ℝ; only the
   index (j-1) uses natural subtraction, guarded by (j>0).
6. For every type (X), finite (C\subseteq X), real functions (\rho,Y),
   and real (a,b), assume (\rho(x)\ge0) for (x\in C), then (a<b),
   then strict cardinality growth between
   (B(a)=\{x\in C:\rho(x)\le a\}) and (B(b)). The quotient of their
   outcome-sum difference by their cardinality difference equals the mean
   over (\{x\in C:a<\rho(x)\le b\}). Also the midpoint (m=(a+b)/2)
   satisfies (m-a=(b-a)/2), (b-m=(b-a)/2), (b-a>0), and (m<b).
   The function (\rho) is supplied numerical data, not required here to be
   an actual geometric distance. The strict growth prevents an empty mean.

## SAP.P008b.T18

Define the real kernel

\[h(r)=2e^{-2r}-(128/3)r^4e^{-4r}.\]

First, for every real (r\ge0), (h(r)>-384/437). Second,

\[-1<-384/437.\]

Third, for every natural number of cells (C), probability law (Q) on all
four-node assignments, baseline (b:\mathrm{Fin}(C)\to\mathbb R), and arrays

\[r,w:\mathrm{Fin}(4)\times\mathrm{Fin}(C)\to\mathbb R,\]

assume, in order, (w_{ic}\ge0) for all (i,c),

\[\sum_c w_{ic}=1\quad\text{for each }i,\qquad r_{ic}\ge0\quad\text{for all }i,c.\]

The outcome at cell (c), amplitude (a), and assignment (z) is

\[Y_a(c,z)=b_c+\sum_{j<4}z_j a h(r_{jc}).\]

The defined toy AMR is one quarter the sum over nodes and cells of the weights
times their overwrite-marginal contrasts. Under the preceding assumptions:

* For every real (a), node (i), cell (c), and assignment (z), in that
  order, (Y_a(c,z^{i\leftarrow1})-Y_a(c,z^{i\leftarrow0})=a h(r_{ic})).
* For every (a,i,c), the analogous difference of (Q)-marginal means also
  equals (a h(r_{ic})).
* For every (a), the toy AMR equals
  (\frac14\sum_i\sum_c w_{ic}a h(r_{ic})).
* Its amplitude-three value is three times its amplitude-one value; its
  amplitude-one value is strictly greater than (-384/437), hence strictly
  greater than (-1), and is unequal to (-126/100=-1.26).

Neither independent assignment nor a geometric realization of (r\) is assumed.
There is no assertion about the numerical AMR at amplitude three. Although (C=0)
is quantified, the four weight-sum hypotheses force (C>0).

## SAP.P008b.T19

There are 200 combinatorial raster cells ((u,v)\in\mathrm{Fin}(20)\times
\mathrm{Fin}(10)). The documented center interpretation is ((u+1/2,v+1/2));
the formulas use integer cell indices. Polygon 0 consists of columns 2 through
6, polygon 1 of columns 12 through 16, both with rows 2 through 6. Their
boundaries are the outer rows and columns. The outcome is (z_0) on columns
3 through 5 and rows 3 through 5, and zero on every other cell.
`polygonRasterEdgeM` and `polygonRasterAreaM` are the means on these boundary
and full-cell sets, respectively.

The unconditional proposition asserts, in order:

* The raster cardinality is 200. For every polygon index (i), the full set
  has 25 cells and its boundary has 16.
* For every (i,c), if (c) is in polygon (i), then it is a boundary cell
  iff some one of its eight neighboring cells has a coordinate outside the
  polygon's integer ranges. The offsets are (a-1,b-1) for (a,b\in\{0,1,2}),
  excluding (a=b=1); arithmetic after the coordinate casts is integer
  arithmetic, so negative neighbors are not truncated.
* For every cell (c) and assignment (z), the outcome is 0 or 1. For every
  (i,z), the boundary mean is zero and the area mean is
  ((9/25)z_0) if (i=0), zero otherwise.
* The uniform law on the four assignments has product Bernoulli parameter
  (1/2); its mass at (z=(1,0)) is (1/4).
* At (z=(1,0)), the boundary and area Hájek contrasts are 0 and (9/25).
  Under the uniform law their finite AMRs are 0 and (9/50). Also (0\ne9/25).
* For every (i), the interior-cell set has cardinality 9; the total outcome
  over the polygon at (z=(1,0)) is 9 for (i=0), zero otherwise.
* For every (i), the area-mean marginal contrast is (9/25) for (i=0),
  zero otherwise. Finally (n_1(1,0)=n_0(1,0)=1).

These are explicit examples and identities with no external hypotheses.

## SAP.P008b.T20

This is a conjunction of four blocks:

1. For every finite (R\subseteq\mathbb Z^2) and real outcome (Y) on the
   lattice, if `rasterBoundary R` is nonempty, then: for every lattice point
   (x), membership in that boundary means (x\in R) and at least one of
   the eight neighbors (x+(a-1,b-1)), (a,b\in\{0,1,2}),
   ((a,b)\ne(1,1)), is outside (R); the edge-zero average is the sum of
   (Y) on this boundary divided by its cardinality; and the area average is
   the sum on (R) divided by (|R|). Nonempty boundary also forces (R)
   nonempty. The three equalities/membership descriptions unfold definitions.
2. The (5\times5) block `Fin 5 × Fin 5` has 25 cells, 16 outer-edge cells,
   and 9 remaining cells. For every block cell its boundary membership is
   equivalent to an eight-neighbor step leaving the integer range
   ([0,5)\times[0,5)). For every cell, membership in the remaining set is
   equivalent to both coordinates lying between 1 and 3 inclusive.
3. For every set (P\subseteq\mathbb R^2), if its topological frontier is
   nonempty, then the set of plane points at zero infimum distance from that
   frontier equals the frontier, and every (x\in\operatorname{interior}(P))
   has strictly positive distance from it. Mathlib's frontier is
   (\overline P\setminus\operatorname{interior}(P)); it is closed. No
   convexity, polygonality or measurability of (P) is assumed. The positive
   distance assertion concerns interior points only, not all points of (P).
4. The explicit raster of T19 again has boundary and area Hájek contrasts
   0 and (9/25) at ((1,0)), and respective uniform-law AMRs 0 and (9/50).

The proposition does not identify a fitted curve or assert a general
inequality between every boundary average and its polygon's area average.

## SAP.P008b.T21

There are no variables or hypotheses. The entire statement is the strict
real inequality

\[-321/10000<-19/625,\quad\text{i.e. }-0.0321<-0.0304.\]

It supplies no randomization distribution, quantile definition or inference.

## SAP.P008b.T22

There are no variables or hypotheses. The entire statement is the disjunction

\[619/50<-797/100\quad\lor\quad797/100<619/50.\]

Thus the real number (12.38) lies strictly outside ([-7.97,7.97]) (the
second disjunct is true). This only evaluates a strict rejection rule at three
numbers. No data-generating model, permutation law, quantile property, test
level or frequentist error bound is asserted.

## SAP.P008b.T23

For every type Ω equipped with a finite enumeration, natural (N),
probability law (Q) on Ω, family of real functions

\[\phi_i:\Omega\to\mathbb R\quad(i<N),\]

array (D:\mathrm{Fin}(N)^2\to\mathbb R), and real cutoff (c), in that
order, assume

\[\forall i,j,\quad c<D_{ij}\Longrightarrow
          \operatorname{Cov}_Q(\phi_i,\phi_j)=0.\]

Then

\[\sum_i\sum_j\operatorname{Cov}_Q(\phi_i,\phi_j)
          \mathbf1\{D_{ij}\le c\}
  =\operatorname{Var}_Q\left(\sum_i\phi_i\right).\]

No symmetry, nonnegativity, triangle inequality, diagonal condition or spatial
realization is required of (D); no positivity is required of (c). The sums
include ordered pairs and diagonal terms. (N=0) is allowed and gives (0=0),
but nonempty (N) is also allowed. Ω cannot be empty because (Q) is normalized.
The statement is an identity of *population covariances*, with a zero-tail
covariance premise. It does not define or validate a sample HAC estimator or
an interval.

## SAP.P008b.T25

Four independent universally quantified assertions are conjoined:

1. For every (N,P,Q,i,d), in that order, if circle (C_i(d)) is valid,
   then for every Boolean (b),
   (m_{i,b}(d)=A_{i,d}(y_{i,b})), and also
   (\tau_i(d)=A_{i,d}(\tau_i(\cdot))).
2. For every (N,P,Q,d), if first (N>0) and then every node's circle at
   (d) is valid, then
   (\operatorname{AMR}(d)=N^{-1}\sum_i A_{i,d}(\tau_i(\cdot))).
3. For every real function (Y) on the 16 four-node assignments, node
   (i\in\mathrm{Fin}(4)), and Boolean (b), the overwrite-marginal under
   the uniform law is
   
   \[E[Y(Z^{i\leftarrow b})]=\tfrac18\sum_{z:z_i=b}Y(z).\]
4. For every such (Y,i), the treated-minus-control overwrite-marginal
   contrast is the treated-group sum divided by 8 minus the control-group
   sum divided by 8.

The spatial clauses have no field-measurability or assignment-independence
hypothesis and use an arbitrary supplied ζ. The finite clauses do not assert
anything about a specific numerical toy outcome.

## SAP.P008b.T26

The first block quantifies (N,P), then assumes (N>0), measurable (F),
and the sharp null

\[\forall x\in F,\ \forall z,\quad Y(x,z)=Y(x,0).\]

Only after these assumptions does it quantify every assignment law (Q).
Its conclusion has three parts: for every (i,x\in F), (\tau_i(x)=0);
for every (i,d), validity of that circle implies (\tau_i(d)=0); and for
every (d), validity of all node circles implies (\operatorname{AMR}(d)=0).
The (N>0) and field-measurability premises scope over even the pointwise
conclusion; they are not confined syntactically to the AMR clause.

The second block is an explicit finite-field example. The field is

\[X=\{-1,0,1\}\subset\mathbb Q\]

with one intervention node at 0 and outcomes

\[Y(1,z)=z_0,\quad Y(-1,z)=-z_0,\quad Y(0,z)=0.\]

`realLineCircle` selects elements of (X) with rational absolute distance
from 0, cast to ℝ, equal to the real radius (d); `realLineM` uses the
counting mean on this selected set. The statement asserts: 0 belongs to the
field; the radius-zero circle has one point and the radius-one circle two;
for every probability law (Q) on the two one-node assignments and every
real (d), if the circle is nonempty its finite AMR is zero; yet

\[Y(1,(1))\ne Y(1,(0)).\]

The example's nonempty radii are exactly 0 and 1. No assertion is made for
empty circles and no embedding as a `SpatialModel` is part of the statement.
Its nonzero point effect and cancellation use nonempty sets, not (0/0).

## SAP.P008b.T27

The first block quantifies, in order, (N,P,Q), a real function (b) on the
plane, and real coefficient functions (g_i) on the plane. Assume

\[\forall x\in F,\ \forall z,\quad
  Y(x,z)=b(x)+\sum_{j<N}z_jg_j(x).\]

Then (i) for every (i,x\in F), (\tau_i(x)=g_i(x)); and (ii) for every
real (d), if (N>0), then (F) is measurable, then all node circles at


(d) are valid, the conclusions are, for every (i),

\[\tau_i(d)=A_{i,d}(g_i),\qquad
  \operatorname{AMR}(d)=N^{-1}\sum_i A_{i,d}(g_i).\]

The second block independently quantifies (N,P,Q,b), and a real radial
function (g:\mathbb R\to\mathbb R). Assume the same additive expression
with coefficients (g_j(x)=g(|s_j-x|)). Then for every (i,x\in F),

\[\tau_i(x)=g(|s_i-x|).\]

For every (d), under the subsequent assumptions (N>0), measurable (F),
and validity of all circles at (d), every node effect equals (g(d)) and
the AMR equals (g(d)). There is no independent integrability assumption on


(b,g_i,g); the validity requirement applies to every potential outcome on
each circle. The pointwise conclusions require neither measurable (F) nor
valid circles nor an explicit positive-(N) premise. No assignment-design
hypothesis is imposed beyond (Q) being a probability law.

## SAP.P008b.T28

For every sequence (Q_n) of probability laws on assignments of (n+1)
nodes, sequence of real node summaries

\[M_n:\mathrm{Fin}(n+1)\times\{0,1\}^{n+1}\to\mathbb R,\]

and fixed real numbers (p,H,e) and fixed natural (D), in that order,
assume, in order:

1. (p>0), then (p<1), then (H\ge0).
2. For every (n) and every (z),
   (Q_n(z)=\prod_{i<n+1}(p\text{ if }z_i=1\text{ else }1-p)).
   Thus treatment coordinates are independent with one common, fixed success
   probability at every sample size.
3. For every (n,i,z), (|M_n(i,z)|\le H).
4. For every (n), there exists a binary relation (G_n) on its node indices
   such that it is symmetric, every node has at most (D) *other* neighbors,
   and the following collection independence holds. For all finite sets of
   node indices (A,B), if they are disjoint and there is no (G_n) edge from
   (A) to (B), then for every pair of predicates (P,R) on vectors of
   Boolean-real pairs, where (P) depends only on coordinates in (A) and
   (R) only on coordinates in (B),
   
   \[Q_n(P(U)\land R(U))=Q_n(P(U))Q_n(R(U)),
     \quad U_i(z)=(z_i,M_n(i,z)).\]
   
   Here `dependsOn P A` means: for every two pair-vectors (u,v), agreement
   of their coordinates throughout (A) implies (P(u)\leftrightarrow P(v)).
   The graph is allowed to change with (n); symmetry is required even on
   diagonal entries, whose presence does not affect the degree count. This
   is independence of arbitrary predicates of separated collections, not
   merely vanishing pairwise covariances or pairwise independence.

Define (\widehat\tau^e_n(z)=e) if (n_1(z)=0) or (n_0(z)=0), and otherwise
the Hájek contrast of (M_n). The conclusion is: for every real (\epsilon>0),

\[Q_n\left(\left|\widehat\tau^e_n-
          \operatorname{finiteAMR}(Q_n,M_n)\right|>\epsilon\right)
       \longrightarrow0\quad(n\longrightarrow\infty).\]

Mathlib's `Tendsto ... atTop (nhds 0)` is ordinary real convergence of this
sequence: every neighborhood of zero eventually contains it. The constants


(p,H,e,D) are chosen before all sample-size and error quantifiers. The target
AMR can vary with (n), and need not have a limit. There is no geometric
circle model required of (M_n), nor a central limit theorem, variance
normalization, HAC estimator, or coverage/type-I-error conclusion.
