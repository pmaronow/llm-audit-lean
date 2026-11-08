# Blind reading

This file was written from `SAP/P008b/Defs.lean`, all seven Defs parts,
`SAP/P008b/Challenge.lean`, and `Challenge/Part1.lean`, before opening either
`claims.json` or `record.json`. The Challenge has thirteen theorems. Each theorem
asserts the proposition named `TxxStatement`; it has no additional parameters or
hypotheses outside that proposition. The readings below include all its conjuncts.

## Common objects and conventions, expanded

* `Assignment N` is the set of all functions from `{0,...,N-1}` to `{false,true}`.
  Write `z_i` for the numerical indicator `bit (z i)`, equal to 1 for true and 0
  for false, and `z[i:=b]` for replacement of coordinate i by b.
* A `FiniteLaw Ω` on a finite type Ω consists of real weights q(z) >= 0 whose sum
  is 1. There is no assumption of strictly positive weights. Its expectation is
  `E_Q f = sum_z q(z) f(z)` and its probability of any predicate A is
  `sum_{z:A(z)} q(z)`. Its covariance is
  `E_Q[(f-E_Q f)(g-E_Q g)]`; its variance is covariance with itself.
  The uniform law assigns mass `1/card Ω` to each element and requires Ω nonempty.
* `marginal Q F i b = E_Q[F(z[i:=b])]`. Thus this averages the overwritten
  potential outcome over the original Q, equivalently over its marginal law of
  coordinates other than i. It is not defined as a conditional expectation.
* `Plane = EuclideanSpace R (Fin 2)` is the real Euclidean plane with its L2
  distance, not the maximum norm on a bare product. A `SpatialModel N` supplies
  an arbitrary subset X of that plane, a point s_i in X for each i, a measure ζ
  on the plane's standard Borel measurable space, and a real function Y(x,z).
  The structure does not require distinct nodes, measurable X, measurable Y,
  finite ζ, positive N, or any relation between ζ and area/arc length.
* The circle `C_i(d)` is `{x in X : dist(s_i,x)=d}`. Set
  `mu_i,d = ζ restricted to C_i(d)` and
  `m_i,d = (mu_i,d(whole plane)).toReal`. For a real f,
  `A_i,d(f) = (m_i,d)^(-1) integral f dmu_i,d`.
  `validCircle i d` means `0 < m_i,d`, `mu_i,d(whole plane) != infinity`,
  and, for every assignment z, Y(.,z) is integrable for mu_i,d.
  These conditions give genuinely positive finite mass and genuine integrals.
* Write `M_i(d,z)=A_i,d(Y(.,z))`, `m_i(b,d)=E_Q M_i(d,z[i:=b])`,
  `tau_i(x)=E_Q Y(x,z[i:=true])-E_Q Y(x,z[i:=false])`, and
  `tau_i(d)=m_i(true,d)-m_i(false,d)`.
  `amr Q d = N^(-1) sum_i tau_i(d)`.
  The analogous `finiteAMR Q M` for any real array M_i(z) is
  `N^(-1) sum_i (E_Q M_i(z[i:=true])-E_Q M_i(z[i:=false]))`.
* The band `B_i(d,k)` is `{x in X : d-k <= dist(s_i,x) <= d+k}`,
  and `bandAverage` is the integral over ζ restricted to this band divided by
  the real mass of that restricted measure. `disk i d` is
  `{x in X : dist(s_i,x)<=d}`.
* `nT(z)=sum_i z_i`, `nC(z)=N-nT(z)` (a subtraction in R).
  `hajek M z = (sum_i z_i M_i(z))/nT(z)
                - (sum_i (1-z_i) M_i(z))/nC(z)`.
  `completedHajek M e z` is e if either arm count is zero and is this contrast
  otherwise. The completion e is a single real constant.
* `countMean S f = (sum_{x in S} f(x))/card(S)`.
  Every division in these definitions is real division; inverse zero is zero.
  Consequently a bare mean over an empty finite set is zero, and the bare Hajek
  expression also has totalized zero-denominator values. The readings below
  specify where theorems exclude these cases.
* Mathlib's real `Metric.infDist x S` is the infimum of distances to a nonempty
  S. It is `ENNReal.toReal (infEDist x S)` and is **zero for empty S**.
  Also `ENNReal.toReal infinity = 0`. The real Bochner integral is **zero for a
  non-integrable function**. `Integrable` requires almost-everywhere strong
  measurability and finite integral of the norm. Restriction of a measure is
  Mathlib's restriction, defined even for a nonmeasurable restricting set; on
  any measurable test set T it has value ζ(T intersection S).
* The topology is the usual Euclidean topology. `interior P` is the largest
  open subset of P and `frontier P = closure P minus interior P`.
* A finite-set difference removes elements of the second set. Finset sums count
  each element once. Fin indices use the indicated finite ranges. Natural
  subtraction `j-1` occurs in `bufferRule`; all its noninitial uses in the theorem
  are guarded by `0<j`. Differences of buffer cardinalities in denominators are
  differences in R, not truncated natural subtraction.

The Mathlib definitions were followed in `Analysis/InnerProductSpace/PiL2.lean`
(EuclideanSpace), `Topology/MetricSpace/HausdorffDistance.lean` (infDist),
`MeasureTheory/Measure/Restrict.lean`,
`MeasureTheory/Function/L1Space/Integrable.lean`,
`MeasureTheory/Integral/Bochner/Basic.lean`, `Topology/Defs/Basic.lean`,
`Logic/Function/Basic.lean` (coordinate update), and
`Order/Filter/{Defs,AtTopBot/Defs}.lean` (limits).

## SAP.P008b.T15

For every natural N, spatial model P with N nodes, index i, real d, and real k,
in that order, if `d>=0` and `k>=0`, both of the following hold:

1. For every assignment z, if the restricted band mass has strictly positive
   real value, that mass is not infinity, and Y(.,z) is integrable on the band,
   then the band average of Y(.,z) is exactly the inverse mass times its integral
   on `{x in X : d-k <= dist(s_i,x) <= d+k}`. This is an expansion of the
   definition of bandAverage, with its natural domain conditions stated.
2. If `0<d-k` and every other node satisfies `dist(s_i,s_j)>d+k`, then
   `{j : s_j in B_i(d,k)}` is empty. No mass or integrability assumptions are
   attached to this second assertion.

There is no explicit N>0 assumption, but the quantified index i exists only for
positive N. Distinct nodes are not assumed outside the displayed separation
condition. No statement about a polygon edge average is present.

## SAP.P008b.T16

This is a closed, concrete conjunction, not a universally quantified claim about
arbitrary polygons. For c=0,1,2,3 let
`rho_c=(0,19/8,27/8,35/8)` and `y_c=(4,2,0,8)`.
There are two rectangular boundaries, the boundaries of
`[100i,100i+1] x [-1,1]` for i=0,1. Eight outcome points, indexed (j,c), are
`(100j+1+rho_c,0)`. Their distance to rectangle i's boundary is `rho_i(j,c)`.
The outcome at (j,c) under assignment z is `z_0*y_c` if j=0 and is 0 if j=1.
The buffer of rectangle i at r selects all eight points with boundary distance
at most r. The centered set selects those at boundary distances in [3,5].
The three arrays of node means use respectively the added cells
`buffer_i(4) minus buffer_i(2)`, the centered set, and `buffer_i(4)`.
For the assignment `(true,false)`, the theorem asserts all of:

* For every i,c, `rho_i(i,c)=rho_c`. For every i,j,c with i != j,
  `rho_i(j,c)>5`.
* Rectangle 0's radius-2 buffer has one point and outcome sum 4; its radius-4
  buffer has three points and outcome sum 6.
* Every one of the three means for node 1 is zero.
* The three Hajek contrasts are respectively 1, 4, and 2, and the first and
  second are unequal. This assignment has one treated and one control node.
* Independently of the plane embedding, on the four indices c the mean over
  `rho_c<=4` minus `rho_c<=2` is 1, the mean over `3<=rho_c<=5` is 4,
  and the mean over `rho_c<=4` is 2.

## SAP.P008b.T17

This proposition conjoins six groups of assertions:

1. For every p,x in the plane and real d>0, the distance from x to the full
   Euclidean circle `{q : dist(q,p)=d}` is `abs(dist(x,p)-d)`.
2. For every p,x,d,k, if d>0 and k>=0, being within k of that circle is equivalent
   to `max(0,d-k)<=dist(x,p)<=d+k`. Under these same hypotheses, **if additionally
   k<=d**, the un-clipped difference `(d+k)-(d-k)` is `2k`.
3. The real numerical equalities `4-1=3`, `4+1=5`, and `5-3=2`.
4. For every N,P,i,d, `P.disk i d` is exactly
   `{x in X : dist(s_i,x)<=d}`. No sign condition on d is needed for this
   definitional equality.
5. For every type X with decidable equality, sequence of finite subsets B_j, and
   real-valued Y: if B_0 is nonempty, `bufferRule B Y 0=countMean B_0 Y`.
   For every j>0, if `B_(j-1) subset B_j` and their cardinalities strictly
   increase, then `bufferRule B Y j=countMean (B_j minus B_(j-1)) Y`.
   Here bufferRule is the first full-buffer mean at j=0, and, at j>0, is
   `(sum_{B_j}Y-sum_{B_(j-1)}Y)/(card B_j-card B_(j-1))`.
6. For every type X, finite C, real functions rho,Y, and real a,b, if rho is
   nonnegative on C, a<b, and the cardinalities of `{x in C:rho(x)<=a}` and
   `{x in C:rho(x)<=b}` strictly increase, their difference-of-sums divided by
   their difference-of-cardinalities equals the mean over
   `{x in C:a<rho(x)<=b}`. Furthermore `(a+b)/2-a=(b-a)/2`,
   `b-(a+b)/2=(b-a)/2`, `b-a>0`, and `(a+b)/2<b`.

The last two means have nonzero denominators by their cardinality hypotheses.
There is no theorem identifying an arbitrary polygon's zero buffer with its area.

## SAP.P008b.T18

Let `K(r)=2 exp(-2r)-(128/3) r^4 exp(-4r)`. First the theorem asserts, for every
real r>=0, `K(r)>-384/437`, and asserts `-384/437>-1`.

Then, universally for a natural C, any finite law Q on four-bit assignments,
any base values b_c, and real arrays r_ic and w_ic, if all weights are
nonnegative, each row of weights sums to 1, and every r_ic is nonnegative,
the following hold. Define
`Y_a(c,z)=b_c+sum_{j=0}^3 z_j a K(r_jc)` and
`AMR_a=(1/4)sum_i sum_c w_ic [E_Q Y_a(c,z[i:=true])
                             -E_Q Y_a(c,z[i:=false])]`.

* For every real amplitude a, index i, cell c, and assignment z, in that order,
  the coordinate-update difference of Y_a is `a K(r_ic)`.
* For every a,i,c, its Q-marginalized difference is also `a K(r_ic)`.
* For every a, `AMR_a=(1/4)sum_i sum_c w_ic a K(r_ic)`.
* `AMR_3=3 AMR_1`, `AMR_1>-384/437`, `AMR_1>-1`, and
  `AMR_1 != -126/100`.

Q need not be Bernoulli or uniform. There are no hypotheses on the base values,
no relation imposed between the distance array and actual coordinates, and no
fixed raster size. C=0 cannot satisfy the row-sum hypotheses; positive C can.

## SAP.P008b.T19

The cell universe is `(u,v)` with 0<=u<20 and 0<=v<10. The two polygon cell sets
are `L_i<=u<L_i+5, 2<=v<7`, where L_0=2 and L_1=12. Their boundaries select
the outer rows or columns (`u=L_i` or `u=L_i+4` or v=2 or v=6).
The outcome is `z_0` on `3<=u<=5,3<=v<=5` and is zero elsewhere.
Let E_i(z) and A_i(z) be the corresponding boundary and whole-polygon cell means.
The theorem asserts, without external hypotheses:

* There are 200 cells, every polygon has 25 cells, and every boundary has 16.
* For every i and every cell c in its polygon, c is on the boundary iff at least
  one of its eight integer-lattice neighbors is outside that polygon. Precisely,
  there exist a,b in {0,1,2}, not both 1, such that
  `(u+a-1<L_i or u+a-1>=L_i+5 or v+b-1<2 or v+b-1>=7)`.
* Every outcome for every assignment is either 0 or 1.
* For every i,z, E_i(z)=0; for every i,z,
  `A_i(z)=(9/25)z_0` if i=0 and 0 if i=1.
* The uniform law on the four two-bit assignments is common independent
  Bernoulli(1/2), in the precise sense
  `q(z)=product_i (if z_i=1 then 1/2 else 1-1/2)`.
  Assignment `(true,false)` has mass 1/4.
* On that assignment the boundary Hajek contrast is 0 and the area contrast is
  9/25. The finiteAMRs under the uniform law are respectively 0 and 9/50.
  Also `0 != 9/25`.
* Each polygon has nine cells outside its boundary. At `(true,false)`, its
  outcome sum is 9 for polygon 0 and 0 for polygon 1.
* For every i the area-mean marginalized own-node effect is 9/25 for i=0 and
  0 otherwise. On the displayed assignment nT=nC=1.

## SAP.P008b.T20

Four groups of conclusions are conjoined:

1. Universally for any finite subset R of the integer lattice and any real
   Y on that lattice, assume its raster boundary is nonempty. For every x,
   x is on that boundary iff x belongs to R and one of the eight offsets
   `(a-1,b-1)`, a,b in {0,1,2} not both 1, gives a point outside R.
   The raster edge-zero average is the sum over this boundary divided by its
   cardinality; the raster area average is the sum over R divided by card R.
2. In the fixed 5x5 block indexed by {0,...,4} squared, there are 25 cells,
   16 boundary cells (a coordinate is 0 or 4), and nine nonboundary cells.
   For every cell, boundary membership is equivalent to an eight-neighbor step
   leaving the block, with integer coordinates. For every cell, nonboundary
   membership is equivalent to both coordinates lying between 1 and 3 inclusive.
3. For every subset P of the plane whose frontier is nonempty,
   `{x:infDist(x,frontier P)=0}=frontier P`; and for every x in interior P,
   `infDist(x,frontier P)>0`.
4. For exactly the fixed two-polygon raster in T19, the Hajek contrasts on
   `(true,false)` are 0 and 9/25, and the uniform-design finiteAMRs are 0 and
   9/50, for boundary and area means respectively.

## SAP.P008b.T21

A single closed strict inequality of real rational numbers:
`-321/10000 < -19/625`, i.e. `-0.0321 < -0.0304`.
There is no random variable, assignment law, quantile, significance level, or
statistical inference in the proposition.

## SAP.P008b.T22

A single closed disjunction of strict inequalities of real rational numbers:
`619/50 < -797/100 or 797/100 < 619/50`,
i.e. `12.38 < -7.97 or 7.97 < 12.38`.
It encodes falling outside a printed interval. There is no randomization
distribution, quantile definition, null hypothesis, or assertion of error rate.

## SAP.P008b.T23

For every finite type Ω (with a Fintype structure), natural N, finite law Q on Ω,
array of real functions phi_i on Ω, real array D_ij, and real cutoff c, in that
order, assume that for every i,j, `D_ij>c` implies
`Cov_Q(phi_i,phi_j)=0`. Then
`sum_i sum_j Cov_Q(phi_i,phi_j) 1{D_ij<=c}
 = Var_Q(z -> sum_i phi_i(z))`.

N may be zero. D need not be a metric, nonnegative, or symmetric, and c has no
sign restriction. Q's normalization precludes an empty Ω. All functions are
finite real arrays, so there are no integration issues. This is a population
covariance identity, with no estimated covariance matrix, interval, coverage,
or asymptotic assertion.

## SAP.P008b.T25

This proposition has four universally quantified conjuncts:

1. For every N,P,Q,i,d, if the circle at i,d is valid, then for every b,
   `m_i(b,d)=A_i,d(x -> E_Q Y(x,z[i:=b]))`, and
   `tau_i(d)=A_i,d(tau_i)`.
2. For every N,P,Q,d, if N>0 and every circle at this d is valid, then
   `amr Q d = N^(-1) sum_i A_i,d(tau_i)`.
3. For every real-valued function F on four-bit assignments, every i in
   {0,1,2,3}, and every b,
   `E_uniform F(z[i:=b])=(1/8) sum_{z:z_i=b} F(z)`.
4. For every F and i, the difference of its two uniform overwrite means equals
   `(1/8)sum_{z:z_i=true}F(z) - (1/8)sum_{z:z_i=false}F(z)`.

The first two conjuncts allow any finite Q, without independent treatment.
No whole-field measurability is assumed in this proposition.

## SAP.P008b.T26

The first conjunct quantifies N,P, then assumes N>0, measurable field X, and the
sharp null `Y(x,z)=Y(x,all-false)` for every x in X and every assignment z.
Then, for every finite assignment law Q, it asserts:

* For every i and x in X, `tau_i(x)=0`.
* For every i,d with valid circle, `tau_i(d)=0`.
* For every d for which all circles are valid, `amr Q d=0`.

The second conjunct is an independent finite example on rational coordinates:
the field is {-1,0,1}, there is a single node at 0, and the potential outcome
is `z_0` at 1, `-z_0` at -1, and 0 elsewhere. A radius-d circle is the subset of
this field satisfying the real equality `abs(x-0)=d`, and M is its counting mean.
It asserts 0 is in the field; the radius-0 circle has one point; the radius-1
circle has two points; and for **every** one-bit law Q and **every** real d,
**if this finite circle is nonempty**, its finiteAMR is zero. Nevertheless the
outcome at 1 differs between the assignments true and false.
There is no claim about AMRs at empty circles in this witness, and it uses the
finite rational-line definitions, not a SpatialModel carrying a plane measure.

## SAP.P008b.T27

There are two universal implications:

1. For every N,P,Q, real base function b on the plane, and real coefficients
   g_i(x), if for every x in X and z,
   `Y(x,z)=b(x)+sum_j z_j g_j(x)`, then every i and x in X satisfy
   `tau_i(x)=g_i(x)`. Furthermore, for every real d, if N>0, X is measurable,
   and all radius-d circles are valid, then for every i,
   `tau_i(d)=A_i,d(g_i)`, and
   `amr Q d=N^(-1)sum_i A_i,d(g_i)`.
2. For every N,P,Q,b and single real function g on R, if for every x in X and z,
   `Y(x,z)=b(x)+sum_j z_j g(dist(s_j,x))`, then for every i and x in X,
   `tau_i(x)=g(dist(s_i,x))`. Furthermore, for every d, if N>0, X is measurable,
   and all radius-d circles are valid, then for every i,
   `tau_i(d)=g(d)`, and `amr Q d=g(d)`.

Neither point-effect conclusion requires N>0 or field measurability beyond the
existence of an index i; those extra hypotheses govern the circle conclusions.
Q is any finite assignment law, and no separate measurability or integrability
is imposed on b or g. Circle validity requires integrability of all Y(.,z).

## SAP.P008b.T28

In order, quantify a sequence Q_n of finite laws on `(n+1)`-bit assignments,
a sequence M_n,i(z) of real arrays, reals p,H,e, and a natural D. Assume:

* `0<p<1` and `H>=0`;
* for every n,z,
  `q_n(z)=product_{i=0}^n (if z_i=1 then p else 1-p)`;
* for every n,i,z, `abs(M_n,i(z))<=H`;
* for every n there exists a symmetric relation G_n on the node indices such
  that every node has at most D **other** related nodes, and the following
  collection independence holds. For every disjoint finite index sets A,B
  with no G_n edge between them, and every two predicates P,R on full arrays
  `u_i in {false,true} x R`, if P depends only on coordinates in A and R only
  on coordinates in B, then
  `Q_n(P((z_i,M_n,i(z))_i) and R((z_i,M_n,i(z))_i))
   = Q_n(P((z_i,M_n,i(z))_i)) Q_n(R((z_i,M_n,i(z))_i))`.
  A predicate depends only on A precisely when agreement of any two full
  arrays on A implies equivalence of the predicate on those arrays. G_n can
  change with n and may have arbitrary self-loops. D is fixed across n.

Then for every real epsilon>0,
`Q_n(abs(completedHajek M_n e z - finiteAMR Q_n M_n)>epsilon) -> 0`
as n tends to infinity. Here convergence means: for every real tolerance
delta>0, this nonnegative probability is less than delta for all sufficiently
large natural n. The target finiteAMR can change with n; its convergence to a
fixed real number is not required. The empty-arm value e is any fixed real,
independent of n and z. Neither coordinates nor a circle representation of M
are part of the hypotheses. No variance lower bound, central limit theorem,
normal approximation, covariance estimator, or confidence interval is asserted.
