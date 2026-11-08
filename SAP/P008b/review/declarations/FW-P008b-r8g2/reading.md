# Blind reading

Saved before opening either `claims.json` or `record.json`. Sources read: all five
Challenge docstrings and theorem types, every source declaration named in
`closure.json`, and all 29 distinct generated auxiliary declarations, printed by
`scratch/PrintClosure.lean` (output in `scratch/PrintClosure.out`). The generated
declarations only establish finite-index bounds, nonemptiness, positivity and
normalization for the uniform law, or numeral elaboration; none adds a statistical
assumption. Source line numbers below refer to the supplied files.

## Conventions used in the fully unfolded readings

The spatial plane is the Mathlib Euclidean space `EuclideanSpace ℝ (Fin 2)`.
An assignment on N nodes is a function from `Fin N` to `Bool`. Write
`e(true)=1`, `e(false)=0` as real numbers. A finite law on a finite type Ω is a
function w:Ω→ℝ, with w(z)≥0 for every z and Σz w(z)=1. Its expectation is
Ew[f]=Σz w(z)f(z), its event probability is Σ over the elements satisfying the
event, its covariance is Ew[(f−Ew[f])(g−Ew[g])], and its variance is covariance
with itself. These are ordinary finite sums, with no measure-theoretic default.
Uniform law on a nonempty finite Ω means w(z)=1/|Ω|.

For an assignment z, let nt(z)=Σi e(z(i)) and nc(z)=N−nt(z), both real numbers.
For real assignment-dependent node summaries A(i,z), the Hajek expression is
`Σi e(z(i))A(i,z)/nt(z) − Σi (1−e(z(i)))A(i,z)/nc(z)`.
The finite marginal at own treatment b is
`Σz w(z) F(update(z,i,b))`, where update replaces coordinate i by b. Thus it
uses the *unconditional marginal distribution of the other coordinates*, not
their conditional law given z(i)=b. The finite AMR is
`(1/N) Σi [Σz w(z) A(i,update(z,i,true)) −
            Σz w(z) A(i,update(z,i,false))]`.
For a finite set C, its counting mean of f is `(Σx∈C f(x))/|C|`.
These formulas are definitions, not independence or unbiasedness assertions.

## SAP.P008b.T20

Location: `SAP/P008b/Challenge/Part1.lean:58–61`; full proposition is
`SAP/P008b/Defs/Part6.lean:70–91`.

The statement is a conjunction of four parts, in this order:

1. Universally quantify a finite set R of integer-coordinate pairs, then an
   arbitrary real function Y on integer-coordinate pairs. Define B(R) to be the
   elements x of R with at least one missing neighbour among the eight offsets
   `(a−1,b−1)` for a,b∈{0,1,2}, excluding (a,b)=(1,1). Assume B(R) is nonempty.
   Conclude, together: for every x, x∈B(R) iff x∈R and such a neighbour is outside
   R; the boundary summary equals `(Σx∈B(R) Y(x))/|B(R)|`; and the area summary
   equals `(Σx∈R Y(x))/|R|`. Both summaries are precisely those counting means by
   definition.
2. On the index square C={0,1,2,3,4}², define B to consist of the cells whose
   first or second coordinate is 0 or 4. Assert |C|=25, |B|=16, |C\B|=9.
   For every cell c, assert c∈B iff one of the eight integer offsets moves at
   least one coordinate below 0 or to at least 5. For every c, assert c∈C\B
   iff both coordinates lie between 1 and 3 inclusive.
3. For every subset P of the Euclidean plane, assume its topological frontier
   is nonempty. Assert that the set of all plane points at Mathlib `Metric.infDist`
   zero from that frontier is exactly the frontier, and, for every x in the
   topological interior of P, the infimum distance from x to the frontier is
   strictly positive. This is an assertion about the frontier, not distance
   to the filled set P, and asserts no integration formula for continuous
   boundary means.
4. Use a fixed raster with indices (u,v)∈{0,…,19}×{0,…,9}. Polygon 0 has cells
   2≤u<7, 2≤v<7; polygon 1 has 12≤u<17, 2≤v<7. Their raster boundaries are the
   outer rows and columns (u equal to the left endpoint or left endpoint+4,
   or v=2 or 6). At assignment z∈{false,true}², the outcome is e(z(0)) for
   3≤u≤5 and 3≤v≤5, and zero elsewhere. Let Aedge(i,z) be the counting mean
   on polygon i's boundary and Aarea(i,z) its counting mean on all 25 cells.
   Assert Hajek(Aedge,(true,false))=0,
   Hajek(Aarea,(true,false))=9/25. Assert also the finite AMR formula above
   for these same summaries is respectively 0 and 9/50 when w(z)=1/4 on all
   four assignments. This law is exactly two independent fair Boolean draws.

The docstring describes discrete boundary versus whole-polygon summaries and
continuous zero-boundary-distance sets, disclosing nonempty boundaries/frontiers
and omission of a fitted-curve sentence. No canonical comparison is made here.

Junk-value audit:

- Real division by zero is defined as zero. In part 1 the nonempty boundary
  makes both denominators positive, because B(R)⊆R. The fixed polygon boundaries
  have 16 cells and the polygons 25. Both assignment arms in the sole Hajek
  evaluation contain one node. The finite AMRs have N=2. None of these uses a
  zero denominator. The uniform law has four assignments and positive mass 1/4.
- `Metric.infDist x S` is `ENNReal.toReal` of the infimum of extended distances
  to S. It is zero when S is empty. The nonempty-frontier premise excludes this
  convention, and distances to a nonempty set in a metric space have finite
  infimum. The frontier is closed, so zero distance indeed characterizes it.
- Integer neighbour arithmetic occurs in ℤ: casting the finite natural indices
  before adding them to an integer and subtracting 1 permits negative
  neighbours. This is not truncated natural subtraction. The finite index
  inequalities in the fixture use natural numbers without subtraction.
- There are no logarithms, square roots, real powers, Bochner integrals,
  partial-function defaults, unbounded real suprema/infima or sequence limits
  in this proposition beyond the explicitly discussed distance infimum.
- The raster outcome and left-endpoint definitions use total conditionals; the
  second branch of the latter is polygon 1 since the index is `Fin 2`.

## SAP.P008b.T21

Location: `SAP/P008b/Challenge/Part1.lean:63–66`; proposition at
`SAP/P008b/Defs/Part6.lean:94`.

There are no objects to quantify and no hypotheses. The entire proposition is
the real-number inequality `−321/10000 < −19/625`, equivalently
`−0.0321 < −0.0304`. It does not define a probability law, quantiles, a statistic,
an empirical data set, or a significance decision. The docstring says exactly
that it retains only the printed numerical comparison and lists the omitted
assignment-law, significance, and empirical conclusions.

Junk-value audit: both denominators are positive natural numerals coerced to
real numbers. No empty types, truncated subtraction, partial functions, logarithms,
roots, powers, integration, `toReal`, suprema/infima or limits are involved.

## SAP.P008b.T22

Location: `SAP/P008b/Challenge/Part1.lean:68–77`; main proposition at
`SAP/P008b/Defs/WholeW1.lean:133–156`. The docstring calls the printed claim false
on the basis of this constructed experiment.

The proposition has three conjuncts. The first is existential, in the order
P then a. P is a spatial model on four nodes: a set F in the Euclidean plane;
four node coordinates in F (distinctness is not required); an arbitrary measure
ζ on the plane; and a real outcome Y(x,z) for every plane point x and Boolean
four-node assignment z. The map a sends six indices k∈{0,…,5} to assignments.

For node i and radius d, C(i,d)={x∈F:dist(node(i),x)=d}; μ(i,d) is ζ restricted
to C(i,d); t(i,d)=μ(i,d)(univ).toReal; and
`A(i,d,z) = (1/t(i,d)) ∫x Y(x,z) dμ(i,d)`.
The statistic S(j,k), for j∈{0,…,4}, is the Hajek expression using these four
summaries at radius d(j)=(j+1)/10 and assignment a(k). All distances here use
the ordinary Euclidean metric of Plane.

For a real sequence s indexed by `Fin (n+1)`, the quantile function at q is
defined by h=nq, j=min(toNat(floor(h)),n), g=h−j, and
`(1−g)s(j)+g s(min(j+1,n))`. It does not itself demand sortedness or q∈[0,1].
The actual sequences below are required to be monotone and q is 1/40 or 39/40,
so this is the usual type-7 interpolation for six sorted observations (n=5).

The existential conjunction requires all the following:

- a is injective; for every assignment z, exactly two entries of z are true
  iff z=a(k) for some k. Thus it enumerates all six two-treated assignments.
- For every k, both real arm counts nt(a(k)) and nc(a(k)) equal 2.
- The spatial sharp null holds: for every x∈F and every assignment z,
  Y(x,z)=Y(x,all-false).
- For every node i and every one of the five radii d(j), the mass t(i,d(j))
  is positive, μ(i,d(j))(univ) is not infinity, and every assignment-specific
  outcome function is Bochner integrable under μ(i,d(j)).
- For every i,j,z, A(i,d(j),z)=i as a real number, i∈{0,1,2,3}.
- For every j, k↦S(j,k) is monotone; its type-7 quantiles at 1/40 and 39/40
  are −15/8 and 15/8; the uniform probability over the six indices of strict
  rejection `S(j,k)<−15/8 or 15/8<S(j,k)` equals 1/3.
- The sequence k↦Σj S(j,k) is monotone; its same quantiles are −75/8 and 75/8;
  its strict rejection probability under that same uniform law is 1/3.
- The real inequality 1/20<1/3 holds.

The second conjunct universally quantifies a finite subset R of the six indices,
then assumes R is nonempty. It asserts its uniform probability is at least 1/6
and strictly greater than 1/20.

The third conjunct is only the fixed real disjunction
`619/50 < −797/100 or 797/100 < 619/50`, i.e. the number 12.38 is outside
[−7.97,7.97].

Consequences and limits visible without any canonical text: the design in the
example is uniform *conditional on exactly two treated nodes*, not four
independent Bernoulli assignments. The quantiles are interpolations of the
six exhaustive support values. There is no variable for a Monte Carlo replicate
count, no collection of independent replicate draws, and no joint probability
over an observed draw and random reference draws. The numerical finite-grid
failure is mathematically meaningful; whether it refutes the intended rule
depends on which rule and design are claimed.

Junk-value audit:

- Circle mass uses `ENNReal.toReal`, which maps infinity to zero; its positive
  mass and non-infinite hypotheses exclude both infinite and zero masses.
  Outcomes are expressly integrable, so the Bochner integral's zero fallback
  for nonintegrable functions is excluded. Circle restriction is Mathlib measure
  restriction; explicit measurable-set hypotheses are absent in this older
  model, though Euclidean spheres themselves are measurable. A finite atomic
  field can satisfy all conditions with genuinely measurable circles.
- Every Hajek denominator on the support equals 2. No statistic uses an empty
  treatment arm. The uniform law has six elements. All printed rational
  denominators, and the radius denominator 10, are nonzero.
- Natural treated counts sum 0/1 values; the separate nc subtraction is in ℝ.
  Coordinates and node indices are cast exactly to ℝ, without rounding.
- Quantile `Int.toNat` truncates negative integers to zero and its `min` caps
  indices. For the two probabilities actually used, h is respectively 1/8
  and 39/8, j is 0 or 4, and g is 1/8 or 7/8. Hence neither out-of-range
  extrapolation nor a default finite index occurs. n+1=6 is nonempty.
- The expression involves no logarithms, square roots, real powers, sequence
  limsups/liminfs or real sInf/sSup. Restriction to a radius with no mass would
  make an average zero in the general definition, but is forbidden here.
- Generated proof constants whose names mention `wholeLine`, `wholeSquare`,
  `wholeSquareCenter`, or T18 are only elaboration proofs for numerals; they
  introduce none of those unrelated fixtures into the proposition.

## SAP.P008b.T23

Location: `SAP/P008b/Challenge/Part1.lean:79–82`; full proposition at
`SAP/P008b/Defs/Part6.lean:101–106`.

Universally quantify, in order: a type Ω, a finite enumeration of Ω, a natural
number N, a finite probability law w on Ω, real functions φ(i,z) for each
i∈Fin N, a completely arbitrary real array D(i,j), and a real cutoff c.
Assume that for every ordered pair i,j, if c<D(i,j), then
`Σz w(z)(φ(i,z)−Σu w(u)φ(i,u))(φ(j,z)−Σu w(u)φ(j,u))=0`.

Conclude that the double sum of exactly those covariances, multiplied by
the indicator of D(i,j)≤c, equals
`Σz w(z)[Σi φ(i,z) − Σu w(u)Σi φ(i,u)]²`.
There is no symmetry, triangle inequality, nonnegativity or geometric
interpretation required of D. There is no random covariance estimator, residual
fitting, interval, estimated standard error, asymptotic assertion, or coverage
probability. The docstring discloses that it retains only this covariance
identity and omits the specific table, coverage, numerical cutoff and empirical
width comparison.

Junk-value audit: there is no division in this statement. An empty Ω cannot
carry a finite law, because total mass would be 0=1. N may be zero, in which
case all contribution sums and their variance are genuinely zero; this does not
make the proposition vacuous for positive N. Finite sums give every expectation
and covariance a defined real value. Conditional indicator branches have
ordinary exact semantics. No truncated subtraction, integration, `toReal`,
partial functions, logarithms, roots, real powers, unbounded infima/suprema or
sequence limits occur.

## SAP.P008b.T25

Location: `SAP/P008b/Challenge/Part1.lean:84–91`; full proposition at
`SAP/P008b/Defs/WholeW1.lean:165–182`.

The measured spatial model now has a type X with an arbitrary measurable-space
structure, injective coordinates c:X→Plane, N nodes x(i)∈X, an arbitrary
Mathlib metric-space structure δ on Plane, a measure ζ on X, and real outcomes
Y(x,z) for x∈X and Boolean assignments z. No ambient measurable subset of the
plane is required. Distances are δ(c(x),c(y)); C(i,d)={x:δ(c(x(i)),c(x))=d}.
For a set S⊆X and a real function f on X its region average is
`(1/(ζ(S)).toReal) ∫x f(x) d(ζ.restrict S)`.

For a law w on the assignments, write
`y(i,b,x)=Σz w(z)Y(x,update(z,i,b))` and
`τ(i,x)=y(i,true,x)−y(i,false,x)`.
Let A(i,d,z) be the region average of Y(·,z) on C(i,d),
`m(i,b,d)=Σz w(z)A(i,d,update(z,i,b))`,
`τnode(i,d)=m(i,true,d)−m(i,false,d)`, and
`AMR(d)=(1/N)Σi τnode(i,d)`.
These unfold every SAP operation in the theorem; all sums are finite.

The proposition is the conjunction of these four assertions:

1. For every X, its measurable structure, N, a model as above, a finite law w,
   a node i, and real d (in that order), assume: C(i,d) is measurable;
   `(ζ(C(i,d))).toReal>0`; ζ(C(i,d))≠∞; and, for every Boolean b and assignment
   z of nonzero w-mass, Y(·,update(z,i,b)) is integrable with respect to
   ζ restricted to C(i,d). Conclude, together: for every b,
   m(i,b,d) equals the region average of y(i,b,·) on C(i,d); and τnode(i,d)
   equals the region average of τ(i,·) on C(i,d).
2. Independently universally quantify X, its measurable structure, N, a model,
   a finite law w, and real d. Assume 0<N and the preceding valid-circle
   conditions for every node i. Conclude
   `AMR(d)=(1/N)Σi [(1/(ζ(C(i,d))).toReal)∫x τ(i,x) d(ζ.restrict C(i,d))]`.
3. For every real function Y on Boolean four-node assignments, every i∈Fin 4,
   and b∈Bool, assert
   `Σz (1/16)Y(update(z,i,b)) = (1/8)Σ{z:z(i)=b}Y(z)`.
4. For every such Y and every i, assert that the difference of the two marginal
   expressions with own treatment true and false equals the difference of those
   two eight-assignment means, with normalization 1/8 on each sum.

There is no independence premise for the first two finite-sum identities; they
use the unconditional other-coordinate distribution described above. The last
two use the uniform law on all 16 assignments, hence independent fair assignment.
No equality between an unconditional and a generally dependent conditional law
is asserted. The docstring presents these as general marginalization/integration
identities plus the four-node illustration.

Junk-value audit:

- `ENNReal.toReal ∞=0`, division by zero is zero, and nonintegrable real Bochner
  integrals default to zero. Measurability, positive finite mass and integrability
  exclude these defaults on all regions and outcome terms with nonzero mass.
  Terms with w(z)=0 may have nonintegrable outcome functions, but contribute
  exactly zero both to the finite marginal function and to the weighted average;
  the asserted identity does not exploit their integral fallback.
- A node i∈Fin N in the first assertion implies N>0; the second assertion
  explicitly requires N>0. Thus normalization by N never uses zero. The four-node
  assignment law has 16 elements, and both own-treatment slices have 8.
- d is an arbitrary real. Negative d produces an empty metric circle and cannot
  satisfy positive circle mass, so the valid-circle premise excludes that case.
  Radius zero is permitted when there is positive atomic mass at that node.
- The metric may differ from the Euclidean metric; each circle's measurable-set
  premise handles the lack of automatic compatibility with the chosen measurable
  structure. X need not be finite, but no conditional law or countably infinite
  sum is used. ζ may be globally infinite while all circles used have finite mass.
- There are no natural/int truncations, nontrivial casts, logarithms, roots, real
  powers, partial-function defaults, unbounded real infima/suprema or sequence
  limits in the actual assertion. Function.update is total on finite coordinates.

