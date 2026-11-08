# Blind reading

Saved before opening `claims.json` or `record.json`. This reading uses only the
Challenge docstrings, the elaborated dependency list, the indicated definitions,
and Mathlib semantics. No judgment against the canonical claims is made here.

## SAP.P008b.T26

Source: `SAP/P008b/Challenge/Part1.lean:93–101`; statement expanded from
`SAP/P008b/Defs/WholeW1.lean:192–202`.

### Objects and definitions

An assignment on N nodes is a function z : {0,...,N−1} → {false,true}.
`bit false = 0` and `bit true = 1`, as real numbers. A finite law Q consists of
real numbers q(z) ≥ 0 with ∑z q(z) = 1. Its expectation is the finite sum
E_Q f = ∑z q(z) f(z). Write z[i←b] for the function equal to z off i and to b
at i. The marginal operation is

    L_i^b(F) = ∑z q(z) F(z[i←b]).

This averages the other coordinates under their unconditional marginal law;
it is not conditioning the joint law on z_i=b. No independence or positive
probability for either own-treatment value is assumed in this theorem.

The spatial object consists of a type X with a sigma algebra, an injective map
c : X → R², N nodes a_i in X, an arbitrary metric δ on R², a countably additive
measure ζ on X, and real potential outcomes Y(x,z). R² here is Mathlib's
two-coordinate Euclidean real vector space (`EuclideanSpace R (Fin 2)`), but
δ is supplied separately and need not be its standard metric. Coordinates
need not be measurable. X itself is the field; no ambient subset is needed.
The model imposes neither global measurability/integrability of Y nor
sigma-finiteness of ζ.

For i and real d, set C_i(d)={x∈X : δ(c(a_i),c(x))=d}, μ_i,d=ζ restricted to
C_i(d), and s_i,d=ζ(C_i(d)). The definitions are

    A_i,d(f) = (s_i,d.toReal)⁻¹ ∫ f dμ_i,d,
    M_i(d,z) = A_i,d(x ↦ Y(x,z)),
    m_i(b,d) = ∑z q(z) M_i(d,z[i←b]),
    pointEffect_i(x) = ∑z q(z)Y(x,z[i←true])
                       − ∑z q(z)Y(x,z[i←false]),
    nodeEffect_i(d) = m_i(true,d) − m_i(false,d),
    AMR(d) = (N:R)⁻¹ ∑i nodeEffect_i(d).

`validCircle Q i d` means all of the following: C_i(d) is measurable;
0<s_i,d.toReal; s_i,d is not infinity; and, for each b and each z with
q(z)≠0, x↦Y(x,z[i←b]) is Bochner integrable for μ_i,d. Thus only the
outcomes used with nonzero weight in the two marginalizations must be
integrable. Integrable includes almost-everywhere strong measurability and
finite integral of the norm. `sharpNull` is ∀x ∀z,
Y(x,z)=Y(x,all-false).

### Quantifiers, hypotheses, conclusion

The theorem is a conjunction of the following universal assertion and a
concrete witness assertion.

1. For every X, every sigma algebra on X, every natural N, and every model
   just described: if the sharp null holds, then for every finite law Q:
   (a) for every i∈Fin N and every x∈X, pointEffect_i(x)=0;
   (b) for every i and every real d, validCircle Q i d implies
   nodeEffect_i(d)=0; and (c) for every real d, if N>0 and every node's circle
   is valid at d, then AMR(d)=0. The sharp-null hypothesis precedes the
   quantifier over Q, so this is genuinely uniform over all finite laws.
2. Fix X=Fin 3 with its standard discrete sigma algebra, c(x)=((x.val:R)−1,0),
   one node a_0=1 (the origin), the standard Euclidean metric, counting measure,
   and Y(x,z)=((x.val:R)−1) bit(z_0). Then (a) for every finite law Q on the
   one-node assignments, its radius-0 and radius-1 circles are valid;
   (b) for every such Q and every real d, validity of its radius-d circle
   implies AMR(d)=0; and (c) Y(2,[true])≠Y(2,[false]). These last two values
   are 1 and 0. The radius-0 circle is {1}, the radius-1 circle is {0,2},
   and all other radii give the empty circle. Outcomes cancel in the second
   circle and are zero in the first. This is a witness to failure of the
   converse of sharp-null ⇒ zero AMRs, not a refutation of that implication.

### Junk values and edge cases

Real inversion sends 0 to 0. `ENNReal.toReal` sends infinity to 0, and the
Bochner integral is defined as 0 for a nonintegrable function. Consequently
the unguarded average definition can return 0 for a zero/infinite-mass
circle or for a nonintegrable outcome. The valid-circle hypotheses exclude
all those possibilities for every nonzero-weight outcome used in each
asserted node effect/AMR. Zero-weight summands may still refer to such totalized
values, but multiplying by the zero weight eliminates them; they impose no
assertion about an undefined statistical quantity. Point effects use only
finite sums of real numbers and have no integration convention.

For N=0 the finite node index is empty, its sum is 0, and the unguarded
AMR definition is 0⁻¹·0=0. Every asserted AMR equality here requires N>0.
Point/node assertions over Fin 0 are empty universal statements, without
making the whole theorem vacuous. Assignments themselves are nonempty even
at N=0 (there is one empty function). A finite law on an empty sample type
would contradict its normalization, but the assignment types are nonempty.
Negative d gives an empty circle by the metric axioms and cannot be valid
when a node is present. Subtraction in coordinates and effects is in Q or R,
not truncated natural subtraction. All natural/rational casts are exact.
The Fin numerals used in the witness (0 in Fin 1 and 0,1,2 in Fin 3) are within
range. `wholeLine` uses the total coordinate-vector conversion `WithLp.toLp`;
there is no out-of-range access. Euclidean norms, when used for the witness,
take square roots of sums of squares, hence nonnegative arguments.
There is no logarithm, real power, infimum/supremum, limsup/liminf, or partial
function/default-value construction in this statement's definitions.

Closure read: `Assignment`, `bit`, `FiniteLaw` including `mass`, `mk`,
normalization and nonnegativity, `FiniteLaw.expect`, `marginal`, `Plane`
(`Defs/Part1.lean`); `finiteAMR` (`Defs/Part4.lean`); `MetricSpatialModel`
including `mk`, `coord`, `node`, `metric`, `ζ`, `Y`, `distance`, `circle`,
`regionAverage`, `M`, `marginalY`, `pointEffect`, `m`, `nodeEffect`, `amr`,
`validCircle`, `sharpNull`, `wholeLine`, `wholeCancellingModel`, and
`T26WholeStatement` (`Defs/WholeW1.lean`). The generated proofs were also
printed: `wholeLine._proof_1` is the dimension-2 instance;
`wholeCancellingModel._proof_1` proves coordinate injectivity by equality of
the first coordinates and injectivity of casts; `_proof_2` and `_proof_3`
certify that the Fin numeral moduli 3 and 1 are nonzero. They do not add
statistical assumptions.

## SAP.P008b.T27

Source: `SAP/P008b/Challenge/Part1.lean:103–110`; statement expanded from
`SAP/P008b/Defs/WholeW2.lean:145–161`.

### Objects and definitions

For this theorem, independently, N is natural; assignments, bits, a law Q,
its weights q(z), and the replacement-based marginal L_i^b are as follows:
assignments are Fin N→Bool, bits are 0 or 1 in R, q(z)≥0, ∑z q(z)=1, and
L_i^b(F)=∑z q(z)F(z[i←b]). Q may have arbitrary dependence and zero masses.
`Plane` is R² with its standard measurable space. A spatial model has a set
F⊆R², nodes a_i∈F, a measure ζ on R², and arbitrary real potential outcomes
Y(x,z) on the whole plane. The model requires no measurability of F or Y.

The quantified radius selector ρ:R²×R²→R is arbitrary: it is not required to
be a metric, symmetric, nonnegative, or measurable. In particular it includes
every metric on the coordinates. For i,d define

    C_i(d) = {x∈F : ρ(a_i,x)=d},
    μ_i,d = ζ.restrict C_i(d),   s_i,d = μ_i,d(R²),
    A_i,d(f) = (s_i,d.toReal)⁻¹ ∫ f dμ_i,d,
    M_i(d,z) = A_i,d(x ↦ Y(x,z)),
    effect_i(d) = ∑z q(z)M_i(d,z[i←true])
                  − ∑z q(z)M_i(d,z[i←false]),
    AMR(d) = (N:R)⁻¹ ∑i effect_i(d),
    pointEffect_i(x) = ∑z q(z)Y(x,z[i←true])
                       − ∑z q(z)Y(x,z[i←false]).

Here `validSelectedCircle ρ Q i d` is the conjunction
(a) 0<s_i,d.toReal, (b) s_i,d≠infinity, (c) μ_i,d-almost every x belongs
to C_i(d), and (d) for every b,z with q(z)≠0, x↦Y(x,z[i←b]) is Bochner
integrable for μ_i,d. The almost-everywhere clause says that the complement
of C_i(d) has μ_i,d outer measure zero. It matters because F and C_i(d)
are not explicitly required measurable: a restricted measure for an arbitrary
set need not otherwise be concentrated on that set.

For base:R²→R and coefficients g:Fin N→R²→R, `additiveOutcome` is

    base(x) + ∑k∈Fin N bit(z_k) g_k(x).

### Quantifiers, hypotheses, conclusion

The theorem is a conjunction of two universal assertions.

1. For every natural N, model P, law Q, selector ρ, function base, and
   coefficient family g, assume ∀x∈F ∀z,
   Y(x,z)=base(x)+∑k bit(z_k)g_k(x). Then:
   (a) for every i and every x, x∈F implies pointEffect_i(x)=g_i(x);
   (b) for every i and every real d, validity of that individual circle
   implies effect_i(d)=A_i,d(g_i); and (c) for every real d, if N>0 and
   every node's circle at d is valid, then
   AMR(d)=(N:R)⁻¹∑i A_i,d(g_i). The local node assertion needs no existence
   hypothesis concerning other nodes.
2. For every natural N, model P, law Q, selector ρ, base:R²→R, and single
   radial function g:R→R, assume ∀x∈F ∀z,
   Y(x,z)=base(x)+∑k bit(z_k)g(ρ(a_k,x)). Then:
   (a) every point effect on F is g(ρ(a_i,x));
   (b) for every i,d, validity of that individual circle implies
   effect_i(d)=g(d); and (c) for every d, N>0 and validity of every node's
   circle at d imply AMR(d)=g(d).

No coefficient bound, independence, equal treatment probability, support
positivity, or measurability of the full field is a formal hypothesis.
Integrability of the needed coefficient on a valid circle follows by taking
finite weighted differences of the integrable potential outcomes and using
the additive identity on the almost-everywhere concentrated circle.

### Junk values and edge cases

The average uses real inversion of the converted total restricted measure:
0⁻¹=0, infinity.toReal=0, and nonintegrable Bochner integrals are 0. Every
conclusion involving a circle average is guarded by positive finite mass,
almost-everywhere concentration and integrability for all nonzero-weight
updated outcomes. These guards give actual averages and prevent the algebra
from using arbitrary values off the circle. Outcomes with zero weights can
have totalized integral values, but those terms contribute 0.

For N=0 node and point index quantifiers are empty, but all AMR conclusions
require N>0. An assignment at N=0 is still the unique empty function. The
empty circle has zero restricted measure and fails validity. There is no
nonnegative-radius hypothesis, consistently with the arbitrary selector;
when ρ is a metric, negative-radius circles fail validity. Finite real sums,
real subtractions, and exact natural casts have no truncation or overflow.
There are no SAP logarithms, square roots, nonintegral powers, extrema,
limsup/liminf, or partial functions in this dependency closure.

Closure read: `Assignment`, `bit`, `FiniteLaw` including `mass`, `mk`,
nonnegativity and normalization, `FiniteLaw.expect`, `marginal`, `Plane`,
`SpatialModel` including `mk`, `field`, `node`, `node_mem`, `ζ`, `Y`,
`marginalY`, `pointEffect` (`Defs/Part1.lean`); `additiveOutcome`
(`Defs/Part2.lean`); `selectedCircle`, `selectedMeasure`, `selectedAverage`,
`selectedM`, `selectedNodeEffect`, `selectedAMR`, `validSelectedCircle`,
and `T27WholeStatement` (`Defs/WholeW2.lean`). The generated
`validSelectedCircle._proof_1` was printed and is only the standard instance
viewing a measure as an outer-measure class.

## SAP.P008b.T28

Source: `SAP/P008b/Challenge/Part1.lean:112–115`; statement expanded from
`SAP/P008b/Defs/Part7.lean:64–75`.

### Objects and definitions

At n∈N the node set is I_n=Fin(n+1), and assignments are functions I_n→Bool.
The law Q_n has nonnegative real weights q_n(z) summing to 1. For an event E,
Q_n(E) is ∑z∈E q_n(z), implemented by filtering the finite universal set;
its value is 0 for an empty event. `bit` is the real indicator of true.
M_n is any real array I_n×(I_n→Bool)→R. No spatial model or circle
construction occurs here: the docstring interprets the array as circle
outcomes. For any such array,

    T(z) = ∑i bit(z_i),
    C(z) = (n+1:R) − T(z),
    HJ_n(z) = [∑i bit(z_i) M_n(i,z)] / T(z)
              − [∑i (1−bit(z_i)) M_n(i,z)] / C(z).

`completedHajek M_n exceptional z` is the fixed real number exceptional if
T(z)=0 or C(z)=0, and is HJ_n(z) otherwise. The target is

    τ_n = (n+1:R)⁻¹ ∑i [∑z q_n(z) M_n(i,z[i←true])
                         − ∑z q_n(z) M_n(i,z[i←false])].

`commonBernoulli Q_n p` means exactly
q_n(z)=∏i (if z_i then p else 1−p). With 0<p<1 this is the law of
mutually independent Bernoulli(p) assignment coordinates.

`dependsOn P A`, where P is a predicate on vectors u:I_n→Bool×R and
A⊆I_n, means: for every u,v, agreement u_i=v_i for all i∈A implies
P(u)↔P(v). The quantification is over all vectors, not only realized ones.

`boundedPairDependency Q_n M_n D` means there exists a relation G_n on I_n
such that (a) G_n is symmetric; (b) for each i the number of distinct j≠i
with G_n(i,j) is at most D; and (c) whenever finite A,B⊆I_n are disjoint
and there is no G_n edge from A to B, then for all predicates P,R depending
only on A,B, respectively,

    Q_n(P(V(z)) and R(V(z))) = Q_n(P(V(z))) Q_n(R(V(z))),
    where V(z)_i = (z_i, M_n(i,z)).

This is independence of arbitrary collections separated in a dependency
graph, not just pairwise independence or zero covariance. Self-loops are
allowed and do not count toward D; disjointness prevents their affecting
the cross-collection condition.

### Quantifiers, hypotheses, conclusion

For every family (Q_n) indexed by all natural n, every family (M_n), every
fixed real p,H,exceptional, and every fixed natural D, assume in order:
0<p; p<1; H≥0; for every n the law is commonBernoulli Q_n p; for every n,i,z,
|M_n(i,z)|≤H; and for every n, boundedPairDependency Q_n M_n D. Then for
every real ε>0,

    Q_n({z : |completedHJ_n(z) − τ_n| > ε}) → 0 as n→infinity.

Formally the sequence of real probabilities tends to the real neighborhood
filter at 0 along the natural-number atTop filter: for every δ>0 there is
n0 such that for every n≥n0 the probability is within δ of 0. This allows
τ_n to vary with n; it asserts convergence in probability of estimation
error, not convergence of τ_n to a fixed limit. There is no coupling between
different n. D, H, p, and exceptional are chosen before n tends to infinity.

### Junk values and edge cases

Raw HJ uses division in R, so its missing-arm summands would be 0/0=0.
The completed estimator explicitly selects exceptional whenever either arm
is empty, and the raw formula is used only with both real counts positive.
This is a meaningful arbitrary completion rather than reliance on the
division-by-zero convention. It is fixed as n varies. Under the prescribed
law the exceptional-event probability is p^(n+1)+(1−p)^(n+1), tending to 0.
At n=0 there is one node and necessarily an empty arm, a permitted finite
initial exception in a limiting result.

Both arm counts and all differences are real subtractions; C(z) is not
truncated natural subtraction. Since T(z) counts at most n+1 true bits,
C(z) is always a nonnegative real integer. The cast of n+1 into R is exact
and positive; the AMR denominator never vanishes. The node set is always
nonempty, while A or B in the dependency definition may be empty; then a
predicate depending on it is constant, and the independence equation has
its usual meaning. All expectations and probabilities are finite real sums,
so there are no integrability, extended-real conversion or infinite-sum
junk values. `Tendsto` uses ordinary filters; no possibly unbounded-sequence
limsup/liminf is involved. There are no logarithms, square roots, real powers,
infima/suprema or partial-function default values in these definitions.

Closure read: `Assignment`, `bit`, `FiniteLaw` including `mass`, `mk`,
nonnegativity and normalization, `FiniteLaw.expect`, `FiniteLaw.prob`,
`marginal`, `nTreated`, `nControl`, `hajek` (`Defs/Part1.lean`);
`commonBernoulli`, `dependsOn`, `boundedPairDependency`, `finiteAMR`,
`completedHajek` (`Defs/Part4.lean`); `T28Statement` (`Defs/Part7.lean`).
