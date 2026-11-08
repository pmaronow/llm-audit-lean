# Blind reading

This document was written and saved before opening `claims.json` or `record.json`.
Only the challenge declarations, their docstrings, the closure manifest, the local
definitions, and Mathlib definitions were used. All 135 distinct declarations in
the five manifest closures were also printed by Lean in `scratch/Closure.lean`;
the successful output is `scratch/closure-print.log`. This includes constructors,
projections, generated numerical instance proofs, and the buffer-mode recursor
and decidable equality. Generated proof names inherited from other statement
definitions carry numerical/typeclass facts, not those other statements.

Throughout, `Plane` means Mathlib's `EuclideanSpace ℝ (Fin 2)`, the real plane
with its usual Euclidean metric, except where an explicitly supplied metric is
used. `Assignment N` means the complete finite function space `Fin N → Bool`.
Write `e(b)=1` for `b=true`, and `e(b)=0` for `b=false`. For a finite set C,
write `avg(C,f)=(∑x∈C f(x))/(|C|:ℝ)`. This is an ordinary finite sum, with
equal weights. For a finite assignment law q, `q(z)≥0` and `∑z q(z)=1`.
`E_q f=∑z q(z)f(z)` and
`marg_q(F,i,b)=∑z q(z)F(update(z,i,b))`: the update replaces coordinate i,
while leaving every other coordinate equal to its value in z. This is
marginalization over the other coordinates, not conditioning on the observed
own coordinate for an arbitrary dependent law.

For `M : Fin N → (Fin N → Bool) → ℝ`, let
`n1(z)=∑i e(z(i))`, `n0(z)=(N:ℝ)-n1(z)`. The SAP Hájek expression is
`H(M,z)=(∑i e(z(i))M(i,z))/n1(z) -
(∑i (1-e(z(i)))M(i,z))/n0(z)`.
The finite AMR is
`A_q(M)=(N:ℝ)⁻¹ ∑i [marg_q(M(i,·),i,true)-marg_q(M(i,·),i,false)]`.
These notations in the sections below are precisely these unfolded formulas.

## SAP.P008b.T15

Sources: `Challenge/Part1.lean:9–17`; `Defs/WholeW1.lean:14–50,204–227`;
`Defs/Part1.lean:13,46`. Its statement is `T15WholeStatement`.

Quantifier order: for every type X with a measurable-space structure, every
natural number N, every model P described next, every index i in `Fin N`, and
every two real numbers d,k, assume `0≤d`, then `0≤k`. The model consists of an
injective coordinate map `c:X→Plane`, a node map `s:Fin N→X`, an arbitrary
`MetricSpace Plane` structure m, a measure ζ on X, and real potential outcomes
`Y:X→(Fin N→Bool)→ℝ`. No distinctness of the nodes, measurability of c, or global
measurability/integrability of Y is built into this structure. Coordinates are
injective; node labels need not map to distinct X-points. Define
`ρ(x,y)=dist_m(c(x),c(y))`, using the supplied metric, not necessarily the
Euclidean metric. The spatial field is X itself, rather than an additional
ambient measurable set.

Put `B={x∈X | d-k≤ρ(s(i),x) ∧ ρ(s(i),x)≤d+k}` and
`S={x∈X | ρ(s(i),x)=d}`. The conclusion is the conjunction of:

1. For every x, membership in B is equivalent to the two displayed inequalities.
2. For every assignment z, **if** B is measurable, `0<(ζ B).toReal`, `ζ B≠∞`,
   and `x↦Y(x,z)` is Bochner integrable for `ζ.restrict B`, then the region
   average `(ζ B).toReal⁻¹ * ∫x Y(x,z) d(ζ.restrict B)` equals the same integral
   divided by `(ζ B).toReal`, with B written out by its inequalities.
3. For every assignment z, **if** S is measurable, `0<(ζ S).toReal`, `ζ S≠∞`,
   and `x↦Y(x,z)` is Bochner integrable for `ζ.restrict S`, then the circle
   outcome `M(i,d,z)`, defined to be that normalized restricted integral, equals
   `∫x Y(x,z) d(ζ.restrict S)/(ζ S).toReal`, with S written out.
4. **If** `0<d-k` and **if**, for every node label j different from i,
   `d+k<ρ(s(i),s(j))`, then `{j:Fin N | s(j)∈B}=∅`.

The existence guards in 2 and 3 are local to the particular z and particular
region; neither all assignments nor both regions must be valid simultaneously
to obtain the other clauses. The final separation condition is needed only for
the node-exclusion clause. The geometric and integral identities are largely
definition expansions, while node exclusion uses the metric axioms.

Junk-value audit: `ENNReal.toReal ∞=0`, real inverse/division at zero is zero,
and the Bochner integral of a nonintegrable function is zero. These conventions
are present in the total definition of the average but excluded in every
asserted averaging identity by `validRegion` (measurability, positive finite
mass, and integrability). An empty region has mass zero and fails this guard.
The supplied metric and injective coordinates give genuine distances. A
negative d-k is allowed and automatically clips the band through nonnegative
distances; no truncated real subtraction occurs. `Fin N` is empty for N=0,
but an i is universally quantified, so there is then no instance of the
statement; positive N instances are not thereby excluded. No log, square root,
real powers, extrema, limits, partial-function defaults, or integer casts occur
in this closure. Natural-to-real casts are exact.

## SAP.P008b.T16

Sources: `Challenge/Part1.lean:19–33`; `Defs/WholeW3.lean:13–121`;
`Defs/Part2.lean:32–34,47–48`; the shared finite means and Hájek definitions
in `Defs/Part1.lean`. Its statement is `T16WholeStatement_W3`.

This is a closed conjunction about fixed objects, with no external hypotheses.
There are two polygon labels i=0,1 and four local cell labels c=0,1,2,3. Define
the **filled** closed square
`P_i=[20i-1/8,20i+1/8]×[-1/8,1/8]`, offsets
`o=(0,5/2,7/2,9/2)`, and eight cell centers `x_ic=(20i+o_c,0)`.
The common raster is `{(a/2,b/2) | a,b∈ℤ}`. Define
`ρ_i(j,c)=Metric.infDist(x_jc,P_i)`, i.e. Euclidean distance to the filled
square, and `B_i(r)={(j,c)∈Fin 2×Fin 4 | ρ_i(j,c)≤r}`. Define
`C_i={(j,c) | 3≤ρ_i(j,c)≤5}`. For every assignment z, the cell outcome is
`Y((j,c),z)=e(z(0))*v_c` when j=0 and zero when j=1, where
`v=(4,2,0,8)`.

Define three region means `M_0(i,z)=avg(B_i(4)\B_i(2),Y(·,z))`,
`M_1(i,z)=avg(C_i,Y(·,z))`, and `M_2(i,z)=avg(B_i(4),Y(·,z))`.
Define grid radii `r_0=2,r_1=4`. The archived summary for `j:Fin 2` is
`F(i,0,z)=avg(B_i(r_0),Y(·,z))` and, when j≠0,
`F(i,j,z)=[∑B_i(r_j)Y-∑B_i(r_(j-1))Y]/[|B_i(r_j)|- |B_i(r_(j-1))|]`,
where both cardinalities are cast to ℝ before subtraction. Let
`z*=(true,false)`. The theorem asserts all of the following:

1. For every i, P_i is nonempty and closed, x_i0 lies in its interior, its
   topological frontier is nonempty, `infDist(x_i0,frontier P_i)=1/8`, and
   `ρ_i(i,0)=0`.
2. The map `(i,c)↦x_ic` is injective; for all i,c its value lies on the common
   half-unit raster; `ρ_i(i,c)` equals `(0,19/8,27/8,35/8)_c`. For all i,j,c,
   if i≠j then `5<ρ_i(j,c)`.
3. For every c, `Y((0,c),z*)=v_c` and `Y((1,c),z*)=0`. Both assignment arm
   counts n1(z*) and n0(z*) equal 1.
4. For every i, `B_i(2)={(i,0)}`, `B_i(4)={(i,0),(i,1),(i,2)}`,
   `B_i(4)\B_i(2)={(i,1),(i,2)}`; this difference also equals the filter
   `2<ρ_i≤4`; and `C_i={(i,2),(i,3)}`.
5. For every i, the B_i(2), B_i(4), difference, and C_i counts are respectively
   1,3,2,2, and the real difference of the first two buffer counts is 2.
6. The sums of treated polygon-0 outcomes in B_0(2) and B_0(4) at z* are 4 and 6.
7. For every i and every assignment z, `F(i,1,z)=M_0(i,z)`.
8. For every mode in `Fin 3`, the polygon-0 mean at z* is `(1,4,2)_mode`,
   and its polygon-1 mean is zero. For every i, `F(i,1,z*)` is 1 if i=0,
   and zero otherwise.
9. `H(F(·,1,·),z*)=1`, `H(M_1,z*)=4`, `H(M_2,z*)=2`, and the first
   of these contrasts differs from the second.

This is an example comparing an adjacent-buffer annulus to a band of the same
total width centered at the outer radius, plus the disk summary. It does not
assert equality between filled-polygon and boundary distances.

Junk-value audit: `Metric.infDist(x,∅)=0` because it is the real conversion
of the infimum extended distance; here each fixed polygon and each frontier is
asserted nonempty. Distances to these nonempty Euclidean closed sets are genuine
finite distances. Empty finite means would be 0/0=0; the explicit cell sets
and positive counts exclude that for every region used in these conclusions.
Hájek's empty-arm divisions are avoided at z* by the two arm counts of 1.
The archived denominator is a real subtraction, not truncated natural
subtraction. Its value is 2. The index j-1 in this particular definition is
**Fin 2 subtraction**, hence modular in general; only j=1 uses the branch,
and 1-1=0, while j=0 takes the other branch. All remaining finite indices
are in their declared ranges; coordinates use exact natural/integer-to-real
casts and divisions by fixed positive rationals. No integrals, limits, log,
sqrt, or general real powers occur in the relevant formulas. The generated
proofs named after the toy kernel or an old polygon-boundary definition merely
certify numeral instances and have no geometric content.

## SAP.P008b.T17

Sources: `Challenge/Part1.lean:35–42`; `Defs/WholeW2.lean:14–68`;
`Defs/Part6.lean:27–49`; `Defs/Part4.lean:55–63`;
`Defs/Part2.lean:21–22`; the shared definitions in `Defs/Part1.lean`.
Its statement is `T17WholeStatement`, a conjunction with the following blocks.

1. For every p,x in the Euclidean plane and every real d, **if d>0**, then
   `infDist(x,{q | dist(q,p)=d})=|dist(x,p)-d|`.
2. For every p,x,d,k in that order, **if d>0 and k≥0**, then
   `infDist(x,{q | dist(q,p)=d})≤k` iff
   `max(0,d-k)≤dist(x,p)≤d+k`; and **if additionally k≤d**,
   `(d+k)-(d-k)=2k`.
3. The real arithmetic equalities `4-1=3`, `4+1=5`, and `5-3=2`.
4. For every N, every spatial model P, every i:Fin N, every real d, its disk
   is `{x | x∈field ∧ dist(node(i),x)≤d}`. Here a spatial model consists
   of `field:Set Plane`, `node:Fin N→Plane`, proofs that each node is in the
   field, a measure on Plane, and potential outcomes `Plane→Assignment N→ℝ`.
   Its measure and outcomes are unused in this disk identity.
5. For every type X with decidable equality, every sequence `B:ℕ→Finset X`,
   every `Y:X→ℝ`, let
   `G(0)=avg(B(0),Y)`,
   `G(j)=[∑B(j)Y-∑B(j-1)Y]/[(|B(j)|:ℝ)-(|B(j-1)|:ℝ)]` for j>0.
   If B(0) is nonempty, `G(0)=avg(B(0),Y)`. For every natural j, **if**
   j>0, B(j-1)⊆B(j), and |B(j-1)|<|B(j)|, then
   `G(j)=avg(B(j)\B(j-1),Y)`.
6. For every type X, C:Finset X, functions ρ,Y:X→ℝ, and real a,b, **if**
   ρ≥0 on C, a<b, and `|{x∈C|ρ(x)≤a}|<|{x∈C|ρ(x)≤b}|`, then the
   difference of buffer sums divided by the real difference of counts equals
   `avg({x∈C|a<ρ(x)≤b},Y)`. Also, with m=(a+b)/2,
   `m-a=(b-a)/2`, `b-m=(b-a)/2`, `0<b-a`, and `m<b`.
7. For every type X, finite set C, map `centroid:X→Plane`, set P⊆Plane,
   real-valued function Y on X, and grid `r:ℕ→ℝ`, in that order, **if** P is
   closed and nonempty, put `B(t)={c∈C|infDist(centroid(c),P)≤t}`. The
   archived summary has a mode from a two-element inductive type (donut,disk):
   `F(mode,j)=[∑B(r_j)Y-∑B(r_(j-1))Y]/[|B(r_j)|-|B(r_(j-1))|]` when
   mode=donut and j≠0, and `avg(B(r_j),Y)` otherwise. The conclusion is:
   - `B(0)={c∈C|centroid(c)∈P}`;
   - for every j, if B(r_j) is nonempty, `F(disk,j)=avg(B(r_j),Y)`;
   - if B(r_0) is nonempty, `F(donut,0)=avg(B(r_0),Y)`;
   - if r_0=0 and `{c∈C|centroid(c)∈P}` is nonempty, `F(donut,0)` is
     its equal-weight average;
   - for every natural j, **if** j>0, `0≤r_(j-1)<r_j`, and the buffer count
     increases strictly, then F(donut,j) equals both the mean on
     `B(r_j)\B(r_(j-1))` and the mean on
     `{c∈C|r_(j-1)<infDist(centroid(c),P)≤r_j}`. With
     `m=(r_(j-1)+r_j)/2`, both m-r_(j-1) and r_j-m equal
     `(r_j-r_(j-1))/2`, `0<r_j-r_(j-1)`, and m<r_j.

Thus no monotonicity of the whole grid, polygon shape assumption, or nonempty
whole raster is an outer hypothesis; each mean or annular identity is guarded
locally. A nonempty closed arbitrary planar set is sufficient for block 7.
The `WholeBufferMode` constructor indices are 0 for donut and 1 for disk;
its case eliminator and derived decidable equality merely select those branches.

Junk-value audit: circle infDist has a nonempty target since d>0 in ℝ².
Polygon infDist has a nonempty target by hypothesis; closedness ensures that
zero distance means membership rather than only closure membership. This
excludes the empty-set infDist=0 convention. Every used mean has a nonempty
set or strictly positive added-cell count. Abstract total definitions still
assign zero to a zero denominator, but no asserted annular mean needs that
completion. Natural j-1 is truncated at 0, but every branch using a previous
radius explicitly assumes j>0, and the first branch is treated separately.
Cardinality differences are real differences. In block 6 a may be negative;
nonnegative distances then give an empty inner buffer, with strict count
increase guaranteeing a nonempty annulus. In block 4 a negative disk radius
gives the empty set, consistently with the displayed definition, and no
average is taken. N=0 makes its indexed disk assertion empty; X or C can be
empty in the finite algebra blocks, but the mean hypotheses then fail rather
than manufacture an existing mean. Integer/natural casts are exact. No
integral, extrema of unbounded sets, limits, logarithm, square root, or real
power occurs beyond the standard distance-to-set infimum described above.

## SAP.P008b.T18

Sources: `Challenge/Part1.lean:44–52`; `Defs/WholeW2.lean:70–98`;
`Defs/Part6.lean:51–67`; `Defs/Part4.lean:40–48`;
`Defs/Part2.lean:30`; the assignment and finite-law definitions in Part1.
Its statement is `T18WholeStatement`.

Define real functions on all of ℝ:
`K(r)=2 exp(-2r)-(128/3)r⁴ exp(-4r)` and
`V(r)=(128/3)r⁴ exp(-4r)`. The statement is the conjunction of:

1. For every real r, if r≥0, `-384/437<K(r)`; also `-1<-384/437`.
2. For every natural C, every finite probability law q on `Fin 4→Bool`,
   every baseline `base:Fin C→ℝ`, and every pair of arrays
   `r,w:Fin 4→Fin C→ℝ`, **if**, successively, all w_ic≥0, each row sums to
   1, and all r_ic≥0, define
   `Y_a(c,z)=base(c)+∑j∈Fin 4 e(z(j))*a*K(r_jc)` and
   `A_q(a)=(1/4)∑i∈Fin 4 ∑c∈Fin C w_ic *
   [∑z q(z)Y_a(c,update(z,i,true))-∑z q(z)Y_a(c,update(z,i,false))]`.
   Then:
   - for every real a, every i,c, every assignment z, the difference of the
     true/false updated outcomes is a*K(r_ic);
   - for every real a and every i,c, its marginalized difference is a*K(r_ic);
   - for every real a, `A_q(a)=(1/4)∑i∑c w_ic*(a*K(r_ic))`;
   - `A_q(3)=3*A_q(1)`, `-384/437<A_q(1)`, `-1<A_q(1)`, and
     `A_q(1)≠-126/100`.
   The arrays need not be distances realized by a common geometric embedding,
   and weights need not be circle selectors. No independence of q is assumed.
3. For every real r≥0,
   `K(r)=gammaPDFReal(1,2,r)-gammaPDFReal(5,4,r)`, using Mathlib's
   gamma density with positive shape and rate parameters.
4. For every real r (also negative r), V has derivative
   `(512/3)r³(1-r)exp(-4r)` at r.
5. For every real r≥0, `0≤V(r)≤V(1)`; and `V(1)=128/(3*exp(4))`.
6. `∑k=0,…,6 4^k/(k!:ℝ)=437/9<exp(4)`.
7. For every real r≥0, `V(r)<384/437`.
8. K is neither monotone nor antitone on `[0,∞)`. These are negations of
   the two usual pairwise order inequalities on that set, not a claim that
   every subinterval contains a change of direction.
9. `|K(1/10)-163/100|<1/200`, `|K(6/5)+55/100|<1/200`, and
   `|K(2)+19/100|<1/200`.
10. There exists a real t, then hypotheses `0<t` and `t<1`, such that
    `3*(t*K(1)+(1-t)*K(0))=-63/50`.

The final existential is explicitly a two-value convex-combination assertion;
it does not itself quantify over an embedded raster or design. In combination
with block 2 it can be represented by a two-cell weight array. The statement
excludes the printed negative magnitude at amplitude one rather than asserting
that magnitude for the unscaled kernel.

Junk-value audit: all scalar denominators (3,4,437,100,200,50,9) are positive;
factorials are positive, and exp(4)>0. There are no divisions by assignment arm
counts or conditional probabilities. q is a genuine probability mass function,
with finite sums only, so every expectation is finite and defined. If C=0,
the hypothesis that each of four empty row sums equals 1 is impossible;
positive C models remain available. Zero weights are harmless. Arbitrary
negative a are allowed and affect only the exact scaling identities, not the
amplitude-one lower bound. Mathlib's gamma density uses real powers:
`if x≥0 then rate^shape/Gamma(shape)*x^(shape-1)*exp(-rate*x) else 0`.
Here shapes and rates are 1,2 and 5,4, so Γ is finite and nonzero, the bases
are nonnegative, and powers reduce to nonnegative integer powers. At r=0,
the first density uses the conventional `0^0=1`, yielding K(0)=2; the second
has `0^4=0`. This is the chosen endpoint version of a density, not an
out-of-domain evaluation. K and V have polynomial/exponential extensions to
negative r; only the derivative assertion uses that extension. There are no
Bochner integrals, infinities, unbounded extrema, limits, logs, square roots,
truncated subtractions, or partial defaults in this closure. Numeral and
continuous-scalar-multiplication auxiliary proofs add no hypotheses.

## SAP.P008b.T19

Sources: `Challenge/Part1.lean:54–56`; `Defs/Part5.lean:32–57`;
`Defs/Part3.lean:33–53`; `Defs/Part4.lean:13–14,32–34`;
the shared finite-law and mean definitions in Part1. Its statement is
`T19Statement`.

This is a closed conjunction about one fixed 20-by-10 raster, not a universal
claim of equality between two summaries. Raster cells are pairs
`c=(u,v)∈Fin 20×Fin 10`, interpreted by the docstring as centers
`(u+1/2,v+1/2)`. Let `L_0=2,L_1=12`,
`R_i={c | L_i≤u<L_i+5 ∧ 2≤v<7}`,
`E_i={c∈R_i | u=L_i ∨ u=L_i+4 ∨ v=2 ∨ v=6}`.
For every assignment z:Fin 2→Bool,
`Y(c,z)=e(z(0))` if `3≤u≤5 ∧ 3≤v≤5`, and zero otherwise.
Let `M_E(i,z)=avg(E_i,Y(·,z))` and `M_R(i,z)=avg(R_i,Y(·,z))`.
The assignment law q is uniform on all four assignments, so each mass is 1/4.
Again let z*=(true,false). All SAP means, marginalizations, AMR, and Hájek
contrasts here are exactly the finite formulas given at the start of this file.

The theorem asserts:

1. There are 200 cells; for every i, |R_i|=25 and |E_i|=16.
2. For every i and every c, **if c∈R_i**, then c∈E_i iff there exist
   a,b:Fin 3 with `(a.val≠1 ∨ b.val≠1)` such that the integer-coordinate
   neighbor `(u+a-1,v+b-1)` is outside the rectangular ranges for R_i:
   its first coordinate is below L_i or at least L_i+5, or its second is
   below 2 or at least 7. Thus E_i is the raster boundary defined by an
   outside neighbor among the eight adjacent cells.
3. For every cell c and every assignment z, Y(c,z) is either 0 or 1.
4. For every i,z, `M_E(i,z)=0`; and
   `M_R(i,z)=(9/25)*e(z(0))` for i=0, zero for i=1.
5. For every assignment z, its mass q(z) equals
   `∏i (if z(i) then 1/2 else 1-1/2)`; in particular q(z*)=1/4.
   This is independent fair treatment assignment.
6. `H(M_E,z*)=0`, `H(M_R,z*)=9/25`,
   `A_q(M_E)=0`, `A_q(M_R)=9/50`, and `0≠9/25`.
7. For every i, |R_i\E_i|=9. For every i, the sum of Y(c,z*) on R_i
   is 9 for i=0 and zero for i=1.
8. For every i, `marg_q(M_R(i,·),i,true)-marg_q(M_R(i,·),i,false)`
   equals 9/25 for i=0 and zero for i=1.
9. n1(z*)=n0(z*)=1.

The conclusion is a genuine numerical distinction between the means on the
specified raster boundary and on the whole raster polygon. The docstring
explicitly calls it a counterexample to a *reading* of the zero-distance edge
guidance. The formal statement includes the discrete boundary criterion and
does not identify a raster-center boundary layer with a continuous frontier.

Junk-value audit: all finite-region denominators are positive (16 and 25),
the AMR denominator is 2, and the evaluated Hájek arm denominators are 1 and 1.
The uniform law is defined only with a Nonempty sample-space instance;
`Fin 2→Bool` has four elements, and its reciprocal cardinality is 1/4.
All outcomes are finite and bounded, so finite-law expectations require no
integrability completion. The AMR uses outcome marginalization at *all*
assignments; it never averages Hájek estimates at all-treated/all-control
assignments, so those possible empty-arm assignments do not invoke division
by zero in a claimed mean. The neighbor offsets subtract 1 after casting to
ℤ: subtraction is neither natural truncation nor wraparound at a Fin bound.
No other subtraction involves natural-valued coordinates. `Finset` difference
is ordinary set difference. No infDist, real powers, logarithms, square roots,
Bochner integrals, infinities, extrema, limits, or partial-function defaults
occur here. The generated proof named `T19Statement._proof_3` supplies the
nonempty assignment-space instance; the other inherited generated proofs only
establish valid numeral/typeclass instances.
