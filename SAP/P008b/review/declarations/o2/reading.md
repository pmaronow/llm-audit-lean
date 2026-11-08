# Blind reading (written before opening claims.json / record.json)

Common definitions (SAP/P008b/Defs/Part1.lean):

- `Assignment N := Fin N → Bool` (Part1:13); `bit b = 1` if `b` else `0` (Part1:15).
- `FiniteLaw Ω` (Part1:17): a real mass function on a `Fintype Ω`, nonnegative, summing to 1 (so Ω is
  necessarily nonempty). `expect Q f = ∑_z Q(z) f(z)` (Part1:22); `prob Q P = ∑_{z ∈ P} Q(z)` (classical
  filter, Part1:25); `cov Q f g = E[(f - Ef)(g - Eg)]` (Part1:28); `var Q f = cov Q f f` (Part1:32).
- `uniformLaw Ω` (Part1:35): mass `1/|Ω|` (needs `Nonempty Ω`).
- `marginal Q F i b = ∑_z Q(z) · F(z with coordinate i overwritten by b)` (Part1:42). This is the expectation
  of F when unit i's treatment is *set* to b and all other coordinates are drawn from the *marginal* law of
  `Z_{-i}` under Q (not the law of `Z_{-i}` conditional on `Z_i = b`). The two coincide for product designs.
- `Plane := EuclideanSpace ℝ (Fin 2)` (Part1:46), so `dist` is Euclidean distance.
- `SpatialModel N` (Part1:48): a field `field ⊆ ℝ²`, nodes `node : Fin N → ℝ²` in the field, a measure ζ on ℝ²
  and potential outcomes `Y : ℝ² → Assignment N → ℝ`. `circle i d = {x ∈ field | ‖node i − x‖ = d}` (Part1:55),
  `circleMeasure = ζ|circle` (Part1:58), `circleMass = (ζ|circle)(univ).toReal` (Part1:61),
  `average i d f = circleMass⁻¹ · ∫ f dζ|circle` (Part1:64), `M i d z = average i d (Y · z)` (Part1:68).
- `nTreated z = ∑ bit(z i)` (ℝ), `nControl z = N − nTreated z` (ℝ, no truncation) (Part1:91,93).
- `hajek M z = (∑_i bit(z_i) M_i(z))/nTreated z − (∑_i (1 − bit(z_i)) M_i(z))/nControl z` (Part1:95).
- `countMean C f = (∑_{x∈C} f x)/|C|` (Part1:99).
- `finiteAMR Q M = N⁻¹ ∑_i (marginal Q (M i) i true − marginal Q (M i) i false)` (Part4:32).

---

## SAP.P008b.T20 (Challenge/Part1.lean:58–61; statement `T20Statement`, Defs/Part6.lean:69–91)

Closure definitions read: Assignment, BlockCell (Part3:13 = `Fin 5 × Fin 5`), FiniteLaw(.mk,.mass,.expect),
Plane, PolygonRasterCell (Part3:33 = `Fin 20 × Fin 10`, index (u,v) = cell with center (u+½, v+½)), bit,
blockBoundary (Part3:15), countMean, finiteAMR, hajek, marginal, nControl, nTreated, polygonRasterAreaM
(Part3:52), polygonRasterEdgeM (Part3:49), polygonRasterOutcome (Part3:46), rasterAreaAverage (Part3:30),
rasterBoundary (Part3:21), rasterEdgeZeroAverage (Part3:27), rasterPolygonBoundary (Part3:42),
rasterPolygonCells (Part3:38), rasterPolygonLeft (Part3:36), uniformLaw.

Plain mathematics. The statement is a conjunction of four parts.

(A) For every finite set of grid cells `R ⊆ ℤ²` and every `Y : ℤ² → ℝ`, **if** the raster boundary
`∂R := {x ∈ R | some 8-neighbour (x₁+a−1, x₂+b−1), (a,b) ∈ {0,1,2}², (a,b) ≠ (1,1), is not in R}`
is nonempty, then
  (i) `x ∈ ∂R ⇔ x ∈ R ∧ (some 8-neighbour of x is not in R)` (this is the definition of `rasterBoundary`),
  (ii) the zero-distance edge average `rasterEdgeZeroAverage R Y` equals `(∑_{x∈∂R} Y x)/|∂R|`, and
  (iii) the area average `rasterAreaAverage R Y` equals `(∑_{x∈R} Y x)/|R|`.
All three are definitional unfoldings (`rasterEdgeZeroAverage = countMean (∂R)`, `rasterAreaAverage =
countMean R`); they record the definitions but assert nothing beyond them. The nonemptiness hypothesis is
not needed for them (they hold by `rfl`).

(B) For the 5×5 block `Fin 5 × Fin 5`: it has 25 cells; `blockBoundary` (cells with a coordinate 0 or 4) has
16 cells; its complement has 9 cells; a cell is in `blockBoundary` iff some 8-neighbour (integer arithmetic,
casts `Fin → ℕ → ℤ`, no truncation) lies outside `{0,…,4}²`; and a cell is outside `blockBoundary` iff both
coordinates lie in `{1,2,3}`.

(C) For every set `P ⊆ ℝ²` with nonempty topological frontier: `{x | infDist(x, frontier P) = 0} = frontier P`
(frontier is closed), and every interior point of P has strictly positive distance to `frontier P`.
I.e. the "zero-boundary-distance" set is exactly the topological boundary, not the polygon.

(D) A concrete 20×10 raster with two 5×5 polygons (polygon 0 = columns 2–6, polygon 1 = columns 12–16, rows
2–6), boundary rings of 16 cells (`rasterPolygonBoundary`), and outcome `Y_c(z) = bit(z₀)` on the 3×3 block
columns 3–5, rows 3–5 (the interior of polygon 0), else 0. With `M_i^{edge}(z)` = mean over the ring of polygon i
and `M_i^{area}(z)` = mean over all 25 cells of polygon i:
  Hájek contrast at `z = (true,false)`: edge = 0, area = 9/25;
  finite AMR under the uniform law on `{0,1}²` (= independent fair coins): edge = 0, area = 9/50.

Quantifier order: ∀R ∀Y (hyp → …) in (A); ∀P (hyp → …) in (C); (B), (D) are closed numerical facts.

Junk-value conventions.
- `countMean` divides by `|C|` (x/0 = 0). In (A) the hypothesis `∂R ≠ ∅` makes `|∂R| > 0` and `|R| ≥ |∂R| > 0`
  (but the identities are definitional, so no junk can matter). In (D) the denominators are 16 and 25.
- `hajek` divides by `nTreated` and `nControl`; at `(true,false)` both equal 1. No junk.
- `finiteAMR` multiplies by `N⁻¹` with N = 2. No junk.
- `Metric.infDist x ∅ = 0`: if `frontier P = ∅` (P = ∅ or P = ℝ²) the set in (C) would be all of ℝ² ≠ ∅;
  the hypothesis `(frontier P).Nonempty` excludes exactly this junk case, and it is a genuine restriction
  only in these degenerate cases (no actual polygon has empty frontier).
- Casts: `Fin.val` to ℤ in (B) and in `rasterBoundary`; subtraction happens in ℤ (checked with
  `pp.coercions`), so no truncated subtraction.
- `uniformLaw (Assignment 2)`: mass 1/4 each.

Observations. The polygon example in (D) uses `rasterPolygonBoundary` (an explicitly listed ring), not
`rasterBoundary` applied to the polygon; T20 does not itself state that the ring is the 8-neighbour boundary of
the polygon (that link is in T19). It also states no relation between the continuous part (C) and the raster
parts; it does not contain any statement about a fitted/smoothed curve.

---

## SAP.P008b.T21 (Challenge/Part1.lean:63–66; `T21Statement`, Defs/Part6.lean:93–94)

Closure: only `T21Statement`.

Plain mathematics: the real-number inequality `−321/10000 < −19/625`, i.e. `−0.0321 < −0.0304`. Closed,
no hypotheses, true by `norm_num` (checked in scratch/Check.lean).

Junk values: none.

Observation: this is a pure numeral comparison; it says nothing about estimates, quantiles, assignment
laws, significance, or spillovers. Any claim beyond "the number −0.0321 is below −0.0304" is not stated.

---

## SAP.P008b.T22 (Challenge/Part1.lean:68–77; `T22WholeStatement`, Defs/WholeW1.lean:124–156)

Closure: Assignment, FiniteLaw(.mk,.mass,.prob), Plane, SpatialModel(.mk,.field,.node,.ζ,.Y,.circle,
.circleMeasure,.circleMass,.average,.M), SpatialModel.sharpNull (Part2:24: `∀ x ∈ field, ∀ z, Y x z = Y x 0`),
SpatialModel.validCircle (Part4:50: `0 < circleMass ∧ circle mass ≠ ∞ ∧ ∀ z, Y(·,z)` integrable on the circle),
T22Statement (Part6:96), bit, hajek, nControl, nTreated, uniformLaw, wholeQuantile7 (WholeW1:100),
wholeTestRadius (WholeW1:112: `r_j = (j+1)/10`, j = 0..4), wholeTestStatistic (WholeW1:114:
`T_j(k) = hajek(M(·, r_j, ·))(a_k)`), wholeTreatedCount (WholeW1:109, ℕ count of trues).

Plain mathematics: a conjunction of three parts.

(A) **There exist** a spatial model P with 4 nodes (Euclidean circles in ℝ², some field and measure ζ, outcomes
Y) and an enumeration `a : Fin 6 → {0,1}⁴` such that
  - `a` is injective and its image is exactly the set of assignments with exactly two treated nodes
    (so the uniform law on `Fin 6` pushed forward by `a` is complete randomization of 2 of 4);
  - each `a k` has `nTreated = nControl = 2`;
  - the sharp null holds (`Y x z = Y x (all control)` for every field point x and assignment z);
  - for every node i and every radius `r_j ∈ {0.1,…,0.5}` the circle average exists in the strong sense
    (circle mass positive and finite, `Y(·,z)` integrable on the circle for all z);
  - the circle averages are `M_i(r_j, z) = i` (node index 0,1,2,3) for all i, j, z;
  - for each radius j: the vector `k ↦ T_j(k)` is monotone (sorted), its type-7 quantiles (R type 7 with 0-based
    index `h = 5q`, linear interpolation) at `q = 1/40` and `q = 39/40` are `−15/8` and `15/8`, and
    the uniform probability over k of the strict rule `T_j(k) < q_{1/40} ∨ T_j(k) > q_{39/40}` is 1/3;
  - the same for the sum statistic `∑_j T_j(k)`: sorted, quantiles `∓75/8`, rejection probability 1/3;
  - `1/20 < 1/3`.
Arithmetic check (by hand): with `M_i = i`, `T(k) = (a+b)/2 − (c+d)/2 = a+b−3` for treated pair {a,b};
the six values sorted are −2,−1,0,0,1,2; type-7 at 1/40: h = 1/8, (7/8)(−2)+(1/8)(−1) = −15/8; at 39/40:
h = 39/8, (1/8)(1) + (7/8)(2) = 15/8; strict rejection only at ±2, probability 2/6 = 1/3. Sum over five
radii = 5T, quantiles ∓75/8, probability 1/3. Consistent.

(B) For every nonempty `R ⊆ Fin 6`, `P_unif(R) ≥ 1/6` and `> 1/20` (no deterministic nonempty rejection region
on 6 equiprobable assignments has size ≤ 0.05).

(C) `T22Statement` (Part6:96): `619/50 < −797/100 ∨ 797/100 < 619/50`, i.e. 12.38 lies outside
`[−7.97, 7.97]` on the right (true; second disjunct).

Docstring reading: "The printed claim is false: …" — the theorem is presented as a refutation of a claim
that a randomization/percentile test of the sharp null has level 0.05 (to be checked against the claim).
The witness has 4 nodes and complete randomization of 2 of 4, so the randomization distribution has only 6
points; the size failure comes from the finite support. A refutation is only valid if the paper's claim
covers such a design (finite exact randomization with a 2.5%/97.5% percentile rule, any N) — to check.

Junk-value conventions.
- `SpatialModel.average`: `circleMass⁻¹` (0 if mass 0 or ∞ since `toReal ∞ = 0`), Bochner integral 0 if not
  integrable. All excluded at the five radii by `validCircle` for every node and every z. But the
  existential also fixes `M = i`, so junk could only matter if validCircle were vacuous — it is not
  (positive finite mass, integrable for all z).
- `hajek`: denominators `nTreated(a k) = nControl(a k) = 2` are asserted, so no x/0 junk.
- `wholeQuantile7`: `Int.toNat ⌊h⌋` truncates negatives to 0 and `min … n` clamps; only q ∈ {1/40, 39/40}
  used, with h ∈ [0,5], so no clamping junk. It presupposes sorted input, which is asserted (`Monotone`).
- `FiniteLaw.prob` uses a classical filter; fine.
- `nControl` is real subtraction, no truncation.
- Measure-theoretic: the circle is not required to be measurable in validCircle (restriction to a
  non-measurable set is still defined in Mathlib); not an issue for an existential since the witness is
  certified, but the witness could in principle use a non-measurable circle — irrelevant, circles in ℝ²
  (closed sets) are Borel, and the field enters only by intersection; if `field` is non-measurable then the
  circle may be non-measurable. Checked: nothing in the statement depends on it beyond the stated averages.

---

## SAP.P008b.T23 (Challenge/Part1.lean:79–82; `T23Statement`, Defs/Part6.lean:100–106)

Closure: FiniteLaw(.mk,.mass,.expect,.cov,.var), T23Statement.

Plain mathematics: for every finite probability space (Ω, Q) (any `Fintype` Ω with a probability mass function),
every N, every family of real random variables `φ_1,…,φ_N : Ω → ℝ`, every real matrix `D : N × N → ℝ` (not
required symmetric, nonnegative or a metric) and every cutoff `c ∈ ℝ`:
if `Cov_Q(φ_i, φ_j) = 0` whenever `D_ij > c`, then
`∑_i ∑_j Cov_Q(φ_i, φ_j) · 1[D_ij ≤ c] = Var_Q(∑_i φ_i)`.
Population (true-law) covariances; not an estimator statement.

Junk values: none (finite sums; Ω nonempty because masses sum to 1). Empty `Fin 0`: both sides 0, fine.

Observation: an identity about population covariances under a finite law. It says nothing about variance
*estimators* (spatial HAC), coverage, interval tables or cutoff values (e.g. 0.4).

---

## SAP.P008b.T25 (Challenge/Part1.lean:84–91; `T25WholeStatement`, Defs/WholeW1.lean:158–182)

Closure: Assignment, FiniteLaw(.mk,.mass,.expect), MetricSpatialModel (WholeW1:14–24: a measurable space X of
field points with an injective coordinate map into ℝ², nodes `node : Fin N → X` (so nodes are field
points), an **arbitrary** metric structure on ℝ², a measure ζ on X, outcomes `Y : X → Assignment N → ℝ`),
.distance (WholeW1:30: chosen metric on coordinates), .circle (WholeW1:33: `{x | distance(node i, x) = d}`),
.regionAverage (WholeW1:39: `ζ(s).toReal⁻¹ · ∫_s f dζ`), .M (WholeW1:49), .marginalY (WholeW1:52:
`marginal Q (Y x) i b`), .pointEffect (WholeW1:55), .m (WholeW1:58: `marginal Q (M i d) i b`), .nodeEffect
(WholeW1:61), .amr (WholeW1:64: `finiteAMR Q (M · d)`), .validCircle (WholeW1:67: circle measurable,
`0 < ζ(C).toReal`, `ζ(C) ≠ ∞`, and for every b and every z with `Q(z) ≠ 0`, `Y(·, z[i↦b])` integrable on C),
.ζ, .Y, .coord, .metric, .node, .mk, Plane, finiteAMR, marginal, uniformLaw.

Plain mathematics: a conjunction of four parts.

(1) For every such model, every finite design Q on `{0,1}^N`, every node i and every real d, if the circle
average at (i,d) exists (validCircle), then for b ∈ {0,1}:
`m_i(b; d) := E_Q[ M_i(d; Z[i↦b]) ] = (1/ζ(C)) ∫_C E_Q[Y_x(Z[i↦b])] dζ(x)`
(marginalization commutes with the circle average), and
`τ_i(d) := m_i(1;d) − m_i(0;d) = (1/ζ(C)) ∫_C (E_Q[Y_x(Z[i↦1])] − E_Q[Y_x(Z[i↦0])]) dζ(x)`
(node effect = circle average of point effects).

(2) For every model, design Q and d, if N > 0 and validCircle holds at every node, then
`AMR(d) := N⁻¹ ∑_i (m_i(1;d) − m_i(0;d)) = N⁻¹ ∑_i (1/ζ(C_i)) ∫_{C_i} pointEffect_i dζ`.

(3) For the uniform law on `{0,1}⁴` (independent fair coins) and any `Y : {0,1}⁴ → ℝ`:
`marginal Y i b = (1/8) ∑_{z : z_i = b} Y(z)`.

(4) Hence `marginal Y i 1 − marginal Y i 0 = (1/8)∑_{z_i=1} Y(z) − (1/8)∑_{z_i=0} Y(z)`.

Junk-value conventions.
- `regionAverage`: `toReal` of ∞ is 0 and `x⁻¹` of 0 is 0, Bochner integral of a non-integrable function is 0.
  The hypothesis validCircle excludes all three for the functions actually used (positive finite mass;
  integrability for every override `z[i↦b]` with `Q(z) ≠ 0`; terms with `Q(z) = 0` are multiplied by 0 on both
  sides). So both sides of (1)/(2) are genuine averages.
- `0 < N` in (2) is not needed (`N = 0` gives 0 = 0); harmless.
- `marginal` = "set Z_i = b, draw Z_{-i} from its marginal under Q" — the meaning of "marginalized outcome"
  for a general (non-product) design must be checked against the paper (for designs with dependence, the
  paper may condition on `Z_i = b` instead). Under the uniform four-node design in (3)/(4) the two coincide.
- The coordinate metric is arbitrary (any `MetricSpace Plane` structure), not necessarily Euclidean; this is a
  generalization.
- Measure on X itself (field need not be measurable in ℝ²); circle measurability is assumed in validCircle —
  a usual measure-theoretic condition.
