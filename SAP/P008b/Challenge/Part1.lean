import SAP.P008b.Defs.WholeW1
import SAP.P008b.Defs.WholeW2
import SAP.P008b.Defs.WholeW3
import SAP.P008b.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- P008-T15; p. 143 (PDF p. 6).
For every chosen coordinate metric, the band of width parameter k about
radius d consists of outcome points at distances between d-k and d+k.
Its average is the normalized integral over those points; the edge average
is the corresponding integral over points at distance exactly d. These
formulas apply whenever the respective averages exist. If the inner radius
is positive and the outer radius is below the distance to every other node,
the band contains no intervention node. -/
theorem SAP.P008b.T15 : SAP.P008b.T15WholeStatement := by sorry

/-- P008-T16; pp. 143 and 145 (PDF pp. 6 and 8); supplied archived
polygon-buffer formula, source lines 115–118; canonical fixture corrected
2026-11-04. The usual measure-theoretic conditions are assumed.
For the filled squares [-1/8,1/8]^2 and its translate by (20,0), the eight
specified centers lie on a common half-unit raster. Their distances to their
own filled polygon are 0,19/8,27/8,35/8 and all cross distances exceed 5.
The center is interior, at distance 1/8 from the topological boundary and zero
from the filled polygon. With outcomes (4,2,0,8) and zero controls, the buffers
at radii 2 and 4 have treated counts/sums (1,4) and (3,6). The supplied archived
donut formula averages the added cells in (2,4], giving 1; the band [3,5], of
the same total width 2 and centered at 4, gives 4; the disk gives 2. There is
one polygon in each assignment arm, so the respective Hajek estimates are
1,4,2. Thus this archived donut estimate differs from the centered-band estimate.
All region counts, the buffer-count difference and both arm counts are nonzero. -/
theorem SAP.P008b.T16 : SAP.P008b.T16WholeStatement_W3 := by sorry

/-- P008-T17; pp. 143 and 145 (PDF pp. 6 and 8); supplied archived polygon-buffer formula.
Circle tolerance selects the clipped radial band, of width twice the tolerance
when the inner radius is nonnegative. A point disk is the full disk. In the
supplied polygon formula disks and the first donut use the full buffer, the
zero-radius buffer consists of the polygon's own nonmissing cells, and later
donuts average the added cells between successive radii, with the stated width,
outer endpoint and midpoint. -/
theorem SAP.P008b.T17 : SAP.P008b.T17WholeStatement := by sorry

/-- P008-T18; pp. 146–147 and 149 (PDF pp. 9–10 and 12), Figures 2 and 4; supplied staged kernel.
The plotted function is the difference of the specified gamma densities and is
nonmonotone. In additive raster outcomes every design's effects and AMR scale
by amplitude. The negative term has the stated derivative and attained maximum;
the exact exponential Taylor bound implies the kernel and amplitude-one AMR
exceed minus 384/437 and hence minus one. The printed magnitude minus 1.26 is
excluded at amplitude one and is attainable in the amplitude-three convex
average model. Rational enclosures give the three stated approximate kernel values. -/
theorem SAP.P008b.T18 : SAP.P008b.T18WholeStatement := by sorry

/-- P008-T19; pp. 145 and 153 (PDF pp. 8 and 16).
The specified 200-cell raster establishes the counterexample to the reading that a zero-distance edge estimate is the contrast of within-polygon area means: the contrasts are 0 and 9/25 and the corresponding AMRs are 0 and 9/50 under independent fair treatment assignment. -/
theorem SAP.P008b.T19 : SAP.P008b.T19Statement := by sorry

/-- P008-T20; pp. 145 and 153 (PDF pp. 8 and 16).
Discrete boundary averages and continuous zero-boundary-distance sets differ from whole-polygon summaries, as the explicit contrasts and AMRs demonstrate.
Restriction: Requires nonempty raster boundaries and nonempty continuous frontiers; omits the corrected sentence about how the reported smoothed curve was fitted. -/
theorem SAP.P008b.T20 : SAP.P008b.T20Statement := by sorry

/-- P008-T21; p. 153 (PDF p. 16), with design discussion on pp. 145 and 151.
The printed estimate minus 0.0321 is below the printed lower cutoff minus 0.0304.
Restriction: Retains only the numerical comparison; omits identification of the actual assignment law and its quantiles, the significance inference, and the empirical spillover conclusions. -/
theorem SAP.P008b.T21 : SAP.P008b.T21Statement := by sorry

/-- P008-T22; pp. 144, 146 and 148–150 (PDF pp. 7, 9 and 11–13).
The printed claim is false: a spatial sharp-null experiment with all six
two-treated assignments, positive finite integrable circle averages at five
radii, and both Hajek arms nonempty has strict type-7 percentile rejection
probability 1/3, greater than 0.05, for each radius and for their sum.
The exact quantiles are respectively minus and plus 15/8 and 75/8. Every
nonempty deterministic rejection set on six equally likely assignments has
probability at least 1/6, greater than 0.05. The printed numbers do satisfy
the nominal rejection rule. -/
theorem SAP.P008b.T22 : SAP.P008b.T22WholeStatement := by sorry

/-- P008-T23; pp. 145, 147–149 and 153 (PDF pp. 8, 10–12 and 16).
Zero covariances beyond a cutoff make the truncated covariance sum equal the variance of the summed contributions.
Restriction: Retains only the cutoff instruction's covariance identity; omits the reported interval table, its coverage interpretation, the assertion that cutoff 0.4 captures toy interference dependence unlike zero, and the empirical interval-width comparison. -/
theorem SAP.P008b.T23 : SAP.P008b.T23Statement := by sorry

/-- P008-T25; pp. 142–143 and 146–147 (PDF pp. 5–6 and 9–10).
For every chosen coordinate metric and suitable measure on the spatial field,
finite marginalization commutes with every existing circle average. Node effects
are circle averages of point effects, and the AMR is the average of these
integrals over a positive number of nodes. Under the uniform four-node design,
each marginalized outcome is the mean over the eight assignments with the
specified own treatment, and its effect is the difference of these means. -/
theorem SAP.P008b.T25 : SAP.P008b.T25WholeStatement := by sorry

/-- P008-T26; p. 144 (PDF p. 7).
For every coordinate metric, spatial field, suitable measure and finite design,
the sharp null makes every point effect and every existing node effect zero,
and makes every existing AMR over a positive number of nodes zero.
The converse fails: on the three-point counting-measure field at (-1,0),
(0,0), (1,0), with one node at the origin, the AMR vanishes at every radius
where it exists, including radii zero and one, although treatment changes
the outcome at (1,0). No ambient field-measurability assumption is needed. -/
theorem SAP.P008b.T26 : SAP.P008b.T26WholeStatement := by sorry

/-- P008-T27; p. 140 (PDF p. 3); additive mathematical content with the definitions on pp. 141–144.
For every design and chosen metric, additive point effects equal their structural
coefficients. Each defined node effect is the genuine circle average of its
coefficient, and the AMR is the average of these node effects. If coefficients
share a radial function g, point effects equal g of distance, every individually
defined circle effect equals g(d), and the defined AMR equals g(d). Only local
circle-average existence is required; no measurability of the whole field is assumed. -/
theorem SAP.P008b.T27 : SAP.P008b.T27WholeStatement := by sorry

/-- P008-T28; pp. 143–145 (PDF pp. 6–8).
The audit's fixed common-Bernoulli model with uniformly bounded circle outcomes and uniformly bounded collection-dependency degree gives consistency for any fixed empty-arm completion.
Restriction: Retains only that explicit sufficient consistency version; omits consistency under the cited general conditions, standardized asymptotic normality, and asymptotic type-I-error conservativeness of spatial-HAC intervals. The nonnegative uniform bound is explicit. -/
theorem SAP.P008b.T28 : SAP.P008b.T28Statement := by sorry
