P008b packages exactly the fourteen unit targets T15–T28: 1 whole, 12 restricted, 0 refuted, 1 omitted. All thirteen listed theorems are proved; there are no open glue tasks.

T19 is whole: it retains the complete canonical 200-cell counterexample, counts, eight-neighbour boundaries, potential outcomes, independent fair design, observed contrasts, node effects and AMRs. T16 is restricted: it retains the distance/outcome lists, buffer counts and sums, zero control means, three treated means and three Hajek contrasts, but replaces the specified square/raster realization with rectangles and eight selected points. These theorems establish their canonical counterexamples; they do not refute those counterexamples. Their docstrings identify the symmetric-band and area-equals-edge readings that the examples contradict.

Target restrictions and omission:

- P008-T15 (restricted): Uses only Euclidean distance, omitting the other permitted metrics; requires integrable outcomes and positive finite band mass; omits the accompanying edge-average display.
- P008-T16 (restricted): Replaces the specified half-side-1/8 squares centered at (0,0) and (20,0), their separation of 20 and half-unit raster realization with rectangles [0,1] × [-1,1] and [100,101] × [-1,1] and eight selected points (100i + 1 + δc, 0), where δ = (0, 19/8, 27/8, 35/8), using distance to the rectangle boundaries. It retains the distance/outcome lists and arithmetic but omits the specified square/raster realization.
- P008-T17 (restricted): Includes the full point-intervention disk and the first full-buffer formula, but omits identification of a zero-radius polygon buffer with all polygon cells and identification of the archived polygon disk branch.
- P008-T18 (restricted): Omits the derivative of the negative kernel term, its maximum characterization and exact maximum value, the explicit exponential Taylor bound, and Figure 4's numerical compatibility with amplitude three.
- P008-T20 (restricted): Requires nonempty raster boundaries and nonempty continuous frontiers; omits the corrected sentence about how the reported smoothed curve was fitted.
- P008-T21 (restricted): Retains only the numerical comparison; omits identification of the actual assignment law and its quantiles, the significance inference, and the empirical spillover conclusions.
- P008-T22 (restricted): States only that nominal decision; omits all general test-calibration and exactness assertions, validation of these inputs as the spatial toy statistic and quantiles, and any assertion of actual error rate 0.05.
- P008-T23 (restricted): Retains only the cutoff instruction's covariance identity; omits the reported interval table, its coverage interpretation, the assertion that cutoff 0.4 captures toy interference dependence unlike zero, and the empirical interval-width comparison.
- P008-T24 (omitted): The only credited row has final status wrong_credit: it refutes a universal statement about arbitrary numerical arrays, without linking its counterexample to the reported cumulative estimate, its permutation percentiles, or a forest-loss event. The three printed values lie in [-1,1], so its range obstruction does not refute their asserted empirical interpretation.
- P008-T25 (restricted): Uses only Euclidean circles and omits the other permitted metrics; averages require positive finite circle mass and integrable potential outcomes, and the AMR requires a positive number of nodes.
- P008-T26 (restricted): The implication uses Euclidean circles and a measurable spatial field; node averages require positive finite mass and integrable outcomes, and the AMR requires a positive number of nodes. The converse witness concerns every nonempty finite circle; no AMR assertion is made for empty circles. Other permitted metrics and fields without the measurability hypothesis are omitted.
- P008-T27 (restricted): Circle conclusions use Euclidean distance, a measurable spatial field, integrable potential outcomes and positive finite circle masses, with a positive number of nodes. Other permitted metrics and cases without whole-field measurability are omitted.
- P008-T28 (restricted): Retains only that explicit sufficient consistency version; omits consistency under the cited general conditions, standardized asymptotic normality, and asymptotic type-I-error conservativeness of spatial-HAC intervals. The nonnegative uniform bound is explicit.

The route uses shared SAP definitions in seven Defs parts. Both Challenge and Solution import those same compiled modules, so their statements and all definitions mentioned in them are the same declarations. Challenge imports no project modules. Each theorem has exactly the same fully qualified name and shared statement constant in both files.

Bridge.lean transfers the three finite-law fields and the five spatial-model fields directly into project structures. Every correspondence is proved by rfl or Iff.rfl: finite expectations, probabilities, covariance and variance; the uniform law and marginalization; circle sets, measures, masses, normalized integrals, outcomes and effects; bands and the sharp null; additive outcomes and Hajek estimates; common Bernoulli laws, collection dependency, finite AMRs and completed estimators; raster means, rectangle distances and line-circle means. The remaining fixed finite definitions unfold to the same bodies under the two namespaces.

Solution proofs instantiate exported declarations and combine their conclusions. Additional glue only unfolds the supplied buffer formula, identifies the difference of nested distance filters with the corresponding annulus, subtracts exported toy marginal means, and performs scalar arithmetic. T19 uses the existing expect_const helper to read its node effects from the exported area-mean formula; its interior counts and outcome sums are arithmetic consequences of exported counts and means. No new probabilistic, analytic, geometric or asymptotic argument is supplied.

Shared rows are explicit in the manifest. T19 uses expect_const, credited as a helper under T25. T20 uses boundary_counterexample and polygon_raster_counterexample, credited under T19, to state the same example expressly required by T20(c). All these shared rows have final status ok. No wrong_credit row is used, and no declaration from another work unit is used.

Undefined-average branches are excluded: band and integral-circle claims require positive finite masses and integrability; AMRs over nodes require a positive node count; generic added-cell means require a strict count increase; first-buffer and raster summaries require nonempty sets. Continuous distance-to-boundary claims require a nonempty frontier. The cancelling example only claims averages on nonempty circles and records masses one and two at radii zero and one. The two fixed counterexamples have nonzero displayed counts and nonempty treatment arms. Empty-arm completion in T28 is part of the canonical sufficient version.

Validation: every Defs part and root, Bridge, Challenge part and root, and Solution compiled with the required sap-lean wrapper in dependency order. The only expected Challenge diagnostics concern its stubs. scratch/P008bAxioms.lean separately checks all thirteen solution theorems, with output in scratch/P008bAxioms.log. Their dependencies are recorded individually in manifest.json and are all permitted. Both JSON files parse; the target and theorem lists, import boundary, forbidden-token scope, and 300-line limit were checked.

The supplied [Comparator result](SAP/P008b/verification/comparator-result.json) and [kernel log](SAP/P008b/verification/comparator.log) record three-kernel acceptance before the T27 summary correction. This correction changes only its Challenge docstring; theorem statements, shared definitions, bridges and solution proofs remain identical to that snapshot. The configuration retains the same thirteen theorem names and required external kernel commands. No new external Comparator run is claimed for this revision.

Interpretive limits: the archived formulas and kernel are supplied mathematical inputs, not Lean verification of software execution or figure provenance. The restrictions preserve the actual final row judgments rather than implementing suggested repairs. No cited general theorem has been added as a hypothesis. The sufficient consistency result is not described as an asymptotic-normality or interval-coverage theorem.

Referee findings (revision 2).

Every entry in [referee A’s findings](referees/round1/a/findings.json) and [referee B’s findings](referees/round1/b/findings.json) was checked against the canonical target in [work.json](work.json), the shared SAP statement and its definitions. The paired table covers all 28 entries. No substantive objection was rejected.

| Target | Referee A / referee B | Resolution and independent check |
| --- | --- | --- |
| T15 | correct_restricted / correct_restricted | Accepted. Euclidean band integration and node exclusion remain stated; positive finite mass and integrability exclude undefined averages. Other metrics and the accompanying edge display remain disclosed omissions. |
| T16 | correct_whole / correct_whole | The arithmetic counterexample is retained, but declaration review later identified the missing specified square/raster realization. The final label is restricted and that replacement is now explicit. |
| T17 | restriction_inaccurate / restriction_inaccurate | Both correct. Fixed the summary to condition the twice-tolerance width on k ≤ d. The two existing polygon-implementation omissions and restricted decision remain unchanged. |
| T18 | correct_restricted / correct_restricted | Accepted. Normalized nonnegative weights give genuine finite means; the retained switching/marginal/AMR formulas, scaling and strict lower bounds leave the listed calculus, Taylor and amplitude-three numerical assertions unstated. |
| T19 | correct_whole / correct_whole | Accepted. The full canonical counterexample remains stated: 200 cells, counts 25/16/9, eight-neighbour boundaries, fair design, contrasts 0 and 9/25, node effects and AMRs 0 and 9/50. The final label is whole. |
| T20 | correct_restricted / correct_restricted | Accepted. Nonempty raster boundaries imply nonempty polygons; the frontier is closed and explicitly nonempty, avoiding the empty-distance branch. The fitted-curve sentence remains omitted. |
| T21 | correct_restricted / correct_restricted | Accepted. Minus 321/10000 is below minus 19/625; the type contains no assignment law, quantile identification or significance assertion. |
| T22 | correct_restricted / correct_restricted | Accepted. 797/100 is below 619/50, giving the nominal rejection disjunction. No calibration or empirical-input validation is stated. |
| T23 | correct_restricted / correct_restricted | Accepted. Finite covariance/variance need no integrability conditions; only the zero-covariance cutoff identity is stated, without the printed interval or coverage claims. |
| T24 | omission_ok / omission_ok | Accepted. The three empirical values lie in [-1,1]; the unrelated array range counterexample supplies neither their forest-loss event nor the asserted empirical interpretation. No theorem is added. |
| T25 | correct_restricted / correct_restricted | Accepted. The local marginal and effect identities require a valid circle, the AMR requires positive N and valid circles for all nodes, and the toy means use uniform four-bit assignments. Other metrics remain omitted. |
| T26 | correct_restricted / correct_restricted | Accepted. The implication retains measurable-field and genuine-circle conditions; the explicit converse witness concerns only nonempty circles, with masses one and two at its supported radii. |
| T27 | correct_restricted / correct_restricted | Accepted. Additive and homogeneous point identities retain arbitrary finite designs. Circle identities retain Euclidean geometry, field measurability and valid-circle conditions; other cases remain disclosed omissions. |
| T28 | correct_restricted / correct_restricted | Accepted. The statement retains fixed common Bernoulli assignment, uniform outcome and collection-dependency bounds, fixed empty-arm completion and consistency. General cited conditions, normality and interval conservativeness remain omitted. |

For A-T17 and B-T17, the independent arithmetic check is d = 1, k = 2: the clipped interval is [0,3], of width 3, whereas twice the tolerance is 4. The [formal width clause](SAP/P008b/Defs/Part6.lean#L34) already assumes k ≤ d, as does canonical T17(a). Only the [Challenge summary](SAP/P008b/Challenge/Part1.lean#L16) needed repair; no proof, hypothesis or shared definition changed.

Revision 2 incorrectly labelled T16 and T19 refuted by applying the refutation rule to the historical printed readings rather than to the canonical counterexample assertions. Declaration review below corrects that distinction. The canonical target, including its specified fixture, controls both the label and any restriction. T18 and T26 retain their disclosed restricted statements.

The thirteen fully qualified theorem names and all mathematical statements and proofs are unchanged. Every SAP module was recompiled in dependency order, all thirteen dependency checks were rerun, both JSON configurations were reparsed, and the import/options/token/line-limit checks were repeated. No open glue task was introduced.

## Declaration review round 1

Accepted every open finding for the two declarations. The reports copied under the two theorem directories contain the same review packet; the resolutions below use the entry matching each declaration. Sources: [T16 findings](fw/round1/T16/r1g1/findings.json), [T19 findings](fw/round1/T19/r1g1/findings.json), and the canonical claims in [work.json](work.json).

- T16, label_wrong/major, issue 1: accepted. The canonical assertion supplies a counterexample with adjacent-annulus, centered-band and full-buffer values 1, 4 and 2. The theorem establishes those facts, rather than negating that canonical assertion. Removed the misleading opening from the docstring, set the final decision to restricted because of issue 2, and explicitly named the reading refuted: an archived donut at a grid radius averages a band symmetric about that radius.
- T16, label_wrong/major, issue 2: accepted. Canonical definitions_needed specifies half-side-1/8 squares centered at (0,0) and (20,0), separation 20, a half-unit raster and treated-side cell centers (0,0), (5/2,0), (7/2,0), (9/2,0). [donutPolygonBoundary and donutSpatialCell](SAP/P008b/Defs/Part2.lean#L40) instead use rectangles [0,1] × [-1,1] and [100,101] × [-1,1] and points (100i + 1 + δc,0). In particular, the first cell is (1,0), not (0,0). Equal distance/outcome lists establish the same arithmetic discrepancy but do not establish the specified realization. The Challenge docstring and manifest now disclose the entire replacement and omit the specified square/raster realization. Restoring its geometry would require an additional geometric argument, so the existing rectangle proof is retained.
- T19, label_wrong/major: accepted. The [shared statement](SAP/P008b/Defs/Part5.lean#L32) establishes the canonical counterexample in full, including the 200-cell field, 25/16/9 counts, fair independent assignment, nonempty treatment arms, contrasts 0 and 9/25, and AMRs 0 and 9/50. Set the decision to whole and kept restriction null. Removed the misleading opening and named the reading refuted: a zero-distance edge estimate equals the contrast of within-polygon area means.

No shared definition, theorem statement, bridge or solution proof changed, so no additional mathematical dependency was introduced. All thirteen theorem names remain proved, with no open glue tasks. Recompiled all seven Defs parts, Defs root, Bridge, Challenge part and root, and Solution with sap-lean in dependency order; reran scratch/P008bAxioms.lean; reparsed both JSON files; checked the full target/theorem lists, exact disclosure agreement, permitted dependencies, both implicit-variable options, import boundary and file limits. The previous T17 width correction is retained.

## Declaration review round 2

Checked the matching declaration entries in [T16 findings](fw/round2/T16/r2g1/findings.json) and [T19 findings](fw/round2/T19/r2g1/findings.json) against the canonical counterexamples in [work.json](work.json), the shared definitions, Challenge docstrings and manifest. Both verdicts are faithful/none, with no current defect and no requested fix. The issues arrays record resolved history, rather than new objections.

- T16, earlier label finding: accepted as fixed. The manifest labels T16 restricted, and the [docstring](SAP/P008b/Challenge/Part1.lean#L11) identifies the symmetric-band reading contradicted by the example. Its contrasts 1, 4 and 2 establish the retained canonical counterexample facts. Kept the current label and statement.
- T16, earlier geometry finding: accepted as fixed by accurate restriction. The docstring and manifest explicitly replace the specified squares, separation 20 and half-unit raster with the two rectangles, eight selected points and rectangle-boundary distances. The specified square/raster realization remains omitted. Kept this disclosure; no restoration of the original geometry is claimed.
- T19, earlier label finding: accepted as fixed. The manifest labels T19 whole, with restriction null. Its [statement](SAP/P008b/Defs/Part5.lean#L33) includes the full raster, counts, eight-neighbour boundary characterization, potential-outcome summaries, fair design, contrasts 0 and 9/25, node effects and AMRs 0 and 9/50. The docstring names the area-equals-edge reading contradicted, rather than claiming to contradict the canonical counterexample. Kept the whole label and statement.


- T27, not_faithful/minor: accepted and fixed. The [review finding](fw/round2/T27/r4g2/findings.json) correctly distinguishes point and node effects. Canonical T27(a) in [work.json](work.json) and [T27Statement](SAP/P008b/Defs/Part7.lean#L46) identify point effects with g_i(x), node effects with the normalized circle average of g_i, and the AMR with the node average. A varying coefficient need not equal its circle average. For example, with coefficient x ↦ x₀, a unit-radius circle about zero, and unit point mass at (1,0), the genuine coefficient average is 1, whereas its value and point effect at (-1,0) are -1. The corrected [summary](SAP/P008b/Challenge/Part1.lean#L61) now says: “For additive outcomes, point effects equal the coefficients, node effects equal their genuine circle averages, and the AMR averages those node effects. For a common radial coefficient function g, node effects and the AMR at distance d equal g(d).” The restriction paragraph and restricted decision are retained. No shared definition, mathematical statement, bridge or proof changes.

Independent checks confirm genuine nonempty quantities: the rectangle boundaries contain their right-edge points, the averaging sets have sizes 2, 2 and 3, and the observed assignment has one node per arm. The raster boundary and area sets have sizes 16 and 25, the fair law has four assignments, and the AMR averages two node effects. The existing definitions and proofs therefore require no additional guard hypotheses. No current finding was rejected.

The T16 and T19 portion of round 2 required no Lean changes. The additional T27 finding requires only a Challenge docstring correction. All theorem statements, shared definitions and proofs remain unchanged. Recompiled every SAP Lean module in dependency order and reran all thirteen dependency checks with sap-lean. Regenerated and parsed manifest.json and comparator.json with the same theorem names, decisions and disclosures; checked both implicit-variable options, import boundaries, file limits and permitted dependencies. All thirteen theorems remain proved, with no open glue tasks. No new external Comparator run is claimed.

## Third-rung revision (Opus)

These checks precede the T27 docstring correction recorded above; their source-hash comparison describes that earlier revision.

Two items are open, both from the round 3 declaration reviews ([T16](fw/round3/T16/r3g1/findings.json), [T19](fw/round3/T19/r3g1/findings.json)). Both reviews return verdict faithful, severity none, with no fix. Each listed issue is a resolved earlier finding marked "FIXED; no current defect". I did not rely on those verdicts. I checked each statement against its canonical `statement` and `definitions_needed` in [work.json](work.json), and against every definition the statement depends on. **Verdict for both items: the referee is right; no defect exists.** Both statements and labels are kept unchanged.

### P008-T16 (`SAP.P008b.T16`, restricted): referee right, kept

*Canonical claim.* The kind is `counterexample`. The statement includes "[Statement refuted] That the archived “donut” estimate at the grid radius $d_j$ is the average over a band symmetric about $d_j$", followed by the validator's counterexample. Its four treated cells are "at distances $0$, $19/8$, $27/8$, $35/8$ from its boundary, with outcomes $4$, $2$, $0$, $8$", and the control cells have outcome 0. Its items are:

1. "Buffer of radius 2 … one cell, sum $4$. Buffer of radius 4: three cells, sum … $6$".
2. "The code's donut value at radius 4 is $(6 - 4)/(3 - 1) = 1$: the average over the cells at distances in $(2, 4]$".
3. The band $[3,5]$ has "average $(0 + 8)/2 = 4$".
4. "The control averages are $0$, so the AMR estimate at radius 4 is $1$ as implemented and $4$ for the centred band. (The full buffer … has average $6/3 = 2$.)"

`definitions_needed` adds: "In the validator's fixture the polygons are squares of half-side $1/8$ centred at $(0,0)$ and $(20,0)$ on a raster of $1/2$-unit cells, and the four cells lie on the line $y = 0$ at $x = 0, 5/2, 7/2, 9/2$."

*Lean statement* ([T16Statement](SAP/P008b/Defs/Part5.lean#L14)). It states:

- `∀ i c, donutSpatialDistance i (i, c) = bufferCellDistance c`, where `bufferCellDistance = ![0, 19/8, 27/8, 35/8]`.
- `∀ i j c, i ≠ j → 5 < donutSpatialDistance i (j, c)`.
- `(donutSpatialBuffer 0 2).card = 1` with sum `4`, and `(donutSpatialBuffer 0 4).card = 3` with sum `6`, at the assignment `![true, false]`.
- `∀ mode, donutSpatialMeans mode 1 ![true, false] = 0`.
- Hajek contrasts `1`, `4` and `2` for the adjacent annulus (2,4], the centered band [3,5] and the full buffer, and `hajek (donutSpatialMeans 0) … ≠ hajek (donutSpatialMeans 1) …`.
- The bare-list means `countMean (bufferCells 4 \ bufferCells 2) bufferCellOutcome = 1`, the `[3,5]` mean `= 4` and `countMean (bufferCells 4) bufferCellOutcome = 2`.

Distances are `Metric.infDist` to the boundaries of the rectangles [0,1] × [-1,1] and [100,101] × [-1,1] ([donutPolygonBoundary, donutSpatialCell](SAP/P008b/Defs/Part2.lean#L40)). The outcome is `bit (z 0) * bufferCellOutcome c` near polygon 0 and 0 near polygon 1.

*Assessment.*

- **Clauses 1–4.** Each is stated. The code's value $(6-4)/(3-1)$ is one-line arithmetic on the stated counts and sums, and it equals the stated annulus mean 1.
- **Label.** The canonical claim is itself a refutation ("[Statement refuted]"). Stating its counterexample is therefore `whole` or `restricted`, never `refuted`. The docstring correctly names the symmetric-band reading it contradicts and does not begin "The printed claim is false".
- **Why restricted.** `definitions_needed` is part of the claim, and it specifies the validator's half-side-1/8 squares, separation 20 and half-unit raster. The Lean realizes the same distance and outcome lists with different rectangles and eight points. So `restricted` is accurate and not an understatement: rule 4 does not apply. Restoring the square fixture would need a new `infDist` computation, which is not glue. The docstring and manifest disclose the replacement exactly.
- **Distance notion.** In the fixture the first cell lies inside its square, so its distance is to the polygon, not to the square's edge. In the Lean every point lies on or outside its rectangle, so distance to the rectangle boundary equals distance to the filled rectangle. The disclosure "using distance to the rectangle boundaries" is accurate.
- **Junk values.** Each rectangle boundary is nonempty (it contains (a+1, 0)), so `infDist` takes no empty-set junk value. The averaging sets have sizes 2, 2 and 3 at each node, and `nTreated` and `nControl` are both 1 at `![true, false]`. No displayed value is a division-by-zero artifact.

*Change:* none.

### P008-T19 (`SAP.P008b.T19`, whole): referee right, kept

*Canonical claim.* The kind is `counterexample`. The statement includes "[Claim refuted] That the value of the edge-based estimate at distance 0 is the contrast of the outcome averages over the area within the village polygons." The fixture is a "Raster of unit square cells covering $[0, 20] \times [0, 10]$ (20 columns, 10 rows; cell centres at half-integers)", with "$P_T = [2, 7] \times [2, 7]$ (treated …) and $P_C = [12, 17] \times [2, 7]$ (control …)". The outcome is 1 at the nine cells with centre coordinates in $\{3.5, 4.5, 5.5\}$. There are 25 cells per polygon, of which 16 are boundary and 9 interior. Its items are:

1. Edge contrast $0/16 - 0/16 = 0$.
2. Area contrast $9/25 - 0 = 9/25$.
3. "$Y_x(z_T, z_C) = z_T$ at the nine central cells of $P_T$ and $0$ elsewhere, with $Z_T, Z_C$ independent Bernoulli(1/2)". The boundary averages are 0 under all four assignments, so the edge AMR is 0. The node effects are $9/25$ and $0$, so the area AMR is $9/50$.

The "What is computed" premise fixes boundary cells as "the cells of the polygon that have a neighbouring cell, among the eight, outside it".

*Lean statement* ([T19Statement](SAP/P008b/Defs/Part5.lean#L33)).

- **Cells.** These are `Fin 20 × Fin 10`, with index (u,v) at centre (u+1/2, v+1/2). `rasterPolygonCells i` has `rasterPolygonLeft i ≤ u < rasterPolygonLeft i + 5` and `2 ≤ v < 7`, with left edge 2 or 12. That gives centres 2.5–6.5 (or 12.5–16.5) by 2.5–6.5: exactly the cell centres in $P_T$ and $P_C$.
- **Outcome.** `polygonRasterOutcome c z` is `bit (z 0)` when `3 ≤ u ≤ 5 ∧ 3 ≤ v ≤ 5` (centres 3.5, 4.5, 5.5) and 0 otherwise. This is canonical item 3's potential-outcome table.
- **Clauses stated.**
  - card 200, and per polygon cards 25 and 16 and interior card 9;
  - the eight-neighbour boundary characterization `c ∈ rasterPolygonBoundary i ↔ ∃ a b : Fin 3, (a.val ≠ 1 ∨ b.val ≠ 1) ∧ (neighbour outside the block)`;
  - outcomes in {0,1}, and `∀ i z, polygonRasterEdgeM i z = 0`;
  - `polygonRasterAreaM i z = if i = 0 then 9/25 * bit (z 0) else 0`, with sums 9 and 0 at `![true, false]`;
  - `commonBernoulli (uniformLaw (Assignment 2)) (1/2)` and mass `1/4`;
  - Hajek contrasts `0` and `9/25`;
  - node effects (marginal differences) `9/25` and `0`;
  - `finiteAMR` values `0` and `9/50`;
  - `0 ≠ 9/25`, and `nTreated` and `nControl` both 1.

*Assessment.*

- **Clauses.** Every clause of items 1–3, the fixture and the boundary convention is stated. The intermediate remark that all 16 boundary cells have outcome 0 is immediate: the outcomes are 0/1 and their mean over 16 cells is stated to be 0.
- **Label.** The canonical claim is itself the refutation of the edge-equals-area reading. Stating it is `whole`, not `refuted`, and the docstring names that reading without saying "The printed claim is false".
- **Junk values.** The averages have stated positive denominators (16 and 25). The fair law is a genuine law on four assignments. The AMR averages marginal effects over two nodes, so no empty-arm Hajek ratio occurs.

*Change:* none.

### Rebuild and checks (this revision)

- **Lean, manifest, comparator.** No Lean file, manifest.json or comparator.json changed. Their SHA-256 hashes still equal the snapshot hashes in [comparator-result.json](SAP/P008b/verification/comparator-result.json).
- **Rebuild.** All twelve SAP modules were recompiled with sap-lean in dependency order: Defs Part1–7, Defs, Bridge, Challenge/Part1, Challenge, Solution ([scratch/opus_build.log](scratch/opus_build.log)). The return code was 0. The only diagnostics are the thirteen expected Challenge stub warnings.
- **Axioms.** [scratch/OpusAxioms.lean](scratch/OpusAxioms.lean) runs `#print axioms` for all thirteen theorems. Each depends on exactly `[propext, Classical.choice, Quot.sound]` ([log](scratch/OpusAxioms.log)).
- **Static checks.**
  - Forbidden tokens appear only as the thirteen Challenge proof stubs.
  - Every SAP file has both implicit-variable options.
  - Every file is at most 138 lines.
  - Challenge imports only `SAP.P008b.Defs`.
  - Both JSON files parse.
  - The manifest lists 14 targets, and comparator.json lists 13 theorem names.

Counts are unchanged: 1 whole (T19), 12 restricted, 0 refuted, 1 omitted (T24). All thirteen listed theorems are proved, and there are no open glue tasks.

## Whole versions (new proofs)

The following seven targets now use their supplied whole statements and proved whole theorems. T22 is `refuted`; the other six are `whole`. The Challenge declarations remain `:= by sorry`. The corresponding exports in `SAP/P008b/Solution.lean` use the whole proof terms, and `SAP/P008b/manifest.json` records the updated decisions, statement definitions, proof dependencies and removed restrictions.

- **P008-T22** (`SAP.P008b.T22`, `refuted`): `SAP.P008b.T22WholeStatement`; proof `SAP.P008b.WH.W1.T22_whole`.
  Files: `SAP/P008b/Challenge/Part1.lean`, `SAP/P008b/Defs/WholeW1.lean`, `SAP/P008b/WH/W1/Leaves.lean`, `SAP/P008b/WH/W1/Proofs/T22.lean`.
  Removed restriction: States only that nominal decision; omits all general test-calibration and exactness assertions, validation of these inputs as the spatial toy statistic and quantiles, and any assertion of actual error rate 0.05.

- **P008-T25** (`SAP.P008b.T25`, `whole`): `SAP.P008b.T25WholeStatement`; proof `SAP.P008b.WH.W1.T25_whole`.
  Files: `SAP/P008b/Challenge/Part1.lean`, `SAP/P008b/Defs/WholeW1.lean`, `SAP/P008b/WH/W1/Leaves.lean`, `SAP/P008b/WH/W1/Proofs/T25.lean`.
  Removed restriction: Uses only Euclidean circles and omits the other permitted metrics; averages require positive finite circle mass and integrable potential outcomes, and the AMR requires a positive number of nodes.

- **P008-T26** (`SAP.P008b.T26`, `whole`): `SAP.P008b.T26WholeStatement`; proof `SAP.P008b.WH.W1.T26_whole`.
  Files: `SAP/P008b/Challenge/Part1.lean`, `SAP/P008b/Defs/WholeW1.lean`, `SAP/P008b/WH/W1/Leaves.lean`, `SAP/P008b/WH/W1/P/T26_L1.lean`, `SAP/P008b/WH/W1/Proofs/T26.lean`.
  Removed restriction: The implication uses Euclidean circles and a measurable spatial field; node averages require positive finite mass and integrable outcomes, and the AMR requires a positive number of nodes. The converse witness concerns every nonempty finite circle; no AMR assertion is made for empty circles. Other permitted metrics and fields without the measurability hypothesis are omitted.

- **P008-T15** (`SAP.P008b.T15`, `whole`): `SAP.P008b.T15WholeStatement`; proof `SAP.P008b.WH.W1.T15_whole`.
  Files: `SAP/P008b/Challenge/Part1.lean`, `SAP/P008b/Defs/WholeW1.lean`, `SAP/P008b/WH/W1/Leaves.lean`, `SAP/P008b/WH/W1/Proofs/T15.lean`.
  Removed restriction: Uses only Euclidean distance, omitting the other permitted metrics; requires integrable outcomes and positive finite band mass; omits the accompanying edge-average display.

- **P008-T17** (`SAP.P008b.T17`, `whole`): `SAP.P008b.T17WholeStatement`; proof `SAP.P008b.WH.W2.T17_whole`.
  Files: `SAP/P008b/Challenge/Part1.lean`, `SAP/P008b/Defs/WholeW2.lean`, `SAP/P008b/WH/W2/Leaves.lean`, `SAP/P008b/WH/W2/Proofs/T17.lean`.
  Removed restriction: Includes the full point-intervention disk and the first full-buffer formula, but omits identification of a zero-radius polygon buffer with all polygon cells and identification of the archived polygon disk branch.

- **P008-T18** (`SAP.P008b.T18`, `whole`): `SAP.P008b.T18WholeStatement`; proof `SAP.P008b.WH.W2.T18_whole`.
  Files: `SAP/P008b/Challenge/Part1.lean`, `SAP/P008b/Defs/WholeW2.lean`, `SAP/P008b/WH/W2/Leaves.lean`, `SAP/P008b/WH/W2/P/T18_L1.lean`, `SAP/P008b/WH/W2/Proofs/T18.lean`.
  Removed restriction: Omits the derivative of the negative kernel term, its maximum characterization and exact maximum value, the explicit exponential Taylor bound, and Figure 4's numerical compatibility with amplitude three.

- **P008-T27** (`SAP.P008b.T27`, `whole`): `SAP.P008b.T27WholeStatement`; proof `SAP.P008b.WH.W2.T27_whole`.
  Files: `SAP/P008b/Challenge/Part1.lean`, `SAP/P008b/Defs/WholeW2.lean`, `SAP/P008b/WH/W2/Leaves.lean`, `SAP/P008b/WH/W2/P/T27_L1.lean`, `SAP/P008b/WH/W2/Proofs/T27.lean`.
  Removed restriction: Circle conclusions use Euclidean distance, a measurable spatial field, integrable potential outcomes and positive finite circle masses, with a positive number of nodes. Other permitted metrics and cases without whole-field measurability are omitted.

Validation: `python3 /home/ubuntu/sap/tools/rebuild_sap.py . P008b` rebuilt all 28 modules from scratch and passed the token scan. A scratch file importing only `SAP.P008b.Solution` ran `#print axioms` on all seven switched theorems; each uses exactly `propext`, `Classical.choice` and `Quot.sound`. Lean compilation ran sequentially, and Lake was never invoked. All other target declarations and manifest entries, and all existing statement definitions and proof files, are unchanged.

## Whole versions (new proofs)

- **P008-T16** (`SAP.P008b.T16`, `whole`): the Challenge now states `SAP.P008b.T16WholeStatement_W3` with the supplied corrected docstring and `:= by sorry`; the Solution uses `SAP.P008b.WH.W3.T16_whole`.
  Files: `SAP/P008b/Challenge/Part1.lean`, `SAP/P008b/Solution.lean`, `SAP/P008b/manifest.json`, `SAP/P008b/Defs/WholeW3.lean`, `SAP/P008b/WH/W3/Leaves.lean`, `SAP/P008b/WH/W3/P/T16_L1.lean`, `SAP/P008b/WH/W3/P/T16_L2.lean`, `SAP/P008b/WH/W3/Proofs/T16.lean`.
  Removed restriction: Replaces the specified half-side-1/8 squares centered at (0,0) and (20,0), their separation of 20 and half-unit raster realization with rectangles [0,1] × [-1,1] and [100,101] × [-1,1] and eight selected points (100i + 1 + δc, 0), where δ = (0, 19/8, 27/8, 35/8), using distance to the rectangle boundaries. It retains the distance/outcome lists and arithmetic but omits the specified square/raster realization.
  The whole proof establishes the corrected filled-square geometry, interior and boundary distances, common half-unit raster, finite selections, counts, means and Hajek contrasts. The supplied definitions, blueprint, leaves and whole proof files are unchanged.

No other Solution proof uses T16, so no dependent proof repairs were needed. Every other target's statement, docstring, proof and manifest entry is unchanged.

Validation: `python3 /home/ubuntu/sap/tools/rebuild_sap.py . P008b` rebuilt all 34 modules from scratch and passed the token scan. A scratch file importing only `SAP.P008b.Solution` ran `#print axioms SAP.P008b.T16`, reporting exactly `propext`, `Classical.choice` and `Quot.sound`. Lean processes ran sequentially, and Lake was never invoked.
