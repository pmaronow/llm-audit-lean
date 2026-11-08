All five reviewed declarations are **faithful**, with severity **none**. Their
definitions render the canonical notions correctly, and their docstrings
accurately describe their statements. No fixes are required.

The blind reading was saved in `reading.md` before opening `claims.json`.
All 135 distinct closure declarations, including generated auxiliary proofs,
were inspected through their sources and Lean's printed declarations. The
claim comparisons were saved in `claim-stage.json` before opening `record.json`.
The record's five `whole` decisions agree with those independent comparisons;
no step-2 conclusion changed after reading the record.

| Declaration | Reason for accepting the whole claim |
| --- | --- |
| `SAP.P008b.T15` | States the outcome-point band, both normalized averages, and the conditional exclusion of intervention nodes for every chosen coordinate metric. The average-existence guards exclude undefined normalization and nonintegrable outcomes. |
| `SAP.P008b.T16` | Includes the corrected filled-square geometry, common raster, exact cell selections, archived formula, positive denominators, and contrasts 1, 4, 2. It establishes the canonical counterexample to the centered-band interpretation. |
| `SAP.P008b.T17` | Includes the clipped circle-tolerance geometry, full disk, nested-buffer identity, first-index branch, zero-radius polygon cells, and later annuli with their width and midpoint. Indexing is shifted consistently from one-based to zero-based. |
| `SAP.P008b.T18` | Includes the gamma kernel, additive and marginalized effects, convex-weight AMR, amplitude scaling, derivative and maximum, Taylor bound, strict lower bounds, nonmonotonicity, and numerical enclosures. The amplitude-three compatibility witness is a genuine convex combination. |
| `SAP.P008b.T19` | Includes the specified raster, eight-neighbor boundary, outcome schedule, independent fair assignment, contrasts 0 and 9/25, and AMRs 0 and 9/50. Its docstring correctly identifies the reading of the edge guidance that the example contradicts. |

The counterexample conditions were checked separately. T16 uses distances to
the **filled** nonempty squares, eight distinct raster centers, the specified
outcomes at assignment `(true,false)`, no cross-polygon contamination, and
nonempty regions and assignment arms. Independent Euclidean-distance proofs
and arithmetic in `scratch/Geometry16.lean` confirm the witness. T19 uses
exactly the half-integer centers of the specified raster and squares; its
eight-neighbor criterion, all-assignment means, product assignment law, observed
contrasts, and AMRs are independently checked in `scratch/Check.lean`.
Neither item is labelled as refuting the canonical claim itself.

The junk-value audit found no dependence on an unintended completion. T15's
guards exclude zero/infinite mass and nonintegrable integrals. The distance-to-set
targets in T16 and T17 are nonempty. All evaluated finite means and Hájek
contrasts have positive denominators. Count differences are real subtraction;
previous-index subtraction is used only in the appropriate later-index branch.
T18's gamma parameters, exponential denominators and factorials are valid.

The following commands completed successfully, using no reviewed theorem as a
premise in the independent checks:

- `/home/ubuntu/sap/tools/sap-lean scratch/Check.lean`
- `/home/ubuntu/sap/tools/sap-lean scratch/Geometry16.lean`
- `/home/ubuntu/sap/tools/sap-lean scratch/Amplitude18.lean`

The checks also construct a positive-mass T15 instance, exercise T17's first
and later buffer branches, and construct a normalized two-cell T18 model whose
amplitude-three AMR is exactly −63/50. Detailed instances are recorded in
`findings.json`. Its five fingerprints were copied directly from `closure.json`.
