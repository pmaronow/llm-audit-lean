# Declaration review

All five declarations are **faithful**, severity **none**. Their current `whole` decisions are correct. No claim-stage classification changed after reading `record.json`.

The blind reading was saved in `reading.md` before opening the canonical claims or review history. Every listed closure declaration was inspected, including the types of all 38 generated auxiliaries. The review used the supplied canonical text and local Mathlib sources.

| Declaration | Result |
| --- | --- |
| T16 | All three geometric witnesses are present, including the full zero-radius interference table, every prescribed L>5, positive-radius contour gap, and exact thin-polygon distances and unbounded counts. |
| T17 | The compact-node diameter cutoff, C3 implication, point specialization, area/diameter count bound, and both missing-bound counterexamples cover the corrected claim. |
| T18 | Both corrected rates are unconditional. The explicit formula identity, balanced witness, scaled variance 4/3, even-row failure, and p=1/2 equality are present. |
| T19 | Both witnesses have the required moments, full dependency graphs, exact fair-sign sums and standardizations, and failure of normal convergence. |
| T20 | The general and normalized corrected CLTs, both actual contrast arrays, exact identities, numerical bounds, shared-source graph, and variance-conditional applications are present. |

The usual measure-theoretic conditions are assumed. Explicit averaging regularity rules out invalid spatial integrals and masses. Measurability and boundedness on probability spaces justify the CLT moments. Positive denominator assumptions protect statistical interpretations. The disclosed empty-arm convention affects events whose probabilities vanish; empty initial rows do not change limits. No statistical conclusion depends on a junk value.

Each counterexample was checked against the assertion it challenges, with the printed reading and its conditions written out in [WitnessChecks.md](scratch/WitnessChecks.md). T16 meets the source-range and area-only premises; T18's fixed balanced outcomes admit the stated local spatial setting; T19's independent underlying signs give full independence across unlinked vertex sets. Their positive sum variances make standardization genuine. The canonical T16 and T19 claims already request these counterexamples, so `whole` is the correct decision.

Two independent scratch files compiled with `sap-lean`, without invoking Challenge theorems or using `sorry`:

- `scratch/Nonvacuity.lean`: a complete compact-node cutoff instance; a spatial sequence satisfying all T18 assumptions jointly; and finite T18/T19 variance and sum calculations.
- `scratch/CLTNonvacuity.lean`: independent-sign arrays satisfying every hypothesis of both general and normalized corrected CLTs.

Additional exact rational checks passed for the balanced error at N=2,4,6,8 and pair cancellation at N=1,3,5,7,9. The witness supplement gives the separate mathematical unit-square count instance and spatial examples with positive scaled variances for both estimators. Finite checks supplement the all-row mathematical arguments. No `lake` command was run; the two-process limit was respected.

All three earlier T20 issues are **fixed**: `Challenge/Part1.lean:47` and `Defs/WholeW2.lean:262` now say “bounds”; the definition docstring at `Defs/WholeW2.lean:232` says “Centered contrast bounds, with no geometry assumed.” None claims optimality. The retained identifier `CLTSharpBounds` does not assert optimal constants. Each earlier issue has its own resolution in `findings.json`.

The report's historical restriction tables are explicitly superseded by its whole-version integration. Current source and record agree. Both output JSON files parse, contain exactly the five requested declarations, and reproduce the closure fingerprints.
