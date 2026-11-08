# Delta statement review

14 targets reviewed. Revised architect decisions accepted: **11 restricted,
2 refuted, 1 omitted**. No positive `whole` decision is claimed in `record2.json`.
Earlier adverse findings: **1 fixed, 0 partly fixed, 0 not fixed**.
New adverse findings: **0**. Severity: none 14; minor 0; major 0.

The requested JSON verdict schema is unchanged. Its counts are
`correct_whole`: 2, `correct_restricted`: 11, `omission_ok`: 1, all other
verdicts: 0. For T16 and T19, `correct_whole` evaluates completeness of the
canonical **counterexample targets**; their accepted architect decision is
`refuted`. It does not label either printed assertion true or change either
architect decision back to `whole`.

## Earlier finding: T17 fully fixed

My sole adverse finding was the unqualified assertion that the **clipped**
radial band has width twice the tolerance. The summary now says:

> Circle tolerance gives the clipped radial band, whose radial width is twice
> the tolerance when k ≤ d; adjacent-buffer differences average the added
> cells up to the outer radius.

This is at [Challenge/Part1.lean:16](/home/ubuntu/sap/tasks/CHFID-P008b-b/SAP/P008b/Challenge/Part1.lean:16).
It accurately describes the existing conditional width clause in
[Defs/Part6.lean:34](/home/ubuntu/sap/tasks/CHFID-P008b-b/SAP/P008b/Defs/Part6.lean:34)
and canonical T17(a). For d=1,k=2, the clipped interval is [0,3], of width 3;
the revised sentence no longer asserts width 4 in this case. The original
restriction sentence is unchanged and accurately identifies the two omitted
polygon-implementation identifications. No theorem change is needed.

The architect's account of this finding agrees with the actual files. The
other referee's adverse entry, as reproduced in the supplied architect report,
concerns the same condition and is addressed by this repair too.

## Changed descriptions and decision labels

All thirteen proposition bodies and their supporting definitions agree with
the mathematical readings saved in
[reading.md](/home/ubuntu/sap/tasks/CHFID-P008b-b/reading.md).
I found no changed hypothesis, quantifier, conclusion, carrier, integral,
probability, distance, normalization or numerical constant. The three changed
Challenge descriptions are T16, T17 and T19. Comparing `record.json` with
`record2.json` finds exactly two record changes: T16 and T19 change from `whole`
to `refuted`.

**T16: `refuted` accepted.** The new opening sentence identifies this as a
refutation. The retained theorem realizes the specified distances and outcomes
with two separated rectangular boundaries. It includes the own-boundary and
cross-boundary distance facts, buffer counts and sums, zero controls, adjacent
and centered means, all three contrasts 1,4,2, and their inequality. The supplied
archived buffer formula gives `(6-4)/(3-1)=1`; the symmetric same-width band
[3,5] gives `(0+8)/2=4`. This refutes the canonical unrestricted identification
of that archived donut rule with a band centered at its outer grid radius.
Changing the incidental square fixture to a rectangle realization does not
invalidate this counterexample. The source-formula identification is a supplied
premise; this is not a claim about software execution, the unavailable older
release, or the empirical plotted bands.

**T19: `refuted` accepted.** The new opening sentence also identifies a
refutation. The theorem still includes all canonical counterexample clauses:
200 cells; polygon, boundary and interior counts 25,16,9; the eight-neighbor
boundary characterization; binary potential outcomes; independent fair
assignment and probability 1/4 of the displayed allocation; zero boundary
means; the area-mean formulas; contrasts 0 and 9/25; node effects; and AMRs
0 and 9/50. These are unequal boundary and whole-polygon functionals in the
paper's spatial/raster setting. They refute the specified distance-zero
identification, without claiming to reproduce the empirical village values.

**T17: `restricted` accepted.** Only its summary changes. The repaired width
qualification, genuine circle-distance identity, clipped radial interval,
point-intervention disk, initial-buffer rule, nested-buffer arithmetic and
distance-buffer midpoint conclusions agree with the original reading and
canonical retained clauses. No new restriction or undisclosed assumption was
introduced.

## Remaining targets

| Target | Revised decision | Delta assessment |
|---|---|---|
| T15 | restricted | Unchanged; Euclidean geometry, genuine band averages and omitted edge display remain disclosed. |
| T18 | restricted | Unchanged; switching, marginalization, scaling and strict lower bounds retained; calculus, Taylor and amplitude-three numerical omissions disclosed. |
| T20 | restricted | Unchanged; nonempty raster boundaries/frontiers and omitted fitted-curve sentence disclosed. |
| T21 | restricted | Unchanged; only the printed rational inequality, without assignment-law, quantile or significance validation. |
| T22 | restricted | Unchanged; only the printed nominal strict-rule decision, without calibration or validation of toy inputs. |
| T23 | restricted | Unchanged; only the population covariance identity, without interval, coverage or toy-cutoff assertions. |
| T24 | omitted | Unchanged and justified; an unrelated out-of-range sum does not establish a refutation of the reported empirical probability interpretation. |
| T25 | restricted | Unchanged; Euclidean circle identities on positive finite integrable averages and the uniform sixteen-assignment calculation. |
| T26 | restricted | Unchanged; measurable-field sharp-null implication and genuine cancelling witness on every nonempty finite circle. |
| T27 | restricted | Unchanged; arbitrary-design additive and homogeneous effects, with the disclosed conditions on circle conclusions. |
| T28 | restricted | Unchanged; the explicit sufficient consistency theorem, without the cited general theorem, normality or interval error-control claims. |

All eleven restriction sentences in the Challenge exactly match `record2.json`.
Their mathematical scope remains as assessed in the first review. No newly
asserted whole claim silently drops a canonical clause.

## Junk values, nonvacuity and verification

The only changes are descriptions and decision labels, so they introduce no
new undefined-value branch or feasibility condition. The rechecked examples
also validate the changed refutation descriptions:

* T16's polygon boundaries are nonempty, so its zero distance is a genuine
  boundary distance. Its adjacent, centered and full-buffer selections contain
  2,2,3 own cells for each polygon. Both treatment arms contain one node.
* T19's boundary and area denominators are 16 and 25; its displayed allocation
  has probability 1/4 and one node in each arm. Its AMRs average valid finite
  means, not undefined Hajek estimates on empty-arm allocations.
* T17's positive-radius circles are nonempty. Strict buffer-cardinality growth
  gives a positive added-cell denominator; the initial mean requires a nonempty
  buffer. Subtractions in those denominators are real subtractions.

The earlier positive-mass circle and band examples, nonzero additive effects,
positive-variance cutoff example, and nonzero-target consistency sequence remain
admissible. Positive finite mass and integrability exclude totalized integral
values; the frontier assertions still require a nonempty frontier. T26 still
guards empty finite circles, and T28 still specifies its empty-arm completion.

`/home/ubuntu/sap/tools/sap-lean scratch/Check.lean` was rerun against the revised
compiled Defs and passed with no diagnostics. `python3 scratch/check_finite.py`
was rerun and passed, reproducing T16's contrasts 1,4,2 and T19's contrasts
0,9/25 and AMRs 0,9/50 with exact fractions and positive denominators. The
supporting files are
[Check.lean](/home/ubuntu/sap/tasks/CHFID-P008b-b/scratch/Check.lean) and
[check_finite.py](/home/ubuntu/sap/tasks/CHFID-P008b-b/scratch/check_finite.py).
The full mathematical graph-independence argument for the T28 nonvacuity
sequence remains reasoning rather than a claimed compiled proof.

Python validation confirmed that `findings2.json` parses, has the same field
and verdict schema as `findings.json`, and covers each canonical target exactly
once. Original review artifacts were preserved. No Solution, Bridge or
Comparator proof was read, no `lake` command was run, and Lean checks ran one
at a time. No additional paper or external source was needed for this delta.
