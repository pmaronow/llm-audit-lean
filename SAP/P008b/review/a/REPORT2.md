Delta review of 14 targets. My earlier T17 finding is **fixed**: 1 fixed,
0 partly fixed, 0 not fixed. No new issue was found.

| Referee verdict in the required existing schema | Count |
| --- | ---: |
| correct_whole | 2 |
| correct_restricted | 11 |
| omission_ok | 1 |
| restriction_inaccurate | 0 |
| not_faithful | 0 |
| vacuous | 0 |
| false | 0 |
| omission_questionable | 0 |
| Total | 14 |

All severities are `none`. The accepted architect decisions in `record2.json`
are **0 whole, 11 restricted, 2 refuted, 1 omitted**. The existing findings
schema has no `correct_refuted` verdict. Its two `correct_whole` entries assess
complete coverage of the canonical *counterexample targets*, T16 and T19;
their accepted architect label is `refuted`. They are not classified as proofs
of the printed assertions.

The revised Defs and all 13 theorem types were compared with `reading.md`.
Their objects, definitions, quantifiers, hypotheses and conclusions match that
saved reading. The changes are the T17 summary sentence and the new refutation
prefixes for T16 and T19. Comparing the records shows exactly two changed
decision fields: T16 and T19 changed from `whole` to `refuted`; their theorem
names and mathematical statements remain the same. The other 12 record entries
are unchanged.

| Target | Earlier finding and delta assessment |
| --- | --- |
| T15 | Previously correct_restricted; unchanged and accepted. Euclidean distance, integrability and positive finite band mass remain explicit; the accompanying edge-average display remains a disclosed omission. |
| T16 | Previously a complete canonical counterexample; revised `refuted` label and prefix accepted. Counts, sums, nonempty summaries and all three contrasts remain present. The refutation and its scope are checked below. |
| T17 | **Fixed.** `SAP/P008b/Challenge/Part1.lean:16` now says “whose radial width is twice the tolerance when k ≤ d”. This agrees with `SAP/P008b/Defs/Part6.lean:34` and canonical T17(a). The two polygon-implementation omissions remain accurate and disclosed. The final verdict is correct_restricted. |
| T18 | Previously correct_restricted; unchanged and accepted. Switching and marginal contrasts, normalized weighted AMR, scaling and lower bounds remain present; the calculus, Taylor and amplitude-three numerical assertions remain disclosed omissions. |
| T19 | Previously a complete canonical counterexample; revised `refuted` label and prefix accepted. The full raster, boundary convention, outcomes, law, contrasts, node effects and AMRs remain present. The refutation and its scope are checked below. |
| T20 | Previously correct_restricted; unchanged and accepted. Boundary formulas, the block example, nonempty-frontier statement and explicit unequal functionals remain; the fitted-curve sentence remains omitted as disclosed. |
| T21 | Previously correct_restricted; unchanged and accepted. Only the true rational comparison is stated, with the assignment law, actual quantiles and significance inference expressly omitted. |
| T22 | Previously correct_restricted; unchanged and accepted. The numerical strict rejection predicate is true; actual input identification, general calibration and error rate 0.05 remain expressly omitted. |
| T23 | Previously correct_restricted; unchanged and accepted. The zero-tail population covariance identity remains; the table, coverage and toy dependence-accounting assertions remain disclosed omissions. |
| T24 | Previously omission_ok; unchanged and accepted. No theorem was added. The supplied account still defines no cumulative forest-loss event or reconstruction that would justify refuting the particular reported values. All three values can lie in the range of a difference of probabilities; an unrelated sum outside that range is insufficient. |
| T25 | Previously correct_restricted; unchanged and accepted. The marginal/integral identities and eight-assignment formulas remain, with disclosed Euclidean and genuine-average conditions and positive node count for the AMR. |
| T26 | Previously correct_restricted; unchanged and accepted. The measurable-field sharp-null implication and nonempty-circle cancelling witness remain; other metrics, fields without the added measurability hypothesis and empty-circle assertions remain disclosed exclusions. |
| T27 | Previously correct_restricted; unchanged and accepted. Point effects retain arbitrary finite designs; the circle and AMR clauses retain the disclosed measurable Euclidean field, integrability, positive finite masses and positive node count. |
| T28 | Previously correct_restricted; unchanged and accepted. Fixed common Bernoulli assignment, uniform bounds, independence of separated collections and fixed empty-arm completion still give only the audit's sufficient consistency statement. The cited general conditions, normality and HAC conservativeness remain disclosed omissions. |

T16's `refuted` label applies to the canonical assertion that the supplied
archived donut formula yields a band centered at the outer grid radius.
At grid radii 2 and 4 the theorem gives buffer counts 1 and 3 and sums 4 and 6,
so that formula gives `(6-4)/(3-1) = 1`. The centered band of the same width,
`[3,5]`, has mean 4. Control summaries are zero and both treatment arms contain
one node, so the differing means also give differing Hájek estimates. The
explicit rectangle boundaries are nonempty; their own-cell distances are
`0,19/8,27/8,35/8`, and cross-polygon distances exceed 5. This is a spatial
counterexample to the claimed identity, with no empty denominator. The canonical
note says the arithmetic example is specified by distances and outcomes, so
the alternative rectangular realization is sufficient. The refutation uses
the supplied archived formula; it establishes no claim about execution of
an unexamined release or the provenance of Figure 8.

T19's `refuted` label applies to the canonical identification of the zero-distance
edge summary with the whole-polygon summary. The theorem retains every clause
of the specified 200-cell example: two 25-cell polygons, 16-cell eight-neighbor
boundaries, nine interior cells, the binary potential outcomes under all four
assignments, the independent fair assignment law and observed-assignment mass
1/4, contrasts 0 and 9/25, node effects 9/25 and 0, and AMRs 0 and 9/50.
These unequal values refute the functional identification under the supplied
boundary-selection premise. They are not asserted as reconstructed values
for the empirical villages. All selected sets and both observed treatment
arms are nonempty.

The repaired T17 statement continues to avoid junk distances and means. Its
circle geometry assumes `d > 0`, so the reference circle is nonempty. Its
clipped interval is `[max 0 (d-k),d+k]`; `d=1,k=2` gives width 3 and is now
outside the conditional twice-tolerance claim. When `k ≤ d`, the clipping
disappears and the stated width is `2k`. Strict buffer-cardinality growth
ensures nonempty added-cell means, and the first-buffer branch assumes a
nonempty buffer. Cardinality differences in the quotient are real subtraction;
the natural index subtraction is guarded by `j > 0`.

The prior nonvacuity checks were rerun against the revised compiled Defs using
the supplied `sap-lean` wrapper, with exit status 0 recorded in
`scratch/lean-check2.log`. Exact rational checks independently reran the two
counterexamples, all four raster assignments, nonempty means and AMRs, as well
as the earlier covariance, cancellation and dependency instances; the results
are in `scratch/finite-checks2.json`. The earlier stage files were preserved.
`findings2.json` was parsed with Python and checked for the original field and
verdict schema, unique coverage of every target, and agreement with the revised
theorem list.
