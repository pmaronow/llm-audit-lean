# Delta referee report

**18 targets: 6 correct whole, 12 correct restricted; no outstanding issues.** All 18 have severity `none`. The one earlier adverse target finding, comprising two T14 disclosure issues, is **fixed**. No earlier issue is partly fixed or not fixed.

| Verdict | Count |
| --- | ---: |
| correct_whole | 6 |
| correct_restricted | 12 |
| restriction_inaccurate | 0 |
| not_faithful | 0 |
| vacuous | 0 |
| false | 0 |
| omission_ok | 0 |
| omission_questionable | 0 |

## Earlier finding: P003-T14

| Earlier issue | Status | Revised evidence |
| --- | --- | --- |
| The disclosure advertised a rescaling/coordinate correspondence absent from the theorem. | **Fixed** | The revised Challenge restriction and `record2.json` explicitly omit a source lattice law `f`, the construction `g(j)=f(j/k)`, and the assertion that this is the pmf of `kX`. |
| The displayed normalization was already part of `IsMass g`, rather than normalization proved by transporting a source law. | **Fixed** | The revised summary calls the mass assumed, and the restriction explicitly retains only normalization already contained in the hypothesis, together with the physical-mean identity. |

The revised [Challenge docstring](/home/ubuntu/sap/tasks/CHFID-P003a-b/SAP/P003a/Challenge/Part2.lean:6) and record use the replacement restriction proposed in the earlier finding, after whitespace normalization and removal of the introductory `Restriction:` label. The account in [architect-report.md](/home/ubuntu/sap/tasks/CHFID-P003a-b/architect-report.md) correctly describes this as a disclosure repair. It does not claim to restore the omitted mathematics.

The [T14 proposition](/home/ubuntu/sap/tasks/CHFID-P003a-b/SAP/P003a/Defs/Part9.lean:13) remains narrower than canonical T14(iii). Its mathematical content is unchanged: the corrected SD examples, impossibility of global decrease for a normalized pmf, fair mean, physical-coordinate mean identity for an assumed `IsMass g`, repeated normalization, and fixed printed-rescaling witness. The new text accurately discloses both the stronger moment hypothesis and omitted law correspondence. Its verdict therefore changes from `restriction_inaccurate` to `correct_restricted`; the earlier `narrower` comparison with the canonical claim remains valid.

## Changes and labels

I reread all ten Defs parts, their import root, both Challenge parts and their import root against the mathematical dictionary and all 18 theorem readings in [reading.md](/home/ubuntu/sap/tasks/CHFID-P003a-b/reading.md). **No change to a theorem's mathematical type or supporting definition was identified.** T14's summary and restriction are the only changed scope description. Comparing the two record files finds exactly one changed field: T14's `restriction`. All decisions, theorem mappings and other restriction texts are unchanged.

This comparison uses the saved mathematical reading; no round-one raw-source hash snapshot was available. Current source hashes and the machine-checked record delta are saved in [scratch/delta-review.json](/home/ubuntu/sap/tasks/CHFID-P003a-b/scratch/delta-review.json).

| Target | Revised decision | Verdict | Delta assessment |
| --- | --- | --- | --- |
| P003-T29 | whole | correct_whole | Unchanged complete coverage statement. |
| P003-T1 | restricted | correct_restricted | Unchanged legal coverage counterexample and disclosed omissions. |
| P003-T2 | whole | correct_whole | Unchanged dependent-missingness coverage, completion inclusion and coupling. |
| P003-T3 | whole | correct_whole | Unchanged union/hull coverage, completion count and repaired numerical example. |
| P003-T4 | restricted | correct_restricted | Unchanged printed-search counterexamples and disclosed omissions. |
| P003-T5 | restricted | correct_restricted | Unchanged sentinel-search guarantees and disclosed omitted consequences. |
| P003-T11 | restricted | correct_restricted | Unchanged all-zero threshold counterexample; general claim still explicitly omitted. |
| P003-T12 | restricted | correct_restricted | Unchanged finite-support repair; experiment specialization still explicitly omitted. |
| P003-T13 | whole | correct_whole | Unchanged table/count SATE identity and both printed-numerator witnesses. |
| P003-T14 | restricted | correct_restricted | Both earlier disclosure issues fixed; mathematical scope unchanged. |
| P003-T9 | restricted | correct_restricted | Unchanged common-Boolean counterexample; second counterexample still explicitly omitted. |
| P003-T10 | whole | correct_whole | Unchanged independent smoothing, center shift and parity-lattice assertion. |
| P003-T15 | restricted | correct_restricted | Unchanged SD theorem; induction facts and gap examples still explicitly omitted. |
| P003-T16 | restricted | correct_restricted | Unchanged normalized signed sum and pair outcomes; other components explicitly omitted. |
| P003-T17 | restricted | correct_restricted | Unchanged fixed extension, rank validity and exact tails; formula derivation/examples explicitly omitted. |
| P003-T21 | restricted | correct_restricted | Unchanged accepted effects, interval and exclusion; enumeration/maximality clauses explicitly omitted. |
| P003-T22 | restricted | correct_restricted | Unchanged minimum-base/reuse completeness and witness; executed confidence-set comparison explicitly omitted. |
| P003-T23 | whole | correct_whole | Unchanged arbitrary-decision rejection cutoff and endpoint consequence. |

The six `whole` decisions retain the canonical content accepted in round one; no clause has been removed. All twelve `restricted` decisions have restrictions matching their Challenge docstrings after whitespace normalization. T14's revised restriction is now complete. There are no `refuted` or `omitted` decisions in `record2.json`.

The counterexample targets T1, T4, T9 and T11 remain accurately labeled `restricted`, because their omitted canonical clauses are disclosed. They continue to refute their specified printed readings: legal missingness coverage below `1-alpha`; wrong return and all-fuel nontermination on legal search inputs; a dependent sum violating SD; and an actual real rejecting half-line with no least member, respectively. The availability of a `refuted` label creates no obligation to relabel these partial canonical packages.

## Junk values and nonvacuity

No mathematical hypothesis, conclusion, domain or definition changed. The nonvacuity instances and checks from round one therefore remain applicable; [findings2.json](/home/ubuntu/sap/tasks/CHFID-P003a-b/findings2.json) supplies an instance or justification for every target.

For T14 specifically, choose `k=2`, `g=zeroMass`. The earlier Defs-only [scratch check](/home/ubuntu/sap/tasks/CHFID-P003a-b/scratch/Check.lean) proves `IsMass zeroMass` and `IsSD zeroMass`. The mass sums to one, has finite support and zero absolute first moment, and both means are zero. Thus the retained lattice component has satisfiable hypotheses and uses a positive denominator. Its explicit `IsMass` premise prevents nonsummable real `tsum` defaults from supplying the mean. The all-integer witness `2*j != 1/2` is ordinary rational arithmetic, independent of `k` and `g`. Repeated normalization is openly disclosed and does not make the entire proposition vacuous.

The unchanged guards still protect positive population/arm sizes, nonempty finite probability spaces, legal natural subtractions, finite or summable means, and positive search-domain lengths. Exact empty inversions still count as noncoverage rather than producing spurious endpoints. No new junk-value or nonvacuity issue was identified.

## Validation

Python checked all 18 target/theorem mappings, all twelve restriction/docstring matches, the single record-field delta, and import boundaries for the fourteen supplied Lean source modules. The revised T14 disclosure was also checked against the precise replacement proposed in `findings.json`. `findings2.json` was parsed and checked for the requested schema, allowed verdicts/severities, target coverage and report counts.

No new Lean proof or compilation was needed for this documentation-only revision. Round-one compilation and exact enumeration are retained as evidence for the unchanged statements. I did not treat the architect's proof/Comparator account as a substitute for this statement review or inspect external project files linked from that account. `lake` was not run.
