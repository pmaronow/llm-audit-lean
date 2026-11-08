All five declarations are faithful to their recorded scopes. T1–T4 cover the
whole canonical claims. T5 correctly discloses its narrower scope.

| Declaration | Verdict | Scope checked |
| --- | --- | --- |
| `SAP.P027a.T1` | faithful / none | Every C1–C6 clause: continuous-start design, demeaning, complete eight-unit witness, all six configurations, and fixed-fraction nonvanishing. |
| `SAP.P027a.T2` | faithful / none | Every (i)–(vi) clause, including arbitrary centered populations, moment-only noise assumptions, both scales of the ratio of averages, empirical size-variance calibration, and the guarded limits and bounds. |
| `SAP.P027a.T3` | faithful / none | Both cluster witnesses, exact probability and zero-pair tables, all required samplewise values and moments, and both conservative bias increases. The canonical mixed witness requires moments, not an additional samplewise table. |
| `SAP.P027a.T4` | faithful / none | Arbitrary almost-sure cluster partitions, preservation on possible samples, both A-star formulas, exact factor 1/2, strict/equal-size cases, degree bound, squared-difference identity, conservativity, and both example directions. |
| `SAP.P027a.T5` | faithful / none | The disclosed subset: four rounding-robust numeric violations and the scalar 120-unit original/grouped witness. Universal and finite-collection bounds, stronger numeric thresholds, explicit phase totals, other table columns, and identification of the reported column are expressly omitted. |

The blind reading and junk-value audit were saved in
[reading.md](/home/ubuntu/sap/tasks/FW-P027a-r5g1/reading.md) before reading the
claims. The independent claim-stage decisions are in
[claim-stage.json](/home/ubuntu/sap/tasks/FW-P027a-r5g1/claim-stage.json).
Reading the record required no change to those decisions. Every closure entry
was reviewed, including the 102 distinct generated proof declarations.

The retained definitions use the paper's positive-joint HT sum, ordered
zero-pair convention, and exponent-2 correction; I checked the conventions
against the [main paper, p. 237](https://www150.statcan.gc.ca/n1/pub/12-001-x/2013001/article/11831-eng.pdf).
The four table pairs agree with the
[supplement, Table A3](https://cyrussamii.com/wp-content/uploads/2013/08/smj_suppl.pdf).
No reviewed declaration labels a refutation of interpretive guidance as a
refutation of the canonical assertion itself.

The nonvacuity instances in
[scratch/Nonvacuity.lean](/home/ubuntu/sap/tasks/FW-P027a-r5g1/scratch/Nonvacuity.lean)
compiled successfully using the prescribed `sap-lean` command. Their printed
axiom dependencies contain no `sorryAx` or Challenge theorem. They include
nonzero noise variance, positive variance-ratio guards, nonzero correlation,
almost-sure clustering with actual disagreement on a null atom, and unequal
linked group sizes. Independent exact rational enumeration in
[scratch/exact_checks.py](/home/ubuntu/sap/tasks/FW-P027a-r5g1/scratch/exact_checks.py)
passed for all five targets; results are saved in
[scratch/exact-results.json](/home/ubuntu/sap/tasks/FW-P027a-r5g1/scratch/exact-results.json).

One historical provenance note at `record.json:149` says the empirical
size-variance derivation is omitted. The current statement includes it in
`SAP/P027a/Defs/WholeW1/Part1.lean:66` and `:188`; it is not an actual restriction
of T2. Its `whole` decision and null restriction agree with the current
statement and docstring. This stale row-use explanation does not change the
declaration's scope or verdict.

Real and ENNReal division, empty types and sums, Bochner integrability, real
square root, and casts were checked. No substantive claim uses a junk value.
The m=0 value in T2's rational limit sequence is only an irrelevant initial
term. No source statement or docstring correction is needed.
