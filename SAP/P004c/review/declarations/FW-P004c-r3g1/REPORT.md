# P004c declaration audit

All five declarations are faithful to their recorded scope. T32, T33, T39 and
T40 cover their whole canonical claims. T34 faithfully states its disclosed
restriction. No defects were found in the statements, dependency definitions,
record labels, or docstrings.

The blind reading of every closure entry was saved in `reading.md` before
opening `claims.json`. The independent claim comparisons were saved in
`claim-stage.json` before opening `record.json`. Reading the record required no
change to those comparisons. In particular, the canonical T34 statement's
asymptotic conclusion and full witness were treated as clauses even though its
audit note describes asymptotics as context.

| Declaration | Claim coverage and record assessment | Verdict |
|---|---|---|
| T32 | Exact local HT expansion, diagonal and four pair-component bounds, total bound, and all component/total O(1/N) rates. Its explicit neighborhood assumptions hold for the canonical geometric neighborhoods; radiuswise eventual C3–C4 thresholds are retained. | faithful / none |
| T33 | Correct linearization and all variance terms, exact centered-effect homophily identity and iff criterion, and all three positive-variance standardized-summand properties. | faithful / none |
| T34 | Correct identities, finite kernel bound, Bernoulli denominator rate, and scalar arithmetic. Both omitted clauses and the empty-arm convention are accurately disclosed. | faithful / none |
| T39 | Exactly the Bernoulli HT expectation equals the forced-coordinate marginal AME, for arbitrary interference. | faithful / none |
| T40 | All point, spatial-average, and node-mean identities under additivity, for every marginal assignment law and genuine spatial integrals. | faithful / none |

T34's narrower coverage is substantial but accurate: it omits the composed
bandwidth conclusion and the realized eight-node assignment/residual/kernel
counterexample, including the derivation of S=−1/4. Its last conjunct proves
only scalar arithmetic. The restriction in `record.json` and the docstring at
`SAP/P004c/Challenge/Part1.lean:26` both say so. It is correctly marked
`restricted`, not `refuted`; it does not refute the corrected canonical claim.

The definitions use actual finite Bernoulli products and sums. Pair conditional
means occur only at distinct nodes. Positive N and interior p protect the
finite denominators; T33 additionally requires positive actual variance before
standardizing. T34's real supremum is over a nonempty finite set, and its
denominator error has an explicit zero extension on empty treated arms.
`WellDefined` protects the spatial averages from zero/infinite masses and
nonintegrable outcomes. For T40, integrability of every coefficient g_i and the
baseline f follows from integrability of the all-false and singleton-treated
potential outcomes. General laws on full assignments represent all marginal
laws after the own coordinate is overwritten.

`scratch/Nonvacuity.lean` compiled successfully with
`/home/ubuntu/sap/tools/sap-lean scratch/Nonvacuity.lean` (exit 0), importing only
Defs and using no admissions. It constructs every hypothesis block, including a
complete spatial sequence satisfying the eventual conditions, an HT example
with variance 4, and a two-node additive example with nonzero coefficients and
measure-one regions. It also independently realizes T34's eight-node data and
checks both arm counts, zero arm residual sums, the actual cross-sum S=−1/4,
and the scalar inequality failure. This independent witness does not enlarge
the audited theorem. Compiler output is in `scratch/Nonvacuity.log`; it contains
only style/unused-variable warnings. No `lake` command was run, and no Challenge
theorem was used to establish nonvacuity.

`findings.json` contains exactly the five requested declarations and their
fingerprints copied from `closure.json`. Both JSON outputs were parsed and
validated with Python 3. The package sources were not edited.
