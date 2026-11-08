# Review of SAP.P011b.T20–T24

All five declarations are faithful under their recorded decisions. T24 is an accurately disclosed restriction; it is not the whole canonical claim.

| Declaration | Recorded decision | Claim coverage | Verdict | Severity |
| --- | --- | --- | --- | --- |
| SAP.P011b.T20 | refuted | Entire canonical counterexample | faithful | none |
| SAP.P011b.T21 | whole | Entire corrected claim | faithful | none |
| SAP.P011b.T22 | whole | Entire corrected claim | faithful | none |
| SAP.P011b.T23 | whole | Entire canonical finite counterexample | faithful | none |
| SAP.P011b.T24 | restricted | Formal content (i) only | faithful | none |

The blind reading and complete dependency audit were saved in `reading.md` before opening `claims.json`. The claim comparisons and witness-condition checks were then saved in `claim-stage.json` and `claim-audit.md` before opening `record.json`. No claim-stage conclusion changed after reading the record. No source declaration was modified.

T20's witness uses independent fair coordinates, not copies of one random draw. It satisfies valid constraints, the specified scaling constants, equal zero means, unit common variance, and every usual measure-theoretic condition. Its strict inside-event probability tends to one, contradicting the printed limit zero. The exact three canonical probabilities are present. Its `refuted` decision and docstring are accurate.

T21 states the complete pair-indexed identity and bound, including the canonical zero-variance convention, and every specified path-witness value. Finite second moments are the only added condition and are expressly allowed and disclosed. T22 correctly handles the adjacency bijection, all constraints, the factor two between quadratic and upper-triangle objectives, the additive diagonal term of V1, maximizers, and the unit-weight edge-count program.

T23 includes both infeasibility examples and unique optimality of edge23 with upper-triangle objective 3/4. Its docstring identifies the interpretation of the nonzero-product instruction being disproved. Its `whole` decision correctly describes coverage of the canonical counterexample. T24 gives the exact non-strict graph feasible-set equivalence and true-graph feasibility. Its docstring and recorded restriction correctly list every omitted textual correction and all of formal content (ii).

Independent validation passed:

- `/home/ubuntu/sap/tools/sap-lean scratch/Check.lean` compiled with no diagnostics, importing only Defs and using no Challenge result. It constructs data satisfying every T21 outer hypothesis; checks the fair-sign source and empty-graph estimator reduction; verifies both T23 incompatibilities and the compatible edge of value 3/4; and constructs valid T24 constraints with attained caps and an empty-vertex instance.
- `python3 scratch/exact_checks.py` passed exact rational checks of the sign probabilities, path covariance matrix and scaled variance, the complete T23 feasible list and unique optimum, and 216 three-vertex graph constraint systems. Lean separately checks the exact binomial counts.
- Generated closure proof declarations were inspected in `scratch/InspectTypes.out`; they supply ordinary instances, numeral validity, graph properties and index bounds, not concealed hypotheses.

No harmful division-by-zero, nonintegrable-integral default, infinity conversion, extremum default, or invalid finite index supports any reviewed result. The allowed zero-correlation convention and empty graph systems have their intended meanings. The supplied canonical journal claims were the comparison authority; an inaccessible publisher PDF and an earlier arXiv version were not substituted for them.
