# P004b declaration review

All five declarations are **faithful**, severity **none**. Every canonical
clause is represented. The five `whole` decisions and null restrictions in
`record.json` are correct; the Challenge docstrings describe the actual
statements without overstating their scope. No step-2 judgment changed after
reading the record.

The blind reading was saved in `reading.md` before opening `claims.json`.
`claim-stage.json` was saved before opening `record.json`. All 112 distinct
declarations in the five dependency closures were examined, including the
generated numerical instances printed by `scratch/BlindProofs.lean`.

| Declaration | Canonical content checked | Verdict |
|---|---|---|
| T21 | Both node-variance expressions, corrected SAH bound and spatial specialization, both two-node witnesses | faithful |
| T22 | Population projection estimator, all five signed variance terms, neighbor's own fit, homophily implication, three-node witness | faithful |
| T23 | Corrected homophily and fitted residual, actual inverse-Gram row, scalar HAC sandwich, IPW numerator, genuine Gaussian quantiles and all event equivalences | faithful |
| T24 | Corrected matrix shapes, projection identities, leverage norm and reciprocal, uniform-kernel sandwich, trace adjustment and nonzero-denominator degrees of freedom | faithful |
| T25 | Corrected centering and conditional formula, means and estimator sums, HT case, eight-node witness, uniform L2-NED preservation | faithful |

General finite tables and arbitrary deterministic fits cover the paper's
spatial outcomes and fitted parameter values. The projection specialization in
T22 defines the population coefficients explicitly. Universal parameters in
T23 permit specialization to the paper's estimates; estimation consistency is
not needed for its algebraic claims. The corrected homophily quantity uses the
neighbor's own residual effect. These definitions contain the intended finite
sums, products and matrix operations, rather than assuming their conclusions.
The population projection coefficients and linearized IPW estimator were also
cross-checked against Appendix A.6 of the
[paper's preprint, PDF pages 68–70](https://arxiv.org/pdf/2010.13599#page=68);
their formulas match. Its proposition numbering differs from the published
supplement; the supplied canonical claims remain the review standard.

The canonical T21 statement expressly excludes feasible-estimator consistency.
The canonical T23 statement corrects displays and event presentations without
asserting coverage. T24 asserts the degrees-of-freedom formula on its ordinary
nonzero-denominator domain, without asserting accuracy of a t approximation.
Those scope boundaries are respected. None of these targets is labelled
`refuted`: the numerical comparisons establish defects in the printed
expressions while proving the corrected canonical assertions.

The explicit witnesses use independent product Bernoulli assignments with
interior probabilities and finite real outcomes. T21's two-node schedules and
T25's eight-node schedule depend only on each node's own coin; T22 uses the
specified shared third coin and full three-node neighborhoods. They are also
realizable as spatial averages at distinct point nodes with counting measure
and radius zero. These are genuine instances of their printed settings, with
bounded outcomes and local dependence; finite patterns can be extended along
a uniformly spaced line of nodes with zero additional outcomes. No witness
uses undefined moments or dependent replacements for independent draws.

Zero division, singular-matrix inverses, nonintegrable Bochner integrals,
infinite measure converted to real zero, and empty/unbounded real infima do
not support any reviewed conclusion. Relevant domains are protected by
positive sample/arm counts, interior propensities, invertibility,
`WellDefined`, proven finite quantile sets, positive variance/bandwidth, or the
explicit nonzero trace premise. The N=0 row in the NED array has no nodes;
the polynomial rate uses positive radii. Nonempty node sets make set-distance
infima ordinary infima.

Validation completed:

- `/home/ubuntu/sap/tools/sap-lean scratch/AuditChecks.lean` succeeds with no
  diagnostics. Its examples construct every hypothesis domain, including
  spatial measurability, positive finite mass and integrability, nonsingular
  population projections, mixed treatment arms, nonzero trace denominator,
  positive bandwidth, and a full uniform NED array. The checks do not invoke
  any Challenge theorem stub.
- `python3 scratch/witness_checks.py` succeeds using exact rational arithmetic.
  It checks the canonical T21, T22 and T25 numerical witnesses and additional
  unequal-propensity/residual-product instances. Results are saved in
  `scratch/witness-results.json`.
- The output JSON files parse and contain exactly one matching entry per
  target; fingerprints match `closure.json`.

No source declaration was modified. No fix is needed.
