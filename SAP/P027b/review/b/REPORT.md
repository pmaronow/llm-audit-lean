# P027b statement audit

Eleven canonical targets were compared with eleven Challenge stubs. The blind
expansion was saved as `reading.md` before `claims.json` was opened. The
claim-only verdicts were saved as `claim-stage.json` before `record.json` was
opened. No step-2 verdict changed after reading the record.

| Verdict | Count |
| --- | ---: |
| correct_whole | 9 |
| correct_restricted | 2 |
| restriction_inaccurate | 0 |
| not_faithful | 0 |
| vacuous | 0 |
| false | 0 |
| omission_ok | 0 |
| omission_questionable | 0 |

Severity counts: none 11, minor 0, major 0. There are no omitted targets or
items requiring a statement or docstring fix.

## Record decisions

| Target | Architect decision | Assessment |
| --- | --- | --- |
| P027-T14 | restricted | Accurate: C1's two fixed M=5 populations and their bias reversal are retained; C2's model-averaged reversal and C3's M=500 expectations and relative biases are explicitly dropped. The quoted simulation rows are context. |
| P027-T15 | whole | All five mathematical clauses are present, including genuine integrated model expectations and the three large-M limits. |
| P027-T16 | restricted | Accurate: C1-C2's numerical correlation discrepancy is realized with independent symmetric signs; the docstring explicitly replaces the printed Gaussian errors and drops C3's divisor interpretation. |
| P027-T17 | whole | All four clauses, both parameter conversions, monotonicity, limit, and all six exact label conversions are present. |
| P027-T18 | whole | All inclusion and covariance cases, including the diagonal, are present; the corrected outcome index is a definition, as the canonical target specifies. |
| P027-T19 | whole | All six canonical clauses are covered by the eight component propositions, including the original-unit estimators, integrated model, decomposition, Gaussian law, tail, four rounding certificates and numerical bounds. |
| P027-T20 | whole | Identity, both common-sign cases and actual examples of both bias signs are present. |
| P027-T21 | whole | Both bias bounds, the correction's expectation, the exact corrected expectation and conservativeness are present for arbitrary pair-dependent conjugate exponents. |
| P027-T22 | whole | The precise sufficient pairwise equality conditions imply unbiasedness; necessity is not asserted. |
| P027-T23 | whole | The displayed quadratic estimator is identified with exponent two and its conservativeness is asserted. |
| P027-T24 | whole | Every sample is compared with every constant positive conjugate pair, with attainment at (2,2). |

T14 addresses the unqualified **bias-ranking** reading of the supplement's
comparison. T16 addresses the **ordinary same-stratum pair-correlation**
reading of the printed label. Their docstrings identify those mathematical
comparisons and their retained scopes; neither declares the printed guidance
false under every interpretation. Both are correctly classified as restricted.

The record's unused auxiliary theorem names are not additional target
omissions. No conclusion in this audit depends on the audit-history `note`
fields adding to or subtracting from a canonical assertion.

## Definition and nonvacuity checks

The SAP definitions were expanded to finite weighted sums, ordinary Bochner
integrals, Mathlib real conjugate exponents and real powers, probability
pushforwards and products, and finite-dimensional subspaces. Positive
first-order probabilities agree with the paper's standing assumption. Ordered
zero-inclusion pairs include both orientations, and positive-inclusion sums
include the diagonal. The N-squared scaling in the supplement is correct.

Moment hypotheses explicitly supply integrability. Each integrated statistic
is a finite polynomial of degree at most two in the specified errors; hence
the integral's default value for nonintegrable functions does not do the work.
The pair-correlation variances are positive. Finite model ratios have positive
denominators on their stated domains, and limits are genuine limits on
eventually positive natural indices.

For T19 the phase design is a relabeling of the described periodic systematic
design: one start in an interval of length 6q selects one residue class modulo
q, containing m units. Its width 2 or 10 gives probabilities 1/(3q) or
5/(3q). The constraints r>0,m>=2 make N>m, N-q>0 and 9q-5>0. Natural
dimension subtractions cannot truncate. When r=1, the two zero-dimensional
components genuinely vanish; their chi-square laws are point masses at zero,
while the within-phase Gaussian component has positive dimension. The
positive-V quotient and positive-noise law/tail hypotheses match the canonical
qualifications. No independence between different generated populations is
added. The rounding event is probabilistic and concerns exact conditional
design expectations, not an extra simulation over design draws.

Meaningful instances are recorded separately for every target in
`findings.json`. In particular T22 has nonzero outcomes, actual zero-inclusion
pairs and total variance 136; it does not rely on zero outcomes or absent
pairs. Product Gaussian coordinate spaces realize the model assumptions on
nonempty populations. Reusing a single vector across every generated
population realizes T19's hypotheses even with fully dependent populations.

## Verification

The following completed successfully:

* `/home/ubuntu/sap/tools/sap-lean scratch/Check.lean`: positive finite designs,
  both signs of A, a direct HT-variance computation, conjugacy, the nonzero
  T22 equality hypotheses, a real zero pair, and exact periodic predictions.
* `/home/ubuntu/sap/tools/sap-lean scratch/Models.lean`: product-Gaussian
  realizations for every finite unit index type and for repeated populations.
* `python3 scratch/verify.py`: exact rational enumeration of T14 and the sign
  witness; the nonzero unbiasedness instance; samplewise stratum identities;
  original-unit periodic V,H,C,W identities, decomposition and signal
  cancellation at r=1,2,3 and m=2,3; all four printed contrasts, rounding
  thresholds, binary exponents and decimal bounds.
* Python JSON parsing and target-coverage validation for `claim-stage.json`
  and `findings.json`.

The scratch Lean files import only `SAP.P027b.Defs`, not the Challenge stubs.
These are supporting statement checks, not a claim to have independently
proved all eleven universal theorem stubs. No Solution or Comparator files
were read, and `lake` was not run.
