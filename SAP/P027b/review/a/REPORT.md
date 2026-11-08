# P027b statement referee report

Audited 11 canonical targets and all 11 Challenge theorem stubs.

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

Severity: 11 none, 0 minor, 0 major. There are no adverse findings or omitted targets.

The two accepted restrictions are complete and accurately disclosed in both the Challenge docstrings and `record.json`:

* **P027-T14 / SAP.P027b.T14:** retains every fixed-population assertion of C1 at M=5. Omits C2's outcome-model-averaged ranking reversal and C3's M=500 true variance, estimator expectations and relative biases. Its reading of the printed guidance concerns bias ranking; the quoted simulation rows supply context.
* **P027-T16 / SAP.P027b.T16:** retains the C1-C2 numerical discrepancy for the explicit product law of three independent fair signs. The docstring explicitly declares the replacement of Gaussian errors, omission of a Gaussian-law witness, and omission of C3's divisor-1/divisor-2 interpretation. The reading tested is common-stratum pair correlation. The finite-law theorem receives credit only for that disclosed scope.

The remaining nine statements cover their full canonical claims. In particular, T18's outcome-index repair is correctly supplied as a definition, as the canonical claim requests. T19 includes its model moments, decomposition, Gaussian law, uniform-in-K tail bound and every row certificate; its positive-variance guards are already in the canonical claim. Its zero-noise moment case remains present.

`reading.md` was saved before opening `claims.json`; `claim-stage.json` was saved before opening `record.json`. No step-2 verdict was changed after reading the record. Audit-history notes and unused-lemma explanations were not used to remove clauses from the canonical claims.

The review followed the SAP definitions to the relevant Mathlib definitions, checked the quantifiers and ordered-pair conventions, and checked denominator positivity, integrability, dimensions, probability conversions and nonempty model instances. Finite outcome labels faithfully represent probability distributions on subsets of a finite population. Harmless empty-population extensions in the general algebraic statements do not replace any required nonempty case.

`scratch/Referee.lean` compiled successfully with `/home/ubuntu/sap/tools/sap-lean scratch/Referee.lean`, importing only the supplied Defs. It checks a positive cluster design with both bias signs, an actual Gaussian product-law instance, and T22's nonzero equality-condition instance with variance 136. It contains no proof holes. `python3 scratch/referee_checks.py` passed independent exact rational checks of the stratum formulas and moment averages, periodic identities and contrast, all four numerical predictions, and all row rounding certificates and exponents. These checks supplement the mathematical statement review; no Solution or Comparator was read and no `lake` command was run.

For T19 the Gaussian projection argument uses mutually orthogonal finite-dimensional noise components. The population-average tail bound follows by the lower contrast bound, convexity of the exponential and the chi-square moment-generating function, so it requires no independence between generated populations. No deterministic exclusion of the reported rounding events is asserted.

`findings.json` gives the per-target verdicts and nonvacuity instances. Both JSON output files were parsed and checked against the complete canonical target list.
