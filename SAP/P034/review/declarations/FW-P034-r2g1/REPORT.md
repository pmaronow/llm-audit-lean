All five declarations are **faithful**, with severity **none**. No statement,
definition, restriction, or docstring correction is needed.

The blind reading in [reading.md](reading.md) was saved before opening the
canonical claims. Its SHA-256 is
`833cefecf5ae0ebea4b7588207c8c36320d35b42fec2ac376903dafd858350c0`.
[claim-stage.json](claim-stage.json) was saved before opening the architect's
record. Every listed dependency was read, including the generated declarations
printed by [scratch/BlindPrint.lean](scratch/BlindPrint.lean). No claim-stage
conclusion changed after reading the record.

- **T1:** Every part (i)–(ix) is represented: the actual weighted finite laws,
  randomization, outcome-dependent missingness, respondent moments, unique real
  coefficient vectors, the nonrejecting sample, and observational equivalence
  with a different population effect. The sample's frequency representation
  preserves all relevant information. The docstring accurately scopes the
  counterexample to the inference licensing complete-case analysis. The
  article's statement that its test detected no attrition difference is an
  empirical report, which this construction does not refute.
  [Article, p. 6](https://tsjournal.org/index.php/jots/article/download/28/15/116#page=6).
- **T2:** The hypotheses match H1 and H2 on an arbitrary measurable probability
  space with the required second moments. All conclusions (a)–(e) appear,
  including full conditional covariate laws, orthogonality, every solution's
  treatment coefficient, and uniqueness under nonsingularity. The finite
  counterexample uses the same genuine World A variables. Explicit
  measurability expresses the canonical random-variable setting.
- **T3:** The specified cells, unique saturated interpolation, both zero main
  coefficients, and both nonzero averaged contrasts are all present. The
  docstring correctly identifies a distinction between interpretations of
  the row labels; it does not declare the printed empirical entries false.
- **T4:** All reference contrasts, weighted identities, and exact equality
  conditions are present. The claim-stage classification is `broader` only
  because the polynomial identities also cover real factor values beyond
  the required binary values. This valid extension drops no clause, so the
  record's `whole` decision is correct. The positive-weight qualification
  is retained; zero weights are correctly handled by the product-zero
  equivalences.
- **T5:** Every literal count and corrected percentage matches the canonical
  transcription. The rational percentage and half-open rounding definitions
  are exact, including rejection of the two printed values and every row
  and column sum. The response-slot total is preserved.

All five `whole` decisions and their docstrings are accurate. No SAP
definition encodes a desired conclusion or replaces a paper notion with a
placeholder. Conditioning denominators are positive; probability masses
cannot be infinite; T2's L² hypotheses ensure integrability of every
displayed product. Intentional empty covariate vectors cause no vacuity.

Independent checks in [scratch/Check.lean](scratch/Check.lean) import only
Defs. They verify both finite distributions, the substantive finite
counterexamples and observed-law equality, a model satisfying every T2
hypothesis, the factorial witness, a positive-weight interaction example,
and all 39 table roundings and totals. The command
`/home/ubuntu/sap/tools/sap-lean scratch/Check.lean` completed with exit
status 0 and no diagnostics. [findings.json](findings.json) contains exactly
the five requested declarations with fingerprints copied from the closure.
