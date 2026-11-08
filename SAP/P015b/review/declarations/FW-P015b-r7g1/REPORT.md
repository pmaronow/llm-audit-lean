# Palomar declaration review

All five declarations are **faithful**, with severity **none**. Their `whole`
labels and docstrings agree with the canonical claims. No correction is needed.

| Declaration | Claim coverage | Verdict | Severity |
| --- | --- | --- | --- |
| `SAP.P015b.T9` | Whole | faithful | none |
| `SAP.P015b.T10` | Whole | faithful | none |
| `SAP.P015b.T20` | Whole | faithful | none |
| `SAP.P015b.T14` | Whole | faithful | none |
| `SAP.P015b.T21` | Whole | faithful | none |

The blind reading in `reading.md` was saved before opening `claims.json` or
`record.json`. It includes all five dependency inventories. Every listed source
declaration was read, and all 46 distinct generated auxiliary declarations were
printed with their proofs. `claim-stage.json` was saved before reading the record;
the record caused no change to those conclusions. The blind-reading SHA256
remained `1872bf7896b5a5b842317b842c2627daf64483fa10b739307d78a8187e4f2f66`.

The decisive checks were:

* **T9:** The explicit example excludes every scalar combination of the two
  zero treatment slopes while preserving the raw GLS calculation. Its data can
  occur with positive probability under independent common-mean coefficient
  draws, covariance identity, independent variance-one errors, and independent
  randomized binary treatment. The docstring accurately identifies the scalar
  interpretation it counters; the `whole` label is appropriate.
* **T10:** Every matrix identity, minimizer clause, prescribed-weight row
  equivalence, block-diagonal sufficient case, bounded-input approximation, and
  within-group limit assertion is present. The regularity assumptions are the
  canonical sufficient reading. The statement makes no unsupported pooled
  consistency assertion.
* **T20:** The law, conditional residual variances, population leverages,
  conditional averages, comparison ratios and printed roundings agree. The
  population leverage reading is explicitly authorized by `definitions_needed`.
* **T14:** The canonical claim specifies a model definition. Its membership
  equivalence therefore faithfully supplies the common parameters and conditional
  success probabilities. The additional injectivity result addresses the printed
  unconditional display under its stated nondegeneracy conditions.
* **T21:** All three exact clauses are covered. Existence and uniqueness concern
  the affine surrogate root, as required. The audit-history remainder examples
  add no omitted clause.

Nonvacuity checks compiled successfully with `/home/ubuntu/sap/tools/sap-lean`:
`scratch/Check.lean`, `scratch/ModelCheck.lean`, and
`scratch/SamplingCheck.lean`. They use no Challenge theorem. In particular, the
sampling check constructs an infinite fair-bit product and proves every
within-group hypothesis of T10 jointly, including its eight moment families,
using Mathlib's strong law. Its population Gram is `[1]` and its residual weight
is `1/4` almost surely. `scratch/PrintClosure.lean` also compiled successfully.

Matrix singularity and zero-denominator conventions do not explain any finite
witness. T10's finite-sample OLS completion at singular samples and its zero-size
initial average are harmless in its asserted probability limit. Conditional
expectations use valid subalgebras and integrable functions, and logistic
likelihoods use strictly positive log arguments. Detailed witnesses are recorded
in `findings.json`.
