All five declarations are faithful to their recorded scope. No defective
definition, vacuous hypotheses, operative junk value, or inaccurate docstring
was found.

- **T19:** covers both corrected simulation recipes, their probability laws,
  type and treatment characterizations, failures of the printed implicit
  treatment equation, and the outcome identity. The normal parameter is
  correctly variance nine; the logistic parameter is correctly scale three.
- **T20:** genuinely refutes the canonical statement's explicit universal
  ignorability implication and retains its true reverse-direction example.
  An independent Lean construction satisfies the actual measure-theoretic IV
  assumptions and typical ignorability while violating latent ignorability.
- **T21:** correctly refutes the two canonical joint implications. Conditional
  independence need not fail to imply latent ignorability: failure of the
  unweighted Wald equality refutes the stated conjunction. The restriction on
  the additional constant-effect result is accurately disclosed.
- **T22:** accurately retains only the RMSE scoring convention. Its definition
  is standard; the definitional equality validates that convention alone. The
  record and docstring explicitly omit the design, estimators, effect
  identification, historical arrays, and reported numerical results.
- **T23:** genuinely refutes the canonical observation-weight fitting contract
  with an admissible interior nested Bernoulli dataset and positive weights.
  An independent Lean check proves an admissible competitor strictly improves
  the actual weighted objective. The bootstrap recommendation is outside this
  refutation, as the docstring states.

`reading.md` was saved before opening `claims.json`; `claim-stage.json` was
saved before opening `record.json`. No step-2 assessment was changed after
reading the record. T21 and T22 remain narrower as described there; their
disclosed scope is accurate. T20, T21 and T23 contradict explicit mathematical
assertions in the canonical statements, rather than an interpretation newly
introduced by this review. Detailed condition-by-condition witness checks are
in `refutation-checks.md`.

Successful independent Lean checks: `scratch/BlindClosure.lean`,
`scratch/PointCheck.lean`, `scratch/FiniteCheck.lean`,
`scratch/MeasureCheck.lean`, `scratch/ConstantCheck.lean`,
`scratch/BasicCheck.lean`, and `scratch/WeightedCheck.lean`, all run with
`/home/ubuntu/sap/tools/sap-lean`. They import definitions, not Challenge
theorems. Exact rational probability, independence, and objective-product
checks also passed in `scratch/witnesses.py`. No paper or implementation
source beyond the supplied canonical material was needed.
