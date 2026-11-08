P027-T9: **omission_ok**, severity **none**.

The architect's stated reason is accurate. In `claims.json`, this target has
`no_lean: true`, `rows: []`, and `coverage_judgments: []`. The Challenge contains
no T9 theorem, and `closure.json` records a null theorem and an empty closure.
The explicit rule allowing omission when the target has no proved row applies.

Reading the canonical statement together with `definitions_needed` and the
standing assumptions, T9 concerns identifying the reported Table A3 C2 entries
with averages of design expectations for the estimator after prescribed cluster
totalling. T5's statement supplies numerical bound violations and a population
witness; T6 supplies estimator formulas and comparisons. Neither asserts that
identification, and their Challenge docstrings explicitly exclude it. Repeating
their numerical or algebraic conclusions would merely restate other targets,
which the review rules exclude. This assessment does not treat the target's
historical `note` as changing its claim.

No restricted theorem is proposed: T9 has no credited rows from which to derive
one under the permitted glue rule. No new proof or Lean compilation was needed.
