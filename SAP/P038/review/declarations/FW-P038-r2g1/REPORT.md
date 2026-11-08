**SAP.P038.T1: faithful; severity none.**

The blind reading and complete closure inspection are recorded in `reading.md`.
This includes individually printing all 17 generated numeric proof declarations.
The claim comparison was saved in `claim-stage.json` before `record.json` was
opened. The record's `whole` decision and absent restriction are correct; no
step-2 conclusion changed after reading the record.

All four canonical mathematical clauses are present in
`SAP/P038/Defs/Part1.lean`: the two-tail-point value and discrepancy (lines
41–46), exact and rounded count characterizations (47–57), nested windows and
the conditional 12-week calculation (58–67), and both added-election-day
calculations and incompatibility conclusions (68–79). Combining the last two
clauses under one quantified conjunct loses nothing. Natural window sizes in
the range 1–100 and total real-valued families on the integers are equivalent
representations of the canonical bounded integer windows and finite families.

The definitions at lines 8–36 correctly use the nonzero integer weeks, strict
comparisons outside the reciprocal thresholds, actual finite-set cardinality,
division by 2m, the specified half-open rounding bins, and the counterfactual
addition of one observation. The caption-based rule and per-side window
interpretation agree with the canonical definitions and the relevant Methods,
caption and footnote in the [published paper](https://link.springer.com/article/10.1186/s13104-016-2148-6).
No underlying crash-count construction is required for the canonical claim's
arbitrary positive RRs. No definition assumes the result or replaces the data
with a fixed answer. Zero reciprocals and zero-window proportions are excluded
where relevant; no other junk-value operation affects the statement.

`scratch/Nonvacuity.lean` compiled successfully using only Defs. With R=2,
r(-14)=r(7)=3 and every other r(w)=1, all positivity, count and specified-tail
hypotheses hold together. The file independently checks the two tail sets,
all four proportions and witnesses for the integer and window bounds. Exact
rational enumeration also confirms that only k=3 gives or rounds to 0.06 on
the 50-point grid, and only k=2 gives or rounds to 0.04.

The target docstring at `SAP/P038/Challenge/Part1.lean:6` accurately describes
the conditional corrected claim. It neither asserts the observed figure-tail
set without a hypothesis nor determines which published output reflects the
final data. This is a whole conditional arithmetic claim; a `refuted` label
would be inappropriate. There are no findings requiring a fix.
