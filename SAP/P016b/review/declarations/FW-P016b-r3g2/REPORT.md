# Review of SAP.P016b.T17–T21

All five declarations are faithful to their declared scope. T19 is a correctly
disclosed restriction; the other four cover their canonical claims. No changes
are needed.

| Declaration | Record decision | Verdict | Severity | Assessment |
| --- | --- | --- | --- | --- |
| SAP.P016b.T17 | whole | faithful | none | States the adjusted mean comparison, both identities for the conditional imputed-treated reading, and the 2-versus-12 example. Both groups must be nonempty. |
| SAP.P016b.T18 | whole | faithful | none | States every coordinate and numerical fact of the canonical constructed witness, together with global nonnegativity of the median criterion. |
| SAP.P016b.T19 | restricted | faithful | none | Retains mathematical clauses (a)–(f); its docstring and record accurately enumerate the omitted empirical assertions. |
| SAP.P016b.T20 | whole | faithful | none | Includes additive recovery and every network clause (b1)–(b4), with the canonical nonnegative-network and positive-beta domain. |
| SAP.P016b.T21 | whole | faithful | none | Includes uniformity recovery, all three exact tails, both cutoffs, and the two strict Monte Carlo bounds under genuinely iid draws. |

The blind reading was saved in [reading.md](/home/ubuntu/sap/tasks/FW-P016b-r3g2/reading.md)
before opening the claims. All 79 distinct closure declarations were inspected,
including Lean's printed bodies of generated auxiliaries. The subsequent
[claim-stage.json](/home/ubuntu/sap/tasks/FW-P016b-r3g2/claim-stage.json) was saved
before opening the record. No claim-stage conclusion changed after reading it.

T19's canonical statement and definitions include empirical power comparisons,
simulation-specific unequal expected adjusted shifts, and approximations 10.069
and 1.035312. Its canonical note cannot remove those clauses. The restriction
at `SAP/P016b/Challenge/Part1.lean:71` and the record explicitly omit all of
them. Positive half-size and nonzero inverse multipliers are existing domains
for the median/minimum and division. The mathematical witness does not claim
anything about the simulation dataset. Recommendations to recompute powers
and revise calibration are accurately described as recommendations.

T17 diagnoses a conditional interpretation of an undefined printed symbol;
T18 proves the canonical constructed witness against an equal-strength reading.
Neither is labelled as refuting the paper's qualitative wording. Their `whole`
decisions are appropriate.

The definitions use actual group means, absolute discrepancies, a sorted even
median, the correct componentwise network mapping, finite probability laws,
inclusive tails, and full product probabilities. Empty-group divisions,
out-of-bounds median defaults, truncated central indices, empty or unbounded
real infima, and zero network denominators cannot affect the asserted clauses.
The treated minimum is finite and nonempty. The normalized uniform design is
inhabited. No definition encodes the desired conclusion as an assumption.

Verification passed with `/home/ubuntu/sap/tools/sap-lean`:

- [scratch/Closure.lean](/home/ubuntu/sap/tasks/FW-P016b-r3g2/scratch/Closure.lean)
  prints every closure declaration.
- [scratch/Nonvacuity.lean](/home/ubuntu/sap/tasks/FW-P016b-r3g2/scratch/Nonvacuity.lean)
  constructs the relevant inputs and proves all hypothesis domains are inhabited,
  including a normalized law with the exact binomial denominator for T21.
- [scratch/Witness.lean](/home/ubuntu/sap/tasks/FW-P016b-r3g2/scratch/Witness.lean)
  checks all discrepancy classes on the actual data and a balanced example of
  the sorted-median behavior. These checks import only definitions, not Challenge.
- [scratch/exact_witness.py](/home/ubuntu/sap/tasks/FW-P016b-r3g2/scratch/exact_witness.py)
  verifies the complete fixed 256-unit numerical witness with exact fractions;
  all 12 grouped checks pass. The full 256-unit median was independently sorted
  in this checker; the separate compiled median example has four units.

Lean emitted only auxiliary-name warnings for closure inspection and one
nonvacuity-file style suggestion. No `lake` command was used. The five-entry
[findings.json](/home/ubuntu/sap/tasks/FW-P016b-r3g2/findings.json) and claim-stage
JSON were parsed and their target coverage and fingerprints checked with Python.
