The five declarations are faithful at their declared scope. T6 and T7 cover their
canonical mathematical claims. T8, T9 and T10 are narrower, with accurate
restrictions in both their Challenge docstrings and `record.json`.

| Declaration | Claim-stage reading | Recorded decision | Finding |
| --- | --- | --- | --- |
| SAP.P029a.T6 | whole | whole | faithful; none |
| SAP.P029a.T7 | whole | whole | faithful; none |
| SAP.P029a.T8 | narrower | restricted | faithful; none |
| SAP.P029a.T9 | narrower | restricted | faithful; none |
| SAP.P029a.T10 | narrower | restricted | faithful; none |

`reading.md` was saved before opening the claims. `claim-stage.json` was saved
before opening the record. The record required no change to a claim-stage
conclusion. Every listed closure declaration was read, including all 60 distinct
generated auxiliaries, printed by `scratch/ClosurePrint.lean`. These auxiliaries
are ordinary numeral/typeclass instances.

T6 contains all clauses (a)–(e): effect five, the positive-replicate RMSE rule,
uniform benchmark moments, all error identities, and both discrepancy signs.
Its definitional RMSE equality uses the standard statistic; it does not replace
the mathematical notion with a placeholder. Positive counts, positive event
mass and the moment assumptions prevent relevant junk-value effects. The two
noise inputs are single admissible finite realizations; no argument treats
repeated copies as independent simulation replicates.

The reading challenged by T7 is: supplied observation weights fit the compliance
model and refit that model in each reweighting-bootstrap replicate. Its conditions
are finite positive weights, binary assignment and receipt, the stated Bernoulli
likelihood and Gaussian-probit parameterizations, receipt clipping in the
two-sided branch, both outcomes in every fitting cell, the displayed sample and
normalized IV weights, and positive perturbation t. The witnesses satisfy each:
their cell totals are positive, their rates are interior and realizable by finite
coefficients, the concrete two-sided fits survive clipping, and their IV
denominators are positive. `T7WholeStatement` includes actual realized fits and
derivatives of the IV expressions. The docstring correctly calls this a refutation
of an interpretation of the package help; the decision is `whole`, not `refuted`.

T8 explicitly stops at free-cell fits and specified-array IV evaluations. It
drops identification with probit fits and the nonconstant-weight contrast of
actual package and corrected probit minimizers. The cell-fit predicates express
optimality as a conclusion, and their positive-total hypotheses are satisfiable.
The restriction accurately accounts for the missing parts of (c) and (d).

The inference challenged by T9 is: the recorded values determine the sign of the
pooled compliance/White association. Its retained conditions are the specified
finite counts, preservation of assignments, contacts, arbitrary outcomes and
compatible recorded labels/codes, one-sided noncompliance, no defiers, and
compatibility with independent random assignment. Both explicit completions
satisfy these conditions and have opposite signs in both conditional directions.
The assignment-support certificate allows the fixed realized vector under a
product-Bernoulli design. The raw-code hypothesis correctly matches codes to
recorded Boolean labels and requires missing raw values in the missing-label
cells. The docstring and record disclose the omitted general sign identity and
independent empirical data summaries; neither claims a raw-file validation or
that the paper's literal positive-association assertion is false.

T10 states the binary-count formulas, both rational comparisons, the Boolean
completions and the finite covariance decomposition. Its docstring accurately
disclaims the empirical score, availability, imputation and exclusion assertions
and raw-string preservation. The distinguished conditional formula requires
positive group probability. Unused groups' totalized means are evaluated only
through realized groups, so they cause no semantic defect.

`scratch/Nonvacuity.lean` compiled successfully using the supplied `sap-lean`
wrapper, importing definitions without Challenge theorems. It constructs a genuine
independent uniform product model, positive-moment examples, positive fitting
totals, compatible and distinct completions, assignment support, strict binary
counts, and a grouped example with within-group term 1/8. Only linter warnings
remain. No `lake` command, external paper search or Solution-source inspection
was needed. The final JSON has one entry for each reviewed declaration, with
fingerprints copied from `closure.json`.
