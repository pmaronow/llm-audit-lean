# Declaration review

All five declarations are faithful, with severity `none`. The `whole`
decisions and null restrictions in `record.json` are correct; the docstrings
accurately describe the statements. No fixes are needed.

| Declaration | Verdict | Severity |
| --- | --- | --- |
| SAP.P013a.T1 | faithful | none |
| SAP.P013a.T2 | faithful | none |
| SAP.P013a.T3 | faithful | none |
| SAP.P013a.T4 | faithful | none |
| SAP.P013a.T5 | faithful | none |

The paired counterexample includes every required finite identity, asymptotic
limit, variance-rate failure and coverage conclusion. The corrected coverage
theorem includes the added lower-tail condition, both joint-probability rates
and their consequences. The signed simulation counterexample uses independent
draws and never divides by its zero-total variant. The corrected simulation
bounds retain the cancellation factor and the nonzero-total and sign guards.
The dependency counterexample uses the literal printed complements and also
includes a symmetric example without self-loops.

The blind reading was saved before opening the claims; the claim-stage JSON
was saved before opening the record. All 142 distinct dependency declarations,
including 42 generated auxiliary declarations, were inspected. The independent
claim and witness-condition comparisons are in `claim-checks.md`.

`scratch/ClosurePrint.lean`, `scratch/Checks.lean` and
`scratch/SequenceCheck.lean` compiled with `sap-lean`. The checks include signed
expectations, positivity, the simulation-definition identity and a complete
shared-exposure sequence violating Condition 4. For T2, the constructed
independent Bernoulli sequence has outcomes identically one, true and estimated
variance 4/N, and zero lower-tail probability. Its full nonvacuity calculation
is given in `claim-checks.md`; its construction, marginals and boundedness are
also checked in Lean. No audited Challenge theorem is used in these witness
checks.

The divisions, logarithms, square roots, normal quantile and real lower limits
have the intended meanings under their guards. Zero joint probabilities occur
only in impossible observations and use the paper's prescribed convention.
