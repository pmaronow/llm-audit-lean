All five declarations are faithful to their recorded scope. T20 is accepted as
an accurately disclosed restriction of clause (ii); the supplied canonical
material does not establish equivalence between its C1/C2 premises and the
referenced T10 assumptions. T21–T24 cover their complete canonical assertions.

| Declaration | Verdict | Severity |
|---|---|---|
| SAP.P018b.T20 | faithful | none |
| SAP.P018b.T21 | faithful | none |
| SAP.P018b.T22 | faithful | none |
| SAP.P018b.T23 | faithful | none |
| SAP.P018b.T24 | faithful | none |

The blind reading was saved in `reading.md` before opening claims or history.
Every closure declaration was read, including generated helpers. The independent
claim comparison was saved in `claim-stage.json` before opening `record.json`;
the record did not change those conclusions.

Both earlier T20 issues are fixed. `record.json:4` now says restricted, and its
restriction enumerates the substantive premises. The Challenge and shared
docstrings explicitly decline equivalence with the unsupplied T10 contract.
The historical name `T20WholeStatement` does not overrule that disclosure.

`scratch/Nonvacuity.lean` compiled successfully using shared Defs only. It
constructs positive-dimensional instances for T20's finite identities, C1, C2
and UI implication; T21's full standing predicate; all T22 Gaussian input
premises; T23's probability/L2 score-product premises; and T24's significance
domains. It also proves both full one-sided significance bounds independently.
Exact rational polynomial integration reproduces T21's nonlinear covariance
matrix; fraction arithmetic checks all T24 table facts. See
`scratch/WitnessAudit.md` for the rare-law existence and tail checks, the
conditional-covariance witness, and one terminology clarification to the blind
reading. The rare infinite-moment witnesses were checked mathematically rather
than reconstructed as additional Lean proofs.

No conclusion relies on a singular inverse, undefined expectation, null-event
conditioning, infinite `toReal`, or another junk value. None of these five
declarations is a refutation of its canonical corrected assertion. No source
declaration was changed, no other review files were consulted, and no `lake`
command was run.
