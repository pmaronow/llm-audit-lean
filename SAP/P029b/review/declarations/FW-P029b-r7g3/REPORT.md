All three declarations are faithful under their recorded decisions.

| Declaration | Recorded decision | Verdict | Severity |
|---|---|---|---|
| `SAP.P029b.T25` | whole | faithful | none |
| `SAP.P029b.T26` | restricted | faithful | none |
| `SAP.P029b.T27` | refuted | faithful | none |

T25 includes the population ITT and LATE identities, the defined finite-sample
centered IV coefficient identity, and every canonical numerical example formula.
Its definitions represent the potential outcomes and IV conditions correctly.

T26 proves correct population weighted moments and final-ratio consistency under
explicit additional hypotheses. Both its docstring and record disclose uniform
maximum-in-sample score consistency, positive fitted scores, almost-sure eventual
definedness, and the omitted separate sample outcome and receipt contrast limits.
This is a correctly described restriction. The usual existence and measurability
conditions are not treated as substantive restrictions.

T27 is a valid refutation of the unqualified asymptotic-bias sentence contained
in the canonical statement. The twelve-atom population has heterogeneous effects
and violates latent ignorability at both profiles, but its profile mean effects
cancel to ATE zero and every observed outcome is zero. The actual sampling law
is an infinite iid product, with random assignment, positive overlap, interior
correctly specified nested receipt probabilities, and consistent ML scores on
events whose probabilities tend to one. Ratios are genuinely defined with
probability tending to one, so the result does not depend on undefined samples.
The counterexample agrees with the canonical integral formulas and constant-score
identity (a)–(c); it refutes the quoted categorical bias assertion itself.
`claim-analysis.md` states that printed reading and checks each condition before
accepting the refutation label.

The blind reading and complete closure audit were saved in `reading.md` before
opening the claims. `claim-stage.json` was saved before opening the record, and
no claim-stage conclusion changed afterward. A clearly marked post-blind
Mathlib addendum records harmless product/pushforward defaults.

Validation: `scratch/ClosurePrint.lean`, `scratch/Check.lean`, and
`scratch/Nonvacuity.lean` compiled using the prescribed `sap-lean` command.
The nonvacuity file contains no proof holes and constructs all T25/T26 hypotheses,
including T26's almost-sure eventual definedness. It also independently verifies
T27's zero observed outcomes, zero ATE, and a finite prefix with an interior fit
and defined ratios. `findings.json` contains exactly the three requested entries
with matching closure fingerprints and parses successfully.
