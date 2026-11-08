All five reviewed declarations are faithful, with severity `none`.

| Declaration | Record decision | Verdict |
| --- | --- | --- |
| SAP.P046.T6 | refuted | faithful |
| SAP.P046.T7 | whole | faithful |
| SAP.P046.T8 | whole | faithful |
| SAP.P046.T9 | whole | faithful |
| SAP.P046.T10 | whole | faithful |

The blind reading in `reading.md` was saved before opening `claims.json` or
`record.json`. Every declaration in the five closures was read, including
Lean prints of the generated auxiliary declarations. `claim-stage.json` was
saved before the record was opened. The record caused no changes to that
assessment. Its labels and the Challenge docstrings accurately describe the
statements.

T6 refutes the canonical population-centred assertion itself. The printed
reading, its complete conditions and the concrete witness checks are written
in `scratch/T6-witness.md`. The witness uses genuinely independent samples,
known true propensities, strict positivity and a continuous covariate. Strict
closed-interval noncoverage at n=100 and alpha=10^-7 is approximately
1.19792910698×10^-7, so the refutation also holds without using equality at
the interval boundary. It asserts neither failure at every level nor failure
of the stated width rate.

T7 uses exactly the common-delta uniformity specified in the canonical
definitions. T8 includes all printed expectation chains, with only the usual
integrability guards, and its broader deterministic-fold domain covers the
claim. T9 preserves genuine extended L2 errors, permits distinct fixed limits
in part (b), and identifies exactly the Hahn variance specified for part (d).
The fixed limits' L2 membership is the usual finite-second-moment condition
for mean-square convergence; no correctness assumption is imposed on them.
T10 has the correct negated-uniform-consistency quantifiers over the unrestricted
canonical class. Its historical common-positivity construction is not an
additional claim clause.

No definition encodes a conclusion. Positivity and the level/sample-size
guards protect the radius and inverse weights; probabilities are finite
before conversion to reals; conditional expectations have legitimate finite
conditioning measures; fitted expectation chains are guarded; infinite L2
errors are retained; and Gaussian truncation cannot hide a negative variance.

`scratch/Blind.lean` and `scratch/Nonvacuity.lean` compile successfully with
the permitted `sap-lean` command. The latter constructs instances for every
target, including both T9 branches and every T8 expectation guard. It uses
the independently certified T1/T4 declarations for the explicit law and
partition, never a target under review. The concrete model was also checked
mathematically, and an independent multinomial enumeration reproduces T6's
exact numerator and 1946 exclusions (`scratch/T6-arithmetic.json`).

`findings.json` and `claim-stage.json` were parsed with Python; all five
findings have the exact corresponding fingerprints from `closure.json`.
