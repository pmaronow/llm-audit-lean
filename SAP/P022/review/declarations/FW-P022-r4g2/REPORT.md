# Declaration review

All five declarations are faithful to their canonical claims and disclosed scope. No adverse findings were identified. Every statement dependency listed in `closure.json` was reviewed, including generated proof and constructor declarations. `reading.md` was saved before opening the canonical claims; `claim-stage.json` was saved before opening the architect's record. The record required no revision of the claim-stage judgments.

| Declaration | Claim-stage coverage | Record assessment |
|---|---|---|
| `SAP.P022.T4` | Whole corrected claim | `whole` is accurate: unbiasedness, Bernoulli variance identities, and both quarter-factor bounds are present. |
| `SAP.P022.T5` | Whole counterexample and equality characterization | `refuted` is justified: the valid constant-one four-unit population contradicts the printed final equality in (11). |
| `SAP.P022.T8` | Whole corrected claim | `whole` is accurate: original widths, midpoint selections, rank identities, weighted means, covariance and variance substitution, and overlap formulas are represented. |
| `SAP.P022.T9` | Whole canonical counterexample package | `whole` accurately describes coverage of the canonical counterexample, general discrepancy identities, and translation behavior. The docstring correctly identifies the printed output assertion as false under the specified real-arithmetic reading. |
| `SAP.P022.T10` | Narrower | `restricted` and its docstring accurately disclose the omitted actual-variance remainder identity, `(0,1)` sample formulas and examples, and R-execution assertions. The retained estimator identities and limits have the claimed scope. |

The relevant locations are `Challenge/Part1.lean:27`, `:31`, `:58`, `:62`, and `:71`; the statement bodies are `Defs/Part5.lean:78`, `:93`, `:200`, `Defs/WholeW1.lean:247`, and `Defs/Part6.lean:14`, respectively, all under `SAP/P022/`.

The permutation model induces the prescribed uniform disjoint-arm design: every arm allocation has exactly `m! k! (N-m-k)!` permutation representatives, and the reviewed statistics are invariant under permutations within the arms and unsampled units. The quantile definitions agree with the empirical inverse CDF on `(0,1]`; endpoint conventions affect only null sets in the integrals. Size assumptions and cell-interior/width conditions keep denominators positive, indices valid, and natural subtractions in range. The quantile integrands are bounded measurable step functions. No operative junk value, circular definition, or inconsistent hypothesis was found.

The refutation readings and condition-by-condition witness checks are recorded in `claim-stage.json`. T5 violates the literal printed quarter-factor equality. T9 violates the literal output assertion in the canonical real-arithmetic interpretation, with the prescribed epsilon and FPvar expression. Both use genuine randomized designs.

Validation: `scratch/ClosurePrint.lean`, `scratch/StructurePrint.lean`, `scratch/Nonvacuity.lean`, and `scratch/CodeCheck.lean` compile with the supplied `sap-lean` command. The latter two construct nonvacuity instances and independently check the counterexamples using definitions and Mathlib. In particular, the T9 witness has mathematical endpoints zero and routine outputs `-1/50331648` in both modes. `findings.json` and `claim-stage.json` were parsed with Python; findings contain exactly the requested five declarations and their closure fingerprints.
