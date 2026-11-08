# Review of T11–T15

All five declarations are faithful to their recorded scope. No defects were found in their statements, dependent definitions, or docstrings.

| Declaration | Recorded scope | Verdict | Severity |
| --- | --- | --- | --- |
| SAP.P001a.T11 | restricted | faithful | none |
| SAP.P001a.T12 | whole | faithful | none |
| SAP.P001a.T13 | restricted | faithful | none |
| SAP.P001a.T14 | restricted | faithful | none |
| SAP.P001a.T15 | restricted | faithful | none |

The blind reading was saved in `reading.md` before opening the claims. `claim-stage.json` was saved before opening the record; none of its conclusions changed afterward. Every closure entry, including the generated auxiliary declarations, was inspected.

T11 states the genuine zero-weight nonidentification example and expressly preserves the contextual identification/uniqueness reading (`Challenge/Part1.lean:85`). T12 covers the complete corrected result through more general consistency, normality and information-bound principles (`Defs/WholeW2.lean:491`). Its positive-log, differentiability, integrability and positive-information guards prevent the relevant junk-value conventions from changing the result. T13–T15 accurately disclose their omitted design predicates, asymptotic consequences and empirical interpretations (`Challenge/Part1.lean:107`, `:112`, `:117`). In particular, T15 claims true-score bootstrap failure and intercept consistency; its restriction expressly omits failure of the estimated-score matching statistic.

`scratch/Check.lean` compiled checks of T11's distinct admissible normalized witnesses, a complete T12 consistency-problem instance, T14's positive-size product-sign experiment, and empty-sample conventions. `scratch/MatchingNonvacuity.lean` compiled normalization of the matching law and an infinite iid realization; its named proofs have no `sorryAx` dependency. All L2 premises hold because the finite-sample statistics and bootstrap variances are bounded Borel functions. The Gaussian location model supplies positive-dimensional nonvacuity for T12's normality, QMD and regular-estimator premises. The finite-choice measurability and Gaussian nonvacuity arguments are given mathematically, rather than fully formalized, in `scratch/claim-audit.md`.

The independent-draw requirement is satisfied: the mixture sample masses are products, and the bootstrap averages over all `n^n` maps, which is the product law of n independent uniform empirical draws. No dependent-replicate witness or undefined quantity is used to challenge a printed assertion. The interpretations addressed by T11, T13 and T15 are identified explicitly; none is labelled as a refutation of the literal hedged wording or of the reported numerical estimates.
