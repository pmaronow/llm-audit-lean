# Declaration review: P010-T6–T10

All five declarations are **faithful**, with severity **none**. Their `whole` decisions are correct. No source changes are needed.

The blind statement and dependency review was saved in [reading.md](reading.md) before reading the claims, prior findings, architect report or record. Every closure declaration was read, including all 30 generated auxiliaries printed by Lean. [claim-stage.json](claim-stage.json) records the independent claim comparison; none of its conclusions changed after reading the record.

| Declaration | Assessment |
|---|---|
| T6 | Includes every corrected else-branch hypothesis and conclusion: validity, strict finite endpoints, sharp infimum/supremum, nonattainment, branch criterion and the two-sided unboundedness equivalence. |
| T7 | Establishes all parts of the specified four-state counterexample while retaining the corollary's valid mean identity. |
| T8 | Includes all four canonical components, including the complete conditional-mean chain; it uses only arm-by-arm independence. |
| T9 | Establishes the two specified population designs, their different passer laws, moments, width formulas, both rational enclosures and the strict numerical gap. |
| T10 | Covers both branches of fixed-observable-law invariance, feasible simulation mixtures and means, sensitivity when λ≠0, and the specified unequal widths. |

The original proof's vector-independence inference and Appendix C's simulation setting were checked against the [published paper, pp. 579–582](https://www.cambridge.org/core/services/aop-cambridge-core/content/view/E92D1CFA434028679E0C156AE58D5EAB/S1047198719000056a.pdf/a-note-on-dropping-experimental-subjects-who-fail-a-manipulation-check.pdf). The canonical claims supplied in this task remain the basis for the verdicts.

For T7, the printed reading is: Assumptions 1–3 and common potential check status imply independence of the whole potential-outcome vector together with observed check status from assignment. Its conditions are SUTVA, per-arm pair independence, positive assignment probabilities, positive passing rates and common checks. The four-state witness satisfies each condition; the factorization failure is 1/4 versus 1/8. Independence of assignment from the whole vector is the conclusion being challenged, rather than an additional premise. Both contrasts remain zero.

For T9, the printed comparison says changing the check correlation between the specified rows leaves population bound width unchanged. The witness must preserve λ=σ=1, passing margins 4/5, Gaussian noise independent of the check pair, independent fair assignment, SUTVA, positive passing and positive always-passer mass. Both product-mixture constructions meet these conditions. The theorem concerns the canonical population widths; it does not identify them with the table's finite-sample average entries.

The earlier T7 and T9 label issues are **fixed**: `record.json:21` and `record.json:51` now say `whole`, and their current docstrings identify the printed assertions their canonical counterexamples challenge. Each earlier issue has a disposition in [findings.json](findings.json). T10's current docstring also correctly includes λ≠0 and feasible correlation changes.

All conditioning masses used as ordinary means are positive and finite. For T6, observable-law equality transfers selected-arm integrability to compatible laws; per-arm ignorability identifies the potential passer law, and restricting to always-passers preserves integrability. Thus compatibility does not admit nonintegrable junk means. Essential endpoints stay in extended reals. T10's feasibility inequalities are exactly the four nonnegative Bernoulli stratum masses; they are inherent in its simulation setting. Its scalar-independent invariance clause can be extracted using the explicitly constructed feasible outer parameters. The algebraic comparison at arbitrary distinct correlations implies the stated mean sensitivity on feasible correlations.

Five scratch checks compiled successfully, with at most two Lean processes and no use of `lake`; all witness files import only `SAP.P010.Defs`, with no Challenge theorem or admitted proof. [scratch/validation.json](scratch/validation.json) lists them. They construct every hypothesis for T6, T8 and T10 and independently check T7's finite law and T9's exact stratum arithmetic and product construction. Floating-point Gaussian diagnostics agree with the certified width enclosures, but are not presented as independent rigorous interval proofs.
