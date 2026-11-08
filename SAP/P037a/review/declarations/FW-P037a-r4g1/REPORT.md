# Review of SAP.P037a.T1–T5

All five declarations are faithful at their declared scope. T1 and T3–T5 cover their canonical mathematical claims. T2 is narrower and accurately declares its restriction; its verdict is faithful to that restricted scope.

The blind reading and totalization audit were saved in `reading.md` before reading the claims. `claim-stage.json` was saved before reading the record. Every closure entry was inspected, including the 114 distinct generated proof helpers. Reading the record required no change to the claim-stage conclusions.

| Declaration | Recorded scope | Verdict | Severity |
| --- | --- | --- | --- |
| `SAP.P037a.T1` | whole | faithful | none |
| `SAP.P037a.T2` | restricted | faithful | none |
| `SAP.P037a.T3` | whole | faithful | none |
| `SAP.P037a.T4` | whole | faithful | none |
| `SAP.P037a.T5` | whole | faithful | none |

T1 uses the exact collapsed hypergeometric design and independent block product law. Its limit concerns actual least-squares minimizers, with existence and vanishing singularity probability included. Its counterexample concerns sufficiency of randomization, an eligible-composition main effect and marginal average linearity; it does not claim to refute the qualified response model.

T2 replaces DM's treated-school conditional moments with unconditional product seed-law moments and omits the joint treatment/seed construction establishing conditional centering. Both its docstring and record say precisely this. Randomized composition remains an explicit identification premise. The other identification, centering, augmentation and witness results are retained. The baseline original-regression comparison is equivalently recoverable from the displayed comparison for `Y+Z/5`: adding a fifth of the third regressor adds exactly `1/5` to its coefficient.

T3 uses the actual standard Gaussian CDF and quantile, strict rounding bins, genuine opposite-decision witnesses and explicit numerical error bounds. T4 defines both weight distributions and proves their different event probabilities, together with genuine unique WLS coefficients. T5 uses the W2 statement, including the correct forward reciprocal Jacobian, inverse Jacobian, joint density and all three simplex constructions. The older T5 definition in WholeW1 is outside this declaration's closure. No reviewed declaration is labelled `refuted`.

No substantive extra assumptions, circular premises, placeholders or operative junk values were found. Positive domains protect the divisions and logarithms; probability measures protect real-valued event probabilities; rank conditions protect the matrix inverses; differentiability accompanies the derivative determinants. The Gaussian quantile set is nonempty and bounded below. Zero-mass padding, singleton strata and empty coefficient types have their correct ordinary interpretations.

Validation passed with `/home/ubuntu/sap/tools/sap-lean scratch/Check.lean` and `/home/ubuntu/sap/tools/sap-lean scratch/Additional.lean`. These files construct nonvacuity data without invoking any audited Challenge theorem. `python3 scratch/check_design.py` independently verifies the 454-state design, conditional moments, matrices, determinant, mixture coefficients, unequal-strata example and all six additional regression fits using exact fractions. Its normal-tail calculations are numerical sanity checks only. The supplied Comparator certification is relied on for the theorem proofs; this review audits their statements and definitions.
