# Declaration review

All five declarations are faithful to their current declared scope, with severity **none**. T17 and T21 state their whole canonical claims. T18–T20 state correct, explicitly disclosed finite underlying-space restrictions. The author permits these narrower statements.

The blind reading in `reading.md` was saved before opening the claims, record, earlier review, or architect report. Every declaration in all five elaborated closures was read, including generated auxiliary proofs. `claim-stage.json` records T17/T21 as whole and T18/T19/T20 as narrower. Reading the record did not change any claim-stage assessment.

| Declaration | Assessment |
| --- | --- |
| T17 | Covers equation (1), the strict-overestimation remark under Assumptions 2–4, and its conditional-mean assertion. The additional false-confession identities and equivalences are valid strengthenings. Failure of monotonicity is almost-sure failure, not failure at a null point. |
| T18 | States the limit of the actual unconditioned iid sampling variance and equation (3), maintaining Assumptions 1–3. Every fixed real empty-cell mean completion is quantified. Its finite underlying-space domain is disclosed in the docstring and record. |
| T19 | Includes positive limiting variance, root-n tightness, the correct Gaussian limit, scaled plug-in consistency, and nominal limiting Wald coverage. The cell sample variances use divisor N−1. The finite-space restriction is accurately disclosed. |
| T20 | States both actual scaled variance limits and their strict comparison. The arm-conditional formula for the standard variance equals the canonical expanded total-variance expression. All four fixed mean completions are quantified, and the finite-space restriction is disclosed. |
| T21 | Includes the full shifted conditional-law equality, its level-test consequence, beta=1, studentized standard normal convergence, and uniform limits for the printed p-value. Its population/testing clauses validly use the weaker Assumptions 1–3 plus positive confessor cells. |

Population conditioning denominators are positive under the relevant hypotheses. In T18–T20, monotonicity and nondegeneracy also ensure positive prevalence and 0 < mu·truthRate < 1. All expectations and variances used are genuine: finite laws have finite support, and the general-space models have measurable, almost surely bounded counts. Event measures and finite product measures are finite, so `toReal` does not collapse infinity. Normal quantiles occur only at interior probabilities, and the Gaussian variance is asserted positive before its nonnegative-real conversion matters.

Sample completions are explicit and harmless for these asymptotic claims. Component cell variances equal zero below two observations; the **entire** plug-in variance estimate receives the arbitrary fixed completion when its formula is undefined. Nonpositive completed variance gives square root zero; division then gives studentized value zero and p-value one. These events vanish asymptotically under the stated nondegeneracy. No definition assumes the claimed identity, convergence, or comparison, and the hypotheses are jointly satisfiable.

All nine issues supplied in `earlier.json` are resolved by the present scope disclosures and restricted labels, as detailed individually in `findings.json`. The finite underlying-space limitations themselves remain. The architect correctly acknowledges that a possible finite observable encoding does not assert the missing arbitrary-space conclusions. No further current defect was found.

Nonvacuity was checked with `/home/ubuntu/sap/tools/sap-lean`, without Lake and with at most two Lean processes at once:

- `scratch/FiniteCheck.lean` compiles a model satisfying all hypotheses of T18–T20: independent fair B,Y,Z, X=Y, W=B, V=B+YZ. Every cell has probability 1/4 and conditional variance 1/4; the variance constants are 3/4 and 3/2. A positive-probability deficient iid sample is also exhibited.
- `scratch/WholeCheck.lean` compiles the corresponding measure-based model for T17/T21, a model satisfying Assumptions 2–4 while violating monotonicity with false-confession mass 1/2, and a witness to T21's uniform level-test premise. It checks the population functional numerically in both monotonicity branches.
- Both final compilation logs (`scratch/FiniteCheck.log`, `scratch/WholeCheck.log`) are clean. The printed nonvacuity-helper axiom lists contain only `propext`, `choice`, and `Quot.sound`; no Challenge stub is used. `scratch/Blind.lean` also compiled successfully to inspect closure auxiliaries.

The JSON outputs were parsed and checked for exact target coverage and fingerprint agreement with `closure.json`. No supplied Lean source was modified.
