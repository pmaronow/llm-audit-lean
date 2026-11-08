All five declarations are **faithful**, with severity **none**. Each states the
whole canonical claim, and each record decision of `whole` is correct. No
step-2 conclusion was changed after reading the record.

The blind unfolding and junk-value audit were saved in `reading.md` before
opening `claims.json`; `claim-stage.json` was saved before opening `record.json`.
Every declaration in every supplied closure was read, including generated
auxiliaries, which only certify elementary facts about the numeral two.

| Declaration | Assessment |
| --- | --- |
| `SAP.P061b.T17` | All three parts are present: equal-margin reduction, unbiased SRS survey mean, and unbiased completely randomized difference in means on any feasible set containing the binary cube. Survey sampling constrains the exposed set, allowing raw assignments with the same exposed set to have different outcomes. The census is included. No stability is added. |
| `SAP.P061b.T18` | The supported revealed-value reduction, both variance expressions, cross-exposure covariance, contrast-variance identity, and diagonal conventions match the claim. Requiring positivity at both bundled exposures loses no single-exposure case: specialize the second exposure to the first. |
| `SAP.P061b.T19` | The two variance estimators match Equations (6) and (7), including ordered diagonal pairs and the distinct treatment of zero joint probabilities. Conservativeness is correctly in expectation. The Young estimator and the uniform observed-data impossibility have the correct meanings and quantifier order. |
| `SAP.P061b.T20` | The adjustment and calibration condition are the printed formulas. Arbitrary design-dependent unit predictions cover the canonical prediction notion. Independence and mean independence are correctly sufficient conditions; no outcome stability is imposed. The extra exposure moment for predictions follows from their full first moment. |
| `SAP.P061b.T21` | All three printed conditions, positivity, and NURVA remain hypotheses, and the conclusion is the full epsilon-tail definition of convergence in probability. Indexing limits by `N+1` covers all positive sizes. Any positive-size sequence can be extended at size zero with empty schedules, `b_0=0`, and an arbitrary atomic design. |

The shared atomic model matches the paper's power-set probability space and
summable probability mass function. Per-unit strict positivity is equivalent
to the printed common positive lower bound in a finite population. Conditional
means, variances, and covariances have their ordinary meanings. Exposure first
moments in T17 and T20 are precisely the author's permitted existence conditions;
NURVA supplies every selected moment used in T18 and T19. No conclusion depends
on a nonsummable real sum defaulting to zero or on division by zero. The
docstrings describe the statements accurately.

For T19's impossibility, fix the design, mapping, exposure and a zero-joint pair.
Their positive supported exposure cells are disjoint. Consider four schedules
indexed by `a,b ∈ {0,1}`, assigning `a` to the first target cell and `b` to the
second, with all other outcomes zero. Each schedule satisfies NURVA and has
bounded outcomes. At any supported assignment, at most one of these two values
is observed. Therefore the mixed difference of the four observed-data statistic
means is zero. The target products have mixed difference
`1·1 − 1·0 − 0·1 + 0·0 = 1`. This is the printed universal-estimation
impossibility, with no inadmissible or undefined-quantity witness.

Independent nonvacuity checks compile with
`/home/ubuntu/sap/tools/sap-lean`:

- `scratch/Check.lean`: survey sampling with within-sample-set outcome variation;
  distinct positive exposures for T18; both positive-joint and zero-joint T19
  cases; and random calibrated, independent and mean-independent predictions
  without outcome stability for T20.
- `scratch/Experiment.lean`: all T17 experiment hypotheses on the full feasible
  set `ℝ²`, with exactly two positive-mass binary assignments.
- `scratch/Asymptotic.lean`: every T21 hypothesis simultaneously, including both
  limits, for a growing population with one randomly exposed unit and nonzero
  outcomes.

These checks import definitions only and do not invoke the audited theorem
stubs. `scratch/BlindPrint.lean` separately inspected closure auxiliaries.
