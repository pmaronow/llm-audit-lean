# Review report

All five reviewed declarations are **faithful**, with severity **none**. No statement, definition, restriction, label, or docstring repair is needed.

The required stages were kept separate: the blind review of the source statements, docstrings, and all 109 distinct closure declarations, together with the saved `reading.md`, was completed before opening `claims.json`. The claims were then compared and `claim-stage.json` saved before opening `record.json`. The elaborated closure, including generated helpers, was inspected with `scratch/Inspect.lean`. No unit source was changed, no `lake` command was run, and scratch compilation used one Lean process at a time.

| Declaration | Record decision | Review |
| --- | --- | --- |
| `SAP.P022.T11` | whole | All three corrected numerical parts are present, with the exact closed rounding bins, shared positive Wald multiplier, percentage bounds, and displayed-input identity. Every hypothesis, including both variance bins, has a simultaneous rational witness. |
| `SAP.P022.T12` | whole | The sharp-null design bias, finite Wald-width inequality, multiplier bound, rounded-number incompatibility, and fixed-multiplier calculations all match. The contradiction clause intentionally proves the impossibility asserted in canonical part (d). It introduces no hidden vacuity into the statistical claim. |
| `SAP.P022.T2` | whole | Both uniform population-CDF limits and both sample-CDF tail bounds hold under exactly the corrected assumptions, with the printed explicit positive nonincreasing integer function. A balanced zero-outcome sequence supplies all hypotheses, including convergence on both sides of an atom. |
| `SAP.P022.T18` | refuted | The existential counterexample contradicts original Lemma 2 under its own conditions 1–3. It does not purport to refute corrected T2. The docstring's description of a printed-claim refutation is accurate. |
| `SAP.P022.T3` | whole | The finite second-moment bounds, assignmentwise errors, finite tails, and allocation-only asymptotic bound match all hypotheses and constants for both endpoints. The asymptotic result adds no distributional-convergence assumption. |

The finite design definitions induce the paper's uniform assignment law: each unordered treatment/control/unsampled partition corresponds to the same number `m! k! (N-m-k)!` of permutations. Population variances, marginal variance estimates, and sharp covariance integrals have the prescribed normalizations. The nested-prefix sequence representation matches the standing asymptotic setting.

No relevant junk-value branch is used. Design sizes make statistical denominators positive; CDF suprema have nonempty ranges bounded by one; probability masses are finite before `toReal`; and scaled limsups are extended nonnegative real, so actual divergence remains infinity. Empirical quantiles agree with the order-statistic inverse on `(0,1]`. Their finite convention at zero changes no covariance integral, and the finite-step integrands are measurable and integrable. T11 and T12 use square roots only on nonnegative inputs. These checks were applied independently to each closure.

`refutation-check.md` records the printed T18 reading and checks every condition for the negative-reciprocal witness. Its fixed outcomes converge to zero, giving weak joint convergence to the origin point mass; both population CDFs agree with the limiting CDF at its only atom. Nevertheless every population CDF distance is one. This is an actual failure of the printed assertion. No nonsingularity or atom-left convergence condition belongs to original Lemma 2.

`/home/ubuntu/sap/tools/sap-lean scratch/Check.lean` completed with exit code 0. It imports only `SAP.P022.Defs`, constructs the nonvacuity examples for all satisfiable premise groups, and independently proves the full T18 existential counterexample. Its only diagnostic is a harmless simplification-style warning in the scratch proof. No Challenge theorem or certified Solution was used for those checks.

No claim-stage conclusion was changed after reading the record. T18's step-2 value `different` records that its logical direction is an explicit refutation rather than a positive restatement; its validity as a refutation was already established at that stage. The record correctly labels it `refuted`. Final findings and copied fingerprints are in `findings.json`.
