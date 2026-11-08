# P006a delta review

**15 targets: 10 correct_whole, 5 correct_restricted; no adverse findings.** Both earlier adverse findings are fixed: 2 fixed, 0 partly fixed, 0 not fixed. No new false, vacuous, unfaithful, inaccurately restricted or questionable-omission item was found. All severities are `none`.

The revised record has 5 `whole`, 4 `restricted`, 6 `refuted`, and 0 `omitted` decisions. The requested findings schema has no `correct_refuted` verdict: complete faithful refutations receive `correct_whole`; T12 receives `correct_restricted` because it retains a disclosed omission. This explains the difference between decision and verdict counts.

## Earlier findings

| Target | Earlier issue | Delta status | Revised verdict |
|---|---|---|---|
| P006-T2 | The restriction failed to disclose omission of both sufficient implementations of vector conditional unbiasedness. | **Fixed.** The docstring and record now name both omissions and say the vector condition is assumed directly. They also distinguish T6's treated-residual implementation from the missing vector implementation. | correct_restricted |
| P006-T3 | Supplied reward and welfare maximizers precede all conclusions, but that additional scope restriction was undisclosed. | **Fixed.** The docstring and record now explicitly require both supplied maximizers for the entire conjunction, including per-policy identities, zero-policy equalities and best-response nonnegativity. | correct_restricted |

These are documentation fixes to the restricted statements. T2's assumptions remain at [Defs/Part5.lean:64](/home/ubuntu/sap/tasks/CHFID-P006a-a/SAP/P006a/Defs/Part5.lean:64), and T3's optimizer binders remain at [Defs/Part5.lean:114](/home/ubuntu/sap/tasks/CHFID-P006a-a/SAP/P006a/Defs/Part5.lean:114). The corresponding revised disclosures are at [Challenge/Part1.lean:13](/home/ubuntu/sap/tasks/CHFID-P006a-a/SAP/P006a/Challenge/Part1.lean:13) and [Challenge/Part1.lean:19](/home/ubuntu/sap/tasks/CHFID-P006a-a/SAP/P006a/Challenge/Part1.lean:19), and match `record2.json`.

The revised T3 still does not cover the round-1 example whose feasible cube omits `(1,1)`: it has an ATT maximum but no attained welfare maximum. That exclusion is now explicit. Both maximizing witnesses do exist in the original Bernoulli/Unit nonvacuity instance, so the retained statement is satisfiable.

## Comparison with the blind reading

I re-read all six Defs parts, both import roots and all Challenge stubs. The common definitions, assumptions and mathematical content of T1–T9 and T11–T15 agree with the saved `reading.md`. The only mathematical change found is the extra guards on T10's two general expectation identities. Documentation/decision changes affect T1, T2, T3, T4, T5, T10, T12 and T15.

| Target | Revised decision | Change and scope check | Verdict |
|---|---|---|---|
| T1 | refuted | New refutation notice; unchanged complete two-unit counterexample, reward formulas, true optimum and welfare gaps. | correct_whole |
| T2 | restricted | Both previously missing omissions are now disclosed; retained identities, threshold frontier and optimizer results are unchanged. | correct_restricted |
| T3 | restricted | All optimizer-dependent scope is now disclosed; the mathematical statement is unchanged. | correct_restricted |
| T4 | refuted | New refutation notice; unchanged two pointwise-unbiased estimator witnesses and actual ATT/TT objectives and regrets. | correct_whole |
| T5 | refuted | New refutation notice; unchanged shared-estimator reversal of both ranking comparisons. | correct_whole |
| T6 | whole | Unchanged; all four qualified clauses remain: score/welfare identity, maximizing-set equivalence and regret, unconstrained positive rule, and independent-estimator implementation. | correct_whole |
| T7 | whole | Unchanged; score identity, positive-effect maximizer and characterization/zero regret of every maximizer remain, with the canonical moment guards. | correct_whole |
| T8 | restricted | Unchanged, accurately disclosed integrability and implementation/supporting-claim omissions; per-policy identities remain outside optimizer hypotheses. | correct_restricted |
| T9 | whole | Unchanged; denominator identity, strict comparison, rational intervals, printed-table bounds and rounding intervals remain conditional on the canonical inputs. | correct_whole |
| T10 | refuted | New refutation notice and ordinary-expectation guards; complete singleton-feasible-class refutation retained. | correct_whole |
| T11 | whole | Unchanged; shifted-law identities, existential unbounded regret and the tie example remain. | correct_whole |
| T12 | refuted | New refutation notice; density-existence counterexample retained, with explicit omission of the two-agent completion. | correct_restricted |
| T13 | whole | Unchanged; all five qualified score/change-of-measure/optimal-value/ranking clauses remain. | correct_whole |
| T14 | restricted | Unchanged; both positive parts must be integrable, with the infinite-expectation exclusion disclosed. | correct_restricted |
| T15 | refuted | New refutation notice; both identification/untreated-positivity counterexamples and singleton-private-covariate heterogeneity remain. | correct_whole |

For each `whole` decision I checked all canonical clauses rather than treating the architect's coverage account as evidence. No clause was lost in the revision. The unchanged restrictions of T8 and T14 remain accurate. T12's omission remains accurate despite its new decision label.

## Refutation labels

The six `refuted` decisions refute the relevant printed reading:

- **T1:** the printed rule `(0,1)` gives reward `3/4`, less than the feasible all-treated reward `19/20`; the printed proof's population conditional mean is `1`, rather than `3/4`. The true optimizer is also identified.
- **T4:** pointwise unbiasedness holds, while evaluated biases are `1` and `-1`. The actual ATT/TT best responses have positive welfare regret. This refutes the consequences drawn from Assumption 1 alone, rather than unbiasedness as a condition.
- **T5:** the common estimator is pointwise unbiased and the common reference weights are `1`; effects `1/4 > 1/8 > 0` meet both ranking premises, while optimized scores are `0 < 5/8` in the reverse order.
- **T10:** the singleton always-treated class satisfies nondegeneracy and invariance but every best response has regret zero under every finite-mean law. Withholding is infeasible. The added guards preserve these facts.
- **T12:** the printed absolute-continuity direction, even with equal support, does not ensure a density in the direction required by the weight. The statement and disclosure do not claim ranking failure when a genuine weight exists, or formal completion of the omitted two-agent experiment.
- **T15:** positive treatment probabilities do not identify untreated means or supply a conditional untreated distribution at every covariate. The statements do not claim failure of a regret bound with a well-defined selected mean.

Each revised refutation docstring identifies that scope. None uses a refuted label to claim the corresponding corrected theorem is false.

## T10 guards, junk values and nonvacuity

The blind reading described an unrestricted algebraic identity for `oneATOExpectation`, and a pushforward-invariance identity for measurable policies. At [Defs/Part5.lean:271](/home/ubuntu/sap/tasks/CHFID-P006a-a/SAP/P006a/Defs/Part5.lean:271) the revised first identity assumes `FiniteOutcomeLaw D` and `Admissible π`. The second assumes finite-moment probability laws for both D and D′ and admissibility of π before equal treated-projection pushforwards. `FiniteOutcomeLaw` still means probability with absolutely integrable potential outcomes, not finite support.

These guards agree with the canonical model: potential outcomes have finite means and policies are measurable functions into `[0,1]`. The revised docstring also names the guards. They do not add the conclusion, require an optimal policy, or impose zero feasibility on the counterexample class.

For an admissible policy, `|π(X)Y1| ≤ |Y1|`. Thus the reduced one-unit reward is integrable. The actual one-unit ATO integrand reduces pointwise to `π(X)Y1`, so it too is integrable. The treated projection is a measurable coordinate projection, and its pushforward determines that expectation. No nonintegrable-integral zero convention contributes to either guarded identity.

`scratch/DeltaT10.lean` compiles against the revised Defs using `/home/ubuntu/sap/tools/sap-lean`. It independently proves integrability of both reward representations under the guards. For every `B>0` it constructs the finite point-mass law with outcomes `(1+B,1)` and the admissible always-treated policy, proves an attained reward maximum, expected ATO `1`, welfare `-B`, regret `0`, and the failure of `0 ≥ B`. It also independently proves zero regret for every reward best response in the singleton class under every outcome law. The named proofs use only `propext`, `Classical.choice`, and `Quot.sound`; they import Defs without Challenge and do not depend on `sorryAx`.

The prior explicit finite and Bernoulli instances still satisfy the unchanged T2/T3 and refutation hypotheses. Positive sample sizes, cell masses and beneficiary counts protect their denominators; the only maximum-deviation supremum used is the bounded nonempty singleton `{0}`. Reference densities still use the correct direction and are finite almost everywhere under finite agent laws. No newly introduced empty-index, unbounded-supremum, invalid-conditional-expectation or totalized-integral issue was found.

`findings2.json` has one object per canonical target and preserves the original schema. The round-1 artifacts remain unchanged. This review assesses revised statements and labels; it does not rely on the historical Comparator certificate to certify the revised snapshot.
