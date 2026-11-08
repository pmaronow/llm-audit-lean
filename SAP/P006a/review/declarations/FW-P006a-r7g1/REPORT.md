# P006a statement audit

All five declarations are **faithful**, with severity **none**. Their definitions
implement the canonical rewards, policy classes, sampling laws, and welfare
quantities. No vacuity, encoded conclusion, or use of a junk value was found.

The blind account in [reading.md](reading.md) was saved before opening the
canonical claims. [claim-stage.json](claim-stage.json) was saved and parsed before
opening the architect's record. Every closure entry was read, including the
generated numeral proofs: 116 distinct unit declarations across the five
closures. The record's five `whole` decisions are correct; no claim-stage
conclusion changed after reading it.

| Declaration | Assessment |
| --- | --- |
| T1 | Covers every part of the canonical two-unit counterexample, including the proof-display mismatch, full reward polynomial, unique fractional optimum, and both welfare gaps. Its product treatment masses satisfy the required independence. |
| T2 | Includes all four corrected clauses, the estimator implementations, and attained finite-support frontier and scalar maxima. Its general measurable-space formulation extends the canonical discrete setting correctly. |
| T3 | Includes the positive-factor identity, zero-policy argument, every-best-response bound, attained-maximum formula, and exact counterexample to the printed regret formula. The proved finite-supremum formulation extends the result to classes without an attained welfare maximum. |
| T4 | Includes both specified estimators and all their evaluation biases, objectives, optima, welfare regrets, and zero-private-heterogeneity specialization. Fixed-query unbiasedness holds; independence from the evaluation sample is not required by this target's assertion. |
| T5 | Includes the specified shared estimator, both conditional biases, both score formulas, and the reversed maxima despite ordered positive effects. The identical agent/reference laws have representing density one, so every density and weight requirement is satisfied. |

The counterexample targets assert these witnesses themselves, so `whole` is the
appropriate decision. Their docstrings accurately describe their scope. Detailed
printed readings and checks of every witness condition are in
[scratch/WitnessAudit.md](scratch/WitnessAudit.md). The paper's reward and ranking
definitions were cross-checked against the
[published PDF](https://proceedings.mlr.press/v238/wang24b/wang24b.pdf).

The usual measure-theoretic conditions are assumed as authorized. The general
Lean statements explicitly provide the relevant measurability and integrability.
Estimator moments are confined to the stated feasible class. Conditional event
means occur only at positive treatment probability; finite probability laws
exclude infinite-measure conversions. The real suprema used in the conclusions
have nonempty bounded images, with attainment asserted where needed. Zero on an
empty treated sample is the canonical reward convention and is essential to T1.

Independent scratch verification compiled successfully using `sap-lean`:

* [scratch/Nonvacuity.lean](scratch/Nonvacuity.lean) constructs one experiment
  satisfying every T2/T3 design and estimator hypothesis over all admissible
  policies, including zero. Direct calculations also construct genuine reward
  and welfare maximizers. It checks positive normalized finite-support masses
  and antitone scores.
* [scratch/FiniteWitnesses.lean](scratch/FiniteWitnesses.lean) checks the finite
  probability masses, T1's polynomial and benchmark values, the printed regret
  expression, and T4/T5's unbiasedness, evaluated biases, and reward formulas.
* Axiom checks on the named scratch proofs show only `propext`,
  `Classical.choice`, and `Quot.sound`; none uses `sorryAx` or a Challenge stub.

[findings.json](findings.json) contains exactly five entries, with fingerprints
copied from `closure.json`, empty issue lists, and individual nonvacuity evidence.
Both output JSON files were checked with Python. No unit source was edited.
