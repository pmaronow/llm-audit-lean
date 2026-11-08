# Review of SAP.P019a.T1–T5

All five declarations are **faithful within their recorded scope**. No defects
were found in their statements, dependency definitions, labels, or docstrings.

| Declaration | Recorded scope | Assessment |
|---|---|---|
| SAP.P019a.T1 | restricted | Correct response discrepancy and exact integrated mixture contrasts. Omission of the joint population and conditional-observable identification is accurately disclosed. |
| SAP.P019a.T2 | restricted | Correct response rules, increments, and both contrast formulas for every affected proportion in [0,1]. The omitted observable identification and approximate power assertion are accurately disclosed. |
| SAP.P019a.T3 | whole | Covers the entire canonical counterexample, including population laws, every-size empty-cell probabilities, missing mass, singleton completion, six occupied-cell moments, product-variance discrepancy, and random treatment count. |
| SAP.P019a.T4 | whole | Covers every corrected finite-sample and asymptotic clause on general probability spaces. Finite pattern fibres correctly express the stated conditioning sigma algebra. |
| SAP.P019a.T5 | whole | Covers the full canonical sign-comparison counterexample and preserves the correct displayed identity, including equality of corrected distribution functions. |

`reading.md` was saved before opening the claims. `claim-stage.json` was saved
before opening the record. Reading the record required no revision of the
claim-stage conclusions. T3 and T5 prove their canonical counterexample
assertions; their docstrings identify the disputed comparison and its scope.

The finite definitions use genuine probability masses and iid product laws.
T3's singleton covariances explicitly concern zero completion; its four-sample
variance comparison conditions on a positive occupied-cell event. T4 guards
substantive conditional moments by positive events. Its null-event values at
sample sizes zero and one affect neither its asymptotic order nor its limit.
Probability, measurability, and bounded counts ensure genuine integrals;
whole-triple independence is stated without weakening it to pairwise independence.

Validation passed using the supplied `sap-lean` command:

- `scratch/ClosureChecks.lean`: inspection of all 59 generated helpers within
  the 169 distinct closure declarations.
- `scratch/FiniteChecks.lean`: independent finite-law checks, all standing
  assumptions for both counterexample populations, a positive-mass occupied
  sample, the affected-proportion hypotheses, and the distribution discrepancy.
- `scratch/MeasureChecks.lean`: an actual measure-backed instance satisfying
  every T4 hypothesis, with an integral-to-finite-sum bridge.
- `scratch/exact_checks.py`: independent rational enumeration of the key
  contrasts and counterexample moments; results in `scratch/exact_checks.json`.

These checks do not invoke T1–T5 as proof steps. No `lake` command was run.
The journal manuscript's Section 4.1 and Appendix B were cross-checked against
the supplied canonical text using the [paper on PMC](https://pmc.ncbi.nlm.nih.gov/articles/PMC5589210/).
The supplement PDF could not be retrieved through the web tool; its supplied
canonical text and local definitions were sufficient for this review.
