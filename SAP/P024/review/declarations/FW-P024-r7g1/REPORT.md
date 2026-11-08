# Declaration review

All five declarations are faithful to their recorded scopes. T1, T2, T4 and T5 cover their canonical claims in full. T6 is narrower than its canonical wording and accurately declared restricted. No current defects were found.

| Declaration | Canonical coverage | Recorded decision | Verdict |
| --- | --- | --- | --- |
| SAP.P024.T1 | Whole four-period timing counterexample | whole | faithful / none |
| SAP.P024.T2 | Whole corrected estimation, testing and bias claim | whole | faithful / none |
| SAP.P024.T4 | Whole dominant-cluster counterexample | whole | faithful / none |
| SAP.P024.T5 | Whole corrected consistency claim and accompanying assertions | whole | faithful / none |
| SAP.P024.T6 | Disclosed sufficient assignment subclasses | restricted | faithful / none |

The blind statement and domain audit was saved in [reading.md](reading.md) before any claim or review-history file was opened. All closure entries were read, including all 66 generated auxiliaries printed in [BlindClosure.lean](scratch/BlindClosure.lean). [claim-stage.json](claim-stage.json) was saved before opening the earlier findings, architect report or record. No claim-stage classification changed after reading the record.

T1 establishes the canonical counterexample. The necessity reading it tests is that randomized timing requires a constant untreated path for unbiased effect estimation or valid sharp-null inference. Its conditions are one outlet, four observed periods, one permanent onset chosen uniformly from three dates, fixed outcomes depending only on current exposure, and assignment as the sole randomness. The explicit functions satisfy each condition. Only periods with both exposure probabilities positive enter the estimator; the sharp-null statistic uses the fixed baseline path. All numerical and testing clauses are present.

T4 also establishes its canonical counterexample. The consistency reading it tests assumes whole-cluster independent common-probability assignment, observed fixed own-treatment outcomes, an individual-level effect and a growing cluster count. The witness has genuine independent Bernoulli(1/2) joint masses and positive cluster sizes; its dominant population share is permitted by that reading. Its error bound holds on every proper nonempty allocation, so arbitrary empty-arm extensions do not rescue convergence. The conditional mean, ancillary complete design, limits and six-cluster checks are all stated.

T2 states all three canonical components. T5 retains the uniform outcome bound and probability margin, both design alternatives, convergence for every positive error threshold, the squared-share equivalence, appreciable finite bias and failure when no dominance is removed. No definition assumes its conclusion or uses an invalid mean. Positive domains or explicit empty-arm extensions control every division convention.

Both earlier issues are fixed. T5's Challenge docstring at `SAP/P024/Challenge/Part1.lean:32` and definition docstring at `SAP/P024/Defs/WholeW1.lean:24` explicitly state a single margin uniform over the sequence. T6's `record.json:286–288` and both current docstrings disclose its fixed-count/common-marginal or conditional-count-uniform hypotheses and excluded dependent varying-count laws. The claim's diagnostic note supplies no additional canonical assumptions. Each earlier issue has its own resolution in [findings.json](findings.json).

[Nonvacuity.lean](scratch/Nonvacuity.lean) compiled with the permitted `sap-lean` command, exit 0, without importing Challenge. It checks genuine timing and cluster witnesses, an entire sequence satisfying every T5 hypothesis, and instances of all four T6 branches. [exact_checks.py](scratch/exact_checks.py) passed exact rational checks of the timing values and cluster formulas, including exhaustive proper-subset checks at K=2,3,4,6,8 and the combinatorial mean over all 2,704,156 twelve-of-twenty-four assignments. JSON outputs were parsed and checked for exactly the five requested declarations and matching closure fingerprints.
