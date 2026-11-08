# Fidelity review

| Declaration | Verdict | Severity |
|---|---|---|
| `SAP.P022.T1` | faithful | none |
| `SAP.P022.T6` | faithful | none |
| `SAP.P022.T7` | faithful | none |

The blind reading was saved in [reading.md](reading.md) before opening the claims or record. All closure entries were read, including generated declarations printed in `scratch/BlindPrint.out`. The independent claim-stage judgments were saved in [claim-stage.json](claim-stage.json). The record's three `whole` decisions agree with those judgments; no step-2 conclusion changed. The Challenge docstrings accurately describe their statements, including the usual measure-theoretic conditions.

T1 includes both canonical counterexamples. Right-CDF convergence at limiting atoms is the printed hypothesis; convergence of left CDFs is absent. Both fixed nested witnesses satisfy the actual hypotheses, including boundedness, and the second has a nonsingular limit. Their finite CDF discrepancies and certain sampled tails refute both asserted conclusions.

T6 states the complete corrected finite and conditional argument. Lemma 2 conclusions and the earlier six bounds are explicitly assumed exactly where the canonical claim assumes them. It includes the allocation minimum and lower-endpoint clauses. Positive C guards reciprocal thresholds, and the zero-C integrals genuinely vanish. A compiled zero-population instance satisfies the combined asymptotic hypotheses, including the universal family of earlier rates needed for optimization.

T7 reproduces both canonical counterexamples. The split `(1,1,1)` is allowed for its equation-(23) refutation. The separate small-tolerance refutation compares the upper estimator with actual variance, and the four-corner witness also satisfies the corrected atom-left condition. Its positive centering gap is substantive. The divisible-by-four subsequence is only reindexed.

Both [scratch/Check.lean](scratch/Check.lean) and [scratch/Witnesses.lean](scratch/Witnesses.lean) compiled with `/home/ubuntu/sap/tools/sap-lean`; no `lake` invocation was used. The constructed condition/rate lemmas and witness-threshold lemmas have no `sorryAx` dependency. The remaining convergence and witness arguments, printed readings, condition checklists and clause mapping are in [claim-checks.md](claim-checks.md). The [paper PDF](https://arxiv.org/pdf/1405.6555) was consulted to check the printed statements and variance centering.

No placeholder definition, hidden substantive assumption, vacuous hypothesis family, or consequential junk-value convention was found. [findings.json](findings.json) was parsed and checked for exactly three entries and matching closure fingerprints.
