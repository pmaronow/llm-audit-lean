# Review of SAP.P018a.T1–T5

All five declarations are faithful to their recorded scope, with severity
`none`. T1–T4 cover their canonical assertions. T5 is narrower, and both its
docstring and the record accurately disclose that restriction.

The blind reading and junk-value audit were saved in `reading.md` before
opening `claims.json`. The five independent claim comparisons were saved in
`claim-stage.json` before opening `record.json`. Reading the record caused no
changes to those comparisons. Every closure entry was inspected, including
the 97 generated declarations printed in `scratch/closure-print.txt`.

| Declaration | Claim comparison | Record/docstring assessment |
| --- | --- | --- |
| T1 | Whole | Includes the fixed nonlinear model, conditional zeros, exact moments and variance, positive leading limit, both limit statements, and repeated/weighted extensions. |
| T2 | Whole | Includes the full conditional decomposition, disjoint remainder, exact single-record formulas, and repeated/weighted covariance identities with their necessary block-mean corrections. |
| T3 | Whole | Includes the exact fair-sign formulas, actual fitted-residual counterexamples, deterministic and spike examples, and the inverse example for every N≥3. |
| T4 | Whole | States absolute consistency for the unconditional target and the correctly scaled finite-moment Chebyshev criterion. |
| T5 | Narrower | Retains the three-unit matrix mismatch, fixed-component GLS calculation and abstract intercept variance bound; accurately identifies the missing general-N, distributional and repeated-observation claims. |

The definitions use independent-unit product measures, actual population
projections, actual OLS fitted residuals, and ordered overlap sums with the
diagonal counted once. Conditional covariances condition on the entire design.
They neither assume conditional centering from projection orthogonality nor
replace block covariances by uncentered moments without the required correction.

In particular, T2's existential witness is permitted by the canonical clause
allowing record functions and counts to vary by dyad and record. Independent
constant units, one intercept record per dyad, and responses +1 and −1 on two
disjoint dyads give total score zero but sparse raw meat 2. This witnesses
insufficiency of global centering; it does not purport to refute the canonical
corrected covariance identity. None of the five record entries is labelled
`refuted`; the counterexample targets assert their canonical examples.

No problematic junk values were found. Population inverses have nonzero
determinants. Sample singularities use the permitted zero completion; relevant
finite identities are guarded by size/rank conditions. Small-N division
completions do not alter the limits. T3's operator-norm supremum is nonempty
and bounded for each matrix, and its infinite expectation is an extended
integral without conversion to a real zero. Probability `toReal` operations
apply to finite measures. The stated finite moments and the usual
measure-theoretic conditions exclude integral and conditional-expectation
fallbacks.

Validation uses `scratch/Check.lean` for independent nonvacuity constructions,
including a Standing kernel, positive-count repeated data with nonsingular
normalized Grams, the fair-sign Standing model, and all antecedents of T5's
variance bound. `scratch/exact_checks.py` independently checks uniform score
moments, enumerates all fair-sign samples at N=6 and N=8, checks the
block-centering witness, and verifies the rational GLS calculations. These
are supplementary checks; the already certified theorem proofs are taken as
given. No claim is downgraded for omitting proof ingredients listed only as
audit history in `finite_lemmas`.

Completed checks: `/home/ubuntu/sap/tools/sap-lean scratch/Check.lean` exited
successfully with no diagnostics; `python3 scratch/exact_checks.py` passed.
Python JSON validation confirmed five unique entries, all required fields,
and fingerprints matching `closure.json` exactly.
