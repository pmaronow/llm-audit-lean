# Review of SAP.P002a.T11–T15

All five declarations are **faithful**, with severity **none**. Their `whole`
decisions are justified. The Challenge docstrings describe the actual statements.
No step-2 conclusion changed after reading `record.json`.

| Declaration | Assessment |
| --- | --- |
| T11 | Includes the corrected centering sign, both finite identities, normalization and exact cancellation, and the fixed-balance Big-O and zero limit. The positive denominator is supplied by the canonical definitions. |
| T12 | States the entire specified eight-unit counterexample: admissibility, bracket −2, 70 reassignments, variance 1/28, erroneous lower bound 1/14, and corrected equality. |
| T13 | Gives both corrected finite lower bounds, including the explicit balance constant. Its arbitrary fixed array specializes to every canonical observed adjusted array and every beta. Every valid design admits the balance parameter needed to extract the first inequality. |
| T14 | Includes the complete balanced-sign counterexample, its hypergeometric law, moments, exact formulas, support, probability-one failure and divergence, and the corrected ratio's mean deficit and tails. |
| T15 | Gives the corrected variance/variance limit for every fixed increasing subsequence, almost surely and simultaneously for all positive tolerances. Positivity of both adjusted population variances is an explicit standing Supplement C assumption. |

T12 and T14 formalize counterexamples that the canonical assertions themselves
request; their `whole` labels are correct. Each witness satisfies the printed
conditions, including genuine independent complete-randomization laws. The
condition lists and an extension of T14's witness to intermediate odd sizes
appear in `claim-analysis.md`.

The finite design averages are genuine expectations and variances, and the
sample variance estimator matches the paper's squared arm denominators. Valid
designs exclude empty arms and empty design spaces. The singleton-complier zero
covariance convention is explicitly authorized by Assumption 3. T11 guards its
normalized denominator. T14's conditional variance is strictly positive. T15
allows early conditional zero variances; its limit forces eventual positivity
almost surely, so this totalization does not change the asymptotic assertion.
Its arbitrary measurable coupling also covers the printed independent coupling.

`reading.md` was saved before opening claims or record; `claim-stage.json` was
saved before opening the record. All listed closure entries, including generated
numeral and finite-index proof instances, were read. `scratch/Blind.lean`
compiled. `scratch/Nonvacuity.lean` independently constructs every sequence
hypothesis, including the probability space and exact marginal laws, directly
from definitions and Mathlib. Its axiom checks exclude `sorryAx`.
`scratch/finite_checks.py` uses exact rational arithmetic to check the eight-unit
witness, an unbalanced T13 instance, a nonzero-beta T11 identity, and every
reassignment for T14 at even sizes 4–16. Results are in
`scratch/finite-results.json`. The finite checks supplement the certified proofs;
they do not replace the universal statements or their asymptotic clauses.

`findings.json` contains exactly the five requested declarations and their
unchanged closure fingerprints. No package source was modified.
