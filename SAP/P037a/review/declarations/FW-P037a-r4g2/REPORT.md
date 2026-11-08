# Review of SAP.P037a.T6–T10

All five declarations are **faithful**, with severity **none**. Their
`whole` decisions and null restrictions in `record.json` are accurate, and
their docstrings describe their statements correctly. The record caused
no change to the decisions saved in `claim-stage.json`.

The blind mathematical reading was saved in `reading.md` before either
claims or record was opened. All 117 closure entries were inspected
(95 distinct declarations, including generated auxiliaries). Those
auxiliaries contain ordinary numeral-instance, constructor, case-analysis,
and probability-normalization facts; none hides a substantive hypothesis.

| Declaration | Canonical content checked |
| --- | --- |
| T6 | All six arithmetic clauses: totals, corrected percentage, robustness to rounding the totals, per-student quantities, exclusion of 25% from the mixed-basis ratio, and the five-point/one-sixth change. |
| T7 | Both feasible overlaps, distinct labels, both general overlap implications, and failure of a function satisfying every printed case implication. |
| T8 | The exact corrected predicates, coverage and uniqueness on every feasible quadruple, and both witness classifications. |
| T9 | Independent product sampling; indicator and frequency moments; variance and Chebyshev bounds; consistency; the repeated-last-draw identity and all three numerical example values. |
| T10 | All uniform two-of-four moments; treatment and control dependence; the general balanced fixed-count argument without uniform probabilities; and the independent two-block law. |

The abstractions preserve the claims. Nonnegative integer counts can be
represented by naturals without loss. Exposure cases are the printed
binary-product conditions unfolded into logical predicates. Finite designs
are nonnegative real mass functions summing to one; their means, variances,
covariances and probabilities are standard finite sums. Arbitrary events
in T9 include every corrected exposure event. Every joint law of four
binary indicators in T10 has a finite representation. None of these
definitions assumes its theorem's conclusion.

For T7, the printed reading is: **the five displayed conditions assign
one exposure to each feasible assignment and student**. Its relevant
conditions are binary school and seed indicators, seeds only in treated
schools, nonnegative peer counts with referent count at most total count,
the hierarchical seed allocation, and at most ten named peers. Both
quadruples have binary indicators with seed ≤ school and counts zero.
The compiled construction has 40 eligibles in four strata of ten, selects
five per stratum, and permits a focal seed or nonseed with no named peers.
It therefore respects the seed quota and peer bound and extends to a
two-of-four treated-school allocation. The overlaps refute the printed
display's function assertion and establish the canonical counterexample.

For T10, the printed reading is: **the between-school randomization makes
schools independent by construction**. The witness conditions are four
schools per block, binary indicators, exactly two treatments, and marginal
treatment probability one half; its first computation additionally uses
uniform probabilities over the six pairs. The enumerated design satisfies
each condition and gives covariance −1/12. The general clause drops
uniformity while retaining every other condition and forces a negative
pair. Independent randomization is imposed between the two blocks, where
the product probabilities and zero covariance hold. This establishes the
canonical counterexample, without asserting failure of the estimator's
consistency or asymptotic normality. Neither T7 nor T10 is mislabelled as
a refutation of its own canonical assertion.

All substantive denominators are positive in their asserted uses. The
general frequency helper's value at zero draws is unused: the bounds
require positive J and the limit uses J+1. Natural subtraction in T6 is
only the positive difference 2695−2012. No integral totalization,
extended-real conversion, extremum, or partial-function default affects
these results. The ordinary finite models automatically satisfy the usual
measure-theoretic conditions.

Nonvacuity and independent arithmetic checks in `scratch/Check.lean`
compiled successfully with `/home/ubuntu/sap/tools/sap-lean`; they import
only Defs and do not invoke the five Challenge stubs. They include all
interval hypotheses together, genuine exposure witnesses, a representative
of every corrected category, independent nondegenerate Bernoulli draws,
and both uniform and unequal fixed-count allocation laws. The closure
printing check also compiled. `findings.json` and `claim-stage.json` were
parsed and checked for exactly the five requested declarations, with
fingerprints copied from `closure.json`.
