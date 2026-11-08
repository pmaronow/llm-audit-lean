# P016a delta review

| Verdict | Count |
|---|---:|
| correct_whole | 8 |
| correct_restricted | 2 |
| omission_ok | 1 |
| restriction_inaccurate | 0 |
| not_faithful | 0 |
| vacuous | 0 |
| false | 0 |
| omission_questionable | 0 |
| **Total** | **11** |

Severity: none 11, minor 0, major 0. No adverse findings remain or were
introduced. All eleven round-1 verdicts are retained.

## Earlier findings and changes

My round-1 `findings.json` contained no adverse findings, no proposed fixes,
and empty issue lists for all eleven targets. There are therefore no earlier
defects to classify as fixed, partly fixed, or not fixed: each has status
**no correction required; prior judgment retained**. The following table
accounts for every earlier entry and the renewed statement check.

| Target | Earlier verdict retained | Comparison with `reading.md` and canonical content |
|---|---|---|
| T1 | correct_whole | Unchanged: both assignment enumerations, pairing covariances, full tables, both designs' tail masses and covariances. |
| T2 | correct_whole | Unchanged: all (A)–(G), including exact coefficients, attainment, the within-group identity, ordering and tail equivalence, moment/multiset and covariance identities, and both network/scalar-KS witnesses. |
| T3 | correct_whole | Unchanged: both constructed exposure examples, conditional means, affine obstructions, normalization, all regression minima, exact-rational table determinant, and all three cutoff examples. |
| T4 | correct_restricted | Unchanged: all seven conjunction groups and the same accurately disclosed additional conditions and omissions. |
| T5 | omission_ok | Still omitted. The architect's expanded semantic rationale supports the same conservative omission; no refutation theorem has been added. |
| T6 | correct_restricted | Unchanged: finite-design model consistency and the strict-cutoff definition, under the same disclosed sample-variance convention and omitted procedure/empirical content. |
| T7 | correct_whole | Unchanged: both mean tails, corrected probabilities, probability-one rejection, adjustment, all 70-assignment KS claims, and raw treated/control separation. |
| T8 | correct_whole | Unchanged: arbitrary-effect adjustment, true-baseline cancellation, law equality, inclusive upper-tail calibration, and the exact mean-shift/equality characterization. |
| T9 | correct_whole | Unchanged: all three literal-reading discrepancies, the complete SSR table, and the universal point-mass and inclusive-tail assertions. |
| T10 | correct_whole | Unchanged: simple-regression characterization, arbitrary-matrix attainment and fitted-vector uniqueness, KS supremum and label properties, and symmetric binary-network columns. |
| T11 | correct_whole | Unchanged: weak and strict KS witnesses, signed gaps, opposite SSR changes, and all four effect-increasing negations. |

I reread every current definition and Challenge theorem and compared them
with the saved blind reading, including the shared definitions on which
apparently unchanged theorem names depend. No semantic changes, new
hypotheses, altered constants or quantifier orders, or missing conjuncts
were found. The current docstrings also retain their previous meanings.
`record2.json` is byte-for-byte identical to `record.json`; all ten theorem
names and all eleven decisions match. The architect's report describes this
as a revision of review explanations, consistent with the statement check.

Current source hashes and the reviewed theorem inventory are saved in
`scratch/revision2-audit.json`. No round-1 Lean-source hash snapshot was
retained, so the source comparison is against the saved reading and earlier
source text, not a claimed historical hash comparison.

## Decision labels and disclosure

Every target labeled `whole` still contains all clauses of its canonical
claim. The counterexample targets already ask for their specified witnesses;
their `whole` labels do not assert the corresponding erroneous printed
readings. No decision is labeled `refuted`, so there is no new refutation
whose connection to a printed assertion needs certification.

T4 retains the extra bank-count hypothesis on the raw similarity/distance
identity and the explicit positive-SD premises for both standardized
exposures. The first condition is stronger than needed for the raw identity;
the second positivity premise is redundant once the exposure relation is
known. Both remain accurately disclosed, satisfiable restrictions. The
omitted complete application/simulation identifications, saved-bank and
reference-draw counts, directional application tails, projected bounds,
and figure/coefficient/rectangle association remain disclosed.

T6 retains sample variance with divisor n-1 on every design index. Its g
is an arbitrary vector-valued function subject to that variance condition;
the conclusion is the stated model cancellation, not an identification of
a unique normalization algorithm. The complete regression/testing procedure,
other variance conventions and empirical rejection proportions remain
excluded by the docstring and record. Neither restricted theorem has been
silently promoted to whole.

For T5, the supplied report now explains the target-level fidelity concern
in addition to the old source-row rejection. The printed comparison leaves
joint information and correlation unspecified. Retained T2 proves
invariance when both empirical group multisets agree; its separate example
also shows that agreement of scalar KS can coexist with different SSR.
Those are distinct statements. The retained finite design examples and
covariance identities are sound, but no formal equivalence to every reading
of the printed information/precision comparison is supplied. I therefore
retain `omission_ok`, without asserting that a chosen precise interpretation
cannot be refuted.

The expanded explanation is in `architect-report.md`; the supplied
`record2.json` still contains the original short omission reason. My decision
does not depend on the report's cited external precedence rule, rejected
source declaration, comparator logs, or other referee's original files,
which are outside the permitted audit inputs. The report's explanation
does not replace the canonical claim in `claims.json`.

## Junk values and nonvacuity

No changed statements introduce a new junk-value or nonvacuity question.
The unchanged safeguards were checked again: group means and ECDFs have
positive group denominators where needed; conditional bank cells are
inhabited by the coverage premise; standardization uses positive SD under
n>=2 or explicitly nondegenerate witnesses; reference counts use positive
bank sizes; and Balanced(8,4) is inhabited with 70 assignments. A finite law
cannot have an empty underlying type because its weights sum to one.
Sample-variance subtraction is over the reals. Least-squares ranges are
inhabited and bounded below, and the KS threshold range is inhabited and
bounded, so real infimum/supremum defaults do not do the work.

The existing `scratch/Nonvacuity.lean` was compiled again against the
refreshed definitions with the permitted command:

`/home/ubuntu/sap/tools/sap-lean scratch/Nonvacuity.lean`

It exited successfully. It retains a nonempty T4 support with both bank
states represented, centered-exposure variance 1/48 and nonzero model
effects; and a T6 model with a genuine three-point line-distance matrix,
two distinct assignments, variance-one centered raw exposures and nonzero
direct/indirect effects. It also checks the positive group counts, an
inhabitant of Balanced(8,4), and the general least-squares range conditions.
The round-1 exact-rational witness checks remain applicable because their
definitions and inputs have the same readings.

`findings2.json` preserves the requested schema and was parsed with Python.
It covers each of the eleven canonical targets exactly once, with theorem
names checked against both the current Challenge and `record2.json`.
