# P023 delta statement review

**12 targets: 8 correct_whole, 4 correct_restricted, 0 adverse findings.**
The architect's labels are **6 whole, 4 restricted, 2 refuted, 0 omitted**.
The two correct refutations receive `correct_whole` in the findings schema;
`refuted` is a record decision, not an allowed findings verdict.

| Findings verdict | Count |
| --- | ---: |
| correct_whole | 8 |
| correct_restricted | 4 |
| restriction_inaccurate | 0 |
| not_faithful | 0 |
| vacuous | 0 |
| false | 0 |
| omission_ok | 0 |
| omission_questionable | 0 |

Severity: **none 12, minor 0, major 0**.

## Earlier findings and their disposition

My first review reported no adverse findings. The accepted restrictions
remain accepted restrictions; restoring their omitted scope was not a
requested repair. On reconsideration I agree with the other referee's
T10 objection and correct my previous approval of the original statement.

| Target | Earlier assessment | Delta assessment and disposition |
| --- | --- | --- |
| T1 | correct_whole | Unchanged; all concrete witness and localization clauses retained. No repair requested. |
| T2 | correct_whole | Unchanged; all degree-seven witness clauses retained. No repair requested. |
| T3 | correct_restricted | Unchanged; exactly the accepted omission and added assumptions remain disclosed. No repair requested. |
| T4 | correct_restricted | Unchanged; all population clauses and disclosed sampling/predictor restrictions retained. No repair requested. |
| T5 | correct_restricted | Unchanged; all witness/family clauses and the disclosed finite-risk predictor restriction retained. No repair requested. |
| T6 | correct_whole | Unchanged; logarithmic rate, norm, single fixed witness, divergent subsequence and RD limit retained. No repair requested. |
| T7 | correct_whole | Unchanged; population formulas, constants, finite FWL and finite conditional-bias clauses retained. No repair requested. |
| T8 | correct_restricted | Unchanged; every population and sampling conclusion and all disclosed guards retained. No repair requested. |
| T9 | correct_whole | Unchanged; pair-indexed partition, demeaning and positive-denominator ratio retained. No repair requested. |
| T10 | correct_whole, incorrectly approving the old scope | **Fixed.** The revised refutation forces a positive-degree counterexample; the other referee's major scope finding is fully addressed. |
| T11 | correct_whole | Unchanged; all-solutions equality for the printed coarsened regression retained. No repair requested. |
| T12 | correct_whole | Unchanged; the selected fixed-law printed reading is still refuted. No repair requested. |

Thus the reported scope defect is **fixed**, with **0 partly fixed** and
**0 not fixed** defects. There are no new adverse findings.

## Changed theorem: T10

The saved blind reading expressly said, in its T10 paragraph, **“J is not
assumed positive in the universal statement being negated.”** My earlier
coverage assessment failed to follow through on that distinction. A
counterexample at degree zero would refute the old universal without
refuting localization for regressions containing a vote-share control.
The presence of a stronger witness elsewhere in the package does not make
the old theorem itself assert that stronger refutation.

`Defs/Part4.lean:196` now has `1 ≤ J` **inside** the universal being
negated. This strengthens the refutation: it asserts existence of a
counterexample with positive degree. It does not impose a new external
hypothesis that could make the theorem vacuous. The other premises stay
the same: finite two-party data, `0 < k < 1`, Condition 1, full rank, and
existence of a polynomial fitted mean strictly between zero and one at
every observation. The conclusion being contradicted remains equality of
the polynomial estimates for every pair of outcome vectors agreeing on
the close window.

The degree-one six-election design supplies every premise. Its exact mean
has coefficients `(1/2, 1/10, 1/20)`. The outcome change at margin `3/4`
leaves the close outcomes fixed but changes the polynomial coefficient by
`-20299/13920200`. Both outcome vectors are in `(0,1)` and can be draws of
one correctly specified model with bounded mean-zero noise. Thus this is
a failure in the intended controlled, correctly specified setting.

The revised Challenge docstring explicitly says **positive-degree
polynomial vote-share controls** and also states the positive-count domain
of the coarsened comparison. Both descriptions match the definitions.
`T10Statement` still conjoins the unchanged coarsened localization theorem.
The `refuted` decision is appropriate. The record's switch to the complete
degree-one witness removes reliance on a broader negation that could have
been established using only degree zero.

No other change in mathematical content was found when the revised Defs
and Challenge were compared with all twelve expansions in `reading.md`.
The original blind reading and first-round reports are preserved.

## Labels and retained restrictions

The six `whole` targets are T1, T2, T6, T7, T9 and T11. Their canonical
clauses remain present, including the finite residual identities in T7,
the explicit unbounded tails in T6, and the all-solutions interpretation
with empty nuisance bins in T11.

The four `restricted` targets retain exactly these disclosures:

- **T3:** drops the separate fixed-tolerance probability inequality; adds
  positive close winner/loser counts to the entire nonlocality component;
  adds the stated probability, positive-degree, positive-bandwidth and
  design-admissibility premises to shared consistency.
- **T4:** adds OLS admissibility at degrees one and seven and RD
  admissibility to sampling; comparisons require measurable predictors
  with integrable squared error. All population clauses remain present.
- **T5:** comparisons require measurable predictors with integrable squared
  error. Every other explicit witness and family clause remains present.
- **T8:** adds RD admissibility and OLS admissibility at every fixed degree
  and every rate-qualified growing-degree schedule. No conclusion (a)–(g),
  including existence of degree schedules, is dropped.

These disclosures agree in `record2.json` and the Challenge docstrings.
The accepted restrictions introduce no new hidden assumption. T12's
unchanged `refuted` label remains appropriate: its fixed uniform-law
continuous witness contradicts the population tolerance conclusion while
satisfying the sampling and RD premises. It does not rely on an empty
window or singular sample convention. There are no omitted targets.

## Nonvacuity, junk values and checks

`scratch/DeltaCheck.lean` compiled successfully with
`/home/ubuntu/sap/tools/sap-lean scratch/DeltaCheck.lean`. It imports only
`SAP.P023.Defs` and checks:

1. The revised negation is equivalent to existence of a counterexample
   whose degree satisfies `1 ≤ J`, with all remaining premises and failure
   of localization conjoined.
2. An independent concrete instance of **every premise** exists at
   `n=6`, `J=1`, `k=1/200`, with the displayed exact-model coefficients.
   This includes direct proofs of full rank and strictly bounded fitted
   values, without assuming `LinearWitness` or the refutation.
3. As a separate logical inference check, the complete `LinearWitness`
   entails the strengthened positive-degree refutation. This conditional
   inference is not used as a substitute for the independent nonvacuity
   instance.

`python3 scratch/audit_exact.py` also passed on the revised files. It
rechecks the genuine degree-one coefficient change as well as the prior
exact finite and population certificates. Full rank makes the finite OLS
coefficient unique, so the revised counterexample cannot exploit the
choice of a singular coefficient. Its close winner and loser counts are
both one. Its index type has six elements. No integral or asymptotic
exceptional branch enters this changed refutation.

The previously checked nonvacuity instances for the unchanged targets
remain valid and are recorded individually in `findings2.json`. No changed
definition introduces a new zero denominator, nonintegrable integral,
unbounded real extremum, empty-type argument or conclusion-assuming
hypothesis. The analytic existence and logarithmic asymptotic in T6 were
not independently reproved in Lean in either review. This review assesses
statements, not the architect's bridge or external-kernel certification
claims.

`findings2.json` parses with Python, has exactly one entry for every target,
and uses the same fields and allowed verdicts as `findings.json`.
