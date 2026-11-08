Delta review completed for eight targets and seven theorem stubs. The verdicts
are three `correct_whole`, four `correct_restricted`, and one `omission_ok`.
All eight have severity `none`. There are no unresolved or new findings.

The requested JSON schema has no separate successful-refutation verdict.
`correct_whole` for T1 and T4 means that the complete canonical counterexample
is retained and the architect's `refuted` decision is correct. It does not
endorse the printed assertion. The revised record's decision counts are one
`whole`, four `restricted`, two `refuted`, and one `omitted`.

| Target | Revised decision | Delta assessment |
| --- | --- | --- |
| P024-T1 | refuted | Correct; unchanged full timing witness refutes the stated necessity reading. |
| P024-T2 | whole | Correct; all three mathematical parts remain present. |
| P024-T3 | omitted | Justified; no new precise independent mathematical claim is specified. |
| P024-T4 | refuted | Correct; unchanged full independent-assignment inconsistency witness. |
| P024-T5 | restricted | Accurate disclosure of the two omitted clauses; retained consistency and equivalence unchanged. |
| P024-T6 | restricted | Accurate fixed-count and actual-marginal restriction; statement unchanged. |
| P024-T7 | restricted | Accurate omission of the general event-mass equality; conditional conclusions unchanged. |
| P024-T8 | restricted | Prior scope finding resolved; revised comparison basis and permitted joint laws are explicit. |

**Earlier finding P024-T8: fixed by scope clarification, with correction of my
earlier interpretation.** The original review had one finding, of minor severity.
The proposed change to `whole` was not adopted; I withdraw that recommendation.
The fixed-count uniform-subset model cited in my original finding is in
`canonical_claim.note`. The actual `canonical_claim.statement` in
[claims.json](/home/ubuntu/sap/tasks/CHFID-P024-b/claims.json) gives the broader
verbal blocked-estimation claim without fixed counts or common within-block
propensities. The associated definitions identify the observed block differences,
population-share weights, and HT estimator using actual unit probabilities.
My first assessment treated the note's sufficient formal model as an exhaustive
statement of the target.

The revised [T8 docstring](/home/ubuntu/sap/tasks/CHFID-P024-b/SAP/P024/Challenge/Part1.lean:49)
and [record2.json](/home/ubuntu/sap/tasks/CHFID-P024-b/record2.json) now explicitly
make the comparison to the canonical statement. They disclose fixed strictly
positive arm counts on every assignment and actual common marginals `m_b/N_b`.
They also state that joint uniformity within blocks and independence across
blocks are unnecessary, including balanced nonuniform laws. This accurately
describes the unchanged theorem. The architect's response identifies the source
of the disagreement, and the local statement/note distinction supports resolving
it. Earlier-finding counts: one fixed, zero partly fixed, zero not fixed.

The restriction has mathematical content. Assign one block of three units
uniformly over its six proper nonempty subsets. Every actual marginal is 1/2,
while the treated count varies between one and two. With control outcomes zero
and treatment outcomes `(1,0,0)`, allocation `{0}` has actual HT estimate 2/3
and observed block contrast 1. Every arm is nonempty. Even with a fixed count,
unequal propensities matter: for two units, treat only the first with probability
1/4 and only the second with probability 3/4. With the same first-unit treatment
outcome pattern, allocation `{0}` has actual HT estimate 2 and observed contrast
1; their expectations are 1/2 and 1/4 respectively. Both examples have strictly
interior propensities and positive group sizes. They support the disclosed
restriction without relying on undefined means or inverse probabilities.

Comparison with [reading.md](/home/ubuntu/sap/tasks/CHFID-P024-b/reading.md)
found no mathematical change in any of the seven theorem propositions or their
supporting SAP definitions. The revised stubs still have precisely the seven
statement types read in round 1. The changes are the two refutation labels and
their opening docstring sentences, and T8's expanded scope documentation.
Consequently there are no changed mathematical hypotheses that could introduce
new vacuity or junk values.

T1's new label is justified by the fixed nonconstant baseline, observed
current-exposure outcomes, unbiased overlap estimator, and separately calibrated
sharp-null test. This refutes the specified no-trend necessity reading; it does
not decide the authors' intended informal meaning. T4's new label is justified
under the printed independent-cluster setting itself: fair independent assignment
gives error probabilities tending to one at tolerance 1/8, for every empty-arm
extension, although the number of clusters grows. The complete-half design is
still treated separately. All auxiliary distributional, conditional-mean, limit,
share, and six-cluster clauses remain present. T2's sole `whole` label retains
overlap estimation, uniform sharp-null validity with ties, and both concrete
before-after bias calculations.

The unchanged restricted statements remain accurate. T5 omits the finite-sample
appreciable-bias remark and the cross-referenced failure without no dominance;
it retains both designs, changing populations/probabilities/effects, arbitrary
empty-arm extensions, all positive tolerances, and the maximum-share/squared-share
equivalence. T6 explicitly requires the fixed treatment count on every assignment
and actual marginals `m/N`, omitting random-count laws including the nonempty-arm
conditional Bernoulli case. T7 omits the general closed conditioning-event formula
while retaining positive event mass, actual normalized conditional masses,
equal-size allocation identities and unbiasedness, arbitrary empty-arm extensions,
and the two-cluster bias witness. Its accepted corrected statement already excludes
the printed consistency and blocking recommendations. T3 remains marked
`no_lean=true`; the precise necessity reading and the sound before-after caution
are handled by T1 and T2.

Verification against the refreshed compiled definitions passed:

* [scratch/Check.lean](/home/ubuntu/sap/tasks/CHFID-P024-b/scratch/Check.lean)
  compiles the existing overlap, fixed-count, actual-marginal, correlated-block,
  and full T5 nonvacuity examples. The T5 example has unit cluster sizes,
  outcomes zero and one, probability 1/2, and maximum share `1/(k+2) -> 0`.
* [scratch/DeltaCheck.lean](/home/ubuntu/sap/tasks/CHFID-P024-b/scratch/DeltaCheck.lean)
  compiles the balanced nonuniform four-unit law, its actual marginals and count,
  its distinction from uniform two-subset assignment, and its observed-block/HT
  equality for explicit nonconstant outcomes.
* [scratch/check_arithmetic.py](/home/ubuntu/sap/tasks/CHFID-P024-b/scratch/check_arithmetic.py)
  again passes the exact timing calculations, dominant-cluster enumeration for
  K=2 through 10, conditional equal-size examples, unequal-size bias witness,
  and canonical blocked example.
* [scratch/delta_arithmetic.py](/home/ubuntu/sap/tasks/CHFID-P024-b/scratch/delta_arithmetic.py)
  passes the two positive-denominator scope diagnostics above; results are saved
  in [delta-arithmetic-results.json](/home/ubuntu/sap/tasks/CHFID-P024-b/scratch/delta-arithmetic-results.json).

The Lean checks import only `SAP.P024.Defs`, use no Challenge theorem, and ran
through the supplied `sap-lean` wrapper, with at most one Lean process active.
No `lake` command was run. The renewed checks introduce no reliance on totalized
zero division, truncated subtraction, empty index types, or unnormalized laws.
