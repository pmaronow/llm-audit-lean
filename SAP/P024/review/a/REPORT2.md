# P024 delta review

All eight revised target decisions are acceptable. The earlier T8 finding
is closed, and there are no outstanding or new issues. No mathematical
definition or theorem formula differs from its saved blind reading;
the changes concern the T1/T4 refutation labels and opening descriptions,
and the T8 scope description.

| Referee verdict | Count |
| --- | ---: |
| correct_whole | 3 |
| correct_restricted | 4 |
| omission_ok | 1 |
| restriction_inaccurate | 0 |
| not_faithful | 0 |
| vacuous | 0 |
| false | 0 |
| omission_questionable | 0 |
| **Total** | **8** |

Severity counts: **none 8, minor 0, major 0**.

The unchanged findings schema has no `correct_refuted` verdict.
`correct_whole` for T1 and T4 means their entire canonical counterexamples
are retained and their new **refuted** decisions are justified; it does
not label the printed assertions true. The revised architect decisions
are **1 whole, 4 restricted, 2 refuted, 1 omitted**.

## Earlier finding: P024-T8

There was one target-level finding in `findings.json`, with two issue entries.

| Earlier issue | Status | Delta assessment |
| --- | --- | --- |
| Fixed counts and common marginals were described as additions despite appearing in the diagnostic formal-reading note. | **Fixed / closed** | The revised docstring and record explicitly identify the canonical statement, rather than that note, as the comparison point. I correct the earlier interpretation described below. |
| The documentation did not describe the admitted balanced nonuniform laws. | **Fixed** | The revised docstring and record explicitly include those laws and explicitly state that within-block joint uniformity and cross-block independence are unnecessary. |

No earlier finding is partly fixed or still open: **1 fixed, 0 partly fixed,
0 not fixed**, counting the target-level finding.

My first assessment promoted `claims.json` → P024-T8 →
`canonical_claim.note` into the mandatory mathematical claim. That note
describes a uniform fixed-count example. In contrast,
`canonical_claim.statement` prints the general blocking/weighted-estimation
sentence and Note 4; it does not stipulate fixed counts or common within-block
propensities. The revised comparison is explicit in
[the T8 docstring](/home/ubuntu/sap/tasks/CHFID-P024-a/SAP/P024/Challenge/Part1.lean:52)
and `record2.json` → P024-T8 → `restriction`.

I therefore withdraw the earlier request to relabel T8 whole. Its fixed-count
assumptions are a substantive restriction of the primary printed statement,
and the revised text accurately discloses them. The earlier mathematical
observation remains valid: the theorem also covers balanced nonuniform laws,
including treatment of {0,1} or {2,3} with probability 1/2 each in a four-unit
block. That valid generality is now disclosed. This correction does not alter
the saved blind mathematical reading or any theorem formula.

The architect's account cites an external precedence instruction. I did not
open that file or any of the external paths linked in its report. The
assessment above rests on the supplied primary statement, its separate
diagnostic note, and the explicit revised comparison.

## Changed labels and documentation

**T1 — refuted: accepted.** Its unchanged witness is a counterexample to the
audited reading that randomized-timing attribution requires an unchanging
untreated path. The untreated outcomes are 1, 4, 9, 16. Nevertheless, the
overlap-date HT estimate has expectation equal to effect 2, and the separate
sharp-null path admits the claimed valid randomization test. The two outcome
schedules remain distinct. All exposure probabilities, estimate values,
variance, ranks, calibration equalities and validity inequalities in the
canonical counterexample are present. The new opening docstring identifies
the false printed reading rather than purporting to prove it.

**T4 — refuted: accepted.** The unchanged witness uses the article's independent
parent assignment, with common probability 1/2, positive cluster sizes,
fixed bounded individual outcomes and effect 1/4. For every empty-arm
extension, its error probability at tolerance 1/8 tends to 1 and fails to
tend to 0 as the cluster count grows. Thus it refutes cluster-count-only
consistency. The complete half-allocation results remain separately stated
and are not substituted for the independent-design counterexample. All
canonical finite formulas, conditional mean, limits, cluster-share facts,
and six-cluster checks remain present.

**T8 — restricted: accepted.** Its formula still requires fixed interior
counts on every assignment and true unit marginals m_b/N_b. It concludes
pointwise equality with actual observed block means and unbiasedness of both
statistics, with population-share weights. Its revised scope description
states the added hypotheses and the omitted variable-count and
unequal-within-block-propensity cases, and now includes balanced nonuniform
laws and cross-block dependence. These are precisely its mathematical scope.

No other theorem or docstring changed mathematically. The remaining label
checks are:

| Target | Revised decision | Assessment |
| --- | --- | --- |
| T2 | whole | All corrected estimation, uniform sharp-null testing and actual before-after bias clauses remain. |
| T3 | omitted | Still justified: no new precise design-strength or robustness claim is supplied; the audited necessity reading is addressed by T1/T2. |
| T5 | restricted | Both-design consistency and the no-dominance equivalence remain; the appreciable-bias prose and the cross-referenced failure assertion are exactly the disclosed omissions. |
| T6 | restricted | The pointwise fixed-count/common-marginal branch remains; random-count laws, including conditional Bernoulli assignment, are explicitly excluded. |
| T7 | restricted | Only the general closed conditioning-probability equality is omitted; positivity, normalization, both conditional conclusions, arbitrary extensions and the witness facts remain. |

## Junk values, nonvacuity and verification

All six Defs parts and both Challenge files were reread against `reading.md`.
The declaration set remains seven theorems, with no theorem for T3. Comparing
the two records shows only the T1 and T4 decision changes and the T8
restriction-text change. The older review artifacts were not rewritten.

The refreshed definitions still give ordinary finite expectations and
probabilities. There are no improper integrals or unbounded limsups. The
maximum cluster share is an attained maximum on a nonempty finite set.
Strict overlap and a nonempty target set protect T1/T2's inverse probabilities
and effect averages; interior counts protect T6/T8's actual means and
inverse probabilities. Positive individual cluster sizes protect cluster
means and population shares. T7 retains positive conditioning mass and the
actual normalized conditional law. T4/T5 explicitly extend the estimator
on empty arms, so those values are not interpreted as observed means.
No equality to be proved appears as an antecedent.

Both following files compiled successfully against the refreshed Defs,
using only the permitted wrapper and at most two concurrent Lean processes:

```text
/home/ubuntu/sap/tools/sap-lean scratch/Check.lean
/home/ubuntu/sap/tools/sap-lean scratch/DeltaCheck.lean
```

The first file rechecks the earlier nonvacuity instances: nonempty timing
overlap, positive conditional event mass, simultaneous count/marginal
hypotheses, linked assignments across two nonempty blocks, a balanced
nonuniform four-unit law, and an entire sequence satisfying all T5
consistency hypotheses. The latter has unit cluster sizes, Y0=0, Y1=1,
B=1, p=1/2, η=1/4, and maximum share 1/(k+2)→0.

The new [DeltaCheck.lean](/home/ubuntu/sap/tasks/CHFID-P024-a/scratch/DeltaCheck.lean)
verifies the substance of T8's count restriction. A uniform assignment over
the six proper nonempty subsets of three units has marginal treatment
probability 1/2 for every unit and positive arm sizes on every assignment,
but no single treated count. With control outcomes zero and treatment
outcomes (1,0,0), the allocation treating only the first unit has actual
HT value 2/3 and observed block difference in means 1. All denominators are
positive. Thus a variable-count case admitted by the broad informal wording
can fail the pointwise identity even with common true marginals; its
exclusion is not merely a cosmetic restriction.

`python3 scratch/audit_checks.py` passed again, including the calendar
arithmetic, tied rank examples, exhaustive small dominant populations,
fixed-count unbiasedness cases, conditional cluster cases, and the canonical
16-allocation block example. Finite checks are supporting evidence, not
proofs of the general or limiting statements. No `lake` command was run;
no Solution, Bridge or Comparator source was inspected; and no supplied Lean
source was edited. `findings2.json` was parsed and its schema and one-to-one
coverage of all eight canonical targets were checked with Python.
