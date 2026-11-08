# Palomar statement audit: P003b

All 17 targets are represented: **6 correct whole claims or faithful whole-claim
refutations, 11 correct disclosed restrictions, and no adverse findings**.

## Counts

| Verdict | Count |
| --- | ---: |
| correct_whole | 6 |
| correct_restricted | 11 |
| restriction_inaccurate | 0 |
| not_faithful | 0 |
| vacuous | 0 |
| false | 0 |
| omission_ok | 0 |
| omission_questionable | 0 |

Severity counts: none 17; minor 0; major 0.

`correct_whole` includes T26 and T27: their statements correctly refute the
printed universal claims. They do not assert those false printed claims. The
other four whole targets are T24, T31, T33 and T34.

## Adverse findings

None. There are no non-`correct_*` findings or omissions requiring a repair.

## Order and record review

The blind expansion in [reading.md](reading.md) was saved before opening
claims.json. After reviewing all canonical claims and standing assumptions, I
saved [claim-stage.json](claim-stage.json), containing 6 whole and 11 narrower
readings, before opening record.json. A subsequent Defs-only Lean print clarified
that subtraction in the Wald denominator occurs in the rationals; that
clarification is recorded in reading.md and changes no verdict.

Every architect decision agrees with the saved step-2 assessment. The restriction
text in each of the 11 restricted record entries is also present in its Challenge
docstring; each accurately describes the retained conclusions and material
omissions. No step-2 classification was changed after reading the record.

| Target | Architect decision | Verdict |
| --- | --- | --- |
| P003-T24 | whole | correct_whole |
| P003-T25 | restricted | correct_restricted |
| P003-T8 | restricted | correct_restricted |
| P003-T19 | restricted | correct_restricted |
| P003-T20 | restricted | correct_restricted |
| P003-T26 | refuted | correct_whole |
| P003-T27 | refuted | correct_whole |
| P003-T30 | restricted | correct_restricted |
| P003-T31 | whole | correct_whole |
| P003-T33 | whole | correct_whole |
| P003-T7 | restricted | correct_restricted |
| P003-T32 | restricted | correct_restricted |
| P003-T34 | whole | correct_whole |
| P003-T6 | restricted | correct_restricted |
| P003-T35 | restricted | correct_restricted |
| P003-T36 | restricted | correct_restricted |
| P003-T18 | restricted | correct_restricted |

The restrictions distinguish the real critical-value enclosure from a certified
normal quantile (T8), composition counts from labeled-table correspondence (T19),
retained symbol identities from omitted feasibility conclusions and examples
(T20), and retained endpoints or probability conclusions from omitted witnesses
and separate proof assertions (T25/T30/T7/T32/T6/T35). T36 and T18 explicitly
limit their operation counts to the stipulated arithmetic/full-shuffle models.
The corrected searches and full j loop are already the intended procedures in
the corresponding canonical targets.

## Definitions and nonvacuity

The randomization law is the finite multivariate-hypergeometric law with the
correct binomial denominator. The integer tail comparison is precisely a scaled
centered Neyman deviation; acceptance includes ties. Possible tables enumerate
binary completions. The retained statements do not obtain their conclusions from
division by zero, truncated subtraction, nonintegrable functions, unbounded
limsup, or empty sampling types.

Finite accepted sets have genuine extrema when nonempty. Nonemptiness is assumed
exactly as qualified by the canonical unbalanced length target, follows from
balance in the balanced targets, and is expressly checked on every state in the
missing-data refutation. Consequently, the unbalanced refutation does not depend
on arbitrary empty-set endpoint values.

The Monte Carlo product spaces give independent batches. Both corrected endpoint
budgets together keep batch indices below the pool size, so modulo access does
not recycle randomness. The general procedure instead uses the required
correlated reuse with independent factorial seeds implementing exact Bernoulli
probabilities. No validity or coverage conclusion is assumed in a hypothesis.
The pair-indexed Big-O has the usual simultaneous product-order meaning, and its
exact-total/eventually-positive-arm families exist.

Every target has a concrete instance or nonvacuity explanation in
[findings.json](findings.json). Defs-only [scratch/Check.lean](scratch/Check.lean)
also verifies the critical-value enclosure, inhabited sampling spaces,
monotonicity hypotheses, a nonempty accepted set, and the joint asymptotic design
family. It proves the two-point printed-search failure for every fuel and
evaluation count. It compiled successfully with
`/home/ubuntu/sap/tools/sap-lean scratch/Check.lean`; the retained log has one
harmless unused-tactic linter warning and the requested definition print. No
Challenge theorem is used by these checks.

## Independent finite verification

[scratch/audit.py](scratch/audit.py) uses exact rational arithmetic and direct
labeled assignments as a reference. All assertions passed:

- 9,499 count-law, deviation-numerator and tail-probability comparisons against
  labeled treatment subsets for totals 2–6.
- 417 balanced observation/level cases checking estimate membership, lattice
  equality and both corrected exact endpoints for totals 2–12.
- 8,084 monotonicity comparisons, including impossible count vectors, for
  totals 4–10.
- 36 stratum-total pairs checking cardinalities, convolution and degree-six bounds.
- 1,218 exact one-step reuse-law checks for totals 2–8.
- Both exact Wald coverage fractions and both stated design medians, with exact
  squared comparisons at the critical-value enclosure boundaries.
- The missing-data refutation: 891 covered assignments out of 1,140, giving
  coverage 297/380 and shortfall 1/2375 below 1-alpha, with both extremal accepted
  sets nonempty on every state.
- All three adaptive trace witnesses, both exact probability inequalities E,
  and the exact rational aggregate lower bound F.
- A size-16 search/cost instance with 12,870 assignments and the five specified
  first-query candidates.

Full exact values are in [scratch/verification.json](scratch/verification.json);
[scratch/audit.log](scratch/audit.log) and
[scratch/lean-check.log](scratch/lean-check.log) retain outputs. These finite
checks support the statement audit and are not presented as universal proofs.
No Solution, Comparator, or author formalization was read; no web lookup or lake
invocation was used.

Both requested JSON audit files were parsed and checked with Python 3 for
required fields, allowed values, complete one-to-one target coverage and theorem
names.
