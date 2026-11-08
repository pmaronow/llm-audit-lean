# Delta referee report

All three earlier findings are **fixed**. No new statement, scope, label, junk-value, or nonvacuity issue was found.

| Verdict | Count |
|---|---:|
| `correct_whole` | 10 |
| `correct_restricted` | 3 |
| `restriction_inaccurate` | 0 |
| `not_faithful` | 0 |
| `vacuous` | 0 |
| `false` | 0 |
| `omission_ok` | 0 |
| `omission_questionable` | 0 |

Severity: 13 none, 0 minor, 0 major. Earlier findings: 3 fixed, 0 partly fixed, 0 not fixed. New issues: 0.

The same verdict schema is retained: `correct_whole` includes the two complete and correct declared refutations, T19 and T20. The revised record itself has 8 `whole`, 3 `restricted`, 2 `refuted`, and 0 `omitted` decisions.

## Earlier findings

| Target | Status | Verified repair |
|---|---|---|
| P005-T25 | Fixed | [The docstring](/home/ubuntu/sap/tasks/CHFID-P005b-b/SAP/P005b/Challenge/Part1.lean:63) identifies positive dimension as canonical, and [record2.json](/home/ubuntu/sap/tasks/CHFID-P005b-b/record2.json:189) changes the decision to `whole` with a null restriction. The unchanged theorem covers the complete stochastic expansion. |
| P005-T26 | Fixed | [The docstring](/home/ubuntu/sap/tasks/CHFID-P005b-b/SAP/P005b/Challenge/Part1.lean:69) and [record2.json](/home/ubuntu/sap/tasks/CHFID-P005b-b/record2.json:199) remove the alleged extra dimension assumption. Both disclose exactly the omitted rate without leverage decay and the omitted exact identification with term (*). The decision remains `restricted`. |
| P005-T27 | Fixed | [The docstring](/home/ubuntu/sap/tasks/CHFID-P005b-b/SAP/P005b/Challenge/Part1.lean:77) and [record2.json](/home/ubuntu/sap/tasks/CHFID-P005b-b/record2.json:209) remove the alleged extra dimension assumption and disclose exactly the omitted rate without leverage decay. The decision remains `restricted`. |

The canonical order-symbol paragraphs still explicitly require `1 <= d_n <= n`: [T25](/home/ubuntu/sap/tasks/CHFID-P005b-b/claims.json:177), [T26](/home/ubuntu/sap/tasks/CHFID-P005b-b/claims.json:193), and [T27](/home/ubuntu/sap/tasks/CHFID-P005b-b/claims.json:209). The revised descriptions now agree with that complete canonical reading. The architect’s account of these three repairs is accurate.

## Comparison with the blind reading and canonical claims

I re-read the revised Defs and Challenge files against the shared dictionary and every theorem section in [reading.md](/home/ubuntu/sap/tasks/CHFID-P005b-b/reading.md). No change in mathematical objects, definitions, quantifier order, hypotheses, conjunctions, or conclusions was identified. The changes relevant to this review are the three docstrings and their classification metadata; the theorem names and proposition types are retained.

| Target | Revised decision | Clause and scope check |
|---|---|---|
| T15 | `whole` | Both collected covariance coefficients, the treatment intermediate fraction, its simplification, and the combined assignmentwise expression are present with both arm sizes at least two. |
| T16 | `whole` | All corrected indicator calculations and finite sums, the coefficient identities, treated and mixed third moments, and complement relations remain present for fixed separately centered scalar arrays. |
| T17 | `whole` | All corrected mathematical parts (a)–(e) remain: centering, the matching-index Gram contraction, scalar simplification, leverage bound, and deterministic orders. The surrounding first quadratic-form variance inequality is explicitly outside this canonical target. |
| T18 | `whole` | The weighted normal equation, all three bracketed vectors, and the identification with the actual observed-residual term remain present, with the population average correctly inside the treated sum. |
| T19 | `refuted` | The negated universal proposition is precisely the printed uncentered expectation/variance conjunction. The refutation does not separately negate its true expectation clause. |
| T20 | `refuted` | Retains the valid exact decomposition and independently refutes the printed third-component signs and the literal logarithm-condition expansion. Both negations use the printed hypotheses. |
| T21 | `restricted` | Both main unbiasedness claims, inverse-free formula, bias decomposition, and inverse-component identification keep the full nonempty-arm domain. Exactly the disclosed proof-step clauses are guarded by both arm sizes at least two; no clause is omitted. |
| T22 | `whole` | Includes bias and corrected-ATE unbiasedness, inverse-free cancellation, both armwise expectations, and the separately quantified centered-covariate-only versions with their stated arm-size conditions. |
| T23 | `whole` | Includes the common-slope and bias decompositions, both component moments, covariance interpretation, and both Remark 1 vanishing implications. |
| T24 | `whole` | Includes both interacted slope decompositions, bias expression, separate first-component moments, and their difference. The false third-component identity is outside this isolated valid target. |
| T25 | `whole` | The unchanged universal sequence theorem gives the full O_p(sqrt(kappa*d/n)) remainder under d/n -> 0, using canonical positive dimension, the standing assumptions, and eventual pooled regularity. No canonical conclusion is omitted. |
| T26 | `restricted` | Retains the common-slope debiased little-o expansion under kappa -> 0. The only omissions are the unconditional O_p(sqrt(kappa/n)) bound and exact remainder identification with (*), both expressly disclosed. |
| T27 | `restricted` | Retains the arm-specific debiased little-o expansion under kappa -> 0. The only omitted conclusion is the O_p(sqrt(kappa/n)) bound without leverage decay, expressly disclosed. |

No target is omitted. Lists of unused supporting proof rows do not omit audited target clauses.

## Junk values and nonvacuity

The changed labels and docstrings introduce no mathematical domain changes. For T25–T27, every sufficiently large n is positive, both allocation sizes are positive, and the randomization design has binomial(n,m) > 0 assignments. The real supremum defining kappa is a finite maximum over a nonempty population. The relevant inverse matrices are nonsingular on every assignment eventually. Their square-root scales are legitimate: under eventual standardization and positive dimension, kappa >= d/n > 0, so sqrt(kappa*d/n) > 0; sqrt(1/n) > 0. Exceptional initial indices cannot establish the asymptotic conclusions. No integrals or limsup conventions enter.

A common nontrivial sequence instance for all three repaired targets is, for n >= 3,

```text
d_n = 1,  m_n = floor(n/2),
x_i = sqrt(12/(n^2-1)) * (i-(n-1)/2),   i=0,...,n-1,
yT_i = x_i^2,  yC_i = 0.
```

The covariates are centered, standardized, and distinct. One can take K=9 and allocation bounds 1/4 and 3/4. Both arms have at least two distinct values for n >= 4, so both arm matrices and the pooled matrix are nonsingular on every assignment. Also kappa_n = 3(n-1)/(n(n+1)) -> 0 and d_n/n -> 0. Thus all hypotheses of the retained expansions are jointly satisfiable with positive covariate dimension and nonzero outcomes. The sequence construction is a mathematical check, not a Lean proof.

The finite witnesses from [audit-evidence.md](/home/ubuntu/sap/tasks/CHFID-P005b-b/audit-evidence.md) still apply. In particular, n=6, d=1, m=2 and x=(-11,-5,-1,1,5,11)/7 give standardized covariates and positive arm and pooled matrices for all 15 allocations. T19’s 19-unit reciprocal-array example gives variance 2483/2807136 greater than the printed bound 1703/1994544. T20’s six-unit third-component expectation is 192/1715 versus the printed -192/1715; its separate positive-dimensional sequence counterexample to the logarithm condition remains valid. Neither refutation relies on empty designs, division by zero, or singular inverses.

## Validation

- Recompiled [scratch/Nonvacuity.lean](/home/ubuntu/sap/tasks/CHFID-P005b-b/scratch/Nonvacuity.lean) against the refreshed SAP definitions using the permitted sap-lean wrapper: exit 0, with only the existing tactic-style linter warning. The check certifies finite standardization, all-assignment arm and pooled regularity, the nonzero third moment, and the third-component sign witness.
- Re-ran [scratch/audit_checks.py](/home/ubuntu/sap/tasks/CHFID-P005b-b/scratch/audit_checks.py): all exact rational assertions passed, including singleton-arm pooled examples, finite cancellation and unbiasedness checks, and both finite refutation witnesses.
- Parsed [findings2.json](/home/ubuntu/sap/tasks/CHFID-P005b-b/findings2.json) with Python and checked its exact field schema, one-to-one coverage of the 13 canonical targets, theorem names, verdicts, severities, and consistency with record2.json.

This review concerns statements and disclosures. Solution, Bridge, and Comparator sources or certificates were not inspected or used as substitutes for the statement checks. The earlier reading and round-one outputs are preserved.
