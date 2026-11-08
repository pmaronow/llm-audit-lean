# P023 statement audit

Twelve targets reviewed: **7 correct_whole, 4 correct_restricted, 1 not_faithful**. Severity counts: **11 none, 0 minor, 1 major**. No target is omitted, and none was judged false or vacuous.

The blind reading was saved in `reading.md` before opening `claims.json`. The claim comparison was saved in `claim-stage.json` before opening `record.json`. Reading the record caused no changes to the step-2 verdicts.

## P023-T10 — SAP.P023.T10 — not_faithful, major

`PolynomialLocalizationRefutation` in `SAP/P023/Defs/Part4.lean:194` negates a universal statement ranging over **every natural degree J, including zero**. At degree zero the design has columns `(1,d)` and no vote-share control. The canonical claim concerns adequate vote-share controls, including the linear and degree-seven specifications. Negating the larger universal statement gives a weaker refutation that can succeed entirely outside that scope. The record calls this target `refuted`, with no restriction, and the docstring does not disclose the degree-zero gap.

This is an executable scope test. Set

* `n=3`, `J=0`, `k=1/2`;
* `x=(-1/4,1/4,3/4)`, `d=(0,1,1)`;
* `y=(0,0,0)`, `y'=(0,0,1)`.

The close set is `{0,1}`, Condition 1 holds, and `(1,d)` has full rank. The constant-half vector satisfies the hypothesis requiring strictly bounded fitted values. The outcomes agree on the close set, while the party coefficients are respectively `0` and `1/2`.

`scratch/DegreeZero.lean` imports only Defs and proves the **entire polynomial-refutation conjunct** `PolynomialLocalizationRefutation` from this degree-zero example. It compiles successfully; its printed axioms contain no `sorryAx`. Thus the issue does not depend on an imagined proof strategy or an inconsistent antecedent.

**Fix:** add `1 ≤ J →` inside the universal statement being negated, before its remaining hypotheses. Update the description to say “The universal localization assertion for positive-degree polynomial vote-share controls fails.” The existing T1 witness has J=1 and supplies a qualifying example for the strengthened assertion. The coarsened-localization conjunct is faithful and needs no change.

## Record and restriction review

The other eleven architect decisions are supported by the supplied statements. The four `restricted` entries accurately disclose their changes in both the record and theorem docstring:

| Target | Disclosed restriction verified |
| --- | --- |
| T3 | Drops the separate fixed-tolerance probability inequality; adds both positive close counts to the nonlocality component; adds the stated law, degree, bandwidth, and design-admissibility premises to shared consistency. |
| T4 | Adds the degree-one/degree-seven OLS and RD admissibility premises; compares measurable predictors having integrable squared error. |
| T5 | Compares measurable predictors having integrable squared error. |
| T8 | Adds RD admissibility and OLS admissibility for each fixed positive degree and uniformly for every growing schedule obeying the displayed eigenvalue rate; retains all displayed conclusions. |

These predicates assert avoidance of degenerate designs, not consistency of the estimators. Their hypotheses are jointly satisfiable. No target is declared omitted. The record's unused supporting rows do not correspond to additional omitted targets; the corresponding mathematical clauses are present or are construction helpers rather than separate requested conclusions.

## Validation and mathematical checks

* `scratch/Nonvacuity.lean` compiles with `/home/ubuntu/sap/tools/sap-lean`. It checks the six-election sign, bandwidth, rank and count hypotheses; a two-election coarsened example with empty nuisance bins; existence of the constant-half fitted vector; and positivity of every bin count actually used in demeaning. It imports no Challenge theorem.
* `scratch/DegreeZero.lean` compiles with the same wrapper and proves the T10 scope test without Challenge imports or admitted facts.
* `scratch/exact_checks.py` uses rational arithmetic to solve both finite normal-equation systems and recompute weights, ranks, perturbation values, RD values and bin labels. It also recomputes the uniform degree-one/degree-seven projection coefficients, residual variances, distant influence shares, sigmoid coefficients, and clustered piecewise-polynomial moments and coefficients. Results are in `scratch/exact_checks.json`.
* An 80-digit numerical computation independently gives degree-seven amplification `4.764200685725225086…`, within the displayed interval. This numerical check is not represented as a formal proof of the decimal enclosure.
* The sampling assumptions have explicit mathematical instances: uniform margins, bounded independent noise, IID product sampling, and `k_N=1/sqrt(N+1)`. Window masses give diverging expected counts. Atomlessness and growing sign counts give the fixed-degree guards. Under the growing-degree rate, `0<lambda_J≤1` implies `J_N=o(sqrt(N))`, which also gives full rank with probability tending to one for this instance. Full analytic probability proofs and the infinite continuous-witness construction were reviewed mathematically rather than independently formalized.
* All denominators used substantively are positive under the relevant premises or explicit witnesses. Demeaning evaluates means only at occupied bins. Compact support and the integrability guards prevent nonintegrable Bochner integrals from deciding risk comparisons. Approximation suprema and infima have nonempty, appropriately bounded sets; the eigenvalue infimum is over a nonempty finite-dimensional unit sphere. T6 expresses unbounded tails and a diverging subsequence explicitly, avoiding a real-valued unbounded `limsup`.

The JSON outputs were parsed and checked with Python, including unique coverage of all twelve target IDs and agreement between the findings and the counts above. No original Lean statement file was edited, no `lake` command was run, and at most one Lean process ran at a time.
