# Palomar statement audit: P015a

12 targets: **8 correct_whole, 2 correct_restricted, 1 restriction_inaccurate, 1 not_faithful**. Severity: **1 major, 1 minor, 10 none**. No false statements, vacuous targets, or omissions were found.

The blind reading was saved before claims were opened; `claim-stage.json` was saved before the record was opened. No step-2 reading or classification was changed after reading the record. The blind reading SHA256 is `5606da9da38d7419c61ebc96e0b9af07f0524f1ef6035f4e6ebd5c591469a3c0`.

## Record decisions

| Target | Architect decision | Referee verdict |
| --- | --- | --- |
| P015-T1 | whole | correct_whole |
| P015-T2 | whole | correct_whole |
| P015-T3 | whole | correct_whole |
| P015-T13 | whole | correct_whole |
| P015-T12 | restricted | restriction_inaccurate |
| P015-T8 | restricted | correct_restricted |
| P015-T5 | restricted | correct_restricted |
| P015-T6 | whole | not_faithful |
| P015-T7 | whole | correct_whole |
| P015-T16 | whole | correct_whole |
| P015-T4 | whole | correct_whole |
| P015-T19 | whole | correct_whole |

The restricted T5 decision is correct: its docstring explicitly withdraws the unsupported refutation of the printed necessary implication while retaining the valid odds-link witness. The restricted T8 decision is correct: its docstring discloses the supported normalized canonical-family hypotheses and the omitted general mean identification, OLS linearization, derived equations/cancellation criteria, and separate discrepancy examples. T12's omitted outside-domain dataset and lack of a separately asserted attained maximum are disclosed, but the scope of its guards is misstated as detailed below. The whole decisions for T1, T2, T3, T13, T7, T16, T4 and T19 are supported by the canonical formal contents. No target is recorded as omitted.

## P015-T6 — not_faithful, major

All enumerated finite probit witness facts are present and appear true. The problem is crediting this as a whole refutation of the printed ML substitution assertion.

Let R be the substituted residual equation and M(theta) mean that theta maximizes the actual likelihood. The printed estimating-equation assertion quoted in the canonical T5 text is **M(theta) implies R(theta)=0**. The T6 witness proves **R(theta0)=0 and not M(theta0)**. This disproves the converse, not the printed necessary implication. In a truth-table row with M false and R=0, the printed necessary implication is true.

The exact evidence is `SAP/P015a/Defs/Part2.lean:147` (zero substituted equation), `:148-151` (genuine nonzero score), and `:152-154` (the displayed parameter is not an optimum), with the additional well-definedness and derivative clauses at `Defs/Part3.lean:60-68`. None asserts an ML maximizer with a nonzero substituted equation. The T6 record says `whole`, and its challenge docstring at `Challenge/Part1.lean:69-72` supplies no restriction. T5 has precisely the needed disclosure at `Challenge/Part1.lean:63-66`; the different treatment of T6 is unjustified.

**Fix:** retain T6 as a restricted witness, set its record decision to `restricted`, and add: “Retains the specified 48-observation probit data, full rank, the well-defined upper quartile, zero substituted residual equation, positive genuine treatment score, likelihood directional derivatives, and nonmaximality at the displayed parameter. This proves failure of the converse that a substituted-equation root must be an ML estimate. It does not refute the printed necessary implication that every ML estimate solves the substituted equation; no actual ML maximizer with a nonzero substituted residual is asserted.” Whole refutation would require an actual admissible ML maximizer with nonzero substituted residual, or an equivalent explicit conclusion proving the necessary implication fails.

This finding does not call the numerical witness false. Nor does it assert that the necessary implication actually holds for the probit data. It concerns what the asserted witness establishes about that implication.

## P015-T12 — restriction_inaccurate, minor

The actual second Taylor clause has the logical form

`(nonempty_circle_image -> bounded_above_circle_image -> exact_radius_exists) AND uniform_error_bound AND geometric_bound_tends_to_zero`.

The antecedents at `SAP/P015a/Defs/Part3.lean:154-155` govern only the power-series existence and radius assertion ending at `:158`. They do not govern the error inequality at `:159-160` or its limiting bound at `:161`. The docstring at `SAP/P015a/Challenge/Part1.lean:38-39` and the record instead describe the circle error constant as “guarded by explicit nonemptiness and boundedness”. That mislocates the guards. The omitted outside-domain dataset is otherwise accurately disclosed.

**Fix:** replace that part of both the docstring and record with: “The circle error constant is defined as the real supremum of the circle norm image; attainment is not separately asserted. Only the power-series existence and exact-radius conjunct is conditional on nonemptiness and boundedness of that image. The uniform error inequality and the limit of its geometric bound are asserted under the radius hypotheses without these two additional antecedents.”

This is a minor documentation issue. The geometric hypotheses ensure a positive-radius compact circle that avoids the inverse-logit poles, so its norm image really is nonempty and bounded; there is no unbounded-supremum or empty-index loophole. For example, p=1/2, r=pi/4, rho=pi/2 satisfies the hypotheses. The Taylor statements themselves appear mathematically correct.

## Checks and limits

`/home/ubuntu/sap/tools/sap-lean scratch/Check.lean` completed with exit code 0 and no diagnostics. It imports only `SAP.P015a.Defs`, not the Challenge stubs. It checks finite probability vectors, positive rare-law normalizer, multivalued residual mean, the actual sample's positive mass and full Gram determinant, odds-link admissibility, square-link admissibility, logistic model premises, a normalized supported canonical family, nondegenerate fair-Bernoulli L2 and cell variance, an actual infinite independent uniform sampling model, and nonzero Taylor-domain parameters. At most one Lean process was active at any time; `lake` was not run.

`python3 scratch/exact_checks.py` passed. Its Fraction calculations independently check the rare-law moments and OLS coefficient, multivalued effective masses and effects, odds score, square-link moment matrices/Jacobian/derivative, and positive causal cell probabilities. The probit quantile/score and Decimal exponential calculations are numerical diagnostics, not formal real-analysis proofs. Analytic and measure-theoretic conclusions were also reviewed mathematically; the audit does not claim to reprove all twelve stubs. No Solution or external formalization source was inspected.

All per-target nonvacuity details are in `findings.json`. The JSON outputs were parsed and checked against all twelve target IDs with Python.
