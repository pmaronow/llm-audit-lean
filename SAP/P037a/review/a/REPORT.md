# Palomar P037a statement audit

Audited 15 canonical targets, including 13 theorem stubs and 2 omissions.

| Verdict | Count |
| --- | ---: |
| correct_whole | 7 |
| correct_restricted | 4 |
| not_faithful | 2 |
| omission_ok | 2 |
| restriction_inaccurate | 0 |
| vacuous | 0 |
| false | 0 |
| omission_questionable | 0 |

Severity: 13 none, 2 minor, 0 major. Both findings concern the task's explicit docstring requirement for interpretation-specific refutations. No false or vacuous mathematical statement was found. Both fixes change documentation only.

## P037-T1 — not_faithful, minor

The statement is a correct restriction to finite clauses (i)–(iv), and the restriction paragraph correctly identifies omission of the repeated-block OLS limit. The architect's `restricted` decision is appropriate.

The docstring at [Challenge/Part1.lean:6](SAP/P037a/Challenge/Part1.lean#L6) does not state the reading being refuted. The canonical statement begins by identifying insufficiency of randomization, an eligible-composition main effect and marginal average linearity **alone**, and says that the witness violates the preferred qualified response restriction. The audit requires the docstring to say which interpretation a counterexample refutes. Merely describing a zero causal slope and a nonzero regression slope leaves that required qualification unstated.

Append:

> This counterexample refutes identification from randomization, an eligible-composition main-effect control, and linearity of the marginal average causal curve alone. The witness violates the preferred qualified response restriction; it does not refute the qualified response-model interpretation.

## P037-T12 — not_faithful, minor

The theorem covers the canonical interpolation properties, and the architect's `whole` decision is appropriate. Its docstring at [Challenge/Part1.lean:55](SAP/P037a/Challenge/Part1.lean#L55) does not identify the interpretation addressed by the examples in canonical clause (iv).

The printed condition says **no more than 64** for schools with fewer than 550 students. Counts 40 and 52 satisfy that inequality. They refute the reading that the parenthesis assigns **exactly 64** to every such school. The docstring should name that reading, as the task requires. This finding concerns source-scope disclosure; it does not treat the literal upper bound as false.

Append:

> The listed examples refute the reading that the upper-cap parenthesis assigns exactly 64 seed-eligible students to every school with fewer than 550 students. The literal upper bound of no more than 64 for those schools remains true under this rule.

## Order, record review and verification

`reading.md` was saved before opening `claims.json`. `claim-stage.json` was then saved and parsed before opening `record.json`. Its relations remain unchanged: five narrower statements (T1–T5), eight whole statements (T6–T13). The two final documentation findings do not revise those mathematical relations. The record's five restricted labels, eight whole labels and two omissions agree with those relations; the five mathematical restriction descriptions accurately identify the omitted clauses.

T2 openly omits the joint treatment/seed construction and conditional-moment derivation while retaining (R) as the canonical explicit premise. T3 makes no Gaussian quantile or tail assumption. T4 and T5 use the correct constant-density simplex measure and expressly omit the normalized-exponential construction. T14's qualified empirical interpretation and T15's undecided individual significance reports are justifiably omitted. The T15 pair's incompatibility already appears in T3.

The definitions were followed into Mathlib's finite product measures, pushforwards, real Bochner and interval integrals, exponential/Gaussian distributions, matrix-vector multiplication and total matrix inverse. Positive-denominator guards, finite event masses, integrability, zero-mass states and empty-index cases were checked. In particular, T11's singular-sample zero coefficient is exactly the canonical convention. No theorem imports a response conclusion, CLT or fitted-coefficient consistency as a premise.

`/home/ubuntu/sap/tools/sap-lean scratch/Nonvacuity.lean` completed successfully (exit 0; tactic-linter warnings only). It imports only `SAP.P037a.Defs` and verifies nonempty seed samples, composition orthogonality with positive centered variance, a bounded independent-block sequence with positive block variance, nonempty covariates with a positive definite Gram, and representative rounding/normalization/arithmetic instances. Its asymptotic example has two retained students per block, one covariate, exact positive probabilities, and variance growing linearly in the block count. The remaining simultaneous fitted-estimator assumptions hold in that example with exact probabilities and constant population moments.

`python3 scratch/exact_checks.py` independently enumerates all 454 positive-mass witness states using rational arithmetic. It reproduces the expected Gram, RHS and determinant, checks seven regression coefficient vectors and their uniqueness, and checks the mixture coefficient on 32 parameter combinations. It also checks the entire finite interpolation range, its rounded formula and cap threshold, plus the relevant rational interval endpoints. Outside the interpolation range the count function is constant; the universal no-tie assertion follows by parity. Results are saved in `scratch/exact-checks.json`.

The audit judges statements and their scope. It does not use a Challenge `sorry` as evidence of truth, inspect the Solution, or recertify Comparator proofs. JSON syntax and one-to-one coverage of the canonical targets were checked with Python 3.
