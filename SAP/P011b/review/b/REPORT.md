# Statement audit

14 targets: **9 correct_whole, 4 correct_restricted, 1 not_faithful**.
Severity: **13 none, 1 minor, 0 major**. No false, vacuous, inaccurate
declared-restriction, or omitted targets were found.

| Verdict | Count |
| --- | ---: |
| correct_whole | 9 |
| correct_restricted | 4 |
| restriction_inaccurate | 0 |
| not_faithful | 1 |
| vacuous | 0 |
| false | 0 |
| omission_ok | 0 |
| omission_questionable | 0 |

## P011-T18 / SAP.P011b.T18 — not_faithful, minor

The record declares the target `whole`, and the
[Challenge docstring](/home/ubuntu/sap/tasks/CHFID-P011b-b/SAP/P011b/Challenge/Part1.lean:30)
says the bracket-only repair disagrees with the true covariance. Canonical
part (d) requires evaluating that partially repaired moment expression.
The proposition instead states only
`(9/16 - (9/16 + 140-70) : ℝ) = -70` and
`cwTrueCovariance ≠ -70`; see
[T18Core](/home/ubuntu/sap/tasks/CHFID-P011b-b/SAP/P011b/Defs/Part7.lean:18).
There is no definition or equality connecting the bracket-only repaired
expression to those numbers. The
[existing printed expression](/home/ubuntu/sap/tasks/CHFID-P011b-b/SAP/P011b/Defs/Part4.lean:73)
retains the uncorrected outer factor 120.

The other four parts of the counterexample are represented correctly.
This is a missing certified identification, with no false value or
vacuity: the omitted expression really evaluates to −70.

To retain `whole`, define the repaired expression and assert its value
and disagreement with the actual covariance. Write F for the fourth
moment block, J for `printedBracket`, and E for expectation under
`constantWitness`. Moving only the opening bracket changes the expression
to

`F - (J + 119 * E[Y₀Y₁] * E[Y₂Y₃])`.

Adding 119 changes the first bracket coefficient from 1 to 120 while
retaining the missing coefficient in the fifth term. A complete
definition and a successful Lean proof that it equals −70 are in
[scratch/Check.lean](/home/ubuntu/sap/tasks/CHFID-P011b-b/scratch/Check.lean:58).
Alternatively mark the target restricted and explicitly disclose that
the bracket-only repaired moment expression is omitted. Exact suggested
text and the corrected assertion are in `findings.json`.

## Record assessment and verification

The declared restrictions for **T15, T16, T19 and T24** accurately and
completely describe the retained scope and omitted clauses. Each
restriction string also occurs verbatim in its Challenge docstring.
The other nine `whole` decisions are supported by the statement audit.
No target is declared omitted. No step-2 verdict changed after reading
the record.

The blind reading was saved in `reading.md` before `claims.json` was
opened; `claim-stage.json` was saved and parsed before `record.json` was
opened. The audit followed the SAP definitions to Mathlib's integrals,
covariance, independence, finite uniform measures, Gaussian cdf,
matrix inverse, L2 membership and limits. The supplied canonical text
and standing assumptions control the paper comparison; no inference
depends on the older arXiv version returned by external retrieval.

`/home/ubuntu/sap/tools/sap-lean scratch/Check.lean` completed successfully
with exit code 0. It imports only `SAP.P011b.Defs`, uses no Challenge
theorem or solution, and checks moment-domain satisfiability, feasible
and maximizing graphs, positive-rank design, exact helper values, and
the proposed missing bracket-only evaluation. No `lake` command was run;
Lean checks ran one process at a time.

`python3 scratch/exact_checks.py` completed successfully. It independently
enumerates the star block laws, checks their exact moments and
expectation coefficients, counts the strict sign events, enumerates the
three-vertex feasible problem, and evaluates the helper and covariance
witnesses. Results are in `scratch/exact-results.json`.
[scratch/nonvacuity.md](/home/ubuntu/sap/tasks/CHFID-P011b-b/scratch/nonvacuity.md)
gives instances for every theorem, including a single fair-sign family
and intercept design satisfying all of T16's outer and conditional
premises and T19's positive-variance and vanishing-spread premises.

Both JSON deliverables parse, have exactly one object per canonical
target, and agree on theorem names. Input Lean files and the supplied
claims and record were left unchanged.
