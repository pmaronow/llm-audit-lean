# P031 statement audit

11 targets: **9 correct_whole, 2 correct_restricted; no adverse findings**.
All 11 severities are `none`. There are no omissions.

| Verdict | Count |
| --- | ---: |
| correct_whole | 9 |
| correct_restricted | 2 |
| restriction_inaccurate | 0 |
| not_faithful | 0 |
| vacuous | 0 |
| false | 0 |
| omission_ok | 0 |
| omission_questionable | 0 |

The eight complete affirmative targets are T1–T4, T7–T9 and T11. T5 is an
accepted refutation and is counted under `correct_whole`, since the requested
verdict vocabulary has no separate correct-refutation value. The claim-stage
comparison still calls T5 `different`: a negation does not assert the positive
claim. That comparison was not changed after reading the record.

No target has a verdict outside `correct_*` or `omission_ok`, so there are no
adverse items requiring a correction.

## Record decisions and disclosed restrictions

**T5 — the refuted decision is justified.** The canonical statement itself says
normality is the only printed hypothesis and specifies that neither arm-growth
nor moment conditions are printed. The theorem supplies a growing sequence
with a genuine standardized Gaussian limit and failure of HR/HC2 relative
equivalence, contradicting a clause of that normality-only assertion. Refuting
one clause suffices to refute the universal conjunction. Its docstring names
the normality-only conjunction and explicitly disclaims a separate failure of
any coverage clause. This does not purport to refute the cited result with its
own assumptions, or a version adding growth of both arms. No clause is removed
on the strength of an audit-history note.

**T6 — restriction accurate and complete.** The canonical contrast assuring
Neyman/HC2 coverage is dropped and expressly identified in both the record and
the Challenge docstring. Both directions of OLS/CE error remain, on the proper
N-times-variance scale and with convergence in probability. A standardized-normal
undercoverage witness is also retained. The witnesses use positive scaled
true-variance limits, so the comparisons do not compare two zero limits.

**T10 — restriction accurate and complete.** Both the record and docstring
identify all omitted assertion clauses: the observed-vector, intercept,
estimated-effect and per-unit residual shift identities in (a); both exact
finite-row scaled-variance formulas and E[r²]=3/(N−1) in (b); and all the
28-assignment numerical calculations in (c). All three explicit families,
their moment identities, deterministic scaled limits, probability and ratio
limits, and universal first-moment/variance shift identities remain. The
record's exclusion of an additional CE limit removes no canonical clause.
The target is correctly recorded as a restricted counterexample package,
not as a refutation of its own affirmative canonical counterexample.

**T11 — whole.** The deterministic limits, bias formula, effect-variance limit,
conditional probability and positive-denominator ratio limits, bounded-outcome
sufficiency and exact shifts are all present. The definition and Challenge
docstring expressly identify sample second-moment consistency as consistency of
both centered arm sample variances. This is the moment consistency used by the
OLS formula; consistency of the final variance estimate is not assumed.

## Verification and limits of the audit

The blind reading was saved in [reading.md](reading.md) before either JSON input
was opened. [claim-stage.json](claim-stage.json) was saved before `record.json`
was opened. No stage-two reading or comparison was revised on reading the
record. Decisions use the canonical statements, definitions and standing
assumptions; `note` and `finite_lemmas` were not treated as assertion clauses.
The [published paper](https://www.sciencedirect.com/science/article/pii/S0167715211003452)
was consulted as a cross-check; the supplied canonical claims govern the audit.

Both commands completed successfully:

```text
/home/ubuntu/sap/tools/sap-lean scratch/Check.lean
/home/ubuntu/sap/tools/sap-lean scratch/CheckLimits.lean
```

These import only Defs and contain no `sorry`. They check finite admissibility,
nonempty randomization spaces for every encoded population, genuine growing
families, and satisfiable limit hypotheses. No Challenge stub, Solution proof
or architect proof was used to establish those checks. `lake` was never run.

[Exact rational enumeration](scratch/audit_checks.py) independently passed for
862 assignments, including heterogeneous seven-unit populations and the three
sign families at N=8 and N=12. It checked the finite estimator chains, exact
randomization and expectation identities, imputed moments and shift invariance.
The results are in [exact-results.json](scratch/exact-results.json).
[Supplemental mathematical evidence](scratch/mathematical-evidence.md) gives the
normality-only counterexample, the hypergeometric witnesses, and the moment
arguments for the limit statements. The general limit arguments were assessed
mathematically, not reproved in scratch Lean.

There is no empty sample space, division-by-zero convention, truncated
subtraction, invalid square root, unbounded limsup or nonintegrable integral
doing substantive work. The encoded arm sizes force all relevant finite
divisors positive. All probabilities are finite uniform probabilities. The
normal CDF is Mathlib's actual Gaussian CDF. The ratio limits have eventually
positive reference variance. No hypothesis assumes the theorem's conclusion.
