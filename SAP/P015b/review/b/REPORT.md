# Referee report

Audited 12 targets. Verdict counts:

| Verdict | Count |
|---|---:|
| correct_whole | 4 |
| correct_restricted | 8 |
| restriction_inaccurate | 0 |
| not_faithful | 0 |
| vacuous | 0 |
| false | 0 |
| omission_ok | 0 |
| omission_questionable | 0 |

Severity counts: none 12; minor 0; major 0. There are no adverse findings or omitted targets.

| Target | Verdict |
|---|---|
| P015-T9 | correct_whole |
| P015-T10 | correct_whole |
| P015-T20 | correct_whole |
| P015-T14 | correct_restricted |
| P015-T21 | correct_restricted |
| P015-T11 | correct_whole |
| P015-T15 | correct_restricted |
| P015-T22 | correct_restricted |
| P015-T23 | correct_restricted |
| P015-T24 | correct_restricted |
| P015-T18 | correct_restricted |
| P015-T17 | correct_restricted |

The blind readings were saved in `reading.md` before opening `claims.json`. The comparison was then saved in `claim-stage.json` before opening `record.json`. No step-2 classification was changed after reading the record.

T10 covers every mandatory finite obligation (i)–(iv). Its architect's “restricted” label is conservative: the accurately disclosed omissions concern the optional limit and surrounding causal/consistency discussion. I therefore retain the step-2 `whole` assessment of the canonical formal obligations. The other restrictions match the actual quantifiers and conclusions. T17 and T18 correctly assess false printed implications through concrete refutations, within their announced scope; their `correct_restricted` verdicts evaluate those certificates, not the false printed claims as affirmative theorems. Supporting proof lemmas listed in the brief are not credited as separately exported statements merely because the record says a proof uses them.

The strongest added condition is `EventuallyDefinedRegression`: there is a deterministic sample-size threshold after which every fixed sample Gram matrix is nonsingular almost surely. It is stronger than nonsingularity with probability tending to one, and excludes i.i.d. finite-support designs with a positive-probability constant-row sample at every size. This is a substantial but disclosed restriction. It is not vacuous: independent continuous uniform treatment and a continuous uniform control give full rank almost surely at every size at least three. Taking baseline outcome equal to the square of the control and effect equal to one plus the control gives a bounded, heterogeneous-effect instance of all regression premises. Nonvacuity details for every target appear in `findings.json`.

Verification used only the supplied source files, permitted Mathlib sources, and scratch files in this workspace. `scratch/Check.lean` imports only Defs and compiles successfully through the supplied `sap-lean` command, without `sorry`; it checks finite probability laws and nonempty full-rank examples. `scratch/audit_checks.py` passes independent exact rational checks of pooling and raw GLS, leverage and roundings, positivity examples, IPW moments, and the square-link score Jacobian. The Taylor diagnostic through degree 80 is explicitly a finite diagnostic; the all-degree assessment uses the canonical coefficient-ratio/pairing argument and the actual all-degree statement in the stub. The continuous-product nonvacuity construction and the square-link maximizer-branch argument were checked mathematically, not fully formalized in these scratch checks. No original formalization or Solution files were read, and no `lake` command or web search was used.
