# Palomar P041 statement audit

The audit covers all 13 targets and 12 theorem stubs. The blind reading was saved in `reading.md` before `claims.json` was opened; `claim-stage.json` was saved and parsed before `record.json` was opened. No step-2 reading-versus-claim classification was changed after reading the record. Findings concern statements and disclosures; the `sorry` Challenge bodies were not treated as proofs.

| Verdict | Count |
|---|---:|
| correct_whole | 5 |
| correct_restricted | 6 |
| restriction_inaccurate | 1 |
| not_faithful | 0 |
| vacuous | 0 |
| false | 0 |
| omission_ok | 0 |
| omission_questionable | 1 |
| **Total** | **13** |

Severity: 11 none, 2 minor, 0 major. No false or vacuous Lean proposition was found. The six accepted restrictions are T2, T7, T8, T9, T10 and T11; their retained content and declared scope agree. T1, T3, T4, T5 and T6 cover their canonical mathematical assertions.

## P041-T12: restriction_inaccurate, minor

`SAP/P041/Challenge/Part1.lean:69` says **“The printed claim is false.”** The canonical claim itself diagnoses the three directional percentages as false while preserving the symmetric arithmetic and directions. The theorem supports a restricted part of that diagnosis: P1, P3, and the negation of the conjunction of the directional rounding assertions. It does not contradict the canonical assertion.

The record correctly labels T12 `restricted`, and the subsequent restriction paragraph correctly lists the dropped exact directional values and individual negations. The opening sentence nevertheless violates the required distinction between refuting the canonical assertion and refuting a specified reading. Replace it with wording identifying the directional-relative-increase reading, and describe the result as a restricted verification of the canonical arithmetic diagnosis. `findings.json` supplies a complete replacement docstring. No theorem-type change is needed.

## P041-T13: omission_questionable, minor

`record.json:169` cites the absence of a named estimand or mathematical definition of bias. That is true of the raw assurance, but `claims.json:204` supplies explicit formalizable content: a universal reading about independent uniform random order and adaptive scheduling, comparing the expected implemented contrast, expected planned contrast and direct effect. It explicitly points to T5's counterexample and T6's sufficient condition.

There is therefore visible mathematical content for a restricted theorem, already checked elsewhere in this package. The absence of a separately credited T13 declaration explains a provenance limitation; it does not establish that the canonical reading lacks mathematical content. The `no_lean` metadata does not erase that paragraph. Add a restricted theorem crediting the appropriate reuse, with a docstring saying exactly which sufficient-condition reading it refutes and making no assertion that the actual estimates are biased. Alternatively, identify the missing credit as the unresolved provenance obstacle. Severity is minor because the concrete counterexample is already present in T5/T6 and no omitted empirical truth is being claimed.

## Verification and limits

`/home/ubuntu/sap/tools/sap-lean scratch/Check.lean` completed with exit code 0. It checks rounded-center witnesses, positive-hazard parameters, positivity of legitimate binomial masses, nonempty balanced sample spaces, an inhabited positive-domain percentage identity, simultaneous p-value premises, a full-rank positive-degrees-of-freedom intercept design, the citation Gram determinant, three failed directional roundings, and a positive-variance standard-error witness. Its printed HC1 definition confirms that the degrees-of-freedom subtraction is real subtraction.

`python3 scratch/numeric_check.py` passed 47 independent checks. Rational arithmetic verifies the percentages, contrasts, cell HC1 calculations, reciprocal enclosures, and all distinct survival slopes. Exact finite enumeration checks the scrutiny and rank/own-treatment formulas for m=1 through 8 and the independent four-rank boundary. Actual binary study designs realize the P/C/F Gram matrices with determinants 75000000, 500000 and 5700. Gaussian/log computations are floating-point sanity checks, not certified analytic enclosures; the normal measure and CDF definitions were followed into Mathlib. Additional direct calculations checked the tight central between-group p tolerance and all three central T11 tolerances.

No Solution or external formalization source was read, no `lake` command was run, and no paper-data extraction was inferred beyond the supplied standing assumptions. At most one Lean process ran at a time. `claim-stage.json` and `findings.json` were checked with Python's JSON parser.
