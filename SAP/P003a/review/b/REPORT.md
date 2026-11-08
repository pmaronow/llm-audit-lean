# Referee report

18 targets audited: **6 correct whole, 11 correct restricted, 1 inaccurate restriction**. There are no findings of falsity, vacuity or questionable omission.

| Verdict | Count |
| --- | ---: |
| correct_whole | 6 |
| correct_restricted | 11 |
| restriction_inaccurate | 1 |
| not_faithful | 0 |
| vacuous | 0 |
| false | 0 |
| omission_ok | 0 |
| omission_questionable | 0 |

Severity: 17 none, 1 minor, 0 major.

## P003-T14 — inaccurate restriction, minor

The theorem is `SAP.P003a.T14`. The restriction in the [Challenge docstring](/home/ubuntu/sap/tasks/CHFID-P003a-b/SAP/P003a/Challenge/Part2.lean:9) and `record.json` says that the lattice-rescaling component, including coordinate correspondence, is retained with the additional finite-first-moment hypothesis. That does not fully describe the statement.

The [actual lattice component](/home/ubuntu/sap/tasks/CHFID-P003a-b/SAP/P003a/Defs/Part9.lean:17) starts with one function `g : ℤ → ℝ` and assumes `IsMass g`. Its conclusions are:

- `∑' j, g j = 1`, already a conjunct of [IsMass](/home/ubuntu/sap/tasks/CHFID-P003a-b/SAP/P003a/Defs/Part4.lean:36);
- `latticeMean k g = (∑' j, j*g j)/k`;
- the fixed printed-rescaling witness, expressed as the zero indicator of `2*j = 1/2`.

The physical-coordinate convention at [Defs/Part4.lean:6](/home/ubuntu/sap/tasks/CHFID-P003a-b/SAP/P003a/Defs/Part4.lean:6) and the definition of `latticeMean` correctly support the mean identity. However, there is no separately supplied lattice law `f`, construction `g(j)=f(j/k)`, or assertion that this construction gives the pmf of `kX`, as in canonical T14(iii). Normalization of the sole input is assumed rather than established by such a correspondence. The docstring should disclose that it uses this direct coordinate representation and omits an explicit law-transport assertion; merely disclosing a stronger moment hypothesis is incomplete.

Suggested replacement restriction, also supplied in `findings.json`:

> Restriction: Retain the impossibility of unrestricted decrease, the corrected SD examples, the fair mean and the fixed printed-rescaling witness. For the lattice component, represent masses directly by g(j) at physical coordinate j/k and assume IsMass g, including an absolutely summable first moment. Retain only the normalization already contained in this hypothesis and the identity latticeMean k g = (sum_j j*g(j))/k. Omit an explicit source lattice law f, the construction g(j)=f(j/k), and the assertion that this construction is the pmf of kX. Canonical normalization and coordinate correspondence require only a probability mass function.

This is a scope/disclosure finding, not a false-theorem finding. Taking `k=2`, `g=zeroMass` satisfies its hypotheses. `scratch/Check.lean` proves that this mass is normalized, has a finite first moment and is SD, directly from Defs; it also verifies that the displayed normalization follows immediately as `hg.2.2.1`.

## Record assessment

The six `whole` decisions are accurate: T29, T2, T3, T13, T10 and T23. The declared restrictions are accurate and complete for T1, T4, T5, T11, T12, T9, T15, T16, T17, T21 and T22. T14 is properly classified as restricted, but its restriction text is incomplete for the reason above. All record theorem mappings agree with the Challenge, and every restriction string agrees with its docstring. There are no omitted targets in this package. No step-2 classification was changed after opening the record.

The retained counterexamples refute their specified printed readings: T1 has actual legal coverage `297/380 < 391/500`; T4 supplies both wrong return and all-fuel nontermination on legal positive-endpoint search inputs, plus an executed balanced-experiment failure; T11 has a nonempty real rejecting set without a minimum; T9 uses a legal dependent common-Boolean law under the intended corrected SD definition.

## Audit evidence and limits

The blind mathematical reading was saved in `reading.md` before opening `claims.json`. The comparison was saved and parsed as `claim-stage.json` before opening `record.json`: 6 whole and 12 narrower. `findings.json` provides a nonvacuity instance and confidence for every target.

Only Defs are imported by [scratch/Check.lean](/home/ubuntu/sap/tasks/CHFID-P003a-b/scratch/Check.lean); no Challenge theorem or `sorry` is used. It compiles using the supplied `sap-lean` wrapper. The checks establish a positive balanced design and genuine missingness law, a nonempty finite-support rejection example, normalized SD input, the T1 critical intervals/tails/possibility contrast and both coverages, the T4 exact interval and executed return, and the T21 accepted set and interval. All Lean invocations were sequential; `lake` was not run. The final compiler output is in `scratch/lean-check.log`.

Independent rational enumeration in [scratch/audit.py](/home/ubuntu/sap/tasks/CHFID-P003a-b/scratch/audit.py), with results in [scratch/evidence.json](/home/ubuntu/sap/tasks/CHFID-P003a-b/scratch/evidence.json), checked:

- 379 uniform labeled-assignment laws against their aggregated binomial state weights, through n=5;
- 3,995 population/design/level exact coverage cases, through n=6;
- 2,584 completion membership/distinctness/count cases, and 2,580 balanced completion-inclusion cases, through n=6;
- all 987 qualifying balanced SD populations at even n=2 through 12;
- 24,570 arbitrary-decision search runs, covering all Boolean decision functions on domain lengths 1 through 12 at three domain translations;
- the exact numerical endpoint/coverage witnesses and a T2 coupling instance with d=1.

These finite checks supplement the mathematical examination of the universal statements; they are not proofs of those universal statements. Positive-arm hypotheses protect all probabilistic denominators; legal states and masks protect natural subtraction; `d>=1` protects search logarithms; finite or explicitly summable masses protect means; finite normalized positive support prohibits an empty index type. The nonempty finite accepted sets used for endpoints are guarded or supplied by the hypotheses/conclusions. No additional mathematical defect was identified in the retained statements.
