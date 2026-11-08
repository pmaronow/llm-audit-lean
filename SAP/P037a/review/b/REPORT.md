Audit result: 15 targets; 8 correct whole, 4 correct restricted, 2 justified omissions, and 1 minor documentation defect. No false or vacuous theorem was found.

| Verdict | Count |
| --- | ---: |
| `correct_whole` | 8 |
| `correct_restricted` | 4 |
| `restriction_inaccurate` | 1 |
| `not_faithful` | 0 |
| `vacuous` | 0 |
| `false` | 0 |
| `omission_ok` | 2 |
| `omission_questionable` | 0 |

**P037-T1 — `restriction_inaccurate`, minor.** The mathematics matches canonical finite clauses (i)–(iv), and omission of the repeated-block OLS limit (v) is accurately disclosed. However, [the T1 docstring](/home/ubuntu/sap/tasks/CHFID-P037a-b/SAP/P037a/Challenge/Part1.lean:7) does not say which interpretation the counterexample refutes. The canonical statement limits it to the reading that randomization, an eligible-composition main effect and marginal average linearity alone identify the causal composition slope, and explicitly says the witness violates the preferred qualified response restriction. The task requires that scope in the theorem's own docstring. The architect's mathematical `restricted` decision is sound; its interpretative disclosure is incomplete.

Replace the first descriptive sentence of that docstring with:

> The fixed four-school hierarchical design is a counterexample to the reading that randomization, an eligible-composition main effect and marginal average linearity alone suffice to identify the causal composition slope: its causal composition slope is zero, whereas its expected-regression slope is nonzero. The witness violates the preferred qualified response restriction.

Keep the existing restriction paragraph. The full corrected descriptive text is also in `findings.json`. No Lean statement change is needed for this issue.

The blind expansion was saved in `reading.md` before opening `claims.json`; `claim-stage.json` was saved before opening `record.json`. No step-2 classification changed after the record was read. T1–T5 remain narrower than their canonical claims; T6–T13 cover their canonical claims. T2–T5 disclose their omissions accurately. T14 and T15 are omitted appropriately: the supplied mathematics does not settle the qualified empirical application or choose the actual significance status.

Verification: `/home/ubuntu/sap/tools/sap-lean scratch/Check.lean` completed successfully, without errors or warnings. It checks a nonempty four-school row sequence with uniform bounds and positive block variance, excludes designs on an empty source type, and checks nonempty coefficient/rounding premises. `python3 scratch/audit_checks.py` independently checks the exact 454-state supported law, all T1 expected matrices and coefficients, the general mixture coefficient by its linear basis, the T2 conditional innovation means and six regression comparisons, and supplementary interpolation values. Its rational results are saved in `scratch/arithmetic-results.json`. The asymptotic conclusions were assessed from their stated hypotheses and the standard bounded independent triangular-array and fitted-regression arguments; the scratch file is a nonvacuity check, not a replacement proof of those limits.

All output JSON was parsed and its target coverage and required fields checked with Python 3.
