# Referee report

All 13 targets were audited. I found no false or vacuous Challenge statement. Three restriction disclosures conflict with an explicit positive-dimension requirement in the supplied canonical definitions; these are minor documentation issues.

| Verdict | Count |
|---|---:|
| `correct_whole` | 9 |
| `correct_restricted` | 1 |
| `restriction_inaccurate` | 3 |
| `not_faithful` | 0 |
| `vacuous` | 0 |
| `false` | 0 |
| `omission_ok` | 0 |
| `omission_questionable` | 0 |

Severity counts: none 10; minor 3; major 0.

`correct_whole` includes the two correctly declared refutations, T19 and T20. Their saved claim-stage comparisons remain `different` because they refute, rather than affirm, the positive printed assertions. No step-2 verdict was changed after reading `record.json`. No target is declared omitted; unused supporting proof rows are not omitted target claims.

The blind reading is in [reading.md](reading.md); the frozen canonical comparisons are in [claim-stage.json](claim-stage.json). [audit-evidence.md](audit-evidence.md) gives nonvacuity constructions and both refutations. The finite positive-dimensional standardization, all-assignment regularity, third-component expectation, and nonzero third-moment example compile in [scratch/Nonvacuity.lean](scratch/Nonvacuity.lean). Independent exact rational enumerations passed in [scratch/audit_checks.py](scratch/audit_checks.py). Infinite sequence witnesses were checked mathematically, not formalized in Lean. No Solution or Comparator files were inspected.

## P005-T25 — restriction_inaccurate (minor)

At [Challenge/Part1.lean:63](/home/ubuntu/sap/tasks/CHFID-P005b-b/SAP/P005b/Challenge/Part1.lean:63), the docstring says positive dimension is added and the canonical claim imposes only `d_n<=n`; [record.json:192](/home/ubuntu/sap/tasks/CHFID-P005b-b/record.json:192) repeats this. However [claims.json:177](/home/ubuntu/sap/tasks/CHFID-P005b-b/claims.json:177), this target’s `definitions_needed` under “Reading of the order symbols,” explicitly specifies `1<=d_n<=n`. On that complete canonical reading, T25 retains the whole claim. The main statement and global Assumption 1 transcription mention just the upper bound, so the source itself needs a consistent domain description. This finding concerns that disclosure inconsistency, not the mathematical validity of the expansion.

Fix: replace the restriction sentence with “Uses positive covariate dimension, 1 <= d_n for every n >= 3, as specified in the canonical reading of the order symbols. No conclusion is omitted.” Set the record decision to `whole` with no restriction. Alternatively, if zero dimension is intended in the canonical domain, correct its order-symbol paragraph first; the present narrower-domain disclosure would then be accurate.

## P005-T26 — restriction_inaccurate (minor)

[Challenge/Part1.lean:69](/home/ubuntu/sap/tasks/CHFID-P005b-b/SAP/P005b/Challenge/Part1.lean:69) and [record.json:202](/home/ubuntu/sap/tasks/CHFID-P005b-b/record.json:202) describe `1<=d_n` as added, while [claims.json:193](/home/ubuntu/sap/tasks/CHFID-P005b-b/claims.json:193) explicitly includes it in the canonical order-symbol reading. The two actual omissions are accurately disclosed: `O_p(sqrt(kappa/n))` without leverage decay, and the exact identification of its remainder with `(*)` on p.1516.

Fix: say positive dimension matches the canonical order-symbol reading; retain `restricted` and list exactly those two omitted conclusions. The complete replacement text is in [findings.json](findings.json).

## P005-T27 — restriction_inaccurate (minor)

[Challenge/Part1.lean:76](/home/ubuntu/sap/tasks/CHFID-P005b-b/SAP/P005b/Challenge/Part1.lean:76) and [record.json:212](/home/ubuntu/sap/tasks/CHFID-P005b-b/record.json:212) likewise call positive dimension added, although [claims.json:209](/home/ubuntu/sap/tasks/CHFID-P005b-b/claims.json:209) already requires it. The omitted `O_p(sqrt(kappa/n))` bound without leverage decay is accurately disclosed.

Fix: say positive dimension matches the canonical order-symbol reading; retain `restricted` for the omitted unconditional order bound. The complete replacement text is in [findings.json](findings.json).

T21’s restriction is accurate: only the (11)/(12) proof-step expectations, equivalent third-bias formula, and coefficient collection require both arm sizes at least two; the main unbiasedness results keep nonempty arms. T15–T18 and T22–T24 cover their canonical targets. T19 negates the exact printed uncentered conjunction, and T20 both retains the valid exact part and refutes the printed sign identity and literal-logarithm expansion.
