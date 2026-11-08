# P035 statement audit

Three targets were audited. There are no adverse findings.

| Verdict | Count |
|---|---:|
| correct_whole | 1 |
| correct_restricted | 1 |
| restriction_inaccurate | 0 |
| not_faithful | 0 |
| vacuous | 0 |
| false | 0 |
| omission_ok | 1 |
| omission_questionable | 0 |
| **Total** | **3** |

Severity counts: none 3; minor 0; major 0.

## Decisions

**P035-T1 — correct_whole.** The theorem states the complete specified counterexample: the six frequencies; denominator LCMs and thresholds; an independent uniform latent design; observational equality, including arbitrary real weights; calibration; zero versus positive campaign effects; the exact raw-enrollment mixture; and nonidentification of both the yearly and overall targets. Extra identities verify this construction. There are no theorem hypotheses, hidden empirical premises, or assumptions of the desired conclusion. All relevant denominators and design masses are positive, threshold subtraction agrees with integer subtraction, and the finite supports are nonempty. Restricting sums to those supports gives ordinary finite probability calculations even though the weight functions themselves are defined on all naturals.

**P035-T2 — correct_restricted.** The theorem covers the two mathematical campaign clauses of the correction. The Challenge docstring and architect's restriction accurately disclose all exclusions: the retained empirical estimate, the instruction to change the wording on p. 5/6, and a separate health-message mediator. The existential finite construction proves compatibility with full campaign enablement of the observed mean porch contrast. It does not decide an actual campaign effect. The additional absent-campaign equality of individual porch outcomes is satisfied by C and supports that compatibility claim.

**P035-T3 — omission_ok.** The target concerns an empirical attribution, and claims.json explicitly marks it `no_lean`. Observationally indistinguishable hypothetical models establish nonidentification; they cannot determine the truth or falsity of the attribution in the actual study. The record's reason for omission is accurate. The formal inference at issue is already addressed by T1 and T2. The distinction between the study's porch intervention, the proposed reinforcement explanation, and its categorical campaign wording is present in the [published paper](https://journals.plos.org/plosone/article?id=10.1371/journal.pone.0189693), Abstract, Introduction, Methods, and Results and conclusions.

## Audit order and evidence

1. Read only Defs and Challenge for the mathematical reading, following finite intervals, filters, cardinalities, sums and arithmetic into Mathlib. Saved `reading.md` before opening `claims.json`.
2. Compared each theorem with the canonical target and standing assumptions. Saved and JSON-validated `claim-stage.json` before opening `record.json`. The step-2 readings are `whole` for T1 and `narrower` for T2.
3. Read the record. Its `whole`, `restricted`, and `omitted` decisions agree with the independent assessment. No step-2 verdict was changed.

The independent check `scratch/Check.lean` imports only `SAP.P035.Defs`; it contains no `sorry` and uses no Challenge, Solution or Comparator theorem. Running `/home/ubuntu/sap/tools/sap-lean scratch/Check.lean` succeeded with exit code 0. It proves the complete T2Statement with U=D and V=C, as well as positive supports and design masses, the LCM identities, calibration, exact yearly effects, and nonidentification. It does not claim to reprove every conjunction of T1.

Separate exact calculations using Python's `fractions.Fraction` verified all six calibration ratios, all three reduced-denominator LCMs, threshold ordering and bounds, positive independent design weights and total mass 1, every yearly effect, and the overall C effect `83755728/5240292055`. These calculations use initial-segment cardinalities; they do not depend on enumerating a large latent population. Together with the explicit compiled witnesses, they rule out the empty-model and arithmetic-convention failure modes relevant here.

There are no items with verdict `restriction_inaccurate`, `not_faithful`, `vacuous`, `false`, or `omission_questionable`. No fixes are required.
