# P041-T13 omission review

**Verdict: omission_ok; severity: none.**

`claims.json` records `no_lean: true`, an empty `rows` list, and no coverage judgments for P041-T13. Thus there is no proved row available for a whole or restricted T13 statement. The task expressly permits omission in this case.

The reason in `record.json` accurately describes the canonical claim: its formalizable content states a random-order/adaptive-schedule implication equating the expected implemented contrast, expected planned contrast, and direct effect. This conclusion does not depend on the canonical claim's historical note or finite-lemma history.

The related statements in `SAP/P041/Defs/Part7.lean` and `Part8.lean`, exposed by T5 and T6 in `SAP/P041/Challenge/Part1.lean`, cover the scrutiny counterexample and the rank-and-own-treatment sufficient condition. They are separate targets, not credited rows for T13; merely restating either does not establish a qualifying restricted T13 statement. The obstacle is absent target-specific credit, as the recorded reason says, rather than an undefined estimand.

No correction is needed. No new proof was attempted, and no Lean compilation was needed because T13 has no credited declarations. The output fingerprint was copied from `closure.json`; `findings.json` was parsed and checked with Python.
