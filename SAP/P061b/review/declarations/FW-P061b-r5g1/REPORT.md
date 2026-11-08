# Review of SAP.P061b.T12–T16

All five declarations are faithful, with severity none. Each covers its entire canonical claim. The five `whole` decisions in record.json are correct, and the docstrings accurately describe the statements. No correction is needed.

The blind reading, including every dependency in closure.json, was saved in reading.md before claims.json was opened. The claim comparison was then saved in claim-stage.json before record.json was opened. No claim-stage conclusion changed after reading the record.

| Declaration | Claim coverage | Verdict | Severity |
|---|---|---|---|
| SAP.P061b.T12 | Whole | faithful | none |
| SAP.P061b.T13 | Whole | faithful | none |
| SAP.P061b.T14 | Whole | faithful | none |
| SAP.P061b.T15 | Whole | faithful | none |
| SAP.P061b.T16 | Whole | faithful | none |

T12 covers common-fiber identification, the unit and average contrast formulas, independence from the design, and the complete Table 3 example (Defs/Part3.lean:9). Global stability applies to every feasible assignment, including zero-mass ones. The identity is asserted only for positive exposure cells.

T13 covers supported-cell identification, the implication from global to support stability, invariance of the observed joint law under off-support changes, a globally stable extension, and equality of the sets of possible observed laws (Defs/Part3.lean:36). The extension is chosen before the event predicate, so the theorem gives equality of whole laws. It does not merely match each event using a different outcome schedule.

T14 gives the two original AEPOs, all three AEEDs, support stability, and the precise off-support witness against global stability (Defs/Part3.lean:57). Its definitions match all rows in Tables 1–2. The canonical assertion does not request separate AEPO or stability results for the two alternate designs; their absence is therefore no omission or docstring defect.

T15 reproduces both binary outcome tables and the complete hidden-version schedule, including no interference when a unit's raw version is fixed (Defs/Part2.lean:35; Defs/Part3.lean:69). All six contrasts and all claimed stability properties are present. The binary exposure category correctly identifies raw versions 1 and 2 while keeping their outcomes distinct.

T16 proves both ordinary-expectation identities and finite absolute first moments, with no stability assumption (Defs/Part4.lean:10). Its exposure-restricted moments are exactly the allowed existence conditions for the conditional-cell means and are explicitly disclosed in the docstring. They add no finite-support, boundedness, independence, or substantive moment-growth requirement. Historical objections based on undefined expectations do not contradict the canonical assertion under the author's stated conditions; this theorem is correctly labelled whole.

The atomic design definition matches standing assumption S1, whose event space is the power set and whose probabilities are sums of atom masses. Countably infinite support remains allowed. For a fixed positive finite population, strict positivity at every unit is equivalent to Condition 4.1's common positive lower bound. The definitions use ordinary real sums and conditional-cell ratios. Positivity guards every relevant exposure denominator; positive population sizes guard averages. Summability follows from stability in T12–T13, finite assignment spaces in T14–T15, and explicit absolute moments in T16. None of the audited conclusions depends on division by zero or Mathlib's zero value for a nonsummable real tsum.

The scratch checks import Defs only and use no Challenge theorem or admitted proof. `/home/ubuntu/sap/tools/sap-lean scratch/ClosureTypes.lean` checks all 56 distinct closure declarations. `/home/ubuntu/sap/tools/sap-lean scratch/Check.lean` verifies nonvacuity and concrete conclusions for every target: a globally stable T12 example; a genuinely support-stable but globally unstable T13 example with an explicit extension and equality for all observed events; every T14 conjunct; every T15 table and stability conjunct; and a full-support unequal-probability T16 example that violates support stability. In that last example the mean expectation and AEPO both equal 11/15, while the contrast expectation and AEED both equal 3/20.

findings.json contains exactly one result per target with fingerprints copied from closure.json. Both output JSON files were parsed and their coverage checked with Python. No source declaration was modified.
