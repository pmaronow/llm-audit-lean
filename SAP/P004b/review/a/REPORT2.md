# P004b delta statement review

The earlier finding is **fixed**. No outstanding or new statement issue
was found. All 15 targets are represented in `findings2.json`.

| Verdict | Count |
|---|---:|
| correct_whole | 1 |
| correct_restricted | 14 |
| restriction_inaccurate | 0 |
| not_faithful | 0 |
| vacuous | 0 |
| false | 0 |
| omission_ok | 0 |
| omission_questionable | 0 |

All 15 severities are `none`. Earlier findings: 1 fixed, 0 partly fixed,
0 not fixed. There are no remaining adverse items to list.

## Earlier finding

**P004-T27 — fixed.** The revised
[Challenge restriction](/home/ubuntu/sap/tasks/CHFID-P004b-a/SAP/P004b/Challenge/Part1.lean:75)
now explicitly says “NED only at the analyzed distance d=1” and omits
“W1's additional NED assertion for every other distance d.” The
corresponding restriction in
[record2.json](/home/ubuntu/sap/tasks/CHFID-P004b-a/record2.json) matches
exactly. This accurately describes the retained
[NED conjunct](/home/ubuntu/sap/tasks/CHFID-P004b-a/SAP/P004b/Defs/Part7.lean:16).
The omission remains intentional and is fully disclosed; no mathematical
clause needed to be added to fix this finding.

## Changes and labels

I compared the current definitions and all 15 Challenge theorem types
with the saved mathematical reading in `reading.md`. I found no change
to the mathematical objects, hypotheses, quantifier order, guards or
conclusions. The theorem names and their statement-definition references
also agree. The revised descriptions concern T26 and T27; the record
comparison confirms that only their `restriction` fields changed.

| Target | Revised description | Assessment |
|---|---|---|
| T26 | Identifies uniform quadratic spacing as canonical and the metric setup as inherited; separately identifies the explicit interior probability and all-sample-size validity and bandwidth assumptions. | Accurate. The corrected canonical T26 statement itself gives the uniform `C_b(1+s^2)` bound, and standing assumption S8 supplies the metric setup. The omitted corollaries, auxiliary-radius assertion and remark remain disclosed. |
| T27 | Qualifies NED as distance 1 only and explicitly drops the other-distance W1 assertion. | Accurate; fixes the earlier finding. The remaining omissions and retained valid-interval facts match the saved reading. |

The revised T26 wording also resolves the two T26 concerns attributed
to the other referee in `architect-report.md`. Its account of my T27
finding and the chosen disclosure repair agrees with the actual files.

The `whole` label remains correct for **T17**. Its statement includes
the compact-node diameter cutoff and C3 implication, the point-node
specialization obtained by setting the diameter bound to zero, the
absence of a diameter-free cutoff, the polygon area/diameter count bound,
and the area-only crowding counterexample with unbounded counts.

The `restricted` label remains correct for **T16 and T18–T30**. Their
declared selections and omissions match their retained statements; T27
now includes the missing qualification. No target is labelled `refuted`
or `omitted` in `record2.json`. T16, T19 and T27 already have canonical
counterexample claims, so selecting disclosed parts of those claims
supports their `restricted` classification. This revision does not
claim to prove a positive assertion that the theorem instead refutes.

## Junk values and nonvacuity

The revised descriptions introduce no mathematical assumptions or
conventions. The previously audited safeguards remain in place:
positive finite region mass and integrability; interior propensities
and positive population size where needed; nonempty arms for matrix
identities; explicit empty-arm error modifications; finite inverse-CDF
set guards; and positive conditional-support cardinalities. Tail
suprema are finite maxima for positive sample sizes. No new use of
division by zero, singular matrix inversion, nonintegrable integrals,
unbounded real suprema or truncated subtraction was found.

For T26, the analytic sequence in
[verification.md](/home/ubuntu/sap/tasks/CHFID-P004b-a/verification.md)
still satisfies every hypothesis: singleton grid nodes with counting
measure, fixed alternating outcomes, `p=1/2`, analyzed distance zero,
the uniform kernel, bandwidth `1+N^(1/12)` and envelope zero. Its region
masses are one, distances form a metric, the quadratic count bound is
uniform, and every exterior-tail envelope is zero. Thus the new wording
does not conceal an inconsistent hypothesis set.

For T27, the explicit sparse construction is unchanged. On its balanced
event at `N>=10`, both arms are nonempty and the arm containing node zero
has size `q>=4`. Its variance is `y^2(q-1)/q^3>0`, where `y` is 1 or
1/4. The event has probability tending to one. The retained interval
equivalence therefore concerns defined intervals; its counterexample
facts do not depend on an undefined studentized statistic. NED at
distance 1 uses conditioning neighborhoods containing the node's own
assignment and hence has zero approximation error.

I reran the existing independent nonvacuity checks against the refreshed
Defs with `/home/ubuntu/sap/tools/sap-lean scratch/Check.lean`.
They passed with exit code zero and no diagnostics;
[check2.log](/home/ubuntu/sap/tasks/CHFID-P004b-a/scratch/check2.log) is
empty. They check interior probabilities, positive arms, finite
dependence neighborhoods, positive estimator variance, nonsingular
regression matrices and positive complete-randomization supports.
Only one Lean process ran at a time; no `lake` command was used.

All 14 revised restriction strings were checked for exact agreement
between Challenge docstrings and `record2.json`. The saved blind
reading and stage-2 comparison retain their original SHA-256 hashes.
`findings2.json` was parsed with Python, and its schema, unique target
coverage and counts were checked against all 15 canonical targets.
