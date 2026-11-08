# Statement audit: P004b

15 targets reviewed. Counts:

| Verdict | Count |
|---|---:|
| correct_whole | 1 |
| correct_restricted | 13 |
| restriction_inaccurate | 1 |
| not_faithful | 0 |
| vacuous | 0 |
| false | 0 |
| omission_ok | 0 |
| omission_questionable | 0 |

Severity: 14 none, 1 minor, 0 major. Every target has a theorem; none is
recorded as omitted. No stage-2 relationship verdict was changed after
reading the record. The record's fourteen restriction strings exactly
match the corresponding Challenge docstrings.

## P004-T27 — restriction_inaccurate, minor

The declaration does not disclose one omitted W1 assertion. The canonical
W1 states NED at the analyzed distance 1 and also at every other distance
`d`, with the proposed coefficient `psi_d(s)=1_{s<=d}`. The actual
[statement](/home/ubuntu/sap/tasks/CHFID-P004b-a/SAP/P004b/Defs/Part7.lean:16) includes only
`NEDConditions sparsePopulation (1/2) 1`. Its
[restriction](/home/ubuntu/sap/tasks/CHFID-P004b-a/SAP/P004b/Challenge/Part1.lean:75), also copied into
`record.json`, says it retains the witness's NED properties and lists
omitted W2–W5 conclusions, but does not mention dropping the all-distance
part of W1.

This is a disclosure defect. The retained distance-1 counterexample facts
are meaningful and appear correct. On the balanced-count event the
theorem asserts positive variance and nonempty arms, so its guarded
inclusion equivalence does not obtain undercoverage from undefined
intervals. The event's probability tends to one.

Fix both declarations to say **“NED only at the analyzed distance d=1”**
and add **“Omits W1's additional NED assertion for every other distance
d.”** The full replacement restriction is in `findings.json`. No theorem
change is needed if this narrower scope is intended.

## Scope and verification

The blind mathematical reading was saved in `reading.md` before reading
`claims.json`. The per-theorem claim comparison was then saved in
`claim-stage.json` before reading `record.json`. The only whole target
is T17; all fourteen other statements retain narrower parts of their
compound canonical claims. Except for the T27 qualifier above, the
declarations adequately identify their retained scope and material
omissions. Intermediate proof-helper lists were distinguished from
conclusions explicitly included in the canonical statement.

The audit traced SAP definitions through the relevant Mathlib definitions
of point-to-set distance, Bochner integration, probability measures,
Gaussian distribution, independence, matrix inversion and little-o.
No retained statement was found to rely on empty index types, zero
propensity denominators, nonintegrable outcome integrals, unbounded real
suprema, or truncated natural subtraction. Empty-arm modifications and
invalid-interval success conventions are explicit restrictions where
used, rather than implicit interpretations of the paper's statistics.

`scratch/Check.lean` compiled successfully using
`/home/ubuntu/sap/tools/sap-lean scratch/Check.lean` with no diagnostics.
It imports only Defs and checks positive arms, interior propensities,
valid finite dependence neighborhoods, a positive linearized-estimator
variance, a nonsingular regression Gram matrix, and positive conditional
complete-randomization supports. The analytic sequence in
`verification.md` satisfies the spatial/NED assumptions and even the
coverage nondegeneracy condition with `N Var(L)>=3` eventually. The
independent-Rademacher construction there satisfies T20's full hypotheses.
These are nonvacuity checks, not claimed independent Lean proofs of the
fifteen target theorems. At most one Lean process ran at a time; no
`lake` command, web search, Solution or Comparator read was used.

Procedural deviation: at the start I opened the installed Lean workflow
skill instructions outside the permitted source paths. They contained
workflow guidance, not mathematical claims or architect decisions. This
did not expose `claims.json` or `record.json` before their required stages,
but the read exceeded the requested filesystem scope.
