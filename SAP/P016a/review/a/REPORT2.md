Delta review: 11 targets, 10 theorem stubs. No mathematical statement,
supporting definition, theorem name, docstring restriction, or decision label
differs from the saved blind reading. `record2.json` is structurally identical
to `record.json`. The substantive review delta is the expanded T5 omission
rationale in `architect-report.md`.

| Verdict | Count |
| --- | ---: |
| correct_whole | 8 |
| correct_restricted | 2 |
| restriction_inaccurate | 0 |
| not_faithful | 0 |
| vacuous | 0 |
| false | 0 |
| omission_ok | 1 |
| omission_questionable | 0 |

All 11 severities are `none`. There are no remaining adverse findings.
Earlier adverse findings: 1 fixed, 0 partly fixed, 0 not fixed.

| Target | Earlier finding | Delta assessment |
| --- | --- | --- |
| T1 | correct_whole | Unchanged; both pairing witnesses, design enumerations, tables, tails and covariances remain complete. |
| T2 | correct_whole | Unchanged; all clauses (A)-(G), group-sum identity and attainment remain present. |
| T3 | correct_whole | Unchanged; both constructed exposure examples, exact table rationals, affine obstructions, regression minima and cutoff examples remain present. |
| T4 | correct_restricted | Unchanged; the bank-count and two-positive-SD hypotheses and omitted procedure identifications remain disclosed. |
| T5 | omission_questionable, minor | Fixed as a rationale finding: the report now explains the target-level fidelity gap. Omission is accepted; no T5 theorem was added. |
| T6 | correct_restricted | Unchanged; sample variance with divisor n-1 and the omitted application/procedure and empirical claims remain disclosed. |
| T7 | correct_whole | Unchanged; both mean tails, raw rejection probability one, and the full seventy-assignment KS comparison remain present. |
| T8 | correct_whole | Unchanged; adjustment, law equality, inclusive-tail calibration and the mean-shift equivalence remain present. |
| T9 | correct_whole | Unchanged; all three discrepancies, all RSS table entries, and the general constant-statistic law remain present. |
| T10 | correct_whole | Unchanged; coefficient characterization, general attainment, fitted-value uniqueness, KS supremum and adjacency identities remain present. |
| T11 | correct_whole | Unchanged; weak/strict KS witnesses, both RSS changes, the CDF table and all four monotonicity negations remain present. |

The T5 resolution concerns the omission rationale, rather than a corrected
mathematical statement. My first review correctly observed that rejecting a
named source row alone would not justify dropping the target. The
[expanded response](/home/ubuntu/sap/tasks/CHFID-P016a-a/architect-report.md:52)
now supplies an independent reason: no formal connection has been established
between the whole printed information/reference-distribution comparison and
the proposed existential at fixed empirical group margins.

On re-examination, my proposed theorem would establish the fixed-margin
interpretation suggested in `claims.json`'s note. I had treated that
interpretation as sufficient to identify the entire printed assertion. It is
not sufficient for that purpose: fixed group margins contain more information
than scalar KS, and the passage also discusses correlation in the reference
distribution and precision. The existing
[T2 example](/home/ubuntu/sap/tasks/CHFID-P016a-a/SAP/P016a/Defs/Part3.lean:82)
has u=(0,1,2,3), assignments 1010 and 1001, equal KS=1/2, and RSS=4 versus 5;
their group margins differ. Thus fixed-margin invariance does not establish
that RSS carries no information discarded by scalar KS. Neither this example
nor the fixed-margin lemma resolves the undefined information/precision
comparison in the printed prose. The common design-dependence identities
also do not supply that missing equivalence.

The fixed-margin negation remains valid and is already covered by T2. It
should not be presented as a refutation of the whole printed T5 without the
missing interpretation being justified. I therefore withdraw the earlier
recommendation to add it under T5 and accept omission of the underspecified
printed assertion. This changes only the omission assessment; none of the
ten saved claim-stage theorem verdicts changes. Acceptance rests on the
visible statement and this mathematical distinction, without relying on the
report's external instruction-precedence, source-row, or certification links.
Those links outside this workspace were not opened.

The labels remain accurate: eight `whole` targets cover every canonical
clause, including the constructed-counterexample claims; T4 and T6 are
`restricted` with their actual added hypotheses and omissions disclosed.
There are no `refuted` decisions and no newly introduced refutation to
audit. T5 remains omitted and is not asserted as true or refuted.

No changed statement introduces a new junk-value or nonvacuity problem,
because the mathematical statements and definitions are unchanged. I also
recompiled the saved `scratch/Check.lean` against the refreshed Defs with
`/home/ubuntu/sap/tools/sap-lean`; it exited successfully with no diagnostics
in `scratch/lean-check2.log`. This rechecks positive group sizes, the
inhabited balanced assignment type, finite-law nonemptiness, nonempty and
bounded-below least-squares ranges, bank support, positive exposure SD, and
nonempty T4/T6 model instances with nonzero coefficients. T4's witness is
the nonempty design `{complete4(1)}` with sample variance 1/48; it does not
assert positive variance at every bank assignment. The T6 witness uses
genuine raw-distance standardization on scores (0,1,2) and assignments 100
and 001.

The earlier 277 exact-arithmetic checks remain applicable to the unchanged
witnesses. A focused new exact check in `scratch/t5-delta-check.json`
independently confirms equal scalar KS, unequal RSS and unequal group
margins in the disputed T2 example. `scratch/delta-review2.json` records
the semantic comparison, unchanged decision counts and current source
fingerprints. This comparison uses `reading.md`; it does not claim a byte
comparison with historical source copies that were not saved. The original
review files are preserved. No `lake` command was run.
