# Delta statement review

All 17 targets are **correct_restricted**. The two revised disclosures are
complete, and there are no outstanding or new adverse findings.

| Verdict | Count |
| --- | ---: |
| correct_whole | 0 |
| correct_restricted | 17 |
| restriction_inaccurate | 0 |
| not_faithful | 0 |
| vacuous | 0 |
| false | 0 |
| omission_ok | 0 |
| omission_questionable | 0 |
| **Total** | **17** |

Severity: none 17, minor 0, major 0. There are no non-`correct_*` or
omission findings to list.

My round-one `findings.json` contained no adverse issues, so there are no
earlier requested repairs from this referee to classify as fixed, partly
fixed or not fixed. All 17 earlier verdicts remain applicable to the revised
package. I agree with the two disclosure gaps identified by the other
referee: my earlier assessment that those disclosures were complete missed
these additional premises. Both gaps are now **fixed**, as checked below.

| Targets | Comparison with round one | Current assessment |
| --- | --- | --- |
| P009-T4 | Disclosure expanded; mathematical statement unchanged | Other referee's disclosure finding fixed; correct_restricted |
| P009-T6 | Disclosure expanded; mathematical statement unchanged | Other referee's disclosure finding fixed; correct_restricted |
| P009-T1–T3, T5, T7–T17 | Readings and restriction disclosures unchanged | Earlier correct_restricted verdicts retained |

I reread all six Defs parts and both Challenge parts against `reading.md`.
No change in mathematical objects, hypotheses, quantifier order or
conclusions was found. The record comparison identifies exactly two changes:
the `restriction` fields for T4 and T6. Every theorem still asserts its
corresponding `TkStatement`; all 17 revised record restrictions agree with
the actual Challenge docstrings.

**T4 — fixed.** The standalone absolute moment-covariance bound still assumes
positive n and full `Regularity E k q s`, including assignment bounds and
potential-response moments at the same k. The canonical standalone component
requires only the observed moment bound with q at least 2a. The revised
docstring explicitly names the additional premises, while preserving the
existing finite-space, finite-order and omitted-chain disclosures. The
distinction is substantive: the fair one-unit identity experiment has fourth
observed moment 1/2, satisfying the canonical observed bound at k=1, but
cannot satisfy full Regularity at k=1. These facts are proved in
`scratch/DeltaCheck.lean`. Full Regularity at k=2,q=4,s=1 does hold for this
experiment, so the retained bound has nonvacuous hypotheses.

**T6 — fixed.** The finite construction still assumes full Regularity of the
original experiment, even though its outcomes are replaced. The revised
docstring explicitly discloses the additional original observed and
potential-response moment assumptions at the same k. A fair one-unit design
with original outcome constantly 3 satisfies the assignment bounds at k=2,
but its fourth moment is 81, exceeding 16; the construction's design domain
therefore exceeds the retained theorem's domain. This strictness check also
compiles. The disclosure continues to state the 0<L<=1 restriction and the
omission of the assembled sequence and sequence-level nonconvergence result.

For T6, the full retained hypotheses have the concrete instance n=1,
E the fair identity experiment, k=2,q=4,s=1,L=1. The compiled scratch check
proves M=1, constructed EATE=1/2, HT=z_0 and absolute error at least 1/2.
The general domain gives sqrt(L)>0 and 1<=M<=n. Thus neither extra moment
premises nor zero denominators make the construction vacuous. The limsup
clause separately has the instance a_t=1,L=1,c=1/2.

All labels in `record2.json` are `restricted`; none claims `whole`, `refuted`
or `omitted`. The retained counterexample targets still refute their printed
readings, with the omissions recorded in their restrictions. There is no
new label that overstates canonical clause coverage. The existing
nonvacuity witnesses for all other targets remain valid, including the
nonzero-B2 family for T12. Shared definitions and mathematical statements
are unchanged, so the earlier finite-probability, integrability, bounded
supremum, denominator and truncated-subtraction checks continue to apply.

Validation: `/home/ubuntu/sap/tools/sap-lean scratch/DeltaCheck.lean` succeeds
using only `SAP.P009a.Defs`; the log is
`scratch/delta-lean-check.log`. Python parsed `findings2.json`, checked its
schema fields, all 17 target IDs and unique theorem assignments, and verified
the record/docstring comparisons and verdict counts. The round-one artifacts
are preserved. No Solution or Comparator source was read and `lake` was not
run.
