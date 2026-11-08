Audited all 17 targets in `claims.json`. The record marks all 17 `restricted`; there are no omitted targets. Fifteen restrictions are accurate and disclosed. Two need a documentation correction. No false or vacuous statement was identified.

| Verdict | Count |
| --- | ---: |
| `correct_whole` | 0 |
| `correct_restricted` | 15 |
| `restriction_inaccurate` | 2 |
| `not_faithful` | 0 |
| `vacuous` | 0 |
| `false` | 0 |
| `omission_ok` | 0 |
| `omission_questionable` | 0 |

Severity: 15 none, 2 minor, 0 major.

The blind mathematical expansion was saved in [reading.md](reading.md) before `claims.json` was opened. [claim-stage.json](claim-stage.json) was saved before `record.json` was opened. All 17 step-2 classifications remain `narrower`; the record prompted no change of reading or claim-stage verdict. The two findings below concern incomplete disclosure of extra hypotheses, rather than the truth of the retained conclusions.

**P009-T4 — `SAP.P009a.T4`: `restriction_inaccurate`, minor.**

The standalone absolute covariance bound at [Defs/Part5.lean:146](SAP/P009a/Defs/Part5.lean#L146) assumes full `Regularity E k q s`. Its canonical condition is only Assumption 1B with q≥2a. Full regularity adds assignment bounds and potential-response moment bounds with the **same k**. The disclosure at [Challenge/Part1.lean:48](SAP/P009a/Challenge/Part1.lean#L48) says this bound is included but does not identify these added premises; `record.json` repeats that incomplete disclosure.

This is a strict restriction despite the paper’s standing regularity assumption: the fair one-unit identity experiment satisfies the observed fourth-moment bound with k=1, and satisfies full regularity with k=2, but it cannot satisfy the exported full-regularity premise with k=1. Changing k also changes the bound k^(2a). Both the canonical moment condition and the failure of the exported premise at k=1 were checked directly in Lean.

Fix the relevant disclosure sentence to: “The absolute pairwise moment bound for powers 1 and 2 is restricted to positive n and full `Regularity E k q s` at the same k: besides its canonical Assumption 1B with q≥2a, it also assumes Assumption 1A and Assumption 1C.” Preserve the existing disclosures about finite sample spaces, finite moment orders and omitted chain links. Alternatively, weaken this component’s hypotheses to k>0, the observed q-moment bound, a∈{1,2} and q≥2a.

**P009-T6 — `SAP.P009a.T6`: `restriction_inaccurate`, minor.**

The finite construction at [Defs/Part5.lean:170](SAP/P009a/Defs/Part5.lean#L170) requires full `Regularity E k q s` on the original experiment. The canonical `finite_lemmas` explicitly allow any design satisfying Assumption 1A. The original outcome moments do not enter the construction, which replaces the outcomes. The disclosure at [Challenge/Part1.lean:75](SAP/P009a/Challenge/Part1.lean#L75) identifies 0<L≤1 and the missing sequence assembly, but omits the added observed and potential-response moment premises; `record.json` has the same omission.

A fair one-unit experiment with original outcome constantly 3 has the required assignment bounds at k=2, but its fourth observed moment is 81>16. It therefore meets the canonical finite construction’s assignment condition and is excluded by the exported full-regularity premise at the same k. Both facts were checked directly in Lean. The exported hypotheses themselves also have ordinary instances, for example fair identity outcomes with k=2,q=4,s=1.

Append to the existing disclosure: “The finite construction also assumes full `Regularity E k q s` for the original experiment, rather than only the Assumption 1A assignment bounds needed by the canonical finite construction; the original observed and potential-response moment bounds at the same k are additional premises even though the outcomes are replaced.” Alternatively, replace that construction’s regularity hypothesis by k>0 and 1/k≤p_i≤1−1/k for every unit.

The remaining record decisions and docstrings accurately identify their retained content and their omissions or additional domain assumptions, including all-index positive variance in T8, all-index nonempty nondependent-pair sets in T10, eventual nonzero B2 in T12, and positive own-arm probabilities for the zero-B1 clause in T14. Counterexamples T1, T3, T5, T7, T9, T11, T13, T15 and T17 retain enough content to contradict the specified printed readings.

Verification used only Defs, Challenge, claims, then record, and the permitted Mathlib sources. Relevant interference and mixing definitions, including the explicit 0^0 convention, were cross-checked in the [paper’s arXiv text](https://arxiv.org/html/1711.06399v4#S5.SS3). The canonical staged claim text controls the journal-version comparison. No existing Solution or Comparator source was read.

[scratch/Check.lean](scratch/Check.lean) imports only the SAP Defs and compiles successfully with `/home/ubuntu/sap/tools/sap-lean`; its eight examples check a positive-size model and the strictness witnesses for the two findings. [scratch/finite_checks.py](scratch/finite_checks.py) passed all exact-rational finite checks, recorded in [scratch/finite-checks.json](scratch/finite-checks.json). These calculations check concrete instances; they do not replace a proof of the universal or asymptotic statements. Every target has a concrete nonvacuity explanation in `findings.json`, including a nonzero-B2 sequence for T12’s final implication.
