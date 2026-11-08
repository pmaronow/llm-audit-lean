# Revision 2 statement review

**14 targets: 5 `correct_whole`, 7 `correct_restricted`, 2 `not_faithful`.** The two new findings concern the attribution of a refutation in the T5 and T9 docstrings and decisions. Their mathematical propositions remain valid. The T6 scope problem is fixed.

| Verdict | Count |
| --- | ---: |
| `correct_whole` | 5 |
| `correct_restricted` | 7 |
| `not_faithful` | 2 |
| `restriction_inaccurate` | 0 |
| `vacuous` | 0 |
| `false` | 0 |
| `omission_ok` | 0 |
| `omission_questionable` | 0 |

Severity: none 12, minor 0, major 2. No targets are omitted.

The required findings schema has no `correct_refuted` value. Accepted refutations therefore retain `correct_whole` or `correct_restricted` according to their coverage of the canonical counterexample; the revised decision labels are assessed separately below.

## Earlier findings and the architect's response

The earlier [findings.json](findings.json) contained no adverse verdicts and all 14 `issues` lists were empty. There are consequently no earlier adverse items from this referee to classify as partly fixed or not fixed.

The architect is right about the **T6 issue raised by the other referee**. My [saved reading](reading.md) placed zero-diagonal and off-diagonal-separation assumptions before all the matrix conclusions, but my first report incorrectly called the restriction disclosure complete. I withdraw that assessment of the old disclosure. The revised statement and docstring fix this problem: separation now applies only to the HC0 specialization. This conclusion follows from the saved reading and the revised source; I did not follow the architect's links to the other referee's workspace or to the external formalization.

| Target | Earlier verdict | Delta disposition |
| --- | --- | --- |
| T1 | `correct_restricted` | Refutation label reviewed and accepted for count-based reference-law identification, with the existing restriction. |
| T2 | `correct_restricted` | No substantive change; earlier acceptance retained. |
| T3 | `correct_whole` | Refutation label reviewed and accepted for the specified interpolated-percentile level assertion. |
| T4 | `correct_restricted` | No substantive change; earlier acceptance retained. |
| T5 | `correct_whole` | Mathematical acceptance retained; **new refutation-attribution problem**. |
| T6 | `correct_restricted` | **Fixed:** the previously overlooked matrix-scope/disclosure gap is repaired. |
| T7 | `correct_restricted` | Refutation label accepted for the stated finite counting/probability reading; geometric omissions remain disclosed. |
| T8 | `correct_restricted` | No substantive change; earlier acceptance retained. |
| T9 | `correct_restricted` | Mathematical acceptance retained; **new refutation-attribution problem**. |
| T10 | `correct_restricted` | No substantive change; earlier acceptance retained. |
| T11 | `correct_whole` | No substantive change; earlier acceptance retained. |
| T12 | `correct_whole` | Refutation label reviewed and accepted for the printed-grid/nonzero-output incompatibility. |
| T13 | `correct_whole` | No substantive change; earlier acceptance retained. |
| T14 | `correct_whole` | No substantive change; earlier acceptance retained. |

The architect correctly describes the mathematical T6 repair and the retained limitations. Its blanket application of the opening “The printed claim is false” does not preserve the distinctions that the canonical T5 and T9 claims expressly require.

## New findings

### P008-T5 — `not_faithful`, major

The [new T5 docstring](/home/ubuntu/sap/tasks/CHFID-P008a-b/SAP/P008a/Challenge/Part1.lean:52) says the printed claim is false, and `record2.json` changes the decision to `refuted`. But the [canonical note](/home/ubuntu/sap/tasks/CHFID-P008a-b/claims.json:88) expressly distinguishes the outcome-range interpretation from the instruction as printed. It says the example does not refute the general instruction when the cutoff bounds dependence between node-level contributions.

The theorem proves that nodes at distance 2 have contribution covariance 1/4, even though each intervention's outcome effect range is 1. Consequently cutoff 1 fails to cover contribution dependence. This refutes **using the outcome effect range as a sufficient dependence cutoff**. It does not refute the printed instruction to choose a cutoff beyond which contribution dependence is absent: that premise is false at cutoff 1 in this example. Nor does the theorem establish coverage failure for the particular printed toy intervals.

**Fix:** restore `whole` for the full canonical counterexample content and remove the unsupported claim of literal printed falsity. A precise opening is:

> P008-T5. The outcome-range sufficiency reading is false: a cutoff equal to the range of outcome effects need not cover dependence between node-level linearization contributions. The two-node example and all its replicated pairs omit half the linearization variance at that cutoff. This does not refute the printed instruction to bound contribution dependence, or establish the coverage of the printed toy intervals.

The Lean proposition needs no change. The new finding concerns its asserted refutation target, not its variance calculation.

### P008-T9 — `not_faithful`, major

The [new T9 docstring](/home/ubuntu/sap/tasks/CHFID-P008a-b/SAP/P008a/Challenge/Part1.lean:100) says the printed claim is false and cites the article's p. 145 cutoff instruction. The [canonical note](/home/ubuntu/sap/tasks/CHFID-P008a-b/claims.json:148) expressly says this finding concerns the later archived package and that the article's sentence is correct as printed.

The theorem correctly demonstrates grid dependence in the supplied `cutoff + position` model: identical radius-1/5 data receive variances 1 and 1/2 on two grids. It also shows that this model's sixth toy-row variance is zero. The latter result rules out this model as the source of the printed positive-width row. It does not show that the article's physical-cutoff instruction is false or that its printed intervals were produced by the later code. Mentioning the archived computation does not make the unqualified first sentence accurate.

**Fix:** restore `restricted`, retain the existing omissions of coefficient/residual/weight vectors and masks, and replace the opening with:

> P008-T9. The later archived cutoff-plus-grid-position computation fails the physical-cutoff specification: identical spatial data at radius 1/5 have variances 1 and 1/2 on the two grids. Its sixth toy-row variance is zero, so the printed positive-width row cannot have come from this computation. This is not a refutation of the article's dependence-cutoff instruction, which is correct as printed.

The Lean proposition needs no change. The external code-to-formula transcription remains a supplied premise.

## Changed mathematics: T6

Relative to the saved reading, T6 is the only proposition whose mathematical scope changed. The underlying finite-law, spatial, estimator and example definitions retain their mathematical content. T1, T3, T5, T7, T9 and T12 have changed labels/openings, which were reviewed above and below.

In the [revised T6 first component](/home/ubuntu/sap/tasks/CHFID-P008a-b/SAP/P008a/Defs/Part6.lean:94), quantification is now:

* For every natural N, assignment z, real vector M, real array D and real cutoff c, assume c≥0 and both arm counts are at least one.
* Define X=(1,Z) and H=(XᵀX)⁻¹. The weighted-contrast identity, OLS weights, OLS/group-residual identity and sandwich-to-score-HAC identity hold under these assumptions alone.
* Only then quantify over the extra assumptions Dᵢᵢ=0 and Dᵢⱼ>c for i≠j, to conclude the three HC0 identities.

This restores the general representation in canonical T6(a). The [new restriction paragraph](/home/ubuntu/sap/tasks/CHFID-P008a-b/SAP/P008a/Challenge/Part1.lean:62) states this distinction accurately. The unchanged geometric assumptions and numerical omissions are also disclosed. T6 remains `correct_restricted`.

Compiled [scratch/Check2.lean](scratch/Check2.lean) with:

```text
/home/ubuntu/sap/tools/sap-lean scratch/Check2.lean
```

The final run exited successfully with an empty [diagnostic log](scratch/Check2.log). The file imports only Defs and independently verifies an example **outside the old separation hypothesis**:

* N=4, z=0011, M=(0,2,4,6), Dᵢⱼ=|2i−2j| and c=12/5.
* Both arms have size 2. The Gram determinant is 4 and H=[[1/2,−1/2],[−1/2,1]].
* D₀₁=2<c, so the old separation premise fails. The OLS residual is (−1,1,−1,1), scores are (1/2,−1/2,−1/2,1/2), and both the sandwich entry and score HAC equal 1/2.
* Nonzero-diagonal arrays also satisfy the general component's domain assumptions, as permitted by the revision.

Thus the enlarged domain is meaningful. Positive arm counts force full rank; no singular-inverse or zero-denominator convention is being used. The calculations involve finite real sums, with no integral or limiting operation introduced by this revision. The unchanged geometric conclusion still has positive finite circle mass, and its support condition makes the relevant integrand zero on the evaluated circle.

## Remaining label, scope and nonvacuity checks

| Revised decision | Targets | Assessment |
| --- | --- | --- |
| `whole` | T11, T13, T14 | All required canonical formal clauses are retained. T11's reconstruction of the unrounded value is explicitly separate from the required bounds; T13 states all exact grid properties; T14 states the defining mean identity, idempotence criterion and example. |
| `restricted` | T2, T4, T6, T8, T10 | Restrictions match the actual hypotheses and omissions. The only change is the correctly restored T6 representation scope. |
| `refuted` | T1 | The fixed labelled observation suffices to refute universal identification of the law from an observation and its count; the four-node examples retain both discrepancy directions. This does not certify a corrected Uganda p-value. |
| `refuted` | T3 | A true sharp null has rejection probability 1/3>1/20 under the specified type-7 rule with all six assignments enumerated. The setting, positive circle masses and nonempty arms are retained. |
| `refuted` | T7 | The companion four-radius sum −4 cannot be a probability difference, so the arithmetic probability interpretation fails. This accepts the labelled counting content under the canonical note's express permission to check items 4–7 from the counts; the docstring still discloses the absence of a certified planar realization. |
| `refuted` | T12 | The printed grid selects no radius in the stated window. All sums and finite type-7 percentiles are zero, contrary to the reported nonzero outputs from those commands. The empty selected radius set is the defect, while the permutation sample is nonempty. |
| `refuted` | T5, T9 | New attribution errors detailed above. |

All eight non-null revised restriction texts match the corresponding Challenge restriction paragraphs after normalization of whitespace and a hyphenated line wrap. Textual agreement was checked separately from semantic accuracy. The previous witnesses remain applicable to unchanged mathematics; each target's witness is retained or updated in [findings2.json](findings2.json). In particular, the fixed counterexamples have nonempty assignment spaces and meaningful finite means, T7's natural subtraction stays nonnegative, and the spatial statements retain their integrability and positive-mass guards. No new mathematical falsity or vacuous statement was found.

The original `reading.md`, `claim-stage.json`, `findings.json` and `REPORT.md` were preserved. No `lake` command was run, and at most one Lean process ran at a time. No source outside the permitted workspace and Mathlib paths was read during this delta review. Both JSON outputs parse with Python; `findings2.json` contains every canonical target exactly once and uses the original findings schema.
