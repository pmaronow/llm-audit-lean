# Revision 3 statement review

**14 targets: 5 `correct_whole`, 8 `correct_restricted`, 1 `restriction_inaccurate`.** Both earlier major attribution findings are fixed. One incomplete restriction disclosure remains, in T8, when the corrected prose is included in the canonical claim as instructed.

| Verdict | Count |
| --- | ---: |
| `correct_whole` | 5 |
| `correct_restricted` | 8 |
| `restriction_inaccurate` | 1 |
| `not_faithful` | 0 |
| `vacuous` | 0 |
| `false` | 0 |
| `omission_ok` | 0 |
| `omission_questionable` | 0 |

Severity: none 13, minor 0, major 1. There are no omitted targets. [findings3.json](findings3.json) contains every target exactly once and uses the original findings schema.

## Earlier findings

| Earlier item | Status | Evidence in the revision |
| --- | --- | --- |
| T5, round 2: outcome-range example wrongly attributed as falsifying the printed dependence-cutoff instruction | **Fixed** | The decision is now `whole`. The [docstring](SAP/P008a/Challenge/Part1.lean:51) identifies outcome-effect-range sufficiency as the refuted reading and expressly separates it from the printed contribution-dependence guidance and coverage of particular printed intervals. |
| T9, round 2: archived-code defect wrongly attributed as falsifying the article's printed cutoff instruction | **Fixed** | The decision is now `restricted`. The [docstring](SAP/P008a/Challenge/Part1.lean:103) identifies the transcribed archived computational model, excludes attribution of the printed intervals to it and retains the intermediate-vector/kernel omissions. |
| T6, round 1 disclosure gap acknowledged in my round-2 review | **Fixed; repair retained** | The [statement](SAP/P008a/Defs/Part6.lean:94) still places separation only inside the HC0 specialization. Its restriction paragraph distinguishes that specialization from the general matrix representation. |

There are no partly fixed or unfixed earlier adverse findings. Round 1 had no adverse issue lists from this referee; round 2 had exactly the two T5/T9 major findings above.

I also correct two earlier scope assessments under the clarified instruction. T7's geometric clauses remain part of the canonical statement regardless of the audit note: the current limited counting theorem is acceptable because those omissions are expressly disclosed, not because a note licenses removal of clauses. T11's actual 7.99649/8.00 correction is part of its statement: my earlier `correct_whole` verdict was too broad. The architect has now correctly labelled T11 `restricted` and disclosed that omission, together with the uncertified empirical percentiles. The original review files remain unchanged as the historical record.

## Governing claim and labels

This review uses each target's `statement`, `definitions_needed` and the standing assumptions. Neither `note` nor `finite_lemmas` adds or removes a clause. In particular, a section called “Formal content” does not erase the corrected assertions that precede it.

All former blanket printed-falsity openings have been removed. `record3.json` has five `whole` and nine `restricted` decisions, with no `refuted` decisions. This is appropriate for the relationship between these theorem propositions and their canonical assertions: the counterexample theorems affirm the canonical counterexamples rather than contradicting them. The interpretations addressed by T1, T3, T5 and T9 are now identified in their docstrings. No assertion of corrected empirical significance follows from these changes.

## Remaining finding: P008-T8

**Verdict: `restriction_inaccurate`; severity: major.** The mathematical theorem is valid. The disclosure of what it leaves out is incomplete.

The [canonical T8 statement](claims.json:131) opens with corrected prose identifying the window's lower and upper empirical permutation percentiles as −0.0304 and 0.0336, its observed sum as −0.0321, and the equally weighted mean interpretation after division by four. These are assertions in `statement`, not merely material in an audit note.

The [Lean proposition](SAP/P008a/Defs/Part7.lean:52) contains general risk/mixture identities, a general scaling theorem for sorted samples, and exact arithmetic on those constants. Its numerical component divides the three constants by four and compares the resulting observed number with the lower number. It specifies no empirical sample, statistic or assignment law that identifies the reported outputs. Proving that every appropriate sample's quantile rescales does not determine which sample or quantile the experiment actually has.

The [restriction paragraph](SAP/P008a/Challenge/Part1.lean:92) lists spatial assumptions, absent explicit extrema and order-statistic formulations, the unconstructed joint sampling space and the unproved planar companion example. It says that the three reported values divided by four are retained. It does **not** disclose that the corrected text's identification of those values as empirical outputs, and the resulting actual estimate, is omitted. This is the same distinction that the new T11 paragraph now discloses correctly. Textual agreement between the record and docstring does not make this missing limitation complete.

**Fix:** keep `restricted` and append the following to both its docstring and record restriction:

> Omits identification of −0.0321 as the actual observed sum and of −0.0304 and 0.0336 as the actual 0.025 and 0.975 permutation percentiles on the stated window and grid. These three reported numbers are treated only as numerical inputs: the theorem proves their division by four and ordering, without certifying the empirical outputs or identifying the actual equal-radius estimate with the normalized sampling target.

No change to the Lean proposition is required to accept this narrower, explicitly disclosed claim. This newly identified disclosure problem follows from the clarified scope rule; it is not a newly introduced mathematical error.

## Target-by-target delta and clause review

All current Defs and Challenge files were read and compared with [reading.md](reading.md). Relative to the original blind reading, T6 retains the previously reviewed scope enlargement; the other propositions retain their mathematical content. Revision 3 changes decisions, descriptions and restrictions, not the retained mathematical formulas. All nine non-null record restrictions match their current Challenge paragraphs after normalizing whitespace and line wrapping; they were also checked for semantic completeness.

| Target | Revision-3 assessment |
| --- | --- |
| T1 | `correct_restricted`: the fixed 121-node observation, swap, normalized supports and both four-node tail discrepancies remain. The missing arbitrary-observation/relabeling quantification is disclosed. The new description names reference-law identification as the reading addressed. |
| T2 | `correct_restricted`: finite-law/conditional calibration, Bernoulli-given-count uniformity and cumulative sharp-null imputation remain. Spatial assumptions, support restriction, weaker imputation conclusion and unformalized documentary/empirical conclusions are disclosed. |
| T3 | `correct_whole`: the complete specified rectangle counterexample, sharp null, circle means, six balanced assignments, both pairs of type-7 quantiles, rejection indices, probabilities and Bernoulli conditional interpretation are retained. The new `whole` decision affirms this canonical counterexample. |
| T4 | `correct_restricted`: complementation and the one-third lower bound for all linear functionals, rejection-set mass obstruction, exact calibration, IID sampling correction and displayed sum remain. The reconstructed values, actual 8.00 output and exact observed p-value are expressly omitted. |
| T5 | `correct_whole`: the pair and all positive replications retain the circles, local outcome rule, marginal means, AMR, scores, covariance/variance calculations, bounds, separation and two-assignment dependence. The asymptotic consequence is excluded by wording in `statement` itself, which expressly marks it not required of a formalization. The interpretation is now accurately named. |
| T6 | `correct_restricted`: the general matrix representation is restored, and separation guards only HC0. The additive covariance, variance decomposition, cutoff condition and geometric sufficient bound remain; geometric regularity and numerical omissions are disclosed. |
| T7 | `correct_restricted`: the Bernoulli counting models, risk probabilities, effects, estimates, normalized weighting and −4 obstruction remain. Planar centres, radii, point construction, circle/field counts and centre outcomes are omitted explicitly. The current docstring claims only these counting components, not an admissible certified planar counterexample. |
| T8 | `restriction_inaccurate`: the valid algebraic and spatial components remain, but the omitted empirical identifications in its corrected prose are not disclosed. See the finding above. |
| T9 | `correct_restricted`: the positive-mass spatial witness, identical data on two grids, scores, variances 1 and 1/2 and sixth-row incompatibility remain. Vector/mask omissions and the computational interpretation are accurately stated. The earlier attribution finding is fixed. |
| T10 | `correct_restricted`: physical-cutoff invariance, all-pairs zero identity, example variances and toy HC0/archived comparisons remain. The strict-positivity characterization is expressly omitted. |
| T11 | `correct_restricted`: all exact five/eight-number sums and rounding inequalities remain. The new paragraph accurately omits identification of the actual unrounded value, its 8.00 display and the kept empirical percentile outputs. |
| T12 | `correct_whole`: the empty selected grid, arbitrary zero sums, zero finite-sample quantiles, nonzero reported constants and next-grid-point check reproduce the complete canonical incompatibility. The new label affirms this counterexample assertion. |
| T13 | `correct_whole`: the 41-point grid, endpoint, spacing, exact four selected indices, sum identity and kilometre conversions retain the canonical exact-grid correction. |
| T14 | `correct_whole`: the defining mean identity, literal-product equality criterion and two-node numerical witness retain the corrected display claim. General real arrays express this definitional target without adding spatial assumptions. |

The architect's accounts of the T5/T9 fixes, T6 repair, T7 restriction and T11 relabelling are supported by these files. Its acceptance of T8 as fully disclosed needs the additional restriction above. Links to inaccessible external formalizations and other referees' workspaces were not followed, and reported Solution/Comparator success was not treated as evidence of statement fidelity.

## Nonvacuity and junk-value checks

No new empty index type, zero denominator, truncated subtraction, nonintegrable-integral use or limiting construction was introduced. The witnesses recorded per target in [findings3.json](findings3.json) remain valid for the retained mathematical statements:

* The fixed assignment supports are nonempty, and all fixed Hájek examples have both arms. The spatial conditional-law example has event probability 1/2, with both arm counts one.
* The rectangle and bandwidth examples have unit positive mass on every evaluated circle and finite atomic integrals. General spatial statements retain the relevant integrability and positive finite mass assumptions. T6's geometric conclusion has an integrand that vanishes on the evaluated circle.
* T5 concerns linearization variance and does not evaluate the ratio estimator on one-arm assignments. T6's two-arm conditions make its binary regression nonsingular; the previously compiled example outside off-diagonal separation remains applicable.
* The risk model's natural thresholds are 79, 679, 400 or 1000, all within the 40000-point cells. T7 remains a nonempty indexed counting model, with no new asserted planar realization.
* Every quantile sample is nonempty; its level is in [0,1], and the scaling divisor is positive. Sortedness is explicit or follows from the stated concrete sample. T12's empty selected radius set is the asserted grid defect, not an empty permutation space.

Compiled [scratch/Check3.lean](scratch/Check3.lean) using `/home/ubuntu/sap/tools/sap-lean scratch/Check3.lean`. It imports only Defs and uses no Challenge theorem or admitted proposition. The final run exited successfully with an empty [log](scratch/Check3.log). It checks:

* A nonempty witness for all five T11 rounding hypotheses whose sum is 7.9935, below the 7.995 boundary. Thus the retained envelope alone cannot certify the actual 8.00 display.
* Two meaningful sorted six-entry samples whose type-7 0.025 quantiles are 0 and 1. A universal scaling identity is compatible with different empirical quantiles and cannot identify an unspecified experiment's output.
* The three reported-number divisions and ordering for positive divisor four.

These are checks of the relevant logical limitations, not counterexamples to the retained Lean propositions. The earlier independent finite-model calculations and spatial nonvacuity checks remain applicable because their definitions are unchanged. Only one Lean process was used in this round, and `lake` was not run.

The original blind reading and both earlier findings files were preserved. Python validation confirms that `findings3.json` parses, has exactly the original fields and allowed verdicts, covers all 14 canonical targets once, and agrees with the counts in this report.
