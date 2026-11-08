# Revision 4 statement review

**14 targets: 5 `correct_whole`, 9 `correct_restricted`.** The T8 disclosure finding is fixed. There are no outstanding adverse findings, new statement problems or omitted targets.

| Verdict | Count |
| --- | ---: |
| `correct_whole` | 5 |
| `correct_restricted` | 9 |
| `restriction_inaccurate` | 0 |
| `not_faithful` | 0 |
| `vacuous` | 0 |
| `false` | 0 |
| `omission_ok` | 0 |
| `omission_questionable` | 0 |

Severity: none 14, minor 0, major 0. [findings4.json](findings4.json) uses the original findings schema and covers every canonical target exactly once.

## Disposition of earlier findings

| Earlier issue | Status | Current evidence |
| --- | --- | --- |
| Round 3, T8: omitted empirical identifications were not disclosed | **Fixed** | The [expanded docstring](SAP/P008a/Challenge/Part1.lean:92) and `record4.json` expressly separate the supplied rational constants from actual observed/permutation outputs. They also disclose the omitted empirical comparison, actual grid and unit weights, actual equal-radius estimate and normalized-target identification, and certification of divided permutation outputs. |
| Round 2, T5: outcome-range example attributed as falsifying the printed dependence-cutoff instruction | **Fixed; repair retained** | T5 remains `whole`; its docstring identifies the outcome-effect-range sufficiency reading and excludes a claim of coverage failure for the particular printed intervals. |
| Round 2, T9: archived-code defect attributed as falsifying the article's printed instruction | **Fixed; repair retained** | T9 remains `restricted`; its docstring identifies the transcribed computational model and does not attribute the printed intervals to it or falsify the article's dependence-cutoff instruction. |
| Earlier T6 scope/disclosure gap, acknowledged in my round-2 review | **Fixed; repair retained** | The general matrix representation is still outside the zero-diagonal/separation assumptions. Those assumptions guard only HC0, as the restriction says. |

There are no partly fixed or unfixed earlier adverse items. My round-3 corrections concerning T7's geometric scope and T11's empirical reconstruction remain applicable: their omissions are accepted because they are explicitly disclosed, not because an audit note removes clauses.

## Changed theorem: T8

The only new mathematical change relative to round 3 is the added unconditional real inequality

```lean
(-321 / 10000 : ℝ) < -19 / 625
```

in [T8Statement](SAP/P008a/Defs/Part7.lean:82). It is exactly −0.0321 < −0.0304, the unscaled numerical comparison in canonical T8(c). The three divisions by four and the scaled comparison remain. No other T8 conjunct, hypothesis, quantifier, definition or witness has been replaced by this arithmetic clause.

Relative to the original [blind reading](reading.md), T6 retains the previously reviewed general-representation scope repair, and T8 now additionally states this true comparison. The other theorem propositions retain their previously reviewed mathematical content. Current Defs and Challenge sources were read to check the changes; the architect's description was not used as a substitute for inspecting them.

The T8 restriction now accurately discloses all of the following:

* Euclidean circles, measurable field, positive finite circle masses and support-specific integrability for the spatial component.
* The absent explicit finite-extrema and separate order-statistic formulations, unconstructed joint sampling space and unproved planar realization of the companion counting model.
* The absence of an identification of the three constants with actual observed/permutation outputs and of the corresponding empirical quantile comparison.
* The absence of the actual application's grid and unit weights, its actual equal-radius mean estimate and identification with the normalized sampling target, and certification of the divided values as reconstructed permutation outputs.

Thus the arithmetic is retained while the omitted assertions in the canonical corrected prose are explicitly identified. The decision `restricted` is accurate; this theorem neither covers the whole empirical correction nor contradicts the canonical assertion. The architect's account of the T8 finding and repair is supported by the revised source and record.

## Labels and remaining targets

The governing claim is `statement` together with `definitions_needed` and the standing assumptions. Audit `note` and `finite_lemmas` fields add and remove no clauses. All nine restriction texts in `record4.json` match the Challenge paragraphs after whitespace normalization. They were checked for scope as well as textual agreement. No `refuted` decisions or unqualified printed-falsity openings remain.

| Targets | Verdict and retained scope |
| --- | --- |
| T3 | `correct_whole`: full prescribed rectangle percentile counterexample, including genuine positive-mass circle averages, sharp null, both test statistics, quantiles and rejection probabilities. |
| T5 | `correct_whole`: the pair and all positive replications, local outcomes, marginal means, scores, variance/covariance calculations, separation and bounded dependence. The asymptotic consequence is marked optional by the canonical statement itself. |
| T12 | `correct_whole`: complete printed-grid/output incompatibility for arbitrary estimates and nonempty finite quantile samples. |
| T13 | `correct_whole`: corrected grid size, endpoint, spacing, selected indices, sum and kilometre conversions. |
| T14 | `correct_whole`: defining mean identity, literal-product equality criterion and numerical witness. |
| T1 | `correct_restricted`: labelled observation and both reference-law discrepancies, with arbitrary-observation/relabeling omission disclosed. |
| T2 | `correct_restricted`: calibration, Bernoulli conditioning and cumulative imputation, with spatial/support and documentary/empirical limitations disclosed. |
| T4 | `correct_restricted`: general complement and inclusive-tail bounds, calibration, IID sampled correction and printed sum; reconstructed observations and exact observed p-value omitted explicitly. |
| T6 | `correct_restricted`: general matrix identities, HC0 specialization, additive covariance/variance and geometric support bound, with remaining geometric/numerical limitations disclosed. |
| T7 | `correct_restricted`: the two counting models and their probability arithmetic, with the required planar realization and centre outcomes explicitly omitted. |
| T8 | `correct_restricted`: valid normalization/scaling theorem and constant arithmetic, with the repaired empirical and other restrictions above. |
| T9 | `correct_restricted`: spatial grid-position discrepancy and toy-width incompatibility, with the computational reading and intermediate omissions stated accurately. |
| T10 | `correct_restricted`: cutoff invariance, all-pairs identity and toy/example values, with strict-positivity characterization omitted explicitly. |
| T11 | `correct_restricted`: exact table sums and rounding bounds, with actual 7.99649/8.00 output and empirical percentiles omitted explicitly. |

The positive counterexample propositions agree with their canonical assertions; they do not merit `refuted` labels merely because they invalidate an interpretation discussed in those assertions. No changed label introduces such an attribution problem in this revision.

## Truth, junk values and nonvacuity

Compiled [scratch/Check4.lean](scratch/Check4.lean) with the permitted command:

```text
/home/ubuntu/sap/tools/sap-lean scratch/Check4.lean
```

It independently proves the entire enlarged five-conjunct numerical block and positivity of its divisors 4, 625, 2500, 10000 and 40000. The final run exited successfully with an empty [diagnostic log](scratch/Check4.log). It imports only Defs, uses no Challenge theorem and contains no admitted proposition.

The added inequality has no hypotheses and uses ordinary real arithmetic with nonzero denominators. It cannot make a hypothesis set empty or rely on a totalized zero quotient. It introduces no integral, limit, subtraction on naturals or index type.

The unchanged T8 hypotheses remain jointly satisfiable. A two-node model with nodes (0,0) and (2,0), whole-plane field, radius 1, measure δ at (1,0), binary outcome identically one and uniform assignments has circle mass one and integrable overrides. The prior compiled witness in [scratch/Check.lean](scratch/Check.lean) establishes these properties. Four radius weights 1/4 and probabilities q₀=0, q₁=1 satisfy the mixture hypotheses. A sorted six-entry sample and positive divisor four satisfy the quantile/scaling hypotheses. The companion model is a nonempty finite counting model; its absent planar realization remains disclosed.

Other earlier witnesses remain applicable: balanced arms guard estimator denominators and binary-regression inversion, fixed spatial examples have positive finite circle masses, natural risk thresholds stay nonnegative, and the quantile samples are nonempty and appropriately sorted. T12's empty selected radius set is its explicit grid defect, not an empty permutation space. Per-target witnesses are retained in [findings4.json](findings4.json).

Only the changed arithmetic block required a new Lean check; no broader repeat of unchanged tests was needed. One Lean process ran in this round and `lake` was not run. External formalization/Comparator links in the architect's account were not followed or treated as evidence of statement fidelity.

## Output checks

Python parsed `findings4.json`, checked its exact field set and permitted verdict/severity values, verified unique coverage of all 14 canonical targets and agreement with the counts above. All issue lists are empty and fixes are null. The blind reading and all prior findings and reports were preserved.
