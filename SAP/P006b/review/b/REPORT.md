# P006b statement audit

| Verdict | Count |
|---|---:|
| correct_whole | 9 |
| correct_restricted | 5 |
| omission_ok | 1 |
| restriction_inaccurate | 0 |
| not_faithful | 0 |
| vacuous | 0 |
| false | 0 |
| omission_questionable | 0 |
| **Total targets** | **15** |

Severity counts: none 15; minor 0; major 0.

No target requires a correction under the requested verdict scheme.

## Decisions

Whole coverage is accepted for T16, T19–T24. T26 and T27 are accepted as faithful refutations of the joint printed universal assertions. Their negations do not assert independent failure of every conjunct; their docstrings accurately state that limitation. Both have finite, positive-mass counterexamples satisfying the printed assumptions.

Restricted coverage is accepted for T17, T18, T25, T29 and T30. Every restriction in `record.json` matches the theorem and is disclosed in its Challenge docstring:

* **T17:** finite selection algebra and the three-type example; the general conditional-outcome-mean connection and the marginal-versus-maximum comparison are omitted.
* **T18:** the exhibited maximizers, best-response reward, regret and numerical mismatch; the samplewise statements, general-policy formulas, uniqueness and general nonnegativity statement are omitted.
* **T25:** constant public covariate, deterministic outcomes, fair binary private type and zero estimator; the specified minimum parameter choices and general unequal-parameter perturbed regret formula are omitted. The existential lower bounds and the equal-parameter unique-response variant remain substantive.
* **T29:** the arbitrary-regret existential headline is covered; the family response characterization uses deterministic treated outcomes instead of every integrable outcome law with the specified means.
* **T30:** the explicit pair with sample sizes 1 and 2 witnesses both ranking failures; the general maximum identity and general sample-size condition are omitted.

**T28's omission is accepted on the visible evidence.** The record identifies a theorem about hypothetical numerical summaries without a connection to either actual fitted analysis. Such a theorem would not, by itself, prove or refute the two particular beneficiary means. This accepts the stated evidentiary reason for omission; it does not endorse the printed numerical claims. The [published paper, Table 1 on PDF page 9](https://proceedings.mlr.press/v238/wang24b/wang24b.pdf#page=9) provides the reported summaries, but this package supplies no Lean bridge from them to the actual fitted-effect vectors. Confidence in this omission assessment is medium because the credited row's source is outside the permitted audit files.

## Checks and order

`reading.md` was saved before `claims.json` was opened. `claim-stage.json` was saved and parsed before `record.json` was opened. No claim-stage verdict was changed after reading the record.

The definitions were followed through to Mathlib's probability measures, kernels, conditional expectations, independence, integrability, density measures, real suprema and filters. The meaningful ratios have positive denominators; empirical group bounds require nonempty groups; attained optimizers or bounded finite objectives protect the welfare suprema. The zero reward when no unit is treated is the paper's explicit reward convention. No statement was accepted because of an empty index type or a non-integrable integral's default value.

`/home/ubuntu/sap/tools/sap-lean scratch/Check.lean` completed successfully. The scratch file imports only Defs and proves a nontrivial `Standing` instance, checks a T16 premise model, finite-law normalization and positive selection masses, empirical means, a T24 model with observation rate strictly between zero and one, and the finite computations underlying the T26/T27 counterexamples. No Challenge theorem or proof from the existing formalization was used. No `lake` command was run, and at most one Lean process ran at a time.

`findings.json` gives one entry for every target, with a concrete nonvacuity instance or the omission reason. Both JSON outputs were parsed with Python and checked for target/theorem coverage.
