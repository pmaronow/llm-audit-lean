# P017 statement audit

Audited all 16 targets. The final counts are:

| Verdict | Count |
| --- | ---: |
| correct_whole | 11 |
| correct_restricted | 5 |
| restriction_inaccurate | 0 |
| not_faithful | 0 |
| vacuous | 0 |
| false | 0 |
| omission_ok | 0 |
| omission_questionable | 0 |
| Total | 16 |

There are no items requiring a correction. All severities are `none`. No target was omitted.

`correct_whole` includes P017-T9 as a faithful **refutation** of the printed universal representation assertion. It does not mean that Proposition 1 as printed is true. T9's type explicitly negates that assertion, and its Challenge docstring says so. The IID IPW construction satisfies the estimator's empirical-measure factorization and asymptotic assumptions and fails on a positive-probability event, so the refutation also applies if IID sampling is required. The canonical standing assumptions themselves leave the sampling scheme unspecified.

The five restrictions are accurate and disclosed in the theorem docstrings:

- **P017-T2:** omits the prescribed bounded atom-indicator weight and the prescribed two-region mixture, including its conditional means, coefficient, bounds and normalized moments. It retains exact attainability, the support consequences and a normalized existential atom witness.
- **P017-T3:** omits the explicit clipping-endpoint comparisons with the support bounds and the separately stated finite-valued-effect example. It retains the general endpoint-atom sufficiency condition, the exact representation criterion, strict-inside equality, support-hull bounds and both limits.
- **P017-T7:** states the combined result under asymptotic normality and omits a separate consistency-only formulation. This correctly avoids the canonical final sentence's overstatement about root-n boundedness: the deterministic sequence hat_n = mu + n^(-1/4) is consistent but sqrt(n)(hat_n-mu) is unbounded in probability. Consistency alone still suffices for the clipping-error event argument; the docstring accurately says that this separate formulation is not stated.
- **P017-T11:** retains the displayed Lebesgue-integral identity and all positive-power limits while omitting the separately stated equivalent normal-moment and standardized-density formulas.
- **P017-T12:** retains every prescribed positive vanishing failure sequence, the logarithmic example and rate-domination existence, but does not specify that the domination witness eventually equals sqrt(r_n).

The architect's decisions agree with the independently saved claim-stage assessment for every target. Reading the record caused no change to any stage-2 verdict. There are no omitted-target decisions to assess. Proof-row selection was not treated as evidence for statement fidelity.

The audit checked finite expectation, positive finite weight denominators, numerator integrability, nonempty real-law supports, extended support bounds, zero and infinite radii, positive-size denominators, quantifier scope, and the distinction between the actual clipping error and the normal-part intermediate error. No claim relies on a nonintegrable Bochner integral being defined as zero. The mean-square statements obtain eventual integrability from their Gaussian-plus-square-integrable-remainder hypotheses; infinite-radius actual errors are identically zero. T1's more general weight clause obtains product integrability from its bounded effect. Probability measures prevent the infinite-measure-to-real convention from doing work.

In T10 the probability-zero implication is under the same support condition as the preceding probability-one conclusion. Its subsidiary premise is therefore impossible in that branch, but the main theorem hypotheses are satisfiable. The probability-one conclusion itself contradicts the printed zero, and the canonical claim puts this discussion under the same suppose/then assumption. This does not make the whole target vacuous.

The journal-version text in `claims.json` was the canonical baseline; the [publisher-provided full text of the paper](https://www.researchgate.net/publication/310050238_Data-Adaptive_Causal_Effects_and_Superefficiency) was also consulted. The differently titled arXiv version was not substituted for the journal text.

`reading.md` was saved before opening `claims.json` or `record.json`. `claim-stage.json` was saved before opening `record.json`. Each target's concrete nonvacuity instance is recorded in `findings.json`.

Independent Lean checks in `scratch/Check.lean` import only `SAP.P017.Defs`, not the Challenge or any Solution. The final command `/home/ubuntu/sap/tools/sap-lean scratch/Check.lean` succeeded with exit code 0 and no diagnostics. It checks a real probability model with a nondegenerate normal estimator and zero remainder, and jointly checks the measurable integrable fair-sign population, its mean zero, nonempty support exactly {-1,1}, radius one, positive-radius/root-n-normal hypotheses, normal remainder and small-remainder condition. It also checks the central shifted-normal clipping calculation, the infinite-radius identity, an admissible weight, and both large logarithmic-example values. Additional cases in `findings.json` are mathematical constructions, not claims of additional Lean compilation. No Challenge proof was relied upon, and no `lake` command was run.

Both output JSON files were parsed and checked with Python, including target coverage, theorem names, required fields, verdicts and counts.
