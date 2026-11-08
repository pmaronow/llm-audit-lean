# P006b statement referee report

Reviewed all 15 targets: 14 Challenge theorem statements and one omission. No false or vacuous theorem statement, undisclosed restriction, or inaccurate restriction was found.

| Verdict | Count |
| --- | ---: |
| correct_whole | 9 |
| correct_restricted | 5 |
| restriction_inaccurate | 0 |
| not_faithful | 0 |
| vacuous | 0 |
| false | 0 |
| omission_ok | 1 |
| omission_questionable | 0 |
| **Total** | **15** |

Severity counts: none 15; minor 0; major 0. There are no items outside `correct_*` and `omission_ok` to enumerate.

## Decisions and scope

The seven complete positive statements are T16, T19, T20, T21, T22, T23 and T24. T24 states the universal local argument for an arbitrary supplied stratum law; applying it in each covariate stratum gives the canonical conditional interpretation. T16's extrema and integrability assumptions make the printed maxima, minima and finite expectations meaningful. Its untreated-arm positivity is imposed almost everywhere, as in the corrected claim, and its sufficient pointwise condition is a separate assertion.

The five restricted targets are T17, T18, T25, T29 and T30. Their restrictions in `record.json` match the Challenge docstrings and the actual statements:

- T17 retains finite selection algebra and the example, and discloses the missing general-policy outcome-mean connection and all of clause (d).
- T18 discloses the omitted samplewise comparison, reward polynomial and uniqueness, welfare formula and separately displayed welfare values, and universal nonnegativity.
- T25 discloses its constant public covariate, deterministic outcomes, fair binary private types, zero estimator, unspecified small parameter choices, and omitted general unequal-parameter regret formula.
- T29 discloses deterministic treated outcomes in its family response characterization. The family still supplies a witness exceeding every positive regret threshold, so the existential headline remains complete.
- T30 retains the concrete two-agent witness and discloses the omitted general maximum identity and sufficient sample-size condition.

T26 and T27 correctly implement the architect's **refuted** decisions. They are counted as `correct_whole` because they soundly refute the bundled printed assertions. This does not assert that the positive printed claims are true. The saved step-2 classifications `different` are unchanged: they record the literal polarity difference between the Challenge negations and the positive transcriptions. Both docstrings explicitly state the negation and avoid claiming separate failure of every conjunct. Independent finite examples refute the actual printed readings, using no nonintegrable expectations or unbounded suprema.

The T28 omission is justified on the supplied evidence. The actual fitted effects and a verified connection to their particular reported summaries are absent. As described in the record, refuting a universal implication for hypothetical summaries supplies neither the required application premises nor a counterexample for either reported analysis. This judgment accepts the omission; it does not endorse the printed numbers, deny the numerical objection, or claim impossibility of a future proof. The credited source row itself was not supplied for inspection, so this omission judgment has lower confidence than the finite statement checks.

## Audit and verification

`reading.md` was saved before opening `claims.json`. It expands all fourteen theorem statements and their shared definitions, including the complete Standing assumptions and quantifier order. `claim-stage.json` was saved and parsed before opening `record.json`. No step-2 classification was changed after reading the record.

The audit followed the SAP definitions into Mathlib's probability measures, Markov kernels, composition-products, independence, identical distribution, conditional expectation, integrability, Bochner integrals and density measures. The statistical uses of division and real suprema have positive finite denominators and nonempty bounded optimization values. Empty sample or type indices do not supply any substantive result. No hypothesis was found that merely assumes the desired conclusion.

Both scratch files compiled successfully with the prescribed wrapper, without `sorry` or importing any Challenge theorem:

```text
/home/ubuntu/sap/tools/sap-lean scratch/Check.lean
/home/ubuntu/sap/tools/sap-lean scratch/Standing.lean
```

`scratch/Standing.lean` proves every Standing field for a concrete experiment with a policy-dependent Bernoulli treatment law and checks the remaining T16 inputs. `scratch/Check.lean` checks finite positive-mass examples, a nondegenerate observation fraction for T24, and the essential reward calculations and fixed-query unbiasedness underlying independent refutations for T26 and T27. These are statement and nonvacuity checks, not a reconstruction of the unavailable Solution/Comparator proofs. Other conclusions were checked mathematically from the definitions. No `lake` command was used, no more than two Lean processes ran concurrently, and no web search was necessary.

The JSON files were parsed with Python, and `findings.json` was checked for exactly one entry for each target, matching theorem names, valid verdict/severity values and consistent counts.
