# P023 declaration review

All five declarations are faithful. The record decisions are correct: T6–T9 are `whole`; T10 is `refuted`. There are no findings and no requested source changes. Reading the record required no change to the claim-stage assessment.

The blind reading was saved in `reading.md` before opening either claim or record. It unfolds the entire statement closure, including the generated auxiliaries printed in `scratch/BlindClosure.out`. The independent claim comparison is preserved in `claim-stage.json`.

- **T6:** All amplification, norm, fixed-function, coefficient/RD and universal non-Lipschitz clauses are present. Unbounded coefficients on every tail and the divergent subsequence faithfully express the infinite limsup. The deterministic response is the displayed mean function. Uniform-law finiteness and nonsingular moment systems prevent integral or choice defaults from affecting these assertions.
- **T7:** All population identities, error bounds, best-approximation criteria, exact specification, finite conditional identities and numerical constants are covered. Regressing the conditional mean gives exactly the normal equations for regressing the outcome; the bounded-test conditional-mean identity recovers the canonical joint-outcome residual formula. The fixed-design integral formulation expresses the conditional finite-sample assertion without adding independence or an unconditional random-design expectation.
- **T8:** Every primitive hypothesis and conclusion (a)–(g), including the slow-schedule existence claim, is present. The setwise residual-square bound expresses bounded conditional variance almost everywhere; the Rayleigh infimum is the smallest moment eigenvalue. Sample rank and window-count limits are not assumed. Arbitrary OLS choices on singular samples and zero-valued empty means affect exceptional finite-sample events whose probabilities vanish under the stated conditions, so they do not supply any claimed limiting conclusion through a junk value.
- **T9:** Both localized sums run over observed pairs themselves. The partition, central-bin identity, zero residuals outside it and positive denominator are explicit. All-bin-intercept normal equations equal the printed intercept-plus-bin-indicator equations on this partition. Empty bins never supply the denominator of an observed pair’s mean.
- **T10:** The refutation contradicts the canonical formal data-dependence assertion under a correctly specified linear model. It does not claim that every quoted sentence is false or draw a conclusion about causal scope. The coarsened-localization assertion is retained. `scratch/RefutationCheck.md` states the printed reading, lists its conditions and checks the witness against each. The bounded-prediction existence guard is redundant, but a genuine correctly specified model and bounded-outcome witness are available independently of it.

Successful independent Lean checks (each imports only `SAP.P023.Defs`, and uses no Challenge theorem):

| File | Evidence |
| --- | --- |
| `scratch/FiniteChecks.lean` | Full-rank finite design; T7 finite conditional hypotheses; T10 coefficient change from 0 to 1/200, positive counts, bounded outcomes and correctly specified stochastic model containing both outcome vectors with positive probability. |
| `scratch/PopulationChecks.lean` | Every T7 population hypothesis at degree one, including independently proved positive definite moments. |
| `scratch/UniformChecks.lean` | Uniform-law probability/support, nonempty T6 norm domain, and every T8 hypothesis using an actual infinite-product IID sample and bandwidth 1/sqrt(N) for N>0. |
| `scratch/PairChecks.lean` | Every T9 hypothesis on a nonrectangular set of three observed pairs, with a genuine coarsened fit. |

T6’s full fixed-function witness is an analytic, nonconstructive existence result rather than a finite numerical instance. No explicit infinite-series Lean witness was recreated. Its nonvacuity follows from the anchored polynomial gliding-hump construction: the series h=(1/4) sum 4^(-m) p_m has norm at most 1/12 and bias at least m/4 at the recursively chosen degrees. This is a genuine continuous function, and its growth rules out Lipschitzness. The law and nonempty function domain were checked separately in Lean.

`findings.json` contains exactly five entries with the fingerprints copied from `closure.json`. JSON syntax, entry count, required fields and fingerprint agreement were validated with Python.
