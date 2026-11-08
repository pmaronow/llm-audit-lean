# Statement referee report

Audited all 14 targets in `claims.json`. The final judgments are **6 correct whole statements and 8 correct restricted statements**. Every declared restriction is accurate and disclosed in the corresponding Challenge docstring. There are no adverse findings and no omitted targets.

| Verdict | Count |
| --- | ---: |
| `correct_whole` | 6 |
| `correct_restricted` | 8 |
| `restriction_inaccurate` | 0 |
| `not_faithful` | 0 |
| `vacuous` | 0 |
| `false` | 0 |
| `omission_ok` | 0 |
| `omission_questionable` | 0 |

Severity counts: none 14; minor 0; major 0.

## Blind-first procedure

1. Read all Defs and Challenge files and followed the relevant definitions into Mathlib, including the Euclidean metric, measure restriction, Bochner integral, extended mass conversion, finite subsets of fixed size and matrix inverse. Saved [reading.md](reading.md) before opening either JSON input.
2. Read the canonical claims and standing assumptions. Saved [claim-stage.json](claim-stage.json) before opening `record.json`. The classifications were whole for T3, T5, T11, T12, T13 and T14, and narrower for T1, T2, T4, T6, T7, T8, T9 and T10.
3. Read `record.json` and reviewed each decision against the saved reading and claim-stage judgments. All decisions agree. All eight restriction texts match their theorem docstrings, allowing whitespace and a hyphenated line wrap. **No stage-2 verdict was changed.**

Blind-reading SHA256: `99f884a233f0444db8ccf9ff8c9926f00995951e3b30f5344d0c300744243a44`.

Claim-stage SHA256: `4515d6976c143f5b23455f160bdbd3a607c76c5978f5e29512768c696124b6eb`.

The paper identified by the supplied citation was also consulted through its [arXiv entry](https://arxiv.org/abs/2106.15081). The supplied canonical claims and their explicit distinctions between formal content, reconstructed evidence and external premises govern these judgments. No Solution, Comparator or external formalization source was read.

## Restricted targets

| Target | Why the restriction is acceptable and accurately disclosed |
| --- | --- |
| T1 | Keeps the fixed labelled 121-node observation, swap, normalized supports and both directions of the four-node tail discrepancy. Explicitly drops quantification over arbitrary initial observations and the relabelling assertion. |
| T2 | Keeps finite-law and conditional calibration, Bernoulli-given-count uniformity and support-level cumulative imputation. Discloses the Euclidean/measurable spatial domain, all-assignment integrability, positive finite circle mass, nonempty arms and the omitted documentary and empirical conclusions. |
| T4 | Keeps the universal one-third bound, rejection-region obstruction, exact calibration, IID sampled-permutation correction and displayed sum. Explicitly drops the reconstructed observed values and exact observed p-value. |
| T6 | Keeps the matrix/HC0 identities, exact toy cutoff comparisons, additive covariance and variance identities, and sufficient geometric support bound. Discloses the geometric domain and support assumptions and the omitted numerical reconstructions. |
| T7 | Establishes the two finite labelled counting examples and their probability arithmetic. Explicitly omits their planar realization, including centres, radii, direction construction, field and geometric circle counts. |
| T8 | Keeps binary fixed-radius normalization, mixture bounds and identities, equal-weight algebra and positive rescaling. Discloses the spatial regularity assumptions and absence of a constructed joint sampling space, explicit finite-extrema display, separate order-statistic characterization and planar realization of the companion example. |
| T9 | Keeps the spatial circle-integral example, grid-position discrepancy and toy zero-width incompatibility. Explicitly drops the separately displayed coefficient, residual and contrast-weight vectors and kernel masks. |
| T10 | Keeps physical-cutoff invariance, the all-pairs zero identity, example values and toy HC0 result. Explicitly drops the strict-positivity characterization. |

The record's `rows_not_used` entries concern source lemmas rather than omitted targets. No target-level omission judgment is needed. Source-row names were not used as evidence of statement fidelity.

## Semantic and nonvacuity checks

Compiled [scratch/Check.lean](scratch/Check.lean) using only the permitted command:

```text
/home/ubuntu/sap/tools/sap-lean scratch/Check.lean
```

The final run exited successfully with an empty diagnostic log. The file imports only the Defs aggregate and uses no `sorry` or Challenge theorem. It checks a common Bernoulli law, the cardinality-two nonempty-arms event, arm counts, and a spatial model with two distinct nodes, positive radius, measurable field, unit circle masses, finite measures, integrable schedules and a true sharp null. It also checks a genuine subminimum-distance cutoff, normalized radius weights and rounding-hypothesis witnesses. With the uniform two-node law the conditioning event has probability 2/4, so these spatial hypotheses are jointly satisfiable with a nonempty evaluated radius set. At most one Lean invocation ran at any time; `lake` was never run.

The exact rational computations in [scratch/arithmetic_checks.py](scratch/arithmetic_checks.py) passed, with results saved in [scratch/arithmetic-results.json](scratch/arithmetic-results.json). They check the finite supports and tail discrepancies, actual atom selection on the validator and bandwidth circles, the percentile rejection example, replicated pair models for M=1 through 4, exact toy-node distance bounds, additive covariance examples, risk probabilities, both bandwidth variances, displayed sums and both grids. These finite checks supplement the mathematical assessment; they do not purport to prove the universally quantified statements. Each target's concrete witness or explanation appears in [findings.json](findings.json).

The potentially dangerous conventions have the following resolutions:

* Finite laws have nonnegative masses summing to one, which excludes an empty assignment-law sample space. The actual fixed supports and quantile samples are nonempty.
* The spatial test and risk statements require positive finite evaluated-circle masses and the relevant integrability. Fixed atomic constructions also have positive circle mass and finite integrals. In T6's geometric conclusion, the integrand vanishes on the evaluated circle, independently of the convention for nonintegrable integrals.
* Both-arm assumptions or explicit balanced assignments guard ratio denominators. T5 concerns linearization variance, as the canonical claim explicitly requires; it does not use a ratio estimator on a one-arm assignment. T6's matrix inverse is nonsingular under its two-arm hypotheses.
* T7's natural subtraction never truncates a negative quantity: its baselines are 400 or 1000 and the treatment decrement is 321. Its zero-based point index correctly represents the canonical one-based threshold after reindexing.
* T12's empty selected radius set is the stated defect being refuted. The theorem still quantifies over nonempty permutation samples. This is a substantive counterexample rather than vacuity.
* The quantile definition does not sort its input. T3 supplies an explicitly sorted sample; T8 assumes monotonicity; T12 supplies a constant-zero sample. All quantile levels lie in [0,1].
* T11 does not claim that the rounding bounds alone force 8.00. The canonical note expressly separates that reconstruction from the exact formal bounds. T14's pointwise difference hypothesis is the defining equality whose average is being rewritten, as the canonical target specifies.

## Items requiring correction

None. There are no findings outside `correct_whole` and `correct_restricted`, and no fixes are requested. The theorem scope does not establish a corrected empirical Uganda p-value, certify the external archived-code transcription, or add the geometric realizations expressly omitted by the docstrings.

Both output JSON files were parsed and checked with Python, including target coverage, unique identifiers, required fields, verdict and severity values, and agreement of the final counts with this report.
