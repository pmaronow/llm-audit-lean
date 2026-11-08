All five declarations are faithful, with severity `none`. The record's five
`whole` decisions agree with the independent claim-stage judgments; no judgment
was changed after reading the record. No corrections are requested.

| Declaration | Assessment |
| --- | --- |
| SAP.P022.T13 | Includes unbiasedness, the exact design variance, covariance and variance bounds for all finite rearrangements, endpoint attainment, and the full empirical-marginal probability-coupling assertion. Uniform permutations count each printed treatment/control assignment equally often. |
| SAP.P022.T14 | States the complete five-estimator ordering for every assignment when n=N, precisely the canonical formal reading. All finite-population corrections agree with the printed definitions. |
| SAP.P022.T15 | Includes all four hypotheses, moments through second order for every compatible law, both population endpoint limits, and joint estimator consistency at scale 1/N. No false uniform-CDF lemma is smuggled into a premise. |
| SAP.P022.T16 | Includes both correctly centered scaled-tail bounds, all positive tolerance splits, and rate functions chosen before the admissible sequence. Their dependence on H,C,theta,rho is allowed by the canonical definitions. A finite lower-bound constant can be absorbed into the existential rate functions. |
| SAP.P022.T17 | Uses T17WholeStatement, including the Gaussian limit, variance limits, coverage, and least assuring leading variance input across compatible nonsingular laws and realizing populations. The narrowness assertion was reviewed as part of the printed statement despite the audit-history note excluding it. Its class of nonnegative Wald inputs has a deterministic leading probability limit and uses the fixed Gaussian critical value. |

Every declaration listed in the five dependency closures was read. The blind
expansions and junk-value audit were saved in `reading.md` before opening the
claims; `claim-stage.json` was saved before opening the record.

No harmful totalization was found. Designs rule out empty means and zero finite
denominators. Quantile endpoint defaults change only Lebesgue-null points, while
sorted-value defaults are unreachable. The square-integrability definition
explicitly guards its real supremum, and limiting moments bound the covariance
extrema. CDF measures are probabilities. T16 takes its limsup in the extended
nonnegative reals, retaining infinity. T17's normal quantile has a nonempty,
lower-bounded defining set for 0<alpha<1; positive limiting scales make its
finite zero-denominator convention harmless for weak convergence.

Nonvacuity checks compiled successfully with:

```
/home/ubuntu/sap/tools/sap-lean scratch/Check.lean
```

The file imports only `SAP.P022.Defs`. It constructs finite data for T13/T14
and, for T15/T16/T17, a single nested population cycling through all four points
of `{0,1}^2`, with balanced allocations and their uniform limiting law. Its
proofs establish all allocation and CDF limits, uniform square integrability
with bounded suprema, bounded third moments, and nonsingularity. The printed
axiom checks contain only standard foundational axioms and no `sorryAx`.
The Wald-input class is nonempty too: for any v>=0, W=v/N is nonnegative and
has N*W=v identically. No audited theorem was used to establish these instances.

`findings.json` contains exactly the five requested declarations, with
fingerprints copied from `closure.json`, and was checked with Python.
