All five declarations are **faithful**, with severity **none**. Each was reviewed
independently with its complete statement dependency closure. No source change
is requested.

`reading.md` was saved before opening the canonical claims. `claim-stage.json`
was then saved before opening the record; its five `whole` conclusions remain
unchanged. The record's five `whole` decisions and null restrictions are correct.
The current theorem and definition docstrings describe their actual statements,
including the specific scope of `PeriodicRowCertificates`.

| Declaration | Review result |
|---|---|
| T19 | Includes all six mathematical parts: exact design expectations, model moments and calibration, orthogonal decomposition, Gaussian laws, the general tail bound, and all four rounding-compatible row bounds. The extra row certificates supply the stated arithmetic. |
| T20 | Includes the ordered zero-pair bias identity, both common-sign cases, and genuine examples of both strict bias signs. |
| T21 | Includes arbitrary ordered-pair conjugate exponents, both bias bounds, unbiased correction, the exact expectation, and conservativeness for arbitrary outcomes. |
| T22 | Includes exactly the inherited conjugacy hypotheses and both sufficient equality conditions; it does not claim necessity. |
| T23 | Defines the displayed quadratic estimator, identifies its exponent-two specialization, and states conservativeness under the standing assumptions. |

For T19, the finite group representation is the stated systematic design after
reindexing. A cumulative-size interval has length 12r. Writing original positions
as 2(a+rj)+b+1, with 0≤a<r, 0≤j<m and b∈{0,1}, gives groups (a,b) of m units.
Their start intervals have lengths 2 and 10, hence probabilities 1/(6r) and
5/(6r). The estimators operate on the original units, including the quadratic
correction, and use the required population-mean scale.

The T19 probability claims concern averages of **exact conditional design
expectations**. They allow dependence between generated populations, as the
canonical claim expressly does. They assert neither deterministic impossibility
nor replacement values for unknown realized rows. None of the five declarations
is labelled or presented as a refutation.

For T20–T23, a finite weighted sample space represents every sampling law on
subsets of a finite population; it is not a substantive restriction. All zero-pair
sums are ordered, and the HT sum includes the positive diagonal. Real
`HolderConjugate` requires precisely positive exponents whose reciprocals sum
to one, without any symmetry assumption.

The junk-value audit found no defect. Positive marginal inclusion probabilities
and guarded joint denominators protect the HT formulas. T19 has m≥2, r>0,
positive tail variance and positive tail thresholds. Its relative-bias quotient
is conditional on a positive denominator. Natural subtractions give the correct
dimensions and degrees, including genuine zero-dimensional parity components
at r=1. Error-moment assumptions or Gaussian laws ensure integrability of all
quadratic statistics; event measures are finite. Negative-variance clipping,
nonintegrable-integral defaults, and `toReal ∞` are not used substantively.

`scratch/Nonvacuity.lean` compiled successfully with
`/home/ubuntu/sap/tools/sap-lean` and imports only the definitions. It checks:

* T19: a nonzero centered population, an actual zero-noise moment model, and
  independent Gaussian coordinate models with variance 17.91 for every row.
  Taking K=1 supplies the population-average hypotheses; any positive threshold
  supplies the tail threshold. More generally Gaussian coordinates provide the
  positive-variance moment model. Calibration is feasible: at ρ=1 take zero
  errors and β=√(900(N−1)/(16N)); all denominators are positive.
* T20: samples {0,1} and {2}, each with probability 1/2, with outcomes
  (1,1,1) and (1,1,−1/4). The compiled witness checks both bias expressions have
  their required signs; their biases are 4 and −1.
* T21: a uniform singleton sample from two units, outcomes (1,2), and conjugate
  exponents (2,2), with a genuine zero pair and nonzero bias.
* T22: the same singleton design with outcomes (3,−3). All equality hypotheses
  hold, and independent computation gives variance and expected estimate 36.
* T23: outcomes (1,2) in that design give true variance 1 and expected quadratic
  estimate 10, demonstrating a nontrivial strict conservative instance.

`scratch/Blind.lean` also compiled, inspecting all 56 generated closure-proof
types and relevant elaborated coercions. The required JSON files were parsed
with Python, and the final five fingerprints were checked against `closure.json`.
