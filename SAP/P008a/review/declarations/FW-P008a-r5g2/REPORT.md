# P008a declaration review

All five declarations are **faithful**, with severity **none**, within their recorded scope. No definition, hypothesis, junk-value, labeling or docstring defect was found.

| Declaration | Record decision | Assessment |
| --- | --- | --- |
| `SAP.P008a.T6` | restricted | General OLS/sandwich and HC0 identities, additive covariance/variance and geometric support bound match. The omitted numerical minimum distance, printed interval reconstruction and c=r warning are explicitly disclosed. |
| `SAP.P008a.T7` | whole | Includes the complete specified planar construction, centres, counting circles, independent Bernoulli design, binary schedules, actual spatial estimands/estimates, sampling probabilities and both probability-interpretation obstructions. |
| `SAP.P008a.T8` | restricted | Retained normalization and rescaling algebra is correct. The docstring accurately discloses the missing empirical attribution, application grid, joint sampling construction and remaining scope limitations. |
| `SAP.P008a.T9` | whole | The actual OLS example, both kernels/variances, generic box bound, normal equations and sixth-row width incompatibility match the supplied computational model. |
| `SAP.P008a.T10` | whole | Covers corrected cutoff invariance, actual OLS sandwich identities, all-pairs cancellation, the toy identity kernel, HC0 and the actual-residual positivity characterization. |

The two counterexamples satisfy their printed conditions. T7 uses the full independent fair-Bernoulli assignment cube, includes the centres in its field and evaluates the Hajek estimate at a positive-probability two-arm assignment. Its companion sum −4 contradicts the probability interpretation. T9 holds the radius, circle means, assignment, distances and cutoff fixed while changing grid position, giving variances 1 and 1/2. Its statement concerns the supplied archived computational model; it does not attribute that model to the article's historical release or refute the article's general cutoff guidance. The record correctly labels these canonical counterexample packages `whole`.

No substantive conclusion relies on totalized zero division, a singular OLS inverse, infinite-measure `toReal`, a nonintegrable Bochner integral, natural-subtraction truncation or a negative square root. Normalized weights ensure a nonempty radius index set; finite type-7 quantiles use a nonempty sorted sample and q in [0,1]. Usual measure-theoretic existence conditions were not counted as restrictions.

I saved `reading.md` before opening the claims and `claim-stage.json` before opening the record. No stage-2 conclusion changed at stage 3. All closure entries were read, including the 86 generated auxiliaries printed by `scratch/ClosureProofs.lean`. Independent checks in `scratch/CheckRegression.lean`, `scratch/CheckSpatial.lean` and `scratch/CheckRisk.lean` compiled successfully with the permitted `sap-lean` wrapper. They verify nonvacuity, actual OLS matrices/scores and variance calculations, positive finite spatial instances, and symbolic binary threshold counts. The large T7 geometry is checked by the unit-direction, inverse-slope, radius and centre-separation argument detailed in `claim-checks.md`, without enumerating its 640004 points in a new Lean proof.

`findings.json` contains exactly the five requested fingerprints and verdicts. Both JSON deliverables were parsed and structurally checked with Python.
