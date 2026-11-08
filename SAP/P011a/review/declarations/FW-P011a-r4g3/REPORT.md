# Review of T11–T14

The blind expansion was saved in `reading.md` before opening the claims; the independent claim comparison is saved in `claim-stage.json` before opening the record. Every named declaration in all four closures, including generated auxiliary declarations, was read. The review concerns statements and definitions, accepting the Comparator's proof certification.

## T11: printed reading and witness audit

Printed reading in one sentence: under the paper's observed-data setting, Assumption 2 and observed-unit homoskedasticity, the auxiliary oracle estimator satisfies P(|n V2star − n Var(betaHat)| < epsilon) → 0 for every epsilon > 0; the intended consistency reading changes < to >.

Conditions and checks for the actual formal witness:

* Finite simple dependency graphs and valid observed constraints: all true and recruitment graphs are empty, all caps are zero, and all units are observed. The coordinates are independent, so the graph meets the full block-independence definition.
* Nested raw outcomes and graphs: on an infinite product of independent fair signs take Y_i=2 for odd one-based i (zero for even i), plus the corresponding sign. Restrict this sequence to each prefix; these are exactly `alternatingModel`'s marginal laws. Prefix empty graphs are nested. The coefficient t_n is allowed to vary with n and is deterministic in each row.
* Linear unbiased target: betaHat is the mean of t_n Y_i and its expectation is exactly 1 for every n, including odd n.
* Uniform bounds: 1/2≤t_n≤1, |t_n Y_i−1|≤2, degrees 0≤1 and |theta_i|≤1<2.
* Nondegenerate limiting scaled variance: n Var(betaHat)=t_n²→1.
* Homoskedasticity: every weighted coordinate has variance t_n²>0. Thus all correlations and moments used are defined; all functions are measurable and all laws have finite support.
* The less-than event at epsilon=3/2 has probability tending to 1, contradicting the printed universal assertion. The greater-than event at epsilon=1/2 also tends to 1, contradicting intended consistency. These are separate assertions. The example preserves Proposition 2's one-sided conclusion.

Thus the counterexample respects the printed setting; it does not exploit dependent replicates, nonmeasurability, missing moments or a zero-variance correlation convention.

## Evidence prepared before reading the record

Independent exact rational enumeration in `scratch/check_witnesses.py` passed for T11 at all sizes 1–10, including its remainder moments and the event probabilities recorded in the canonical audit history. Both T13 instances were enumerated over all feasible original graphs and all gadget matchings; every maximum matching decoded optimally and obeyed the recovery identity. T14's six-unit integer optimum and triangle integer optimum were enumerated, and the specified fractional points and variance values checked. The global LP bounds also follow directly from weight ≤1, nonnegative edge variables, and twice total edge mass equal to total degree mass.

The supplementary paper lookup returned an earlier arXiv version with different notation and pagination, while the journal endpoint required a security check. It was not substituted for the supplied canonical journal transcription. The earlier version's proof step and graph setting can be inspected in the [paper preprint](https://arxiv.org/pdf/1602.00359); the supplied `claims.json` remains the authority for this audit.

## Final comparison with the record

All four declarations are **faithful**, severity **none**. No claim-stage classification changed after reading `record.json`.

* **T11, whole:** the unconditional explicit counterexample states the canonical finite moments and both failure limits, and preserves the one-sided conclusion. The docstring distinguishes the literal printed step from its intended reading.
* **T12, whole:** every finite identity, bound, scalar comparison and tail estimate in clauses (i)–(iv), and the final conservativeness assertion, is present. Removing observed-graph nesting from `WholeScaling` covers the printed setting and yields a stronger rowwise result. It adds no equal-means or variance-limit restriction. The model's finite-dimensional real space is standard Borel and the weighted boundedness supplies all required moments.
* **T13, restricted:** the canonical comparison is narrower, and both the record and docstring accurately list the retained finite content and omitted program/optimum/algorithmic assertions. Saturated natural residual capacities are harmless because the feasibility test is unsaturated and the decoding assertion is guarded by feasibility. Cleared optional weights and the recovery denominator are exact, including empty optional sets.
* **T14, whole:** a universal certified-bound inequality includes optimized bounds by specialization and controls every compatible graph, including all integer maximizers. Both exact gap examples and their factor-of-two program values are present. There is no claim that an arbitrary feasible LP point gives an upper bound.

`scratch/Check.lean` supplies compiled nonvacuity and numerical examples; its T12 hypothesis instance uses the separately certified T11 result, while its finite graph and matching checks are independent of the Challenge theorems. `findings.json` contains exactly the four reviewed declarations and their original closure fingerprints.
