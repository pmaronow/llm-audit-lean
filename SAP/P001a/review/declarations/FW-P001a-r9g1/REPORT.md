# Declaration review

All five declarations are **faithful**, with severity **none**, relative to
their recorded scope. Every closure entry was read, including the generated
auxiliaries printed by `scratch/BlindCheck.lean`. `reading.md` was saved before
opening the claims; `claim-stage.json` was saved before opening the record.
No claims-stage conclusion was changed after reading the record.

| Declaration | Claims-stage comparison | Record assessment |
| --- | --- | --- |
| `SAP.P001a.T1` | Narrower explicit witness | The disclosed omissions are accurate; the witness still refutes the asserted Hadamard implication. |
| `SAP.P001a.T2` | Whole | Both the sample-mean CLT correction and the finite-variance zero-direction witness are covered. |
| `SAP.P001a.T3` | Whole mathematical gap witness | The restricted interpretation is accurately disclosed: disagreement of global extensions outside the CEF domain. |
| `SAP.P001a.T4` | Whole | Local representative equality, transfer of existing derivatives, and sufficient-but-not-necessary support condition are covered. |
| `SAP.P001a.T5` | Whole | Both the local L2 counterexample and the separate endpoint supplement, with t >= 2, are covered. |

## Refutation and interpretation checks

**T1 printed reading:** finite variance makes the mean functional Hadamard
differentiable for the uniform CDF topology, even on the finite-second-moment
domain. Its conditions and witness check are:

* Probability law and genuine finite moments: the geometric masses sum to one,
  their mean is 1 and second moment is 3, giving variance 2.
* Admissible perturbations: for n >= 2, the mixture weights are nonnegative and
  sum to one; shifting the geometric law preserves finite second moments.
* Positive scales tending to zero: t_n = n^(-2).
* Directions converge uniformly to zero: this is exactly the final quantified
  assertion of `T1Statement`.
* The mean quotients equal 1, contradicting convergence to the value 0 that a
  linear Hadamard derivative must take in the zero direction.

Thus `refuted` is justified without undefined expectations or nonmeasurable
objects. The docstring accurately lists the formulas and abstract derivative
predicate not separately stated.

**T3 interpretation:** the stronger assertion being denied is that global CEF
extensions differentiable on the positive-density domain must determine one
derivative at the mean even when that mean is outside that domain. The fixed
law is jointly continuous, bounded, independent across its two coordinates,
and has an integrable covariate with mean zero. Both extensions are C1 and
agree with zero on the entire positive-density domain. Their derivatives at
zero differ, but zero is outside that domain. Consequently this is accepted
as the disclosed extension witness, with the `restricted` decision; it is not
accepted as a refutation under an admissible-domain/existence reading. The
canonical statement's mathematical witness is fully represented, consistent
with the claims-stage comparison.

**T5 printed reading:** iid sampling, a smooth CEF on compact interval support,
and J_n -> infinity with J_n/n -> 0 suffice for consistency in local L2 on
regions of positive probability. Every condition is met: the observation law
is independent uniform/standard Gaussian, moments exist, the CEF is smooth
and zero, the degree schedule has both rates, and [0,delta] has probability
delta for every 0 < delta <= 1. Fits minimize squared residuals and are Borel
statistics of the sample. The primary counterexample concerns integrated
error on those regions, not merely a point. The supplementary endpoint bound
uses its own degree schedule and excludes t = 1, exactly as the canonical
statement requires.

## Nonvacuity and totalized operations

Both `scratch/Nonvacuity.lean` and `scratch/NonvacuityT4.lean` compile using
`/home/ubuntu/sap/tools/sap-lean`; they import only Defs and Mathlib, not the
Challenge theorems. They independently check geometric normalization and
moments, representative mixture masses, every sampling premise of T2 and T5,
normalization of the gap product law, vanishing of the bump on its support,
and its genuine derivative at zero. The T4 file supplies all hypotheses of
its probability/CEF block in dimension one with a positive Gaussian density,
an open neighborhood, continuous zero CEFs and an existing derivative.

For T5, fit existence is explicitly asserted for both schedules, so the
universal failure conclusions are not over empty classes. Independently,
minimum-norm coefficients are limits of ridge coefficients
(V^T V + eta I)^(-1)V^T y as positive eta decreases to zero. This gives Borel
minimizing selections for every finite design, including singular and empty
designs. The scratch checks construct the sampling experiments; they do not
independently reprove these selection or tail-bound conclusions.

No definition encodes its conclusion or substitutes a placeholder notion.
Summability and integrability prevent default-zero sums and integrals; all
probabilities are finite, all local polynomial integrals are finite, and the
liminf is of a sequence in [0,1]. Zero-size samples, truncated subtraction,
total derivatives, and density-version changes have the safeguards detailed
in `reading.md`. None supplies spurious mathematical content.
