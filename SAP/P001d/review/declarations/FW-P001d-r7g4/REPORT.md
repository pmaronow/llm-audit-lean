# Declaration review

All four declarations are faithful to their recorded scope. No statement,
definition, junk-value, nonvacuity, or docstring defect was found.

| Theorem | Claim comparison | Record | Verdict |
|---|---|---|---|
| `SAP.P001d.T73` | Entire canonical four-point counterexample | whole | faithful |
| `SAP.P001d.T74` | All five general residual properties and the classical Gaussian clause | whole | faithful |
| `SAP.P001d.T75` | Fixed-covariate weighted mean and bounds; conditional-law implication omitted | restricted, accurately disclosed | faithful |
| `SAP.P001d.T76` | Gaussian likelihood formulas, optimization equivalences, scale invariance and unique inverse-Gram solution | whole | faithful |

`reading.md` was saved before opening the claims. `claim-stage.json` was saved
before opening the record. Reading the record required no change to those
judgments. Every dependency listed in `closure.json` was inspected, including
the generated declarations printed by `scratch/BlindCheck.lean`.

For T73, the printed assertion being tested is that deviations
`e = Y - E[Y|X]` are generally independent of X, including for a linear CEF.
The witness satisfies each relevant condition:

* It is a probability law: the four atoms have mass 1/4 each.
* X and Y are random variables: both are measurable on the finite sample space.
* The required moments exist: every function of the realized X values and all
  residual quantities are bounded on four atoms.
* The residual uses a genuine linear CEF: the two conditional means are 2
  and 3, and the event-integral definition certifies the version `2+x`.
* All five CEF residual identities hold, while the joint event probability
  1/2 differs from its marginal product 1/4.

The attribution to general CEF deviations is the false printed assertion
identified in the canonical claim. Independence under a classical conditional
Gaussian model is a separate, valid assertion, included in T74. T73 establishes
the canonical counterexample and is correctly recorded as `whole`.

T74's conditional mean uses the actual measurable-event integral
characterization. Its conditional variance uses Mathlib conditional expectation,
and the variance branch assumes an integrable residual square. Its conditional
law definition requires probability kernels, measurability, and all rectangle
identities. The pointwise Gaussian shift concerns the specified model version;
the other conditional-expectation identities are almost-sure identities.
The additional explicit assumptions are the permitted usual measure-theoretic
conditions.

T75's weighted expression is exactly the two-point mean, and the theorem's
docstring and record both disclose the missing conditional-law-to-CEF argument.
Its elementary algebra does not conceal an assumed conditional-expectation
conclusion. T76 uses all K+1 coefficient coordinates and holds scale fixed.
Positivity guards the logarithms and scale divisions; invertibility guards the
matrix inverse; positive n guards the mean-square normalization.

`scratch/Nonvacuity.lean` compiled successfully using the prescribed
`sap-lean` command. It constructs the four-atom probability measure and CEF,
proves actual non-independence, supplies the moments for T74's general branch,
constructs a positive-scale Gaussian conditional-law instance, checks T75 at
`h=1/3`, and activates every T76 hypothesis with a nonsingular two-observation
design and a concrete global least-squares minimizer. No Challenge theorem
proof is used in these checks. Only the permitted compiler was used; no `lake`
command or external review material was accessed.
