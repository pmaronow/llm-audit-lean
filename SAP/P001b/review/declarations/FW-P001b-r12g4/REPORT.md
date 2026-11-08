All four declarations are faithful to their recorded scope. T35, T37 and T38
cover their canonical claims; T36 states an accurately disclosed restriction.
There are no current issues.

| Declaration | Canonical coverage | Record decision | Verdict |
|---|---|---|---|
| `SAP.P001b.T35` | All three event identities | whole | faithful / none |
| `SAP.P001b.T36` | Listed density and extended-integral facts | restricted | faithful / none |
| `SAP.P001b.T37` | Marginal versions and positive finite slice ratios | whole | faithful / none |
| `SAP.P001b.T38` | Zero combination and both singular correlation endpoints | whole | faithful / none |

The blind reading was saved in `reading.md` before opening the canonical claims
or review history. It unfolds every SAP dependency and accounts for the generated
closure declarations. `claim-stage.json` records the subsequent claim comparison;
reading the record required no changes to those conclusions.

T35 states the nonnegative triangular event formula, the full event's decomposition
by its negative-Y portion, and the exact zero-missing-mass criterion. Its density
predicate correctly represents an absolutely continuous joint probability law.
Probabilities are finite, and exceptional nonintegrable sections do not affect
the iterated integral by Fubini.

T36 uses exactly the canonical explicit function. In the installed Mathlib,
`ContDiff ℝ ⊤` is analytic order ω, so the analyticity disclosure is accurate.
The docstring and record list the omitted boundedness, logistic identities, CDF
and mixed-derivative assertions, zero-slice limit, positive slice integrals, and
marginal derivative assertion. The earlier review correctly observed that an
infinite zero slice cannot disprove an equality presupposing a finite real slice
integral. That issue is **fixed**: the current introduction states only the
retained density facts, and `Challenge/Part2.lean:58–59` expressly disclaims such
a refutation. These facts are clauses of the canonical statement itself, so
retaining them with the restricted decision is legitimate.

T37 uses `T37WholeStatement`. It covers every finite nonnegative marginal version
agreeing almost everywhere, with the CDF identity at every threshold. Its selected
slice ratio has an integrable, strictly positive denominator. No global Borel
premise narrows that normalization assertion. The canonical claim requires this
positive finite slice domain; it does not add a separate disintegration identity.

For T38, the printed normal-combination assertion permits arbitrary real
coefficients and any finite independent family of positive-variance normal
inputs. The singleton standard-normal family satisfies independence automatically;
coefficient zero is allowed, measurability holds, and all moments exist. Its zero
combination is therefore a genuine atom with no PDF or positive-variance normal
law. The printed bivariate parameter range requires real means, positive standard
deviations and correlation in [−1,1]. Means zero, standard deviations one and
correlation ±1 satisfy each requirement and make both denominators zero. The
canonical claim already asserts these defects, making **whole**, rather than
**refuted**, the correct label. The additional zero-function identities describe
the explicitly documented totalized formula; the separate denominator equations
certify the ordinary formula's singularity.

`/home/ubuntu/sap/tools/sap-lean scratch/Nonvacuity.lean` completed successfully.
It independently constructs all T35 hypotheses and both sets of T37 hypotheses
using the unit-square uniform law, checks T36 positivity and the analytic-order
interpretation, and verifies T38's witnesses. It uses no Challenge theorem.
T36 has no conditional hypotheses requiring an instance. Its normalization and
slice behavior also follow directly from the logistic integral and the
substitution t = exp(x), as detailed in `findings.json`.

The review leaves all supplied Lean sources and records unchanged. Findings copy
the closure fingerprints and include a separate resolution of the sole issue
in `earlier.json`.
