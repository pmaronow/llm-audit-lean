# Review of SAP.P026b.T13–T17

Work: Aronow & Middleton (2013), *A Class of Unbiased Estimators of the ATE in Randomized Experiments*, J. Causal
Inference 1:135–154. Files: `reading.md` (blind reading, step 1), `claim-stage.json` (step 2), `findings.json` (final).

| Theorem | Record | Verdict | Severity |
|---|---|---|---|
| SAP.P026b.T13 | whole | faithful | none |
| SAP.P026b.T14 | whole | faithful | none |
| SAP.P026b.T15 | whole (refutes a reading of the package help) | faithful | none |
| SAP.P026b.T16 | whole | faithful | none |
| SAP.P026b.T17 | refuted | faithful | none |

## Notes per declaration

* **T13** (`Defs/Part3.lean:38`). Covers every law on {0,1}^N with positive marginals and every assignment-dependent
  prediction f. It states eq. [17] (corrected), eq. [18] (the `a = false` case, where `indicator false` = 1 − T_i)
  and eq. [19]. No extra hypotheses, and no junk values: π > 0 is built into `UnitExperiment` and N ≥ 1 comes from
  `Nonempty I`.
* **T14** (`Defs/Part4.lean:49`).
  * Out-of-block logit: `tableLogitPrediction` (`Part2:104`) gives units of block 1 the fit of block 2 and vice
    versa, as the claim specifies.
  * The estimator is HT on the residual cluster totals with N = 16, which equals Δ̂_G for these fixed predictions.
  * `printedVariance` (`Part1:80`) is eq. [35], ε convention included.
  * All ten rounded rows and the falsity of the six printed entries are stated.
  * I recomputed in floating point from the Lean data and reproduced the claim's coefficients and values
    (Var 0.0610543, SD(V̂) 0.0125667).
  * Caveat: the publisher's page was blocked by the sandbox, so I checked Table 1 only through the claim's own data
    facts and these high-precision values.
* **T15** (`Defs/Part3.lean:78`). Every clause of the counterexample is present.
  * `generalized` with one f for both arms equals the package's residual contrast at every assignment.
  * `packageLeastSquares` ties the fitted values to the unique OLS fit on an intercept and X.
  * The docstring names the reading it refutes and does not say "The printed claim is false", which is correct
    for a `whole` refutation of a reading.
  * Small point: the eq. [19] check `-(1/3)(3+3/2)(1/6+0+1/6) = -1/2` is pure arithmetic and is not linked to the
    definitions. The claim only asks for that numeric agreement, and the general link is T16(b).
* **T16** (`Defs/Part3.lean:96`). All clauses (a)–(c) are present:
  * (a) fixed g;
  * (b) OLS by orthogonal projection, which works at any rank, with the least-squares property asserted;
  * the bias formula;
  * the T15 example;
  * zero covariance as a sufficient condition for any f;
  * the sharp null as a sufficient condition for any function of the observed outcomes.
* **T17** (`Defs/Part4.lean:60`). The refutation is genuine.
  * **Conjunct 1** negates "for every design with positive marginals and positive disagreement: cross support AND
    Var ≤ E V̂". That contradicts the printed conjunction of (i) with (iii)/(v).
  * **Remark (not a defect):** conjunct 1 can be witnessed by the failure of support alone. It therefore does not
    show that conservativeness fails on its own. The docstring describes the failure of the combined "support and
    variance-conservativeness assertion", which is accurate.
  * Conservativeness does fail on its own: I compiled E V̂ = 2.875 < Var = 3.375 for `realAsymmetricTwo` with
    x = z = 1 (`scratch/T17.lean`). A stronger statement would be possible, but none is required.
  * **Conjunct 2** refutes footnote 9 (and the second claim of (iii)). The witness satisfies every printed
    condition: the standing assumptions, distinct indicators, π_11 > 0 and π_00 > 0 for all pairs, the sharp null,
    and the constant f = 0.

## Compiled checks
* `scratch/Check.lean`:
  * a `UnitExperiment (Fin 1)` exists;
  * a constant prediction has zero covariance under any `UnitExperiment`, so T16(c)'s hypothesis can be satisfied.
* `scratch/T17.lean`: `realAsymmetricTwo` satisfies the hypotheses of conjunct 1, has no cross support, and its
  V̂ is anticonservative.
* `scratch/table.py`: independent float recomputation for T14.
