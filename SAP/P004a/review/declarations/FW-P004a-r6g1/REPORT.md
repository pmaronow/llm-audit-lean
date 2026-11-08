All five declarations are faithful to their canonical claims. The five `whole`
decisions in `record.json` are supported; no step-2 judgment changed after reading
the record. There are no current issues or proposed source changes.

| Declaration | Verdict | Severity |
|---|---|---|
| SAP.P004a.T1 | faithful | none |
| SAP.P004a.T2 | faithful | none |
| SAP.P004a.T3 | faithful | none |
| SAP.P004a.T4 | faithful | none |
| SAP.P004a.T5 | faithful | none |

`reading.md` was saved before the canonical claims or prior-review files were
opened. Every closure entry was inspected, including the 95 distinct generated
auxiliary proofs. `claim-stage.json` was saved before opening `record.json`.
The audit includes the actual spatial integrals, finite product law, inverse
information, residual fits, probability limits and quantiles.

For T1, the printed reading is that the displayed projection-based linearization
approximates fitted logistic IPW with an error smaller than N^(-1/2), under bounded
outcomes, local interference, bounded node density, independent overlapping
logistic assignments, bounded fixed-dimensional confounders, compact parameter
space, nonsingular Gram matrices and an actual constrained MLE. The witness meets
each condition: deterministic bounded outcomes, ten-unit spacing, independent
probabilities (1/3,1/2,2/3), bounded covariates, interior truth and a genuine
compact-set likelihood maximizer. Its two homophily expressions are zero and its
printed variance is positive. T1 states every W1–W6 clause, including the actual
nonvanishing remainder, block law and moments, Gaussian limits and coverage
deficit. The change from one-based to zero-based coordinates is a common
translation preserving every distance and integral.

For T3, the printed reading is conservative normal-interval coverage using the
specified double-weighted variance, under those regularity conditions and the
additional residual homophily condition. Its independent two-group design meets
each condition: probabilities 1/2 and 1/10 have the stated overlap, the separated
disk field is bounded and measurable, the Gram matrix is positive, the truth is
interior, the clipped group logits are actual likelihood maximizers, homophily
is 1/4 and the linearized variance is positive. All W1–W4 clauses are stated.
The standardized coverage event excludes zero variance, whose probability tends
to zero. Both docstrings correctly describe the normalized residual sum R/N.

T2 includes all corrected clauses (a)–(e), with the exact score fits, conditional
second moments, oracle bounds, nondegeneracy condition, corrected homophily and
both interval rules. Its usual domain conditions are disclosed. T4 includes the
raw-residual definition, both weighting identities, the bound for deterministic
node-and-arm fits, and the exact and asymptotic fitted-witness comparisons.
Neighborhood self-membership follows from the paper's neighborhood definition.

For T5, the reading being tested equates an unweighted sum over a partition with
the normalized area-share effect of its union. Its required binary spatial
outcomes, area measure, specified partition, independent fair assignment and
nonempty realized arms are all realized. All three cases and the refinement of
the same field are included. The docstrings correctly identify the interpretive
scope and assert no corrected empirical application value. Its `whole` decision
covers the canonical counterexample claim.

The earlier T2 issue is fixed at Challenge/Part1.lean:25 by the explicit usual-
conditions notice. The T3 normalization and T5 interpretation fixes described in
the architect report also match the current text. Their resolutions are recorded
in `findings.json`; historical issues are absent from the current `issues` lists.

Independent checks passed:

* `sap-lean scratch/ClosureProofs.lean` printed every auxiliary closure declaration.
* `sap-lean scratch/ReviewChecks.lean` compiled without errors or warnings, using
  definitions and Mathlib only. It constructs actual MLEs, complete finite T2/T4
  premise instances, an intercept LogisticConditions instance, and checks concrete
  block moments, probabilities, group sizes, arm counts and area arithmetic.
* `python3 scratch/ReviewExact.py` reproduced T1's constants and block calculations,
  T3's exact N=32/64 variances and expectations, T4's corrected N=32 expectation,
  and all T5 effects and refined areas. Results are in `scratch/ReviewExact.json`.

The full spatial nonvacuity arguments and the nondegenerate asymptotic T2 example
are given in `findings.json`. The independent finite checks supplement the
statement audit; the supplied certified asymptotic proofs were not re-proved.
No claim depends substantively on a totalized undefined quantity.
