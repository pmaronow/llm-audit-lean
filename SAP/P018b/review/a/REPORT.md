# Statement audit: P018b

All 14 targets are accounted for. The package has **6 correct_whole** and
**8 correct_restricted** verdicts. There are **0 defects, 0 vacuous statements,
0 false formal statements and 0 omitted targets**.

| Verdict | Count |
|---|---:|
| correct_whole | 6 |
| correct_restricted | 8 |
| restriction_inaccurate | 0 |
| not_faithful | 0 |
| vacuous | 0 |
| false | 0 |
| omission_ok | 0 |
| omission_questionable | 0 |

There are no items requiring a correction.

## Decisions and scope

| Targets | Architect's decision | Assessment |
|---|---|---|
| T15, T16 | whole | All canonical algebra and numerical content is present. Arbitrary finite injective two-element incidence families and arbitrary record scores extend the domain without removing any canonical instance. |
| T17 | restricted | The full-rank negative-diagonal sample and specified bounded-population/event certificate are retained. The spectral/intercept/normal-design examples, additional formulas and classifications, and distributional-limit identification are omitted exactly as disclosed. |
| T18 | restricted | The incidence/PSD decomposition, guarded square-root domain and truncation conclusions are retained. The fixed-target restriction on the rarity limit and omission of an OLS counterexample are disclosed. |
| T19 | restricted | Only existence of a bounded two-record model with the listed rank, residual, moment and limit properties is claimed. The concrete law, detailed formulas, proof events and directed reformulation are explicitly omitted. |
| T20 | restricted | Only abstract moment convergence from weak convergence and UI squares remains. All missing estimator specializations and other canonical parts are disclosed; coordinate L2 guards are explicit. |
| T21 | restricted | Only the finite conditional-covariance sum identity remains. Counts and the unconditional-variance correction are expressly omitted. |
| T22 | restricted | The error distribution, covariance and conditional-error-mean statements are retained. The response mean and correctly specified response-regression conclusion are expressly omitted. |
| T23 | whole | Correct predictor, derivatives, dimensions and sample sums are present. The generic expected outer product uses the same data in both factors and has L2 guards. |
| T24 | restricted | All exact table arithmetic is retained. Both significance implications are restricted jointly to the declared two-sided rounding intervals, with a positive HC denominator. |
| T25, T26, T28 | refuted | Each theorem refutes the printed universal reading. These correct_whole verdicts certify the refutations; they do not affirm the false printed assertions. |
| T27 | restricted | The probability-consistency conclusion uses the unconditional score covariance. The additional deterministic-cutoff, eventual a.s. sample-rank premise is accurately disclosed, with the standing and fitted-moment conditions retained. |

All eight restriction texts agree between the record and Challenge docstrings
after whitespace normalization. Comparing those texts with the definitions and
canonical claims revealed no undisclosed substantive restriction. The record has
no omitted-target decisions; unused supporting rows are not omitted targets.

`claim-stage.json` was saved before opening `record.json` and has not been
changed. Its `broader` labels for T15/T16/T23 describe harmless extensions that
cover the entire canonical content. Its `different` labels for T25/T26/T28
record that these theorems assert refutations of the printed assertions. No
step-2 reading or verdict was revised in response to the record.

## Concrete checks

* `scratch/Check.lean` imports only the supplied Defs. It compiled successfully
  with `/home/ubuntu/sap/tools/sap-lean scratch/Check.lean`, without `sorry` or
  added axioms. It checks a nonempty injective two-element incidence family,
  the negative sample's Gram determinant, inverse, OLS coefficients, residuals
  and covariance, the N=3 covariance-family obstruction, and all T20 premises
  in dimension one. The only remaining diagnostic is a style warning.
* `scratch/exact_checks.py` passed all exact rational assertions; results are in
  `scratch/exact-results.json`. These cover the six-dyad arithmetic, the sample
  and bounded-population matrices and event, every table ratio and rounding
  bound, and finite fair-sign moment checks. These finite computations do not
  substitute for asymptotic proofs.
* T26 has a concrete bounded witness even with eventual a.s. sample rank:
  iid U uniform on [-1,1], X_ij=(1,U_i+U_j), Y_ij=(U_i+U_j)^2.
  The whole design determines every residual, so the printed conditional meat
  is zero; at N=3 the intercept score-sum variance is 12/5. This refutes the
  printed conjunction without claiming its asymptotic-law clause is false.
* For both T27's nonvacuity and T28's refutation, the fair-sign intercept model
  gives G_N=D_N, residual bound 4, E[e_d^2]=2-4/N and neighboring
  E[e_d e_f]=1-4/N. All T27 premises hold with rank cutoff 2 and moment cutoff
  5. For T28 the literal printed target is 4/D_N, while N Var(bhat)=4.
* T19's nonvacuity is supplied mathematically by the countable unit model in
  the canonical claim. Its strictly positive scales give all-sample rank, and
  rare disjoint events give the divergent extended moments. This full witness
  and its asymptotic results were not re-proved in the scratch Lean file;
  confidence is correspondingly lower than for the finite arithmetic checks.

## Definition safeguards

The reading follows the SAP definitions through Mathlib: singular matrix
inversion, nonintegrable real integrals, conditional-expectation defaults,
real variance's infinity-to-zero convention, Gaussian variance coercions,
finite-dimensional norms, and positivity definitions were all inspected.
No finding depends on an empty index type, truncated subtraction, an
infinite measure converted to zero, or an assumed conclusion. The extended
integrals in T19 correctly express divergent moments; T20 has L2 hypotheses;
the population score covariances are integrable by boundedness; and the
fair-sign variances in T28 are finite. Tail statements avoid the initial
N=0,1 singular-design conventions.

The paper's OLS, dyadic sandwich and repeated-dyad formulas were also checked
against the [paper preprint](https://arxiv.org/pdf/1312.3398). The supplied
`claims.json` remains the reference for canonical published-page wording and
scope; the preprint has different pagination.

The blind reading is saved in `reading.md`. Full per-target verdicts and
nonvacuity explanations are in `findings.json`. Both requested JSON files were
parsed and checked against all target IDs with Python.
