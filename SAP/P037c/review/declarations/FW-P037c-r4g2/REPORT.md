Both declarations are **faithful**, with severity **none**. The blind expansion
was saved in `reading.md` before opening `claims.json`; the two `whole`
comparisons were saved in `claim-stage.json` before opening `record.json`.
Every closure entry was read, including the generated proof declarations
printed in `scratch/closure-proofs.log`. The record caused no change to either
claim-stage conclusion.

**SAP.P037c.T34.** `Defs/Part5.lean:11–60` supplies canonical clauses (a)–(c),
including the printed imputation, residual-plus-design decomposition,
coefficient and standardized-mean shifts, and variance equality for means and
contrasts. `Defs/WholeW1.lean:139–173` covers clause (d): the reduced fit retains
the projected control contribution, a strict collapse of the two probability
controls loses a genuine omitted contribution, and the two actual variances
can differ. Lines 176–206 cover the required extension to full-rank bases,
unique fitted values, and estimable functionals for aliased presentations.
The `whole` decision in `record.json` is correct. The Challenge docstring at
`Challenge/Part1.lean:48–59` accurately states these conclusions and the usual
measure-theoretic conditions. A law on the finite exposure-assignment set adds
no substantive restriction to this fixed-population claim.

The compiled examples in `scratch/Nonvacuity.lean` exhibit the positive-weight,
full-rank, reduced-control, and genuinely aliased premise families. A separate
exact-rational calculation over all 96 concrete states verifies the law and
marginals, every relevant Gram matrix's invertibility, the point coefficients,
every imputation shift, and the unequal full and collapsed variances
(`scratch/t34-exact-check.json`). The total matrix inverse's singular value is
therefore not supplying a spurious concrete counterexample. The explicitly
aliased cases use minimizers or an injective basis instead of that inverse.

**SAP.P037c.T43.** `Defs/Part6.lean:10–92` implements exactly the finite
nonnegative normalized law, actual four-school demeaning, raw moment and span
premises, design-expected projection, structural outcome model, actual expected
normal equations, bias formula, and common-intercept corollary of the canonical
claim. `Defs/WholeW1.lean:225–290` additionally states all four derived
orthogonality identities and the specified nondegenerate certificate. Neither
orthogonality nor the desired coefficient value is assumed. The canonical
statement expressly permits real treatment variables satisfying its moments;
the formal generality is intentional. The recorded `whole` decision and the
Challenge docstring at `Challenge/Part1.lean:62–70` are accurate, including the
usual measure-theoretic conditions.

The complete T43 certificate and all remaining model premises were independently
compiled in `scratch/Nonvacuity.lean`: binary complementary assignments,
compositions 1/4 or 3/4, nonconstant fixed untreated levels, E[t't]=1,
K=1/16, and an actual expected-normal-equation solution. Both divided quantities
are protected by the canonical nondegeneracy premises. `scratch/Innovation.lean`
also checks that the defined residual differs from the seed innovation on the
certificate. No finite-sample OLS unbiasedness, seed-sampler derivation, or
incomplete-block assertion is introduced. Neither reviewed declaration is a
refutation.

Validation used `/home/ubuntu/sap/tools/sap-lean`; no `lake` command was run.
The compiled nonvacuity proofs do not invoke T34 or T43. Both output JSON files
were parsed with Python, and the final entries' identifiers and fingerprints
were checked against `closure.json`.
