P036: **2 whole, 0 restricted, 0 refuted, 0 omitted; 2 proved, 0 open glue tasks.**

The package covers exactly the two targets in `work.json`.

| Target | Decision | Coverage |
| --- | --- | --- |
| P036-T1 | whole | Corrected indicator/coefficient roles; conditional means with and without covariates; existence, uniqueness and identification of the unadjusted OLS minimizer; connection to binary response-count inputs; both exact coefficient pairs and all four three-decimal displays. |
| P036-T2 | whole | Gram entries and inverse certification; matrix OLS coefficients and both leverages; both assignment-wise HC2 equalities; all treatment-effect and sample-variance moments; expected HC2, its exact nonnegative gap and constant-effect equality criterion; binary sample variance; connection to counts, both exact HC2 variances and both rounded standard errors. |

There are no restricted or omitted targets and no open glue tasks. The 14 T1 rows and 42 T2 rows are each accounted for in `manifest.json`. Eight T1 rows and fourteen T2 rows are applied directly; the other rows are either incorporated in those existing results or unnecessary to the target's conclusions. Their individual reasons are recorded in the manifest.

The shared-definitions route uses three `Defs/Part*.lean` modules, importing only Mathlib and earlier definition parts. `Challenge` imports these shared definitions without any project or Bridge imports. `Solution` imports the same compiled definitions and the project through `Bridge.lean`.

All 32 correspondence lemmas in `Bridge.lean` are proved by `rfl`. Each has the name of its SAP definition followed by `_eq` and equates that function with its project counterpart. They cover the indicator and model functions, conditional and finite means, least-squares objective and coefficients, rounding predicate, matrix and HC2 functions, table calculations, and finite-randomization functions. No structural adapters are needed. Both solutions use these equalities to transfer the existing declarations.

The remaining glue is conjunction and instantiation, extracting existence and uniqueness from the existing minimizer equivalence, substituting arm sizes and response totals into the coefficient definitions, and deducing nonnegativity of the exact gap from the existing conservativeness inequality. No additional mathematical result or published-theorem premise is introduced.

The probability-space clauses explicitly use measurable regressors and the canonical integrability conditions. The model equations then ensure integrability of the outcomes. Both conditional arm probabilities are positive. Finite OLS requires both arms nonempty; HC2 and sample variances require at least two units per arm. The randomization constraints ensure a nonempty assignment set and positive population-variance divisor. Thus the statements avoid undefined statistical quantities represented by total Lean functions.

The empirical arm sizes and response counts are supplied inputs, not certified observations. The statements connect arbitrary binary observations satisfying those inputs to the estimators; no mission-level data are invented. T2 concerns the corrected unadjusted specifications (1) and (4), exactly as its canonical claim requires. It makes no assertion about adjusted regressions, a bound for each realized assignment, or conservativeness of expected standard errors.

All eight SAP Lean modules compiled with `/home/ubuntu/sap/tools/sap-lean`, in dependency order. `scratch/P036Axioms.lean` compiled and reported, for each of `SAP.P036.T1` and `SAP.P036.T2`, exactly `[propext, Classical.choice, Quot.sound]`.

`scratch/P036StatementIdentity.lean` separately loaded the Challenge and Solution environments and checked literal expression equality of both theorem types and their universe parameters. It also checked the types, bodies and universe parameters of all 34 shared SAP definitions, including the two statement definitions. All checks passed. This local check does not constitute Palomar certification.

`manifest.json` and `comparator.json` parse and agree on exactly the two proved theorem names. The comparator configuration contains the requested permitted dependencies and external-kernel commands. Every new file is below the 300-line limit; imports and forbidden-token placement were checked. Existing source and input files were not changed.

Palomar certification remains unrun: no comparator tool was exposed, and the comparator and external-kernel commands were unavailable on PATH. The configuration is ready for that separate run. Compilation emitted only the required Challenge-stub warnings and the advisory warnings for the two sigma-algebra definitions that intentionally are not typeclass instances.
