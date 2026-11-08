P034: 5 whole, 0 restricted, 0 refuted, 0 omitted. All 5 Challenge statements
have proved counterparts in `SAP/P034/Solution.lean`. There are no open glue
tasks and no unused credited rows. Only P034-T1 through P034-T5 are packaged.

The canonical claims in `work.json` govern these decisions. Every credited
row has final status `ok`. T1 and T3 are already counterexample claims, so
their counterexamples receive decision `whole`, rather than `refuted`.

| Target | Clauses retained | Existing declaration used |
| --- | --- | --- |
| P034-T1 | All (i)-(ix): normalized positive finite law; randomized assignment and overlap; zero unit and population effects; equal completion rates; outcome-dependent completion; biased complete-case means; the displayed Gram matrix, right-hand side and determinant; unique real population OLS solution; the 400-record sample, its positive observed-cell probabilities, count table, expected counts, zero Pearson statistic, p-value one and unique real sample OLS solution; the second population and matching observed-data probabilities with a different population effect. | `AronowAudit.P034.missingness_counterexample` |
| P034-T2 | All (a)-(e), with the canonical measurability, second-moment, randomization, overlap and independent positive completion assumptions: positive completed-arm probabilities, respondent overlap, arm means and their contrast, covariate laws and orthogonality, identification for every normal-equation solution, unique existence under nonsingularity, and the fixed failure of equal completion rates to imply identification. | `AronowAudit.P034.corrected_complete_case_identification` |
| P034-T3 | All (i)-(iii): the unique saturated interpolation and both zero reference contrasts versus the two equally weighted contrasts of one. | `AronowAudit.P034.factorial_counterexample` |
| P034-T4 | All (i)-(v): both general conditional contrasts, all four binary specializations, both weighted averages, both exact equality characterizations and both positive-weight characterizations. | `AronowAudit.P034.corrected_factorial_contrasts` |
| P034-T5 | All (i)-(iv): the count additions, both exact ratios and rounding intervals, correctness of the repaired roundings, failure of both printed roundings, all 39 repaired category cells, all 13 row totals and all three column totals. The exported response-slot identity is also retained. | `AronowAudit.P034.corrected_oa3_table` |

The package uses the shared Defs route. Five Defs parts import only Mathlib
and earlier Defs parts; the root imports those parts. The Challenge part
imports only `SAP.P034.Defs`, and the Challenge root imports only that part.
Neither imports project modules or the Solution. Both theorem modules use
the same compiled definitions, including the `T1Statement` through
`T5Statement` propositions.

`SAP/P034/Bridge.lean` supplies the correspondences. `toAudit` copies the
four fields of the SAP survey structure into the project structure. Both
concrete-model equalities, both bundle equalities, all finite-fact and
identification equivalences, and all fitted-function and table-definition
equalities are proved by reflexivity. The Solution instantiates the
credited T2 row with that adapter and transports its conclusions. T3-T5
use the credited rows after only the definition equalities.

For T1, finite probabilities, moments and independence are expressed by
exact rational finite sums and factorization identities, as in the
credited declaration. Boolean values encode binary outcomes and covariates.
The real normal-equation matrices and vectors are the entrywise rational
embeddings. `Bridge.normal_equations_cast` transports the exported solution
using Mathlib's multiplication map and the exported nonzero determinant
using its determinant map, then applies Mathlib's matrix injectivity result.
The sample determinant is nonzero by the exported identity
`sampleGram = 200 • witnessGram`, the determinant scaling identity and the
exported determinant `1/16`. Thus both uniqueness quantifiers range over
real coefficients. This is scalar transport of the existing system, with
no new statistical or identification argument and no new enumeration of
the witness.

The finite-law positivity, positive outcome strata and positive completed
arm probabilities are retained. Every conditioning event in the witness
is a nonempty union of those positive cells. Pearson expected counts are
100, and all three table denominators are positive printed constants.
The chi-square reference uses the upper tail of the square of a standard
Gaussian probability measure. For T2, the canonical L2 assumptions ensure
the moments exist; H1/H2 give positive conditioning events and respondent
overlap. No additional identifying assumption or theorem is made a premise.

The counterexamples concern the logical justification for analysis and
the interpretation of model coefficients. They make no assertion of bias
in the actual surveys and do not refute the recorded empirical estimates.
T4 packages the explicitly designated mathematical contrast algebra; the
empirical sentence about the reported intervals and the replication
program's behavior are context, as specified in the target. T5 concerns
the transcribed response-slot counts and the target's half-open rounding
convention.

All Defs parts and their root, Bridge, Challenge part and root, and Solution
compiled with `/home/ubuntu/sap/tools/sap-lean` in dependency order. The only
unfinished-proof warnings were the required Challenge stubs. The scratch
file `scratch/P034/PrintAxioms.lean` checked all five Solution theorems:
each depends exactly on `propext`, `Classical.choice` and `Quot.sound`.
The two JSON files parse, and all listed theorems have status `proved`.
All SAP files are at most 300 lines and have both required implicit-variable
options immediately after their imports. Existing project files were not
modified.

The Comparator configuration is provided at `SAP/P034/comparator.json`.
The Palomar Comparator and the external kernels were not run in this
session; their executables were not available on PATH. Compilation and
the permitted-axioms checks passed, but external certification is not
claimed.
