# Statement referee report: P029a

All 13 canonical targets have Challenge declarations. The result is **8
`correct_whole` and 5 `correct_restricted`**, with no substantive defects.

| Verdict | Count |
| --- | ---: |
| `correct_whole` | 8 |
| `correct_restricted` | 5 |
| `restriction_inaccurate` | 0 |
| `not_faithful` | 0 |
| `vacuous` | 0 |
| `false` | 0 |
| `omission_ok` | 0 |
| `omission_questionable` | 0 |

Severity counts: none 13, minor 0, major 0. There are no items requiring a
corrected statement or docstring and no omitted targets.

## Audit sequence

1. Read all Defs and Challenge files and the relevant Mathlib definitions;
   saved `reading.md` before opening either JSON input.
2. Read `claims.json`, including the complete standing assumptions, canonical
   statements and `definitions_needed`; saved `claim-stage.json` before opening
   `record.json`. Audit-history notes were not used to remove clauses.
3. Read `record.json` and checked its declared decisions/restrictions against
   the expanded statements and Challenge docstrings. No step-2 classification
   was changed after reading the record.

## Assessment of every record decision

| Target / theorem | Referee verdict | Record assessment |
| --- | --- | --- |
| P029-T1 / SAP.P029a.T1 | `correct_whole` | The specified six-atom law includes the full potential-pair independence and all means and Wald values. Its receipt-ignorability/latent-ignorability contrast identifies the implication being refuted. |
| P029-T2 / SAP.P029a.T2 | `correct_whole` | The record accurately describes the additional explicit premises, but its `restricted` label is conservative: those premises are redundant under canonical part (c), as shown below. Both incomparability witnesses are retained. |
| P029-T3 / SAP.P029a.T3 | `correct_whole` | Both independence readings and all specified finite witness quantities are represented; the docstring identifies the marginal and conditional readings. |
| P029-T4 / SAP.P029a.T4 | `correct_restricted` | The record and docstring correctly retain the finite-support population identities and sufficiency results while omitting sample consistency/convergence in the canonical corrected prose. Finite support is already canonical. |
| P029-T5 / SAP.P029a.T5 | `correct_whole` | Both 500-row inputs, actual cross-products, determinant and coefficient recovery are represented. The benchmark uses the canonical latent covariates; the regression uses the separately specified observed noise covariates. |
| P029-T6 / SAP.P029a.T6 | `correct_whole` | Every positive replicate count, constant sample/population/complier effect, benchmark moment and error-discrepancy identity is represented. The explicit admissible inputs supply both signs. |
| P029-T7 / SAP.P029a.T7 | `correct_restricted` | The record and docstring fully disclose that scores and rates are prescribed, their fit interpretations and nested-probit realizability are omitted, and the derivative is not certified as a refitting effect. The objective statements and numerical evaluations remain correct. |
| P029-T8 / SAP.P029a.T8 | `correct_restricted` | The general and three concrete free-cell fits are certified. The record and docstring disclose the missing identification with finite-coefficient probit fits and the omitted nonconstant-weight comparison of package/corrected probit minimizers. |
| P029-T9 / SAP.P029a.T9 | `correct_restricted` | The nine-cell completions, pooled counts, both association directions, arbitrary outcomes, compatible raw codes and assignment support are retained. The record/docstring accurately omit the standalone count-sign identity, independent source-data summaries and unknown-code subdivision, and source-file validation. |
| P029-T10 / SAP.P029a.T10 | `correct_restricted` | The record/docstring disclose the empirical corrected-prose omissions and absence of raw-string preservation. The rate calculations, binary counts, completions and covariance decomposition are correct. Positivity of the distinguished group is explicitly stated. |
| P029-T11 / SAP.P029a.T11 | `correct_whole` | Both constant-effect SEM laws include the asserted moments; neither correlation uses a zero variance. The counterexamples address the specified SEM-to-IV inclusion. |
| P029-T12 / SAP.P029a.T12 | `correct_whole` | Both SEM witnesses, the common-error/common-covariate potential-outcome identity and the heterogeneous IV witness establish the two failed inclusions. ATE, LATE, effect masses and first stage are retained. |
| P029-T13 / SAP.P029a.T13 | `correct_whole` | The closed receipt-probability triangle and natural-power boundary convention are expressly canonical. Maximality, fit values, polynomial bounds, finite-sample bias and the five-per-arm enumeration are represented. |

### Why T2 has no mathematical loss of scope

Canonical part (c) assumes D0=0 almost surely, so the defier event has measure
zero. At its selected covariate profile x,

`P(C) >= P(C and X=x) = P(X=x)c(x) > 0`.

Random assignment and one-sidedness imply

`E(D|Z=1) - E(D|Z=0) = P(C) > 0`.

Thus the no-defier and global-relevance components retained inside
`IVConditions` follow from the canonical premises. The remaining components
render the same measurability, outcome integrability, random assignment and
assignment positivity already in the canonical statement. The Challenge
docstring accurately describes its premise packaging. The saved `whole`
classification therefore stands; this is a semantic assessment, not a change
made in response to the record.

## Definition and nonvacuity checks

The finite means use ordinary real division, which is zero at a zero
denominator in Lean. In the actual finite witnesses all conditional events and
Wald denominators used for substantive conclusions are positive. In T4,
positive compliance on each positive-mass covariate cell and finite support
give positive complier/weight denominators; null covariate cells contribute
zero only on null sets. Finite covariate weights preserve outcome
integrability. The SEM examples have strictly positive instrument and error
variances.

The population identities either assume integrable potential outcomes or L2
functions, or integrate an identically constant function after cancellation.
In particular unrestricted baseline functions in `ConstantPopulationEffect`
do not invoke the nonintegrable-integral fallback. The logarithm identities
use positive arguments; zero weights use the expressly defined extended
objective. T13's boundary likelihoods use the canonical `0^0=1` convention.
The design determinant and positive-weight nonsingularity prevent the
matrix-inverse fallback from doing any work.

`scratch/Nonvacuity.lean` compiled successfully with
`/home/ubuntu/sap/tools/sap-lean scratch/Nonvacuity.lean`. It supplies an actual
fair-Bernoulli, constant all-complier population satisfying the complete
one-sided premise bundle and both T4 joint-independence alternatives; a
nonempty two-cell likelihood model with positive success/failure totals; and
a nondegenerate finite binary-count model. Its only compiler messages were
deprecation/unused-variable warnings. The file imports Defs and contains no
`sorry` or added axioms.

`python3 scratch/exact_checks.py` also passed. Its independent rational
computations check normalization and independence in the finite laws,
positive conditioning/Wald denominators, weighting ratios and free-cell
totals, the noise design determinant and actual cross-products, both race
association directions, SEM exogeneity/endogeneity moments, and the four-atom
and 36-atom score-bias enumerations. It deliberately uses division that raises
on zero. `scratch/exact-results.json` records the passed check groups.

For the universal benchmark-moment hypotheses an explicit model is the
product of 3n Uniform(-1,1) measures with coordinate projections, for any
n>0. The L2 error identity admits constant t=B=5. The grouped decomposition
admits any nonempty finite partition with a positive distinguished group.
The raw-code compatibility premise admits codes W/B on known White/non-White
cells and missing codes on the other cells. Detailed per-target nonvacuity
instances are in `findings.json`.

## Items requiring correction

None. Both output JSON files parse, contain each of the 13 target IDs exactly
once, and agree on theorem names and substantive scope.
