# Review of P032 declarations

All five declarations are **faithful**, with severity **none**. T11 is faithful
to its accurately disclosed restriction; it is not a whole rendering of its
canonical claim. No step-2 conclusion changed after reading the record.

| Declaration | Comparison with canonical claim | Record and docstring |
| --- | --- | --- |
| `SAP.P032.T4` | Covers the common-score decomposition, exhaustive coefficient count, subject-id discrepancy, arbitrary real scaling, and record-level repair. Unused members are allowed as the canonical definition permits. The universally quantified scaling factor includes the asylike expression by substitution. | `whole` is correct. No claim of executing the software repair or rerunning analyses is made. |
| `SAP.P032.T2` | Covers the actual OLS contrast variance on arbitrary probability spaces, omitted ordered-pair sum, every sign equivalence, both PSD characterizations, and bounded sign witnesses. | `whole` is correct; the docstring describes population orderings without promising an ordering of realized residual estimates. |
| `SAP.P032.T11` | States the unadjusted OLS residual-sandwich decomposition with the exact member, repeated-dyad, and record masks. Full rank and occurrence of every counted member match the claim. | `restricted` is correct. Both record and docstring list the omitted pointwise identity, multiway equivalence, software assertion, standard-error rule, and clipping assertion. |
| `SAP.P032.T7` | Covers genuine spectral clipping, its quadratic formula, PSD and fixed points, the exact gate criterion, the two-by-two criterion, and the specified ten-record rank-one example. | `whole` is correct; the docstring describes precisely these assertions. |
| `SAP.P032.T12` | Covers the covariance correction, the five-primitive additive model, and both strict and both equality cases. Pairwise zero covariance is explicitly sufficient in the canonical statement. | `whole` is correct; the docstring accurately states the finite-variance setting. |

The blind reading was saved in `reading.md` before opening the claims. Every
closure definition was inspected, including the types of all 128 distinct
closure entries; generated auxiliary proofs only supply literal bounds, dyad
cardinalities, or normalized weights. `claim-stage.json` was saved before the
record was opened. Claims were assessed from their statements, definitions and
standing assumptions, without using audit-history notes to remove clauses.

All three independent scratch files compile with `sap-lean`, importing only
`SAP.P032.Defs`:

- `scratch/AlgebraChecks.lean`: all four incidence cases, a nonzero subject-id
  discrepancy, every T11 hypothesis with nonzero residuals, nontrivial clipping,
  positive-diagonal indefiniteness, the exact ten-record covariance, genuine
  bread and residuals, and a strictly positive eigenvalue discriminant.
- `scratch/ProbabilityChecks.lean`: a nondegenerate centered finite probability
  model satisfying every T2 hypothesis, and a T12 model with positive shared
  variance and actual variance comparisons in both strict directions.
- `scratch/SurvivalChecks.lean`: actual record, id, dyad and member component
  values of T4's fixed survival example, including both incorrect subtractions.

There are no contradictory or conclusion-assuming hypotheses. The OLS
nonsingularity hypotheses exclude singular-inverse defaults. The L² hypotheses
express the canonical finite-moment conditions and exclude nonintegrable
Bochner integrals and infinite variances converted to zero. All fixed
denominators are nonzero, cardinality subtraction is in the reals, and the
spectral example uses square roots within their domain. Empty type instances
do not trivialize the assertions: the compiled witnesses use nonempty types
and nonzero scores, residuals or shared variance. No target is labelled
`refuted`, and none relies on refuting an alternative reading of printed prose.

`findings.json` contains exactly the five requested declarations and their
unchanged closure fingerprints. No package source was edited.
