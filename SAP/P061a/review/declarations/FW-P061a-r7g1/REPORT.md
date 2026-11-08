All five declarations are faithful to their canonical claims. The five `whole`
decisions in `record.json` are accurate; no correction or restriction is needed.

| Declaration | Result | Principal checks |
|---|---|---|
| SAP.P061a.T1 | faithful, none | All clauses (a)–(g), both raw hybrid readings, hidden-version obstruction, exact HT moments and tail bound. |
| SAP.P061a.T2 | faithful, none | Exact exposure image, positive cells and stability, both domain obstructions, genuinely independent repeated pairs at every positive even population size. |
| SAP.P061a.T3 | faithful, none | Both comparison alternatives, targeted moments, independence from the whole remaining vector, positive-mass hybrid feasibility, unit and population identities. |
| SAP.P061a.T4 | faithful, none | Full binary-cube encoding, the actual product law, both graph degrees, every finite clause (a)–(f), variance formulas, coverage bounds and population-normalized limits. |
| SAP.P061a.T5 | faithful, none | Actual AEED/ADE transfer, both coverage limits at continuity endpoints, shifted-law alternative, rate counterexample, full local range-times-TV bound and rate sufficiency. |

`reading.md` was saved before opening the claims; `claim-stage.json` was saved
before opening the record. Every declaration in each closure was inspected,
including Lean's generated numeral helpers. Reading the record caused no change
to a claim-stage conclusion. T5 uses `T5WholeStatement_W2`, as its elaborated
closure specifies.

The definitions match the standing discrete design setting. Nonnegative
summable masses totaling one give ordinary atomic probabilities; targeted
absolute moments give ordinary conditional means. The hypotheses or conclusions
guard all relevant divisions and sums. T3's infeasible-hybrid zero default has
no positive-mass contribution. T4 excludes the exceptional small parameters
from its numerical assertions. T5 requires attained range extrema, finite local
support, positive conditioning probabilities, and almost-sure hybrid feasibility;
its limiting interval measure is finite. Consistency makes nonpositive estimated
scales negligible. No placeholder, conclusion-as-hypothesis, vacuity, or material
junk value was found.

The counterexamples agree with their canonical assertions. T1's reading is the
raw-coordinate comparison under the allowed coarsened exposure mapping; its
uniform independent ternary design has bounded, own-coordinate responses and
positive exposure cells. T2's reading is membership of the displayed hybrids in
their stated domains; its uniform independent pairs satisfy positivity and
stability. These items are correctly `whole`, and their docstrings identify the
interpretations contradicted. T4 certifies the canonical bounded-degree
construction with individualistic exposures, finite moments, positive cells,
independent pairs and feasible replacements. No item claims a refutation of its
own canonical assertion.

For T2, repeated pairs give full-vector raw-domain success probability
`(1/2)(1/4)^(K−1)` (Defs/Part4.lean:48), preserving the domain failure in
canonical clause (e). That clause's “same holds” concerns persistence of the
obstruction; the original pair's probability `1/2` does not remain the success
probability for the entire larger vector. For T3, requiring a total `H` merely
extends its relevant-domain values arbitrarily. For T5, the canonical
`finite_lemmas` add no conclusions: complete-randomization refinements and
attainment of the TV bound are not missing clauses.

Independent checks compiled successfully with the supplied `sap-lean` wrapper:

* `scratch/ClosurePrint.lean`: printed all generated closure helpers and the
  design constructor/projection.
* `scratch/FiniteWitnesses.lean`: normalized uniform and product families,
  the version witness, adjacent-pair cells and image points, full support of
  the correlated-pair family, and exact pair covariance/variance at `m=2`.
* `scratch/UniversalNonvacuity.lean`: all hypotheses of both T3 alternatives,
  and simultaneous population, law, scale, local-bound and rate hypotheses
  for T5, with distinct target labels.

These scratch checks use definitions without invoking the Challenge theorems.
The certified proofs were taken as given; the audit checks their statements.
