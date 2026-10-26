# Glossary

**Target:** one recorded claim or passage selected from a work, identified by `PNNN-Tk`; some passages make no separate mathematical assertion and receive no proof credit.

**Component result:** a target paired with a Lean declaration. One declaration can serve several targets.

**Credited:** a component result with status `proved` or `counterexample_proved` and an axiom record containing only the standard axioms. Credit does not certify the whole target or work.

**proved:** proves the component under its stated assumptions (for a corrected statement, the corrected version).

**counterexample_proved:** belongs to a refutation of the claim as recorded in its target, under its stated assumptions: proves the counterexample itself or a step of it; where the target states a specific reading of the printed text, the refutation applies to that reading.

**Conditional:** a result that assumes a published theorem as an explicit hypothesis. `conditional_on.hypothesis` is the fully qualified Lean name of the published-theorem premise taken by the declaration’s statement (following an explicit statement definition if necessary); `source` is the public citation verbatim for credited results and per-work results; highlights retain their curated citation or source explanation. Concrete universe arguments such as `.{0}` may be retained; strip them to locate the declaration.

**Helper:** a supporting declaration without independent target credit; helpers may be highlighted.

## Target kinds

- `headline_result`: a principal mathematical claim selected from the work.
- `result_touched_by_finding`: a claim or passage affected by a finding of the audit; the passage need not itself be a mathematical assertion.
- `counterexample`: a counterexample to the proposition specified in the target, under its stated assumptions and interpretation.
- `corrected_statement`: a corrected or narrower claim; its proof does not establish the broader printed claim.

## Areas

- `probability`: Probability.
- `asymptotic-statistics`: Asymptotic statistics.
- `randomization-inference`: Randomization inference.
- `experimental-design-and-estimation`: Experimental design and estimation.
- `survey-sampling`: Survey sampling.
- `interference-and-networks`: Interference and networks.
- `causal-identification`: Causal identification.
- `partial-identification-and-bounds`: Partial identification and bounds.
- `regression-and-variance-estimation`: Regression and variance estimation.
- `resampling`: Resampling.
- `optimization-and-computation`: Optimization and computation.
- `foundations`: Foundations.

## Highlight sections

- `top_25`: The most helpful results.
- `reusable_libraries`: Reusable libraries.
- `counterexamples`: Counterexamples and corrections.
- `mathlib_candidates`: Candidates for Mathlib.
- `further_useful`: Further useful results.

## Catalog fields

The schemas in [catalog/schema/](../catalog/schema/) specify the exact fields and types.

- `work_id`, `target_id`, `lean_name`: the triple identifying a component result.
- `target_kind`, `status`: the target classification and credited result status defined above.
- `module`, `file`, `line`: the importable module, repository-root source path and one-based declaration line.
- `conditional_on`: the Lean premise identifier in `hypothesis` and its public citation in `source`.
- `axioms`: the declaration’s axiom dependencies; allowed values are `propext`, `Classical.choice`, `Quot.sound`.
- `highlight_ids`: highlights that feature the declaration as a principal or related declaration.
- `work`: public title, authors, venue, year, type, DOI, arXiv identifier and citation.
- `overview`: curated overview, areas, key results, corrections and caveats for a work.
- `targets`: public target identifiers, kinds, headlines, locations, explanations, `credited` and results. `credited` is true exactly when results are nonempty; `excluded_associations` retains the public status and optional Lean name of excluded associations. `not_applicable` supplies no proof credit and is not a credited result status.
- `association`: highlight status and the work and target identifiers associated with its principal declaration.
- `sections`, `section`, `rank`, `group`: all highlight sections, the first section, optional top-25 rank and reusable-library group.
- `summary`, `statement`, `use`, `mathlib_relation`, `notes`: public highlight explanation and scope.
- `declaration`, `related_declarations`: principal and companion source locations and axiom lists.
- `counts`, `vocabularies`, `line_coverage`: totals, permitted labels and source-location coverage. `vocabularies.status_descriptions` defines the credited statuses. `counts.modules` counts library modules under `AronowAudit/`, excluding the root import module `AronowAudit.lean`.
- `files`: every repository file with `path`, `bytes`, `records` and optional `schema`. A JSON array counts its elements; a JSON object counts as one record; JSONL counts its lines; other files have a null record count.


`counts.targets` includes all 1,021 catalog targets; `counts.targets_credited` counts the 1,000 targets with a credited result. `counts.targets_without_credit` is 21. In this release their excluded associations have status `not_applicable`; an empty results array does not denote an unresolved Lean proof.
