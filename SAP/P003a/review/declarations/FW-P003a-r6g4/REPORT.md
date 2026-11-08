All three declarations are **faithful, severity none**. The record's `whole`
decisions are correct, and the Challenge docstrings accurately describe the
statements. No step-2 assessment changed after reading the record.

The review followed the required order: `reading.md` was saved before opening
the claims, and `claim-stage.json` was saved before opening the record. Every
dependency listed in `closure.json` was read, including compiler-generated
structure operations, recursive helpers and auxiliary proofs. The certified
proofs were taken as given; the scratch checks below do not invoke any of the
three target theorems as evidence.

* **T21:** All five canonical clauses are present, including every attained
  maximum, all six members of the effect-minus-one numerator fiber, exactly
  the accepted effects 0 and 1/9, and both possible p-value-one witnesses.
  The exact p-value correctly weights treated type counts by the number of
  labeled assignments and includes ties. All relevant denominators are
  positive. Lean constructs the stated true population and a seven-unit
  assignment realizing the observation. An independent Python enumeration of
  binary-table completions and all 36 labeled assignments reproduces the 42
  populations, ten maxima and accepted set.
* **T22:** The corrected traversal advances through every treatment-outcome
  total at every effect. Its coverage equivalence and minimum-base/reuse
  decomposition express the complete canonical combinatorial assertion.
  Output membership uses the actual strict plus-one rank comparison and
  correlated reuse samples. Lean checks the legal two-unit table, both
  traversal supports and estimand-value sets, and proves that every constant
  statistic test has rank one. Thus the omitted value 2 is a genuine witness
  for the first-feasible-line reading. The docstring identifies that reading;
  it does not label the corrected claim false. A separate feasible four-unit
  example exercises two positive reuse steps.
* **T23:** The generic search clause allows arbitrary decisions and proves
  both strict cutoff properties and the necessary condition for any integer
  endpoint. The application uses Algorithm 4.4's ordinary Monte Carlo mean,
  chronological whole compatibility queries and a pool whose used indices
  are proved not to wrap. Positive balanced arms ensure a nonempty exact
  accepted set and an endpoint on the effect lattice. The conclusion is a
  necessary condition, as claimed. Lean supplies all input hypotheses for
  observation `(0,2,0,2)`, `K=1`, `alpha=1/2`, `epsilon=0`: distinct successive
  assignment slots produce queries `(1,accept),(2,reject)` and returned
  numerator 1. Independent exact enumeration confirms upper endpoint 1/4.

The universal assertions over realized samples and seeds include the outcomes
of independent uniform draws. Neither T22 nor T23 replaces independence with
dependent random variables to manufacture a refutation; neither makes an
additional distributional or accuracy claim. For the reuse implementation,
each positive type-group size divides `n!`, so uniform factorial residues
realize the prescribed Bernoulli choices. The corresponding moves match
equations (5.21)-(5.26) in the [paper, arXiv v2, PDF page 18](https://arxiv.org/pdf/2305.09906#page=18),
whose pagination differs from the journal version.

No junk value changes any asserted experimental meaning. Population reuse
subtractions are bounded, divisions used as probabilities or effects have
positive denominators, all list accesses are in range, and the real supremum
is taken over an explicitly nonempty finite accepted set. Total definitions
outside legal experiments add valid algebraic cases, without removing any
clause on the canonical domain.

Validation succeeded with:

* `/home/ubuntu/sap/tools/sap-lean scratch/Closure.lean`
* `/home/ubuntu/sap/tools/sap-lean scratch/Nonvacuity.lean`
* `python3 scratch/labeled_oracle.py`

The final JSON files were parsed and checked for exactly the three requested
declarations and fingerprints copied directly from `closure.json`.
