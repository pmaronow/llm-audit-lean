# P033 statement audit

| Verdict | Count |
| --- | ---: |
| correct_whole | 12 |
| correct_restricted | 3 |
| restriction_inaccurate | 0 |
| not_faithful | 0 |
| vacuous | 0 |
| false | 0 |
| omission_ok | 3 |
| omission_questionable | 0 |
| Total targets | 18 |

No adverse findings. All 18 architect decisions agree with the audit. No
step-2 verdict was changed after reading the record.

The three restrictions are accurate and disclosed in the challenge docstrings:

* **P033-T1:** omits the four one-side probabilistic variance/covariance
  identities; retains the deterministic certificates and both full-estimator
  probability calculations.
* **P033-T2:** omits an explicit higher-differentiability assertion; retains
  the exact polynomial definitions, continuity and every coverage and
  nonidentification conclusion.
* **P033-T5:** adds nonzero treatment discontinuity and positive standardizing
  SD to the general count-scaling clause; retains the entire concrete witness.

Omissions P033-T16–T18 are justified. They concern diagnoses of particular
studies, reported summaries and implementation descriptions. The supplied
mathematical witnesses do not prove or refute those empirical assertions in
full. Their separately specified mathematical content is covered by the
earlier targets.

## Scope and definition checks

The audit used each canonical `statement` together with `definitions_needed`
and the standing assumptions. Notes and finite-lemma histories did not add or
remove clauses. The [journal article](https://journals.sagepub.com/doi/10.1177/20531680231166457)
was consulted for the main-text notions of identification, inference,
standardization and the caliper benchmark. Supplement and replication-file
provenance was assessed as supplied in the canonical material; those empirical
premises were not independently reconstructed.

The Gaussian parameter in Mathlib is variance. Every probability calculation
here uses a probability law, a normalized density, or a nonempty finite
uniform space. Second-moment hypotheses or explicit bounded/Gaussian models
justify moment integrals. Conditional probability denominators are explicitly
positive. Sample variance denominators have sample size at least two. The
normal quantiles used are finite interior quantiles; honest half-length
infima are over nonempty sets bounded below. Concrete natural subtractions
do not truncate negative quantities. Empty types, infinite-measure-to-zero
conversion and nonintegrable-integral defaults do not generate the results.

T4 uses normalized positive-weight coordinates. They are exactly the physical
scores divided by bandwidth 1/n in the canonical shrinking construction;
exterior records have zero weights. This removes irrelevant coordinates
without changing its statistics or limit.

The M1/M2 witnesses address pointwise calibration and nonidentification from
estimator comparisons. They do not establish uniform model-class validity or
falsify the empirical diagnosis. The caliper witnesses address the finite-window
equal-mass interpretation under absence of selection. The funnel witness
directly contradicts the stated slope, while its variance/SD example merely
distinguishes two standardization readings. The architect uses `whole` or
`restricted`, with no `refuted` label or assertion that these witnesses falsify
broader printed empirical claims.

## Validation and artifacts

The blind reading was saved before opening the claims. The claim-stage file
was saved and parsed before opening the record.

* [reading.md](reading.md): mathematical expansion of every theorem, including
  hypotheses, quantifiers, coefficient certificates and Mathlib conventions.
* [claim-stage.json](claim-stage.json): unchanged step-2 assessments, 12 whole
  and 3 narrower.
* [findings.json](findings.json): one final finding for each of the 18 targets.
* [scratch/Nonvacuity.lean](scratch/Nonvacuity.lean): successfully compiled with
  `/home/ubuntu/sap/tools/sap-lean scratch/Nonvacuity.lean`, importing only the
  definitions. It checks a genuine Gaussian product probability law, positive
  SEs, the nonempty sign space, a Gaussian HasLaw instance, a normalized
  nonnegative density supported on [0,4], and nonempty cell/scaling examples.
* [scratch/audit_checks.py](scratch/audit_checks.py) and
  [scratch/check-results.json](scratch/check-results.json): passing independent
  exact rational checks of coefficients, WLS equations, Gram determinants,
  binary/count examples, binomial tails and table arithmetic; exhaustive
  enumeration of all 1,024 pure-cluster outcomes; finite-n shrinking-design
  checks; and 90-digit numerical checks of all delicate normal-power,
  folded-normal, quantile and bias-half-length enclosures.

These checks support the statement review; the numerical calculations are
not formal certificates of the analytic theorems. The supplied challenge
stubs were not treated as proofs. No solution or comparator files were read,
no `lake` command was run, and at most one Lean process was active at a time.
