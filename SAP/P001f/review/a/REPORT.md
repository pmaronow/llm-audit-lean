# Referee report

19 targets: 18 theorem stubs and one omission.

| Verdict | Count |
| --- | ---: |
| correct_whole | 8 |
| correct_restricted | 8 |
| restriction_inaccurate | 2 |
| not_faithful | 0 |
| vacuous | 0 |
| false | 0 |
| omission_ok | 1 |
| omission_questionable | 0 |

Severity: 17 none, 2 minor, 0 major. No false or vacuous theorem statement was found. Both adverse findings concern the description of scope; the underlying assertions appear true.

## P001-T108 — restriction_inaccurate, minor

The canonical claim states the expectation, variance, and Chebyshev results for each fixed finite iid family. Its note explicitly says these are statements for each fixed n≥1. The theorem instead requires `IndependentCopies` for a sequence indexed by all natural numbers: see `SAP/P001f/Defs/Part4.lean:34` and the definition at `SAP/P001f/Defs/Part1.lean:34`.

This is an additional hypothesis about the family on its given probability space. A single fair Bernoulli draw is a valid n=1 iid family, but on its two-atom probability space there is no second independent equally distributed draw. `scratch/Check.lean` certifies the corresponding example on R with measure `(1/2) dirac(0) + (1/2) dirac(1)`: no `IndependentCopies` sequence can have its zeroth observation equal to the identity. The infinite-product Bernoulli model satisfies the theorem, so this is a scope restriction rather than vacuity. A construction on a larger probability space and transfer by equality of finite joint laws could recover the finite-family assertion, but that transfer is not part of this statement.

The architect's `whole` decision and null restriction are therefore inaccurate. The docstring at `SAP/P001f/Challenge/Part1.lean:92` does not disclose the added hypothesis.

Fix: mark the record `restricted` and append this docstring text:

> Restricted: assumes an infinite measurable iid sequence and proves the formulas for its positive-size initial segments. It does not state the formulas for an arbitrary fixed finite iid family on its original probability space or provide a transfer from such a family.

Alternatively state the same three conclusions using a finite iid family for each positive n.

## P001-T113 — restriction_inaccurate, minor

The record describes population integrability of `m(X)` as an added restriction that excludes correct-propensity cases with only the combined augmented score integrable through cancellation. The docstring at `SAP/P001f/Challenge/Part1.lean:130` makes the same exclusion claim.

However, `claims.json`, target P001-T113, `canonical_claim.note`, expressly states that integrability of the nuisance regression in case (ii) is implicit under footnote 2, p.45. Those cancellation-only cases are already outside the supplied canonical claim. In case (i), integrability of the correct respondent regression also follows from integrable Y, MAR, and uniform response positivity. The Lean statement includes the correct integrability premise and covers both canonical branches. Its claimed loss of canonical cases is inaccurate.

Fix: set the record to `whole`, with null restriction, and replace the restriction paragraph by:

> The nuisance regression m(X) is integrable in both branches, following the canonical claim's finite-expectation convention. Conditional means, correctness and overlap are interpreted as versions up to null sets.

The Lean statement needs no change. Both branches have concrete nonvacuity examples with the other nuisance incorrect; these are given in `findings.json`.

## Other decisions and validation

The eight other restricted decisions accurately disclose their omitted components or retained premise profiles. In particular, T111 accurately says that population integrability of the respondent regression is retained as a premise rather than derived; this premise is mathematically redundant under its MAR and overlap assumptions. The T102 negation retains the joint-density premise and admits a genuine counterexample with the covariate mean outside its support. T103 uses positive scales and an actual unbounded mixture likelihood. T104 has a normalized countable-mass counterexample with both arms in every cell. None relies on zero denominators, nonintegrable-integral defaults, infinite-toReal defaults, or empty quantification to establish its substantive claim.

T105's omission is justified on the visible record: the informational-completeness premise has no supplied formal predicate, and the credited negation is reported to lack the binary-treatment restriction as well. Negating that larger contract would not certify the printed implication's refutation. The underlying credited row and credit statuses were not inspected; the authorized material contains only their descriptions.

`reading.md` was saved before opening `claims.json`; `claim-stage.json` was saved and parsed before opening `record.json`. No claim-stage verdict was changed after reading the record. The final T102 witness uses a cutoff of 1/2 inside the gap, so it is differentiable even at positive-density support endpoints.

`/home/ubuntu/sap/tools/sap-lean scratch/Check.lean` completed successfully. It imports only `SAP.P001f.Defs`, and contains no `sorry` or added axiom. Its checks include nonempty positive cell masses, finite-law normalization and denominators, the two missing-data estimator values, a valid mixture parameter, a nondegenerate fair probability law, binary response, its constant-covariate propensity, constant conditional independence and conditional means, and the finite-sample extension obstruction for T108. Other nonvacuity witnesses and refutation constructions are spelled out mathematically in `findings.json`.

Python 3 successfully parsed both output JSON files and verified all required fields, the 18 theorem-to-target mappings, and exactly one finding for each of the 19 canonical target IDs.
