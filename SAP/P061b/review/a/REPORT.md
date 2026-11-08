Audited 10 targets and 10 theorem stubs. The blind readings were saved in
`reading.md` before opening `claims.json`; `claim-stage.json` was saved before
opening `record.json`. No step-2 classification was changed after reading the
record.

| Verdict | Count |
| --- | ---: |
| correct_whole | 8 |
| correct_restricted | 2 |
| restriction_inaccurate | 0 |
| not_faithful | 0 |
| vacuous | 0 |
| false | 0 |
| omission_ok | 0 |
| omission_questionable | 0 |

Severity counts: none 10; minor 0; major 0. There are no adverse findings and
no omitted targets.

The `correct_whole` verdict for P061-T16 accepts the architect's **refutation**
of the canonical unrestricted unbiasedness assertion. It does not affirm that
positivity guarantees an ordinary expectation. A countably supported geometric
design with alternating, unbounded finite outcomes satisfies positivity but has
no HT first moment. Both signs have infinite weighted total, so this is an
existence failure within the canonical standing assumptions, as the docstring
states. It does not rely on assigning zero to a divergent Mathlib sum.

The two restrictions are accurate and fully disclosed:

* P061-T17 retains the equal-margin identity and the experiment on the binary
  cube. It omits the entire general survey unbiasedness assertion, including
  the census, and the extension of the experiment to larger feasible sets with
  additional zero-mass interventions.
* P061-T19 retains the joint-positive unbiased estimate, its expectation
  formula, the conservative estimate, and Young's inequality. It omits the
  quoted impossibility assertion about unbiased estimation of a missing
  product. The quote is part of the canonical statement; its omission is
  acknowledged explicitly.

The remaining statements preserve their canonical scope. In particular,
P061-T20's moment assumptions implement the explicit existence clause in
`definitions_needed`, rather than importing a restriction from audit history.
In P061-T18, setting the second exposure equal to the first recovers the
single-exposure formulas with only their canonical positivity hypothesis.
P061-T21 retains every printed asymptotic condition and uses positive
population denominators.

Independent Lean checks succeeded using the prescribed `sap-lean` tool and
imports of Defs only:

* `scratch/FiniteChecks.lean` proves the complete finite T14 and T15
  propositions, positive margins and joints, a normalized completely
  randomized design, an unstable-outcome adjustment instance, concrete
  nonzero-variance and zero-joint conservative-estimate computations, and
  simultaneous satisfaction of all T21 premises.
* `scratch/T16Counterexample.lean` constructs the geometric design and proves
  the exact negation of `GeneralHTUnbiased` independently of the Challenge
  stub.

Nonvacuity instances and target-specific assessments are in `findings.json`.
The general variance and consistency statements were assessed from their
definitions and mathematical implications; the checks above are independent
examples, not a certification of every theorem's proof.
