# P010 statement audit

Audited all 23 targets and all 23 Challenge stubs. The blind reading is in
[reading.md](reading.md); the comparison saved before opening `record.json`
is in [claim-stage.json](claim-stage.json). No step-2 classification was
changed after reading the record. The per-target verdicts, fixes,
nonvacuity instances and confidence are in [findings.json](findings.json).

| Verdict | Count |
| --- | ---: |
| correct_whole | 20 |
| correct_restricted | 1 |
| restriction_inaccurate | 0 |
| not_faithful | 2 |
| vacuous | 0 |
| false | 0 |
| omission_ok | 0 |
| omission_questionable | 0 |
| **Total** | **23** |

Both adverse findings have **major** severity. No target is omitted.

## P010-T21 — not_faithful

`SAP.P010.T21` asserts an existential inequality between totalized
`meanOn` values without requiring that either selected conditional
outcome mean or the conditional effect mean exists. The canonical claim
uses ordinary conditional expectations; the standing assumptions explicitly
require each displayed conditional mean to exist.

The precise gap is at `Defs/Part4.lean:115–119`, using the definition at
`Defs/Part3.lean:25–30`. Mathlib's Bochner integral returns zero for a
nonintegrable integrand. Consequently this stub admits a witness whose
inequality is solely an artifact of assigning zero to undefined means.

For example, let H be standard Cauchy, independent of fair assignment,
put Y0=H and Y1=H+1, and make both checks always true and X=0. Every
written hypothesis holds, including common check status, all-pass mass
one, and check/assignment independence. Both selected restricted
integrands are nonintegrable, so both `meanOn` values are zero, while
the integrable constant effect has mean one. The asserted inequality
becomes 0−0≠1 although the ordinary selected means do not exist.

The record's restriction and `Challenge/Part1.lean:91–97` accurately
disclose the literal total-function assertion. The architect's decision
still fails the requested fidelity test: changing conditional expectation
to a total function admits nonintegrable-integral artifacts. An assertion
about such values does not establish the canonical counterexample with
existing conditional means. This verdict concerns the statement's meaning;
the literal Lean proposition is true and has genuine bounded witnesses.

**Fix:** require integrability of `response` under each selected-arm
restriction and of `potentialOutcome 1 - potentialOutcome 0` under the
all-pass restriction for the same existential measure. Use
`selectionPopulation (1/2)`: its selected means are 0 and 1/2, its mean
effect is zero, and its all-pass mass is 1/3. Replace the current
totalization docstring with an assertion about ordinary conditional means.
The full corrected conditions and replacement text are in `findings.json`.

## P010-T23 — not_faithful

`SAP.P010.T23` has the same representational gap on the covariate-restricted
events, at `Defs/Part4.lean:128–135`. It requires positive all-pass-and-X=0
mass, covariate ignorability and balance, but requires no integrability of
the three displayed conditional-mean integrands.

The preceding Cauchy model, with X identically zero, also satisfies every
hypothesis of this stub and gives the totalized inequality 0−0≠1 with
undefined ordinary selected means. Thus the statement does not certify
the canonical finite-mean covariate-balance counterexample.

The restriction in the record and `Challenge/Part1.lean:103–109` accurately
describes this altered total-function assertion. Fixing two arms and a
constant scalar covariate is a valid way to give an existential witness.
Permitting nonintegrable outcomes changes the conditional-mean notion and
fails the stated audit rule.

**Fix:** require integrability of `response` on each selected-arm-and-X=0
event and of the potential effect on the all-pass-and-X=0 event for the
same existential measure. Again `selectionPopulation (1/2)` is a bounded
witness with contrast 1/2, effect zero and all-pass-and-X=0 mass 1/3.
Remove the totalization restriction from the docstring. Full corrected
conditions and replacement text are in `findings.json`.

## Accepted restriction and other record decisions

P010-T12 is `correct_restricted`. It retains Bayes identities, reciprocal
transport, scale cancellation and the entire finite-normalizer
printed-odds clause. It drops exactly the final assertion about infinite
squared-density-ratio mass, as both the record and the Challenge docstring
say. Integrability of that a.e. measurable nonnegative ratio expresses the
canonical finite-normalizer premise; it adds no such condition to the
reciprocal transport clauses. A strictly positive two-cell example realizes
all the retained branches.

The other 20 `whole` decisions agree with the independently saved readings.
In T4–T6 the focal passer integrability transfers under ignorability to the
potential outcome on its passing event, and hence to its all-pass subset
in every compatible population. Omitting a separate integrability field
from `compatiblePopulations` therefore does not create the T21/T23 problem.
The empirical binary subtractions are the required finite-count
truncations with positive retained counts. Extended-real essential
endpoints retain infinities without an unbounded-real-limsup convention.

## Verification and limits

* [scratch/Check.lean](scratch/Check.lean) compiles with the permitted
  `sap-lean` wrapper and imports only `SAP.P010.Defs`. It checks a nonempty
  probability population, ignorability, positive passing, common checks,
  integrability, the literal nonintegrable-integral convention, and the
  zero-quantile endpoint. It also proves that **every** real-valued function
  is integrable under `selectionPopulation q` for every q, and derives the
  missing restricted-integrability certificates independently of any
  Challenge theorem. Thus supplying these certificates for the intended
  witness is feasible.
* [scratch/audit_numeric.py](scratch/audit_numeric.py) passes exact rational
  checks for all trimming ranks, empirical endpoints and gaps, the finite
  independence counterexamples, beta/heavy-tail moments and truncated
  means, and finite transport arithmetic. Its normal-mixture calculations
  are explicitly floating-point sanity checks: they reproduce widths
  1.7985772989680666 and 1.767983385221887 but do not independently certify
  the rational enclosures.
* [scratch/totalization.md](scratch/totalization.md) gives the analytic
  Cauchy artifact and verifies all its hypotheses. This analytic example
  was not formalized in Lean. It identifies a missing semantic guarantee,
  rather than refuting either literal existential proposition.
* Nonvacuity instances are supplied separately for every target in
  `findings.json`. Universal claims have actual nonempty models, including
  both trimming branches and nonconstant covariates for T22. No hypothesis
  was found to assume its conclusion.
* The supplied canonical text was compared with the published
  [paper](https://www.cambridge.org/core/services/aop-cambridge-core/content/view/E92D1CFA434028679E0C156AE58D5EAB/S1047198719000056a.pdf/a-note-on-dropping-experimental-subjects-who-fail-a-manipulation-check.pdf).
  Raw data and external formalization proofs were not inspected; the
  empirical counts are audited as supplied inputs. No `lake` command was
  run, and Lean checks ran one process at a time.

Both output JSON files were parsed and checked for complete, duplicate-free
target coverage using Python.
