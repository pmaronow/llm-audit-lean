# P010 statement referee report

Audited all 23 targets, with one Challenge theorem for each. No target is omitted.
The blind reading was saved before opening `claims.json`; `claim-stage.json`
was saved before opening `record.json`. No step-2 verdict was changed after
reading the record. Only the supplied definitions, challenges, claims and record,
and the permitted Mathlib sources were inspected; no Solution or Comparator
proofs were used.

| Verdict | Count |
| --- | ---: |
| `correct_whole` | 19 |
| `correct_restricted` | 1 |
| `restriction_inaccurate` | 0 |
| `not_faithful` | 3 |
| `vacuous` | 0 |
| `false` | 0 |
| `omission_ok` | 0 |
| `omission_questionable` | 0 |

Severity: 20 none, 1 minor, 2 major.

## P010-T15 — not_faithful, minor

The substantive finite-branch upper bound is correct. The separate equality
between the potential and observed upper-tail means, however, is stated
**without** the finite-branch guard. See `Defs/Part6.lean:205`; the implication
on the next line guards only the final two conclusions. The record calls this
whole, and the docstring does not disclose an extension of the meaning of a mean.

Take `boundedPasserPopulation`. Every hypothesis of T15 holds: there is positive
always-passer mass, the observed law is atomless, and the selected response is
integrable. Both pass rates are 1/3 and the trimming ratio is 2. The passer law
is Beta(3,3). Its defined quantile at 2 is +infinity, so the two upper-tail
events are empty and the stated equality is 0=0 through `meanOn`'s zero-mass
convention. These are not existing ordinary conditional means, as required
by the canonical standing assumptions. The generic facts about quantiles
and totalized tails above probability one are separately Lean-checked.

**Fix:** put the tail-mean equality inside `trimmingRatio μ a < 1 → ...`,
alongside the corrected upper bound. Keep the distribution and trimming-share
identities unconditional. `findings.json` gives the replacement conclusion and
docstring text. This repairs a domain-rendering defect, not a false finite bound.

## P010-T21 — not_faithful, major

The exported existence statement has no integrability requirement on either
selected-arm outcome or on the always-passer effect (`Defs/Part4.lean:115–119`).
Under `meanOn`, a nonintegrable restricted Bochner integral is zero. The canonical
claim assumes the displayed ordinary conditional means exist.

An extraneous formal witness demonstrates the difference. Let U be standard
Cauchy, set Y₀=U and Y₁=U+1, let both potential checks always pass, set X=0,
and independently assign each arm with probability 1/2. All stated probability
conditions hold. Both selected responses are nonintegrable, so their totalized
means are zero; the unit effect is identically one and has ordinary mean one.
The formal inequality is therefore 0≠1, with **everyone passing** and no ordinary
selected means. This does not refute the printed equality on its meaningful domain.

The record and docstring disclose the missing finite means accurately in a literal
sense. That disclosure does not turn a changed notion of expectation into a
restriction of the canonical claim; it violates the audit's exclusion of
nonintegrable-integral conventions doing the work. The statement is formally
true, and a proper finite witness exists, so the verdict is neither false nor vacuous.

**Fix:** add integrability of `response` on each selected-arm event and of
`potentialOutcome 1 - potentialOutcome 0` on `allPass`. Replace the restriction
with a statement about finite ordinary means. The supplied
`selectionPopulation (1/2)` already supplies the genuine contrast 1/2 versus 0;
a Defs-only scratch lemma proves every real function integrable on every event
of this finite population, so the missing certificates can be provided.

## P010-T23 — not_faithful, major

The same defect occurs on the two selected-arm/X=0 events and the
always-passer/X=0 event (`Defs/Part4.lean:128–135`). Neither positive mass nor
covariate balance ensures outcome integrability.

Use the same always-passing Cauchy/shift model, with X constantly zero.
Covariate ignorability and balance hold, and the always-passer/X=0 event has
mass one. The formal selected contrast is again zero by totalization, whereas
the ordinary effect is one. Both ordinary selected conditional means are
undefined. Thus the exported inequality is about a different object from
Corollary 5. Its accurate disclosure as a total-function assertion does not
make it a faithful restricted conditional-mean result.

**Fix:** add the three restricted integrability conditions, now including X=0,
and state the result for finite ordinary means. For `selectionPopulation (1/2)`,
these selected events each have mass 1/6, the always-passer event has mass 1/3,
and the selected contrast is 1/2 versus a zero effect. Its covariate is already
the permitted constant zero vector and its event integrability is Lean-checked.
Exact replacement statements and docstrings are in `findings.json`.

## Record decisions accepted

The other 19 `whole` decisions agree with the blind reading and the canonical
mathematical content. In particular, ignorability is correctly per arm rather
than joint-vector independence; finite-branch sharpness includes attainment;
else-branch extrema are EReal essential support endpoints; and the counterexamples
to printed conditioning or tail direction concern the actual printed formulas.

T12 is `correct_restricted`. The record and Challenge docstring accurately retain
Bayes identities, reciprocal transport and scale cancellation, and the
printed-odds formula and characterization with a positive finite normalizer.
They drop exactly the final infinite-normalizer assertion. Positivity makes
integrability of the squared-density ratio equivalent to finiteness of its
nonnegative mass here. No additional restriction was found.

Unused auxiliary rows in the record do not constitute omitted targets: their
asserted mathematical content is included in the primary statements or is a
specialization of a retained general statement. No unseen proof row was relied on.

## Verification and nonvacuity

`/home/ubuntu/sap/tools/sap-lean scratch/AuditCheck.lean` completed with exit code 0
(one deprecation warning). It imports only `SAP.P010.Defs`, and uses no Challenge
stub. It verifies a genuine two-arm probability instance with positive passing
and assignment, common checks and integrable potentials; positivity of all
empirical retained denominators and validity of binary counts; density-hypothesis
nonvacuity; integrability on every event of the finite selection witness; the
zero default for nonintegrable means; and the out-of-domain quantile/tail behavior
used in the T15 finding. At most one Lean process ran at a time; `lake` was not run.

`python3 scratch/audit_checks.py` passed exact rational checks of every empirical
cutoff and endpoint, overlaps and gaps, finite population independence and means,
beta/heavy-tail moments, and finite-cell transport. Its separate numerical
normal-mixture calculation gave widths 1.7985772989680666 and 1.767983385221887,
inside the stated enclosures, with difference 0.0305939137461797. This last
calculation is a numerical check, not a formal enclosure proof.

Every target has a concrete nonvacuity explanation in `findings.json`, with
mathematical Gaussian or beta instances where the required atomlessness prevents
a finite-atom witness. There are no discovered contradictory hypotheses,
empty-index tricks, false formal assertions, or unbounded-real-limsup defaults.
The three findings concern faithfulness of conditional means.

The saved blind reading SHA-256 is
`0bd474d5744774b4b67c022c5afa7cb98bb1a3b9a4b5e2efff77b3f822ca15ad`.
All output JSON files were parsed and checked for complete, unique target coverage.
