# Statement referee report

Audited all **14** targets in `claims.json`.

| Verdict | Count |
| --- | ---: |
| `correct_whole` | 6 |
| `correct_restricted` | 7 |
| `restriction_inaccurate` | 1 |
| `not_faithful` | 0 |
| `vacuous` | 0 |
| `false` | 0 |
| `omission_ok` | 0 |
| `omission_questionable` | 0 |

Severity counts: **13 none, 1 minor, 0 major**. All 14 targets have theorem
stubs; there are no omitted targets to assess.

## P008-T6 — restriction_inaccurate, minor

The statement appears true, but the disclosed restriction misses an added
hypothesis on its matrix representation.

In [Defs/Part6.lean:96](/home/ubuntu/sap/tasks/CHFID-P008a-a/SAP/P008a/Defs/Part6.lean:96),
`hsep : ∀ i j, i ≠ j → c < D i j` is a premise of the **entire** first
conjunct. It therefore restricts the weighted-contrast, OLS weight/residual and
[sandwich-to-score-HAC identity](/home/ubuntu/sap/tasks/CHFID-P008a-a/SAP/P008a/Defs/Part6.lean:102),
as well as the ensuing HC0 equalities.

Canonical T6(a) gives the regression/sandwich representation for a general
cutoff, then imposes separation to obtain HC0. The
[Challenge restriction paragraph](/home/ubuntu/sap/tasks/CHFID-P008a-a/SAP/P008a/Challenge/Part1.lean:59)
and `record.json` both say “Retains the general distance-array matrix/HC0
identities,” but neither discloses that the representation itself is only
asserted when the kernel is diagonal. The geometric restrictions and numerical
omissions are otherwise accurately disclosed. The architect's `restricted`
classification is appropriate; its description is incomplete.

This excludes meaningful instances: take assignment 0011, data (0,2,4,6),
D_ij=|2i−2j| and c=12/5. Both arms have size two and the ordinary OLS
representation remains meaningful, but adjacent pairs are included and `hsep`
fails. Its score HAC is 1/2, compared with the diagonal sum 1. With c=2/5
the same data satisfy all current premises and give HAC 1, so the retained
statement is also nonvacuous.

The smallest repair is to change the first sentence of the restriction to:

> The Hajek weighted-contrast, OLS weight/residual and sandwich-to-score-HAC
> identities are asserted only in the HC0 regime: c >= 0, both arm counts at
> least one, D_ii = 0 and D_ij > c for every i != j. The general sandwich
> representation for cutoffs including off-diagonal pairs is omitted.

Keep the other accurate restrictions, and make the same correction in
`record.json`. A complete replacement paragraph is provided in
`findings.json`. Alternatively, state the representation before introducing
`hsep`, and retain `hsep` only for the HC0 equalities.

## Audit order and validation

`reading.md` was saved before opening `claims.json`. `claim-stage.json` was
saved and parsed before opening `record.json`. Its six `whole` and eight
`narrower` classifications were unchanged after the record review. A wording
correction in the blind reading of T3 is explicitly recorded there: the law is
on all sixteen **four-node assignments**, not on a four-element assignment
space. This did not affect a verdict.

The other seven restricted targets disclose their material restrictions:
T1's fixed labelling, T2's spatial/support assumptions and documentary omissions,
T4's omitted reconstruction, T7's labelled counting scope without a planar
realization, T8's spatial assumptions and omitted sampling-space construction,
T9's omitted intermediate vectors/masks, and T10's omitted positivity assertion.
The six whole targets match their canonical mathematical content. In
particular, T11 concerns the exact printed-number and rounding assertions
specified in its formal content; it does not certify the supporting empirical
reconstruction of 7.99649.

The definitions were followed to Mathlib's Euclidean distance, restricted
measures, Bochner integral, extended-nonnegative-real conversion, finite sums
and matrix inverse. The relevant totalization conventions do not supply a
counterexample by accident: evaluated averages have positive finite mass and
the required integrability; empty-arm ratios are excluded wherever used;
the risk thresholds never trigger truncated subtraction. T6's final integrand
is zero on each relevant circle by the triangle inequality, so that clause
does not need a separate integrability premise. T12's empty selected range is
the intended exhibited defect, rather than an empty index assumption.

Validation completed:

* `/home/ubuntu/sap/tools/sap-lean scratch/Check.lean` — passed. This compiles a
  distinct-node model with nonempty radius-one circles of mass one, a positive
  conditional event with both arms present, the full T2 spatial premises, T8
  override integrability/binary premises, a T6 geometric instance with excluded
  pairs, and a nondegenerate IID product law for T4.
* `python3 scratch/check_finite.py` — passed. Independent exact rational checks
  cover finite support examples, tails, rectangle circle means and type-7
  quantiles, replicated-pair variances for one through three pairs, a nonconstant
  additive covariance example, risk counts, rescaling, bandwidth variances,
  rational toy squared distances, rounding margins and both distance grids.
* Output JSON syntax, required fields, verdict/severity values, target coverage
  and theorem correspondence were checked with Python.

These are statement and nonvacuity checks; they do not replace the package's
Solution/Comparator proof certification. No Solution or other formalization
source was inspected, and no `lake` command was run. Nonvacuity evidence for
each target is recorded in `findings.json`.
