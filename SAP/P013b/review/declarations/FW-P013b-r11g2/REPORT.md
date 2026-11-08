# Declaration review

All five declarations are **faithful, severity none**. T24 is faithful to its
accurately disclosed restriction; the other four cover their canonical claims.
No current issue was found.

`reading.md` was saved before any claim or record was opened. Every declaration
in the five elaborated closures was read, including the 41 distinct generated
helpers, inspected using `scratch/ClosureHelpers.lean`. `claim-stage.json` was
saved after reading the canonical claims and before opening the earlier review,
architect report, or record. The record required no change to those judgments.

| Declaration | Claim coverage and record judgment |
|---|---|
| T20 | Whole. Independent exact-design-law replication, both matrix limits, identity smoothing, and all exposures and entries on one probability-one event are present. The same-exposure conclusion also covers K=1. Measurable replicates and measurable singletons are usual conditions. |
| T22 | Whole. Every corrected clause (a)–(f) is present: exact changes, joint-shift equivariance, residuals and target changes, both iff characterizations, fixed-prediction and HT cases, mean-zero errors, and calibration. The two-unit example demonstrates that shifting predictions is not necessary. |
| T21 | Whole. The specified three-unit certificate includes its hypotheses, baseline and shifted tables, translation errors, expectations and variances, and joint-shift repair. Its docstring accurately limits the counterexample to fixed numerical predictions. |
| T24 | Restricted, accurately. Parts (a)–(e), arithmetic and conditional numeric scaling are retained. The docstring and record both disclose omitted empirical counts/zero coding, released-indicator provenance, rounded Table 2 reproduction, inter-set containment, and separate strictness of the sufficient condition. The conditional scaling premises match the actual statement. |
| T23 | Whole. All three binary worlds, identical records, estimator/effect/loss/bias tables, nonidentification and respondent comparison are present. The docstring correctly concerns wearing interpretation plus the additional zero-scoring rule. |

The common definitions correctly render finite randomization probabilities,
expectations, potentials, HT and difference estimators, exposure-specific
recording, lost means, and subset numerators/denominators. None encodes a
conclusion or replaces the paper's quantity with a placeholder.

The counterexample readings were checked against their conditions separately.
For T21, the reading says that shifting outcomes while keeping numerical
predictions fixed always shifts totals by cN and preserves the mean contrast.
Its conditions are a known finite law, positive exposure probabilities,
exposure-specific potentials and consistent observation, fixed predictions, and
the same assignment/design after translation. The witness satisfies all of them;
own treatment equals its exposure-1 indicator, and the predictions have zero
covariance with it. For T23, the reading says that the recorded-outcome estimator
estimates and identifies wearing effects under zero scoring. Its conditions are
a known finite law, distinct positive exposures, binary exposure-specific wearing
and recording potentials, and consistent observation of the recorded outcome.
Each world satisfies them. Wearing consistency is not claimed for the zero-filled
data. These theorems establish their canonical counterexamples, so `whole` is the
appropriate record decision; neither is labelled `refuted`.

All relevant denominators are positive under their hypotheses or in the explicit
witnesses. T20's cross ratio at R=0 uses 0/0=0, which cannot affect its limit.
Positive finite design weights make `ENNReal.ofReal` faithful. The literal natural
subtractions in T24 do not truncate. No result relies on a non-integrable mean,
nonmeasurable witness, empty/unbounded extremum, or other junk value.

Both `scratch/Nonvacuity.lean` and `scratch/ScalingNonvacuity.lean` compiled
successfully with `/home/ubuntu/sap/tools/sap-lean`, with no warnings or errors.
They import Defs only. They construct nondegenerate IID draws for T20; verify the
T21 witness and its failure of equivariance; satisfy T22's positive-probability
and calibration hypotheses; check T23's identical-record/different-effect
witness; and construct T24's sufficient-condition, deletion and numeric-scaling
instances, including a nonzero retained score. No more than two Lean processes
ran concurrently. The certified target proofs were not re-audited.

The single earlier issue is **fixed**: `record.json:4` now calls T20 `whole`, with
null restriction at line 6. Its current docstring has no provenance-based
restriction. Proof-credit history at line 50 does not change mathematical scope.
This resolution is recorded in T20's `resolved` entry; there is no remaining
current issue to list.
