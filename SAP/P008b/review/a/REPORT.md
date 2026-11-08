Audited 14 targets: 13 exported theorem statements and one omission.

| Verdict | Count |
| --- | ---: |
| correct_whole | 2 |
| correct_restricted | 10 |
| restriction_inaccurate | 1 |
| not_faithful | 0 |
| vacuous | 0 |
| false | 0 |
| omission_ok | 1 |
| omission_questionable | 0 |
| Total | 14 |

Severity: 13 none, 1 minor, 0 major. The one issue concerns the description of
T17; no exported Lean proposition was found false or vacuous.

**P008-T17 — restriction_inaccurate, minor.**
`SAP/P008b/Challenge/Part1.lean:16` says: “Circle tolerance gives the clipped
radial band of width twice the tolerance”. That width assertion needs `k ≤ d`.
The retained theorem correctly includes this condition at
`SAP/P008b/Defs/Part6.lean:34`, and canonical part (a) does too. With `d = 1`
and `k = 2`, its clipped radial interval is `[0, 3]`, so its radial width is 3,
whereas twice the tolerance is 4. These values satisfy the theorem's initial
geometry hypotheses `0 < d` and `0 ≤ k`. The discrepancy is independently
kernel-checked in `scratch/Check.lean`.

Replace the descriptive sentence with:

> For a Euclidean circle of radius d > 0 and tolerance k ≥ 0, circle tolerance
> gives the clipped radial band [max 0 (d-k), d+k]; its radial width is twice
> the tolerance when k ≤ d. For strictly growing nested finite buffers,
> adjacent-buffer differences average the added cells at distances in (a,b].

The architect correctly classified T17 as restricted: the zero-radius polygon
buffer identification and the archived polygon disk branch are absent and are
explicitly disclosed. The unqualified width wording still makes its description
inaccurate. No theorem change is needed. `findings.json` gives the complete
replacement docstring.

The remaining record decisions agree with the statements:

| Targets | Assessment of the record |
| --- | --- |
| T16, T19 | Whole: their explicit geometry/cell data, nonempty means, contrasts and stated AMRs reproduce the full canonical counterexamples. T16's canonical note specifies that its distances and outcomes, rather than the validator's original polygon coordinates, define the arithmetic example. |
| T15 | Restricted as disclosed: Euclidean bands, genuine integrals, and no accompanying edge-average display. |
| T18 | Restricted as disclosed: retains additive effects, amplitude scaling and the strict bound; drops the derivative/maximization/Taylor assertions and amplitude-three numerical compatibility. |
| T20 | Restricted as disclosed: nonempty boundaries/frontiers and no fitted-curve assertion. Its arbitrary-set frontier statement correctly specializes to polygons. |
| T21, T22 | Restricted as disclosed to true arithmetic comparisons/nominal decisions; neither validates empirical inputs, a reference distribution or an error rate. |
| T23 | Restricted as disclosed to the population covariance identity; no printed interval, coverage or toy cutoff-accounting conclusion. |
| T25 | Restricted as disclosed to Euclidean circles with positive finite mass and integrable outcomes, and positive node count for the AMR. Its unconditional overwrite marginal is the canonical marginal over other assignments. |
| T26 | Restricted as disclosed: measurable Euclidean field, genuine circle averages, and the cancelling converse witness only at nonempty circles. |
| T27 | Restricted as disclosed: the added whole-field measurability and genuine Euclidean circle hypotheses are explicit; point-effect identification remains valid under arbitrary finite assignment laws. |
| T28 | Restricted as disclosed to the audit's sufficient consistency version. The dependency definition requires independence of separated collections, the completion is fixed before the limit, and no normality or HAC conservativeness is claimed. |
| T24 | Omission accepted: the canonical note supplies neither a defined cumulative forest-loss event nor a reconstruction of the particular empirical values. A range obstruction for another array does not refute the printed interpretation of these values, all of which lie in [-1,1]. This assessment does not rely on trusting the record's row-status labels. |

`reading.md` was saved before opening `claims.json`; `claim-stage.json` was saved
before opening `record.json`. The stage-2 classifications remain unchanged.
The T17 wording issue was already recorded at stage 2. The final finding
distinguishes the correct restricted Lean proposition from its inaccurate
docstring.

Nonvacuity instances and exact finite checks are supplied per target in
`findings.json`. `scratch/Check.lean` imports only `SAP.P008b.Defs` and checks
positive-radius atomic circle averages, substantive two-node separation,
nonzero additive effects, a sharp-null instance with nonempty circles,
nonempty boundaries, buffer and cancellation denominators, a positive-variance
cutoff example, all-size fair product laws, and the arithmetic claims.
`scratch/verify.py` separately checks the complete finite counterexamples using
exact rational arithmetic and supplies the all-size nontrivial dependency-graph
instance. Its results are in `scratch/finite-checks.json`. These checks concern
the supplied mathematical formulas; no archived software implementation or
unavailable formalization was inspected.

The paper's identity was checked only at its
[arXiv record](https://arxiv.org/abs/2106.15081). The canonical statements and
standing assumptions used for the audit are those supplied in `claims.json`.
