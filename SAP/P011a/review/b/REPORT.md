# P011a statement referee report

14 targets reviewed: **7 correct_whole, 6 correct_restricted, 1 restriction_inaccurate**.
Severity: **13 none, 1 minor, 0 major**. No false, vacuous, not_faithful, or omitted targets.

## Finding: P011-T1 / SAP.P011a.T1 — restriction_inaccurate, minor

The architect marks this target `whole`, with no restriction in either `record.json` or its
Challenge docstring. Canonical part (f) includes a numerical evaluation of the limiting coverage
at α=0.05, approximately 0.805. The theorem asserts the exact expression
`2*Phi(normalQuantile α * Real.sqrt (7/16)) - 1` for every α∈(0,1), with strict undercoverage,
but contains no certified numerical approximation for α=1/20. See
[CycleCounterexample](SAP/P011a/Defs/Part3.lean#L68),
[T1Statement](SAP/P011a/Defs/Part5.lean#L229), and
[the Challenge docstring](SAP/P011a/Challenge/Part1.lean#L6).

This is a small undisclosed omission. The exact expression, substantive counterexample,
hypothesis checks, finite moments, and negative-estimate example match the canonical claim.
Independent numerical evaluation gives 0.8051603321887559, consistent with the canonical
approximation; the objection concerns which assertion is certified, not its truth.

Fix: classify T1 as restricted and append this docstring text:

> Restriction: Retains the cycle laws, their hypotheses, singleton compatibility, exact variance
> and bias, finite moments, probability limits, exact all-alpha coverage formula, and
> negative-estimate example. Omits only the decimal coverage evaluation at alpha = 0.05
> (about 0.805).

Alternatively, retain whole credit by adding a certified approximation, for example that
the expression at α=1/20 lies strictly between 0.8045 and 0.8055.

## Review against the record

The other seven `whole` decisions are accepted: T3, T5, T6, T8, T11, T12 and T14.
The six declared restrictions match both their Challenge docstrings and the actual statements:

| Target | Accurately disclosed omissions |
| --- | --- |
| T2 | Sharper 27/5 outcome bound; pointwise S/L/Q expansions and multiblock centering identity; decimal coverage evaluation. |
| T4 | Replacement of the PSD condition by nonnegative traces against admissible covariances, and the diagonal/true-edge support observation. |
| T7 | Residual-sign clique characterization of maximizers; confidence-interval consequence. |
| T9 | Explicit slope weight representation, per-sample-size scaled true variance 2, pointwise residual sum, and n=4,8 numerical specializations; fitted-map measurability is explicit. |
| T10 | Separately quantified universal-estimator consequence; unscaled-zero consistency and additional-design-information observations. |
| T13 | Equivalence to the paper's programs, explicit uniqueness/separate optional optimum, general maximum-matching existence and independent optimum-value identity, and runtime/complexity conclusions. |

There are no omitted targets to assess. No step-2 verdict changed after reading `record.json`;
the T1 omission was already recorded in `claim-stage.json`.

## Evidence and limits of the checks

The blind expansion, saved before either JSON source was opened, is in [reading.md](reading.md).
The subsequent independent claim judgments are in [claim-stage.json](claim-stage.json).
[findings.json](findings.json) contains one final object per target, with nonvacuity witnesses.

The shared nonvacuity witness is the genuine independent-sign family: n=k+1, β=0, covariance I,
empty graphs, θ=1, and Scaling constants (1,1,1,2). Its limiting scaled variance is 1.
The residual theorems additionally admit an intercept-only design, true and fitted coefficient 0.
The counterexamples and matching/relaxation problems have their own explicit nonempty instances.
Full details, including all hypotheses and checks of totalized operations, are in
[scratch/nonvacuity.md](scratch/nonvacuity.md).

`/home/ubuntu/sap/tools/sap-lean scratch/Check.lean` completed with exit code 0. The file imports
only Defs and verifies nonempty finite feasibility, both remaining-cap vectors, concrete negative
quadratic values, and existence of a compatible maximizer for every real objective whenever a
compatible true graph is supplied. Thus the maximizer premises in T5/T9 are satisfiable and do
not add a statistical assumption. No Challenge `sorry` declaration was used.

[scratch/check_finite.py](scratch/check_finite.py) completed successfully. Its independent exact
rational enumeration verifies cycle moments at n=4,8,12; both path families at n=3,6,9;
alternating moments/probabilities at n=1,2,3,4,8; unstable OLS moments at n=4,8; spectral
majorant principal minors; both matching optima; the finite comparison/sign formulas through
n=5; and the six-unit/triangle integer optima and fractional witnesses. Results are in
[scratch/finite-results.json](scratch/finite-results.json). These finite checks supplement the
statement audit; they are not proofs of the infinite-sequence conclusions.

The audit found no use of divergent Bochner integrals, zero statistical denominators,
unbounded real liminf defaults, or empty index types to obtain the conclusions. Matching
feasibility is checked before natural subtraction, and all lcm denominators are positive.
Samplewise maximized objective values are finite maxima of measurable functions, even when
tie-breaking graph selectors are not required measurable.

The canonical claims and supplied standing assumptions are the comparison source. Publisher
access did not yield the journal PDF; the accessible arXiv version differs from the journal
version, so it was not substituted for the supplied journal transcriptions. Solution and
Comparator sources were not consulted, and no proof certification is inferred from the stubs.
