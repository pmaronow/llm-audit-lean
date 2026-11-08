# P029b statement audit

13 targets: **3 correct_whole, 9 correct_restricted, 1 omission_ok**.
There are **0 restriction_inaccurate, 0 not_faithful, 0 vacuous, 0 false,
and 0 omission_questionable** findings. All severities are `none`.

The restricted results say less than the canonical claims, and their
Challenge docstrings accurately disclose the material omissions and extra
hypotheses. The refutations of false printed claims are counted as correct
when they refute the canonical reading. No substantive issue or correction
is required on the visible statements.

| Target | Verdict | Scope checked against the record and docstring |
| --- | --- | --- |
| P029-T14 | correct_restricted | Distributional properties of the clipped rate difference; ML characterization, uniqueness, interior parameterization, extreme-event formula and joint-strata assertion omitted. |
| P029-T15 | correct_restricted | Genuine constant-score counterexample; type-7 quantiles only, without the separate power-level clause or numerical receipt arm means. |
| P029-T16 | correct_restricted | Correct finite bounds and finite-covariate limits; stated finite omissions and additional almost-sure eventual definedness of both ratio sequences disclosed. |
| P029-T17 | correct_restricted | Likelihood reduction and maximizer equivalence; general additive-factor formulas and lower bound omitted. |
| P029-T18 | correct_restricted | General positive-profile nested identities and an explicit misconditioning witness; full integral and corrected-estimator equalities omitted. |
| P029-T19 | correct_restricted | Correct pointwise simulation algebra; stochastic noise/assignment recipe omitted and index formulas only defined. |
| P029-T20 | correct_whole | Refutes typical-to-latent mean ignorability and supplies the separate baseline-selection example in the other direction. |
| P029-T21 | correct_restricted | Both joint independence implications refuted; true constant-effect result has disclosed version/overlap/profile restrictions and no sample limit. Marginal refutation explicitly uses the complier indicator. |
| P029-T22 | omission_ok | Available RMSE expansion has no demonstrated connection to the historical simulation or derivation of its homogeneous causal target. |
| P029-T23 | correct_whole | Exact interior Bernoulli counterexample to the package's weighted-fitting contract, with positive likelihoods and weights. |
| P029-T25 | correct_whole | Population ITT/LATE identities, defined-sample centered-IV equality and exact worked-example numbers. |
| P029-T26 | correct_restricted | Actual ATE probability limit with disclosed uniform score consistency, measurable versions/estimates, support conditions and eventual ratio definedness. |
| P029-T27 | correct_restricted | Genuine complier law and LATE integral, restricted sample limit and defined-sample constant-score identity. |

## Record review

The architect's decisions are supported by the visible statements. No
step-2 reading or fidelity verdict was changed after opening `record.json`.
The stage-2 `narrower` verdict for T21 is consistent with the record's
`refuted` decision: the two false joint implications are refuted, while
the accompanying true constant-effect assertion is restricted and that
restriction is disclosed.

T22's omission is justified within the visible package. The canonical
claim explicitly withholds the historical simulation arrays and cautions
against asserting the printed Monte Carlo numbers. The record describes
only an arbitrary-array RMSE expansion with 5 supplied as the benchmark;
it does not connect that array to the estimators or establish the design's
sample, population and complier effects. That helper would not by itself
certify this target. No historical estimate or simulation number has been
treated as verified.

## Nonvacuity and definition checks

The finite laws are genuine probability laws. The concrete conditional
means and population weighted ratios used as witnesses have positive
conditioning masses and nonzero first stages. Positive binomial arm sizes
avoid undefined rates, and the bounded `Fin` counts make the natural
subtractions in their exponents ordinary nonnegative subtraction. The
logarithms in T23 have strictly positive arguments throughout the parameter
space. T27's density is the actual normalized complier pushforward;
zero-score profiles have zero complier mass, so the conditional effect
version need not be specified there to define the complier integral.

For the asymptotic hypotheses, a simultaneous nonvacuity instance is the
countable product of independent fair Boolean assignments, a single
covariate value, all-complier units with `Y0=0,Y1=1`, exact scores and
versions `c=m=a=1`, estimates `s(n,i)=1`, and cutoff 1. Choose `alpha=1`
and overlap constant `epsilon=1/2`. Uniform score error is identically
zero; all measurability, integrability, iid and support conditions hold.
Both assignment values appear after a finite number of draws almost
surely. Every subsequent sample contains both arms and has first stage 1,
so both original and Winsorized ratio definedness conditions hold. This
argument is mathematical; the full infinite-product instance was not
Lean-compiled.

The T20 forward counterexample has complier/always/never masses
`1/2,1/4,1/4`, independent fair assignment and `Y0=0,Y1=1_C`. Both
received-treatment `Y1` means are `1/2`, while the population and complier
effects are `1/2` and 1. Separate finite witnesses for T21 give
`ATE=IV=1/2, ICSW=5/12` under marginal independence, and
`ATE=ICSW=1/2, IV=3/4` under conditional full-type independence.
Thus the negations refute the printed joint implications on ordinary
finite probability laws, without relying on undefined conditionals.

## Verification and audit order

`reading.md` was saved before opening `claims.json`; `claim-stage.json`
was saved before opening `record.json`. The blind reading follows the
SAP definitions through the relevant Mathlib definitions, including total
division, Bochner-integral and conditional-expectation defaults,
independence, pushforward laws, measure support and convergence in measure.

`/home/ubuntu/sap/tools/sap-lean scratch/Check.lean` completed with exit code
0 and an empty diagnostic log. It imports only `SAP.P029b.Defs` and checks
the six-point valid IV law, its score and weighted Wald value, a strictly
positive binomial bias example, a nonconstant type-7 quantile and changed
count, nonempty one-sided likelihood hypotheses, an interior package
parameter, defined two-unit sample ratios and the reverse T20 example's
baseline means. No Challenge theorem was used in those checks.

`python3 scratch/nonvacuity.py` completed successfully using exact rational
arithmetic. It checks finite IV laws and conditioning masses, both T20
witnesses, both T21 independence witnesses and a strictly better admissible
weighted likelihood for T23. Its results are in
`scratch/nonvacuity.json`. These are witness checks, not substitutes for
proving every universal theorem.

Both requested JSON outputs were parsed and their theorem/target coverage,
verdict values and required fields were checked with Python.
