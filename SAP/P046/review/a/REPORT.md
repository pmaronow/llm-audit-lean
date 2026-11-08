# P046 statement audit

All ten targets are represented. Counts: **3 correct_whole**, **7
correct_restricted**, **0 restriction_inaccurate**, **0 not_faithful**, **0
vacuous**, **0 false**, **0 omission_ok**, **0 omission_questionable**. All
severities are `none`. There are no adverse findings or requested fixes.

The `correct_whole` count includes T6's complete, legitimate refutation of the
printed population-tail assertion. It does not mean that the printed positive
assertion is true.

## Order and evidence

The blind mathematical reading was saved in `reading.md` before opening
`claims.json`. The comparison in `claim-stage.json` was saved and parsed before
opening `record.json`. No claim-stage classification was changed after reading
the record. Canonical `statement`, `definitions_needed`, and standing assumptions
determined scope; neither `note` nor `finite_lemmas` supplied additional clauses.

The relevant Mathlib definitions were read directly, including real Bochner
integrals, conditional expectation and conditional independence, finite product
measures, L2 membership, variance, weak convergence, and zero-variance Gaussian
laws. The [published paper](https://pmc.ncbi.nlm.nih.gov/articles/PMC12139723/)
was also consulted. The earlier arXiv version has a different Proposition 3 and
was not substituted for the canonical published statement.

## Decisions against the record

| Target | Verdict | Assessment of the architect's decision and disclosure |
| --- | --- | --- |
| T1 | correct_restricted | Retains the explicit valid continuous design, exact strict noncoverage and state count. The record and docstring disclose the omitted count variables, multinomial distribution, statistic reductions, exclusion equivalences, logarithmic mass sum, total-state count and separate coverage/tail conclusions. The exact rational representation is correct. |
| T2 | correct_restricted | Retains a positive-probability failure of the conditional proof step. The pointwise generated-outcome/HT assertions and conditional-centre explanation are expressly omitted. Conditional expectation uses the original product law; restriction to the event occurs only in the outer almost-everywhere assertion. |
| T3 | correct_restricted | Retains corrected population coverage, the strict radius bound, the width rate and the known-bound alternative. The omitted proof assertions (i)-(iv), their probabilistic ingredients, and the separate inverse-propensity bound are disclosed. No conditional coverage assertion is substituted for population coverage. |
| T4 | correct_restricted | Retains the actual opposite-fold empirical fits, convergence, finite-sample means/variances and both normal limits. The omitted training-loss analysis, population criterion and uniqueness, scalar table/moments, bounded-summand assertion, explicit zero-closure exclusion, outcome variance and explicit risk-gap assertion are disclosed. The docstring identifies the treated-case weighted-loss reading. |
| T5 | correct_restricted | The working-family clause includes the canonical zero-closure alternative. The family-free clause's extra L2 conditions on the deterministic limit and every finite-sample fit are accurately disclosed, including exclusion of vanishing-probability infinite-error events. |
| T6 | correct_whole | `refuted` is justified: the theorem negates the actual canonical universal population-tail inequality with the printed random radius. T1 contradicts that inequality itself. The docstring's statement that the printed claim is false is appropriate here. |
| T7 | correct_whole | All canonical conclusions and quantifiers are present. In particular, the common positivity constant in the uniform assertion comes from `definitions_needed`, rather than from audit-history commentary. Variance zero is handled correctly. |
| T8 | correct_restricted | Full-sample integrability of each evaluated fitted prediction is an added hypothesis and is explicitly disclosed. It is stronger than integrability of the final estimator. Allowing arbitrary deterministic folds is a valid finite-sample generalization. |
| T9 | correct_restricted | Both parts add almost-sure L2 membership of each finite-sample fit. The fixed L2 limits and integrable squared-error expectations in (b) are disclosed. The two fold limits can differ. The numerical Hahn normal limit is exactly the canonical meaning of attainment; a separate semiparametric lower-bound theorem is not demanded by that definition. |
| T10 | correct_whole | The explicit quantifiers correctly express failure of uniform consistency for every measurable observed-data estimator. The law can depend on sample size, and the unrestricted model need not have a common positivity constant. The stronger fixed-constant construction in `finite_lemmas` is not part of the canonical assertion. |

No target is omitted, so there are no omission decisions to assess. T1, T2 and
T4 are counterexample targets whose canonical statements already specify the
witnesses. They are appropriately restricted relative to those statements;
T4's refutation is expressly tied to its specified weighted-loss reading.

## Independent checks

`python3 scratch/referee_arithmetic.py` passed. Its exact rational calculation
checks all 5,151 feasible T1 states. A positive-term logarithm series with a
rational remainder bound encloses `log(20000000)` between
`16.8112428315182650975431723042487260212817116...` and
`16.8112428315182650975431723042487260212832151...`. Every logarithmic comparison
agrees with `certifiedCut`; the smallest distance from the enclosure is greater
than `0.008757`. The failing-state count is 1,946, the complete multinomial mass
is one, and the numerator exactly matches the theorem. Strict noncoverage is
`1.197929106979562547257672262560145...e-7 > 119/10^9 > 10^-7`.

The same script bounds T2's squared radius above by `0.022771<1/4` and recomputes
T4's atom probabilities, means, second moments, variances, risks, weighted norm,
variance excess and ratio using fractions. Its saved output is
`scratch/referee-arithmetic.json`.

`/home/ubuntu/sap/tools/sap-lean scratch/RefereeCheck.lean` completed successfully
(only unnecessary-`simpa` linter warnings). It imports Defs and no Challenge or
Solution. It constructs measurable opposite-fold zero fits; proves zero-family
L2 membership, zero-benchmark membership, L2-in-probability and mean-square
convergence, finite-sample evaluated-prediction integrability, and a measurable
observed-data estimator instance; and checks the concrete positivity constants.
Evaluation of the package's own integer numerator comparison and failing-state
count both returned `true`. The log is `scratch/referee-lean.log`. No `lake`
command was run, and only one Lean process ran at a time.

## Nonvacuity and totalized operations

A common nondegenerate study is: `W` uniform on `[0,1]`, independent fair
Bernoulli `X,Y1`, `Y0=0`, `pi=m=1/2`, and `delta=1/4`. Its law is a genuine
product probability measure, the covariate is atomless, both supplied functions
are measurable, positivity is strict, the conditional means have the required
versions, and treatment is conditionally independent of each potential outcome.
It has `mu=1/2` and HT summand variance `3/4`.

For T5 choose the singleton zero working family, parameterized by one unused
real coordinate, and deterministic zero fits on half-splits. Every parameter is
an empirical minimizer; the population minimizer is zero, its L2 errors vanish,
and the direct comparison holds with equality. T8 uses the same zero fits. T9(b)
uses the zero fits and fixed zero limits; T9(d) uses deterministic fits equal to
`m=1/2`, yielding Hahn variance `1/2`. These satisfy all the added integrability
conditions. Replacing `Y1` by zero additionally witnesses the allowed degenerate
normal limits. The folds have sizes `floor(n/2)` and `ceil(n/2)`, so balancing
does not rely on empty folds. T1, T2 and T4 have their own explicit valid
generators; T2's adverse event has strictly positive mass.

For T10 there is an independent short lower-bound argument over the claimed
unrestricted class. For each `n>=1`, take `p=1/(4n)`, `delta=p/2`, uniform `W`,
independent Bernoulli(p) `X`, `Y0=0`, and compare laws with `Y1=0` and `Y1=1`.
The observed samples agree when all treatments are zero; that event has
probability at least `1-np=3/4`. For every estimator value on that common data,
at least one error exceeds `1/4`. Consequently one law's error probability is
at least `3/8`. This supplies a positive error threshold and probability lower
bound at every positive sample size, hence the exact asserted quantifiers.

Real Bochner integrals and real variance are totalized at nonintegrable inputs,
but no retained assertion obtains its content from that convention. Positivity
and binary outcomes make the HT integrals and moments finite; all relevant
fixed or fitted squared errors in T5 and T9 have the explicit L2 guarantees.
T8's evaluated predictions are explicitly integrable. Valid sample laws are
probabilities, so `ENNReal.toReal` does not discard infinite mass. Every
finite-sample probability conclusion uses `n>0`; the zero-sample terms in
asymptotic sequences cannot affect a limit at infinity. T1's natural-number
subtractions occur within `0<=s<=k<=100`, with a separate case split for the
absolute deviation, so truncation does not change its integer test. No
conclusion is assumed as a hidden hypothesis.
