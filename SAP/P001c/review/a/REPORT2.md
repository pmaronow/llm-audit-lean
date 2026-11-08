# P001c delta referee report

The earlier T42 wording finding is **fixed**. No finding is partly fixed or
unfixed, and no new issue was found. All revised decisions are appropriate,
including the four `refuted` labels. The mathematical statements still match
the saved blind readings.

## Counts

| Findings verdict | Targets |
| --- | ---: |
| correct_whole | 9 |
| correct_restricted | 9 |
| omission_ok | 1 |
| restriction_inaccurate | 0 |
| not_faithful | 0 |
| vacuous | 0 |
| false | 0 |
| omission_questionable | 0 |
| **Total** | **19** |

Severity: 19 none, 0 minor, 0 major. Earlier issues: 1 fixed, 0 partly fixed,
0 not fixed. New issues: 0.

The revised record has 8 `whole`, 6 `restricted`, 4 `refuted`, and 1 `omitted`
decisions. `findings2.json` retains the requested original findings schema,
which has no `correct_refuted` verdict. A correct refutation with complete
canonical-counterexample coverage is therefore `correct_whole` (T41); a correct
refutation with accurately disclosed omissions is `correct_restricted`
(T44, T53, T56). This accounts for the difference between the two sets of counts.

## Earlier finding

| Target | Earlier issue | Resolution |
| --- | --- | --- |
| T42 | The docstring called [-1,1] the “unit interval,” conventionally [0,1]. | **Fixed.** `SAP/P001c/Challenge/Part1.lean:34–35` explicitly says “[-1, 1]” and identifies the extreme values as 1 and -1. The formal range and both almost-sure characterizations remain correct. |

This was the only issue in my earlier `findings.json`. The other 18 target
entries had no adverse finding; their accepted mathematical coverage and the
T47 omission remain justified. The architect's response accurately acknowledges
and addresses the issue.

## Comparison with the saved reading

I reread all six revised Defs parts and both Challenge parts and compared their
objects, hypotheses, quantifiers, definitions and conclusions with `reading.md`.
No mathematical change was found in any of the 18 theorem statements or their
shared definitions. The changes affecting the review are the corrected T42
docstring and the new refutation prefixes and decision labels for T41, T44,
T53 and T56. The previously disclosed restrictions remain in place.

The decision comparison between `record.json` and `record2.json` changes only
T41, T44, T53 and T56 to `refuted`. No theorem name, omission, or restriction
text changes. I checked the new prose against the actual statements rather than
accepting the labels solely from the architect's report.

## New refutation labels

All four docstrings begin with “The printed claim is false:” and identify the
particular assertion contradicted by the retained mathematical witness.

| Target | Printed reading refuted | Check and coverage |
| --- | --- | --- |
| T41 | Correlation 1 or -1 implies the corresponding affine relation at every outcome. | The three-outcome PMF has positive variances 1/4 and correlations 1 and -1, yet neither corresponding everywhere affine relation exists, even allowing arbitrary real slopes. Probability-one relations remain true. This is the complete canonical counterexample; the correlation bound and reverse implications are not refuted. |
| T44 | The BLP is the only affine function satisfying the covariance equation. | With X=Y taking -1 and 1 equally often, g0(x)=x and g1(x)=x+1 have covariance 1 with X but different values and risks 0 and 1. Risk zero makes g0 optimal; g1 has the same covariance without being optimal. The retained example refutes the uniqueness claim. The second example and general covariance formula remain explicitly omitted. |
| T53 | Finite positive variance of X supplies the finite variance of X² required by the cited finite-variance WLLN. | The normalized power-tail masses have E[X²]=7/4 and Var(X)=7/18>0, but infinite fourth moment. Thus the square lacks the needed finite centered second moment. The docstring explicitly preserves sample-variance consistency and discloses the omitted probability-space/IID realization and separate squared-variance assertion. |
| T56 | Every Hadamard-differentiable plug-in is asymptotically normal with strictly positive limiting variance. | For the actual constant functional T=7, the theorem states a zero derivative, an identically zero root-n statistic, and nonconvergence to every positive-variance Gaussian law. IID Bernoulli sampling is realizable. This refutes the printed implication without challenging the nondegenerate delta method. The quadratic example's omitted auxiliary assertions remain disclosed. |

For T53, the infinite fourth-moment witness really obstructs the cited theorem:
writing m=E[X²]=7/4, the pointwise inequality

X⁴ ≤ 2(X²−m)² + 2m²

shows that a finite centered second moment of X² would force a finite fourth
moment, contrary to the displayed extended-real sum. The normalized masses give
a probability law on ℕ, and IID draws can be realized by its countable product.
These constructions explain the refutation; the Challenge accurately declares
that it does not separately export them. No claim that Mathlib's real-valued
variance equals infinity is made. The convergence conclusion in the printed
sample-variance theorem remains true and is not labelled refuted.

## Whole and restricted labels

Each of the eight targets still labelled `whole` retains all canonical result
clauses, with the standing finite-moment and random-variable conventions:

| Target | Canonical result clauses present |
| --- | --- |
| T42 | The range [-1,1] and both equivalences between extreme correlation and almost-sure affine dependence, with positive variances and the correct slope signs. |
| T45 | The covariance equation fixes exactly the slope; adding the mean equation fixes both coefficients; the coefficients uniquely minimize affine squared risk. |
| T46 | The corrected conditional-mean version 10X², the uniform moments and covariance giving slope 10 and intercept -5/3, and the resulting BLP. Optimality and uniqueness are explicit. |
| T48 | All covariance-matrix entries, symmetry, variance diagonal and the full double-sum variance rule. |
| T49 | The intercept at zero, unit increment in every coordinate and every coordinate derivative for arbitrary affine coefficients. These identities apply to the BLP as a special case. |
| T50 | The finite-population PMF and moments, every specified numerical example value, the corrected variance sign and discrepancy, and the empirical mean and variance formulas. |
| T52 | The indicator expectation identity for every measurable real set and IID empirical-CDF consistency at every fixed ordinate. |
| T55 | Both centered-zero formulations and the two-way equivalence between variance and standard-error consistency, with the correct estimator argument and normalization. |

The six `restricted` decisions remain accurate and fully disclosed:

| Target | Disclosed restriction checked |
| --- | --- |
| T39 | Omits the general non-implication from zero correlation to independence for normal marginal laws. Retains nontrivial independent normal sums and all corrected bivariate-density conclusions. |
| T40 | Omits the first-order differentiation calculation and certification of the drawn curve. Retains the general MSE results, coin moments, loss values and factor-two formulas. |
| T43 | Omits joint differentiability and the zero-regressor-variance footnote. The Hessian, CEF and residual block requires a supplied square-integrable conditional-mean version. Neither existence nor separate second-differentiability certificates is claimed. |
| T51 | Retains the exact eventual-level equivalence for p in [0,1). Omits a separately exported complementary-event limit theorem and an explicit p=1 counterexample. |
| T54 | Retains both sample-variance conclusions. Omits the general integrable WLLN and intermediate sample-mean and sample-second-moment limits from the corrected proof. |
| T57 | Supplies a probability bridge with tangent support and Gaussian finite-dimensional laws, a measurable scalar plug-in and an L² derivative image with positive variance. Omits bridge existence and the degenerate alternative. The process and scalar limits remain conclusions. |

The three restricted refutations' retained omissions are addressed in the
refutation table above. None silently acquires complete canonical coverage by
being relabelled `refuted`.

T47 remains appropriately omitted. The canonical composition-only transformation
scope does not automatically supply global Borel or marginal-law measurability.
The scope difference and mathematical countermodel in `nonvacuity.md` remain
applicable; the rejected rows cannot silently be credited as the whole claim.

## Junk values, nonvacuity and validation

The changed prose introduces no new mathematical hypotheses or conclusions.
The refreshed definitions preserve the earlier protections: finite moments for
ordinary means and risks, positive correlation/regression denominators, positive
sample sizes for empirical probability laws, bounded Hadamard directions and
norms, and bounded tests with genuine integrable majorants for outer expectations.
No new empty index type, undefined integral, unbounded supremum, or zero
denominator is used.

For the relabelled targets, the witnesses are genuine: T41 has three actual
outcomes and normalized nonnegative weights with positive variable variances;
T44 has a nondegenerate two-point law; T53 has a normalized law on nonempty ℕ,
summable real first and second moments, and a divergent fourth-moment sum in
the extended nonnegative reals; T56 has an actual IID Bernoulli realization.
T41's null outcome is the intended counterexample to everywhere equality.
T56's degenerate statistic is the intended counterexample to positive-variance
asymptotic normality. Neither is an unsatisfiable antecedent.

I reran `/home/ubuntu/sap/tools/sap-lean scratch/Check.lean` against the refreshed
Defs. It completed with exit code 0 and no diagnostics. This file imports Defs
only, so its nonvacuity checks do not use the Challenge stubs. It rechecks the
normalized finite weights, positive-variance Gaussian instances, conditional-mean
inputs, IID product laws, the Bernoulli hypotheses, the uniform/Gaussian model,
a nondegenerate root-n limit and an evaluation Hadamard derivative. The complete
mathematical T57 bridge instance in `nonvacuity.md` remains unchanged and valid.
Only one Lean process was used at a time; no `lake` command was run.

`findings2.json` has exactly the original findings schema and one entry for each
of the 19 canonical targets. Python parsing, required fields, unique IDs,
theorem-name coverage and verdict counts were checked. The earlier reading,
findings and report were preserved. The architect's proof-certification account
was not treated as a substitute for this statement review.
