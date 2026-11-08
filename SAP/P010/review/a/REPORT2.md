# P010 delta statement review

All three earlier findings are **fixed**. No new statement or label defect was
found. The revised package has 15 correctly labelled `whole` targets, seven
correctly labelled `refuted` targets, and one accurately disclosed `restricted`
target. No target is omitted.

The requested findings schema has no separate `correct_refuted` verdict. In
`findings2.json`, `correct_whole` means that the complete canonical target is
faithfully stated, including a canonical target whose content is a refutation.
Thus its 22 `correct_whole` entries comprise 15 whole results and seven complete
refutations. It does not classify the seven refuted printed assertions as true.

| Verdict | Count |
| --- | ---: |
| `correct_whole` | 22 |
| `correct_restricted` | 1 |
| `restriction_inaccurate` | 0 |
| `not_faithful` | 0 |
| `vacuous` | 0 |
| `false` | 0 |
| `omission_ok` | 0 |
| `omission_questionable` | 0 |

Severity: 23 none, 0 minor, 0 major.

## Earlier findings

| Target | Previous finding | Delta disposition |
| --- | --- | --- |
| T15 | Tail-mean equality asserted outside its positive-mass domain | Fixed |
| T21 | Existential witness lacked the three required integrability conditions | Fixed |
| T23 | Same defect after conditioning on zero covariates | Fixed |

**T15.** `Defs/Part6.lean:208-211` now places the upper-tail equality, the
always-passer/event identity and the upper bound together under
`trimmingRatio μ a < 1`. The distribution, marginal-pass-probability and
trimming-share identities at lines 205-207 remain unconditional. This matches
the meaningful canonical claim and preserves every clause on its stated domain.
The revised docstring at `Challenge/Part1.lean:70-71` says precisely which
identities need the finite-branch condition. The `whole` decision is correct.

The previous ratio-two counterexample no longer generates an assertion about
empty-tail means. A genuine active-branch instance is `normalCommonPopulation`:
allPass has mass 4/5, pass rates are 4/5, and r=1/4. Standard normal integrability
and atomlessness give genuine upper tails of relative mass 3/4; the selected-arm
tail event has mass (4/5)(1/2)(3/4)=3/10. The selected-arm and potential-passer
laws are probability laws by positive passing and assignment. The potential
outcome on allPass is integrable by transfer of the selected-passer integrability
under per-arm ignorability and then restriction. There is no new hidden moment
assumption. At r=0 the defined quantile is -infinity and the upper tail is the
whole passer population, with positive mass; at r>=1 the tail identity is not
asserted. No quantile-to-real or zero-denominator default does the work.

**T21.** `Defs/Part4.lean:118-126` still asserts an existential probability law
with Assumptions 1-3, independent observed check status and assignment, and a
positive always-passer event. It now also explicitly requires positive mass of
both selected-arm events, integrability of each selected response, and
integrability of the potential-outcome difference on allPass. The unequal
contrast is unchanged. The docstring at `Challenge/Part1.lean:94-95` describes
positive conditioning masses and finite ordinary means; the former totalization
restriction is removed. The `whole` label is correct: these are existence
certificates for the intended means, not a replacement estimand or a hypothesis
assuming the inequality. Fixing K=2 supplies the canonical existential witness.

Use `selectionPopulation (1/2)`: its six atoms each have mass 1/6, each arm has
mass 1/2, each selected-arm event has mass 1/3, and allPass has mass 1/3.
The selected means are 0 and 1/2, while the unit effects and always-passer effect
are zero. The two ordinary selected means and the effect mean are finite. The
previous always-passing Cauchy/shift construction violates the new selected-arm
integrability conditions, so it cannot satisfy this revised statement.

**T23.** `Defs/Part4.lean:135-148` similarly retains the probability law,
positive passing rates, covariate ignorability, conditional covariate balance,
positive allPass/X=0 event and unequal contrasts, while adding positive mass
for both selected-arm/X=0 events and integrability for all three restricted
integrands. The revised docstring at `Challenge/Part1.lean:102-103` faithfully
states the ordinary-mean existence claim. Its `whole` label is correct. A constant
covariate is expressly permitted by the canonical counterexample; no variation
or continuity of X is required. Since the events have positive probability,
there is no conditioning-on-a-null-covariate-event convention.

The same finite witness has X identically zero, so the selected events at X=0
have the same masses and means as T21. I correct my earlier nonvacuity description:
each selected-arm/X=0 event has mass **1/3**, not 1/6. Each contains two atoms
of mass 1/6. The allPass/X=0 event also has mass 1/3. The architect's correction
is right and has been checked independently from the current definitions. This
was an error in my earlier explanatory calculation, not a defect in a theorem.
The original review files are retained as history; the new JSON uses the
correct masses.

## Changed statements and definitions

I compared all six revised Defs parts and every Challenge statement against the
saved `reading.md`, and re-read the relevant canonical claims and standing
assumptions. The mathematical statement changes are exactly T15, T21 and T23,
reviewed above. The remaining statement formulas, quantifier order, hypotheses,
numerical constants, conclusions and supporting constructions match the blind
reading. This includes the unchanged finite- and else-branch sharpness clauses,
attainment or nonattainment, both quantile-integral formulas, and simulation
mixtures and width enclosures.

The uniform `autoImplicit=false` and `relaxedAutoImplicit=false` settings and
explicit natural-number/type binders do not change the mathematical objects
or add assumptions. In particular the population is still the same finite
real-potential/binary-check/assignment/covariate product; ignorability remains
per arm, rather than whole-vector independence. `meanOn` has the same formula;
its updated comment now correctly points to T21/T23's explicit ordinary-mean
certificates. The compatible-law sets, extended-real essential endpoints,
quantiles, density transport and every explicit population witness are unchanged.
No new empty index type, truncated-subtraction, nonintegrable-integral,
unbounded-real-limsup, or infinite-mass convention was introduced.

The unconditional identities retained in T15 have positive conditioning masses
from the population assumptions. All means now actually asserted in its tail
branch have a probability cutoff in [0,1), positive retained mass and integrability.
T21/T23's probability measures make every event mass finite, so the explicit
positive masses have strictly positive finite real denominators; the restricted
integrability conditions prevent Bochner-zero defaults.

## Revised labels: seven refutations

Each new `refuted` decision names the correct printed assertion, rather than a
true repaired claim or a different interpretation. Their mathematical content
is unchanged; the new docstrings state the refutation directly.

| Target | Printed reading refuted | Certificate content retained |
| --- | --- | --- |
| T1 | The three estimated intervals overlap for both outcomes, under either overlap reading | Preference arm 0 is disjoint from each other arm, so neither universal pairwise overlap nor common intersection holds |
| T3 | The Proposition 1 bounds with no passing event in the outer means | Both smooth finite-moment populations have the same observables but target means -1 or 1 outside the printed interval [-3/4,3/4] |
| T5 | The else-branch infinite endpoints are sharp under unbounded observed support | Full observed support coexists with compatible always-passer means strictly between zero and one and sharp extrema zero and one |
| T7 | Common potential check status and per-arm ignorability imply joint-vector independence | The four-state law satisfies the premises but has intersection mass 1/4 versus product 1/8; the corollary's mean identity still holds |
| T9 | The two specified correlation designs have equal bound widths | Valid normal-mixture designs have the stated distinct positive width enclosures and strictly positive gap |
| T11 | The printed odds transport replication covariates to the original distribution | The attained finite logistic fit gives normalized mass 27/28 rather than 1/4, with positive finite normalizer 7/3 |
| T13 | The proof's printed lower-tail expression is an upper bound | A valid Gaussian population has target mean zero and a strictly negative printed bound, with a positive corrected bound |

These are concrete nonvacuous counterexamples, with finite ordinary means where
means occur. T1 uses positive retained counts and the intended truncation of
binary counts. T3 and T13 use interior quantiles and positive-mass tails. T5
refutes claimed sharpness, not validity of the trivial infinite outer interval.
T7 refutes the proof's vector-independence step, not Corollary 1. T9 refutes the
correlation illustration, not the true fixed-observable-law invariance sentence.
T11 retains a finite attained likelihood fit and positive overlap. No new claim
of refuting a repaired theorem is made.

## Retention of all whole clauses and the restriction

| Targets labelled `whole` | Clauses checked |
| --- | --- |
| T2 | All empirical counts, cutoff equivalences, endpoint pairs, overlaps, preference separations and fractional-trimming calculations remain |
| T4 | Both corrected finite bounds, compatible endpoint attainment, bounds on every compatible mean, trimming-mass identity and criterion, zero trimming and both quantile-integral forms remain |
| T6 | Essential-endpoint bounds, strictness at finite endpoints, sharp infimum/supremum, finite nonattainment, branch criterion and two-sided unboundedness characterization remain |
| T8 | Almost-sure check identity, per-arm independence, common positive pass rates, event identity and every conditional-mean equality remain |
| T10 | Observable-law invariance, all admissible simulation laws, correlation and passing formulas, both mixtures and means, change with correlation and the fixed width inequality remain |
| T14 | Fixed-mass upper-tail optimality over all couplings, the attaining coupling, monotonicity, union-bound share inequality and potential upper bound remain |
| T15 | All meaningful law/share and finite-branch mean/bound identities remain, now with the required domain guard |
| T16 | Every interior assignment probability, all finite-witness assumptions, zero effects and corrected selected means and contrast remain |
| T17 | The corrected passing condition is defined and its equality/equivalence to potential passing is retained |
| T18 | The selected contrast equals the always-passer effect under exactly the canonical moment and common-check hypotheses |
| T19 | Both component arm-mean identities and their intent-to-treat contrast remain |
| T20 | Common potential checks still imply observed-check/assignment independence without added moment or passing conditions |
| T21 | The full ordinary-mean existential nonimplication is restored |
| T22 | Covariate independence conditional on every positive-mass status remains under the stated covariate ignorability |
| T23 | The full ordinary-mean existential nonimplication at positive-probability X=0 is restored |

T12 remains `correct_restricted`. Its unchanged docstring explicitly retains
Bayes identities, corrected reciprocal transport, the exact reciprocal normalizer,
positive scale cancellation, and the printed-odds formula and equality
characterization when the squared-density-ratio normalizer is finite. It omits
exactly the final infinite-mass/non-normalizability clause. It adds no moment
condition to reciprocal transport. The finite-normalizer premise is already
part of the canonical printed-odds clause. No restriction is hidden.

There are no omitted targets. The revised record's unused narrower existential
proof rows for T21/T23 do not affect these statement judgments; their new
statements themselves include the previously absent certificates. No Solution,
Bridge, external project file, or proof-accounting claim was used to infer a
mathematical statement's meaning.

## Independent checks

`/home/ubuntu/sap/tools/sap-lean scratch/DeltaCheck.lean` passed with exit code 0
and no warnings. It imports only `SAP.P010.Defs` and no Challenge theorem.
It verifies from the six-atom definition that each selected-arm event and each
selected-arm/X=0 event has real mass 1/3, as do allPass and allPass/X=0. It also
proves event integrability of every real function under this finite population
and explicitly instantiates all six integrability requirements added across
T21 and T23. These masses are positive; exact finite enumeration separately
verifies probability, positive assignment/passing, both ignorability conditions,
check/assignment independence, covariate balance and the 1/2 versus zero contrasts.
Its result is saved in `scratch/delta-arithmetic.json`.

Only one Lean process ran at a time and `lake` was not run. Mathematical
nonvacuity for T15 is the nonconstant Gaussian example above. Each other target's
unchanged nonvacuity explanation is carried into `findings2.json`, and T21/T23's
entries use the freshly checked finite witness and corrected event masses.

`findings2.json` was parsed with Python and checked for exactly one entry for
every target, all required fields, valid verdicts and severities, and matching
theorem names. The earlier reading and original referee artifacts were not edited.
