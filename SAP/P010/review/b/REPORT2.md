The revised package has **23 accepted targets, no remaining findings and no omissions**. Both of my earlier adverse findings are **fixed**. The archived `reading.md`, `claim-stage.json`, `findings.json` and `REPORT.md` remain unchanged.

| Revised verdict | Count |
| --- | ---: |
| correct_whole | 22 |
| correct_restricted | 1 |
| restriction_inaccurate | 0 |
| not_faithful | 0 |
| vacuous | 0 |
| false | 0 |
| omission_ok | 0 |
| omission_questionable | 0 |

`record2.json` has **15 whole, 1 restricted and 7 refuted** decisions. All are accurate. The requested findings schema retains the original verdict vocabulary: the seven complete canonical counterexample targets therefore receive `correct_whole` in `findings2.json`, with their `refuted` decisions explicitly assessed below. That verdict does not endorse the printed assertions they refute.

My earlier findings were resolved as follows:

| Target | Earlier finding | Disposition and evidence |
| --- | --- | --- |
| T21 | Missing integrability of the two selected outcomes and the always-passer effect | **Fixed.** `Defs/Part4.lean:122–124` requires all three certificates for the same existential measure. |
| T21 | A Cauchy/shift population could supply a totalization artifact | **Fixed.** The selected-outcome integrability conditions exclude that population. All three conditioning masses are explicitly positive; probability guarantees finiteness. |
| T21 | The disclosed total-function assertion did not establish the ordinary-mean claim | **Fixed.** `Challenge/Part1.lean:94–96` now describes existing finite ordinary means, and the obsolete restriction is removed from both the docstring and record. |
| T23 | Missing integrability on the three covariate-restricted events | **Fixed.** `Defs/Part4.lean:141–144` requires precisely those three restricted-integrability certificates. |
| T23 | Constant-covariate Cauchy/shift population could supply an artificial inequality | **Fixed.** The same existential measure must now have positive masses and integrable outcomes on both selected-arm-and-X=0 events. |
| T23 | The disclosure substituted totalized values for ordinary conditional expectations | **Fixed.** `Challenge/Part1.lean:102–104` and the `whole` record entry describe the restored finite-mean non-implication. |

For T21 the revised mathematical statement is existence of a law on `Population 2 1` satisfying population assumptions, observed-check/assignment independence, positive all-pass and both selected-arm masses, integrability of response on each selected-arm event, and integrability of the potential effect on all-passers, with unequal selected and always-passer contrasts. For T23 the same three mass and integrability requirements apply after intersecting each event with X=0; probability, positive passing, covariate ignorability and conditional covariate balance are also required. These are genuine ordinary conditional-mean counterexamples. Fixing two arms and a constant scalar covariate is the explicit canonical witness specialization and preserves the full existential claims.

All nine revised SAP files were inspected, including every definition and statement. Relative to `reading.md`, only **T15, T21 and T23 change mathematically**. T1, T3, T5, T7, T9, T11 and T13 change their labels and docstrings. The strict implicit-variable options and explicit natural-number/type binders preserve the earlier mathematical parameter types, quantifiers and hypotheses. The underlying population coordinates, conditional-law formula, quantiles, trimming formulas, compatibility sets and witness laws retain their earlier definitions. The `meanOn` body is unchanged; its updated comment correctly points to the new witness certificates.

The complete target and label check is:

| Target | Revised decision | Statement and label assessment |
| --- | --- | --- |
| T1 | refuted | Unchanged two disjoint preference intervals refute both universal pairwise overlap and a common intersection in the printed empirical reading. Supplied counts and unweighted point-estimate intervals retain their intended meaning. |
| T2 | whole | All exact counts, rank-cutoff equivalences, preference and approval endpoints, common points, positive contrast gaps, fractional-trimming endpoints and fractional gaps remain. |
| T3 | refuted | Both continuous, integrable same-observables populations violate the printed bounds whose outer conditioning omits passing. Their target means are −1 and 1 versus printed bounds −3/4 and 3/4. |
| T4 | whole | Validity for every compatible mean, both attained endpoints, the mass identity and equivalence, zero trimming, and both quantile-integral forms remain under the canonical finite-branch assumptions. |
| T5 | refuted | The full observed-support witness has finite sharp extrema 0 and 1 despite trimming ratio 2. This refutes the printed **sharpness of infinite endpoints**. The outer order inequality with infinite endpoints remains true. |
| T6 | whole | Branch equivalence, essential bounds, strictness at finite endpoints, compatible-law sharp extrema, finite nonattainment and the two-sided unboundedness equivalence all remain. |
| T7 | refuted | The four-state witness refutes the printed proof's full-vector independence inference under per-arm ignorability and common check status. It preserves the true Corollary 1 means. |
| T8 | whole | All a.e. check identities, per-arm independence, positive common passing probabilities, event equality and conditional-mean identities remain. |
| T9 | refuted | The two specified designs have different observable passer laws and strictly different population bound widths. This refutes the printed correlation-varying illustration; fixed-observable-law invariance remains intact. |
| T10 | whole | Fixed-observable-law invariance, feasible joint-check probabilities, both Gaussian passer mixtures and means, their change with correlation, and the two-design width inequality all remain. |
| T11 | refuted | The attained finite logistic fit gives normalized printed-odds mass 27/28 instead of the original 1/4, with strictly positive cells and finite positive normalizer. The reciprocal direction recovers the original law. |
| T12 | restricted | Exactly the final infinite-normalizer assertion is dropped. Bayes identities, reciprocal transport, its exact normalizer, scale cancellation, and the complete positive finite-normalizer printed-odds formula and characterization remain. Record and docstring agree. |
| T13 | refuted | The common-normal witness has zero target mean and a strictly negative printed lower-tail upper bound, with finite moments, full support, positive all-pass mass and ratio 1/4. |
| T14 | whole | Maximization over all couplings at each discarded share, the attaining upper-tail coupling, monotonicity, the union-bound inequality and the corrected potential upper bound all remain. |
| T15 | whole | Conditional passer-law equality, all marginal passing-rate identities and trimming-ratio equality remain unconditional. Tail-mean equality now joins the target identity and upper inequality under r<1. This preserves every ordinary-mean clause on its canonical domain. |
| T16 | whole | The complete bounded three-stratum calculation remains for every interior assignment probability, including all zero-effect identities, passing rates, independence and the corrected positive contrast. |
| T17 | whole | The corrected observable positive-passing assumption, its potential-probability equivalence and marginal probability identities remain. |
| T18 | whole | The common-check selected-contrast identity remains under exactly the specified finite-first-moment assumptions. |
| T19 | whole | Both component arm-mean identities and their intent-to-treat contrast remain. |
| T20 | whole | Common potential check status still implies observed-check/assignment independence under consistency and per-arm ignorability. |
| T21 | whole | Restored integrable, positive-mass existential counterexample establishes the printed corollary's non-implication. It supports that corollary; a `refuted` label would be incorrect. |
| T22 | whole | Conditional covariate balance at each positive-probability check value remains under common check status and covariate ignorability. |
| T23 | whole | Restored covariate-restricted finite-mean counterexample establishes the full printed non-implication. The constant covariate is a legitimate nonempty one-dimensional witness. |

T15's guard repairs the domain issue described by the other referee and recorded in `architect-report.md`. My earlier reading explicitly identified the unguarded equality, although my first findings did not reject T15. The revised form excludes its use on zero-mass tails. Under the theorem's assumptions r≥0. For an atomless probability passer law, the upper tail at a quantile with r≥1 has mass zero: for r>1 the extended quantile is +∞, and at r=1 any finite endpoint has no atom. Thus an ordinary conditional tail mean cannot occur there. The canonical text introduces the corrected display for r<1 and presupposes that its conditional means exist. Guarding the identity preserves its meaningful domain without dropping an ordinary-mean case.

Changed-statement nonvacuity and junk-value checks were checked independently of the architect's proof account:

* `scratch/DeltaCheck.lean` imports only `SAP.P010.Defs` and compiles with the permitted `sap-lean` wrapper. It proves exact mass 1/3 for each selected-arm event and for the all-pass event of `selectionPopulation (1/2)`, equality of each event's mass after intersection with X=0, and every new restricted-integrability condition of T21 and T23. All three conditioning events have mass **1/3**, each comprising two atoms of mass 1/6. This confirms the architect's numerical correction concerning the other referee's ancillary example.
* In that finite population, both assignment masses are 1/2, passing rates are 2/3, and assignment is independent of the potential stratum. Its selected means remain 0 and 1/2 and its always-passer effect is identically zero. All new hypotheses therefore hold jointly with the asserted unequal contrasts. The previous totalization artifact is excluded.
* T15's finite branch is realized by `normalCommonPopulation`: rates 4/5, r=1/4, standard-normal passer law, and retained tail probability 3/4. The selected observed upper-tail event has population mass 3/10. Its restricted outcome is integrable. The r=0 boundary is realized by `commonOutcomePopulation true (gaussianReal 0 1)` and retains the entire passer law.
* The seven relabelled counterexamples retain their previously audited numerical values and nonvacuity instances. T1's denominators and retained counts are positive; T3, T9 and T13 use ordinary integrable continuous laws; T5 uses bounded passer outcomes; T7 and T11 use finite witnesses. Their new labels introduce no empty index, zero denominator, nonintegrable-integral or unbounded-real-extremum convention.

The new scratch proof ran one Lean process at a time, without importing any Challenge theorem or reading an external formalization. No `lake` command was run. The unchanged normal-mixture enclosure constants retain the earlier numerical sanity check; this delta review does not claim a new formal interval certificate or a comparator/kernel certification.

`findings2.json` contains exactly one object per canonical target, with the same fields and permitted verdicts as `findings.json`. Python parsing, schema checks, target coverage and the report counts pass. No further correction is requested.
