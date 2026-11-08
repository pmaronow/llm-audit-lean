# Delta referee report

**19 targets: 9 correct_whole, 10 correct_restricted; 0 outstanding issues.** All severities are `none`. The earlier T36 finding is **fixed**: both issue entries are resolved; none is partly fixed or not fixed. No new mathematical, scope, label, or nonvacuity problem was found.

| Verdict | Count |
|---|---:|
| correct_whole | 9 |
| correct_restricted | 10 |
| restriction_inaccurate | 0 |
| not_faithful | 0 |
| vacuous | 0 |
| false | 0 |
| omission_ok | 0 |
| omission_questionable | 0 |

The revised architectural decisions are **6 whole, 5 restricted, 8 refuted**, all accepted. The original findings schema has no `correct_refuted` verdict. Accordingly, `findings2.json` preserves the distinction between complete canonical coverage (`correct_whole`) and correctly disclosed partial coverage (`correct_restricted`). The latter includes the five successful refutations whose canonical witness details are partly omitted: T25, T27, T31, T34, and T36. This does not reject their new `refuted` decisions. The other three refutations retain complete canonical coverage.

## Earlier finding: P001-T36

| Earlier issue | Status | Current evidence |
|---|---|---|
| Literal `ContDiff ℝ ⊤` asserts real analyticity, stronger than the old description of smoothness. | Fixed in the description; the true mathematical assertion is retained. | `SAP/P001b/Defs/Part4.lean:80` is unchanged. `SAP/P001b/Challenge/Part2.lean:42` now says “A real analytic strictly positive normalized joint density”. The scratch analyticity proof passes again. |
| The retained stronger regularity was missing from the record and scope disclosure. | Fixed. | The T36 `restriction` in `record2.json` and `SAP/P001b/Challenge/Part2.lean:43` both say “Retains real analyticity (and hence smoothness)”. The omission list remains complete. `architect-report.md` expressly accepts and explains this repair. |

The relevant Mathlib convention was rechecked at `Mathlib/Analysis/Calculus/ContDiff/Defs.lean:91,1068,1196`: the outer top is omega, while the embedded inner top is infinity. No weakening of the theorem or new hypothesis was introduced to address the finding.

## Comparison and label audit

I reread all current Defs, both Challenge parts, `claims.json`, `record2.json`, and `architect-report.md`, comparing the mathematical content with the saved `reading.md`. No mathematical change was found in any supporting definition, proposition, quantifier, hypothesis, or conclusion. All 19 declarations still have type `TnnStatement` as in that reading. This is a comparison against the saved mathematical reading, not a claim of an independently retained bytewise source snapshot.

The changed descriptions and decisions concern T21, T25, T27, T29, T31, T34, T36, and T38. Each now has decision `refuted` and a docstring beginning “The printed claim is false:”. T25, T27, T31, T34, and T36 retain explicit `Scope:` disclosures. The five remaining `restricted` targets retain `Restricted:` disclosures. A script checked every theorem name and statement header, every refutation opening, and verbatim agreement of every nonnull record scope with its corresponding docstring.

| Target | Revised decision | Assessment of the retained statement and label |
|---|---|---|
| T20 | restricted | Correctly retains overlap versus pointwise positivity, the uniform-bound implication, and the finite-support converse. The conditional arm-support identities and normalization bridge, infinite-support counterexample, and nondiscrete probability-space formulation remain expressly omitted. |
| T21 | refuted | Refutes the information-implies-ignorability implication: the fully coded four-atom voter model has propensity 1/2 but joint conditional probability 3/8 versus product 1/4. It also retains the 25 versus 5 contrast. This does not claim that ignorability is false in the actual Swiss data or refute its stated plausibility. |
| T22 | restricted | Still exactly the T21 witness, constituting corrected clause (i). The description-only response implication (ii) and ATE identification formula (iii) remain expressly omitted. No additional literature premise is assumed. |
| T23 | whole | All canonical clauses remain: corrected inclusion gloss, monotonicity, subtraction, empty-event probability, bounds, complements, addition, and failure of the reversed gloss for every proper inclusion. |
| T24 | whole | Both countable total-probability formulas remain, with positivity restricted to conditional ratios. Nonnegativity alone is insufficient, the event/complement nonemptiness criterion and repaired partition remain, and so do the two-event decomposition and arithmetic example. |
| T25 | refuted | The normalized one-atom integer-valued zero law gives lower-tail probability 1 and printed sum 0, directly refuting the third printed bullet. The second Bernoulli witness is omitted and disclosed. One counterexample suffices for the universal refutation. |
| T26 | restricted | Correct integer lower-tail identity, exact missing nonpositive mass, and equality criterion remain. Only the fair-die specialization is omitted, as disclosed. |
| T27 | refuted | Positive summable weights of total one define a genuine countable atomic law. Its CDF is continuous at 1/3 but is constant on no neighborhood there, refuting the specified non-jump local-flatness reading. The omitted level-sum calculation, injectivity and exact range identification, and separate zero-atom assertion remain disclosed. None is needed for this refutation. |
| T28 | whole | All canonical clauses remain: countable point-mass CDF formula, finite ordered interval formulas and resulting constancy, and all six fair-die evaluations. The extra finite-gap equality is correct. |
| T29 | refuted | All three nonnegative density versions have the same CDF and differ pointwise; the CDF fails to be differentiable at both endpoints. These refute both specified assertions, without refuting nonnegativity or normalization of integral densities. |
| T30 | restricted | All univariate corrections, joint almost-everywhere uniqueness, the uniform mixed-derivative boundary example, product CDF, and continuous independence/product-law equivalence remain. The separate pointwise discrete PMF clause is expressly omitted. |
| T31 | refuted | The measurable inclusion of the normalized fat-Cantor probability space has a genuine density and literal range C containing no nondegenerate interval. This directly refutes the range-contains-an-interval reading. The removed-length calculation and quantitative stage bounds remain disclosed omissions. |
| T32 | whole | All canonical clauses remain: atomlessness, uncountability of actual range and sample space, and unconditional existence of a density-bearing variable with interval-free actual range. The irrational subset witness is permitted by the existential canonical claim. |
| T33 | whole | The true pointwise equivalence on the actual range remains. Omitting irrelevant measurability premises gives a valid generalization. Functions defined only on a larger domain containing the range can be extended to all reals without changing either side. |
| T34 | refuted | A normalized, integrable joint density on (0,1) times (-1,0) gives the printed event probability 1 and the displayed iterated integral 0. The event is the printed event, with no added nonnegative-Y constraint. Omission of the second uniform-square witness remains disclosed. |
| T35 | whole | The corrected triangle formula, decomposition of the printed event into the triangle and negative-Y portion, and exact zero-missing-mass criterion all remain. No support hypothesis is added. |
| T36 | refuted | The genuine normalized analytic joint density has infinite nonnegative slice integral at y=0, contradicting the printed assertion of a finite marginal PDF value at every y. Analyticity is now accurately disclosed. All omitted auxiliary claims remain explicitly listed; none is represented as newly formalized. |
| T37 | restricted | Marginal slice finiteness and every finite nonnegative almost-everywhere version remain unrestricted by a new Borel premise. Global Borel measurability is added solely to selected-slice normalization, exactly as disclosed, with an integrable slice and positive finite denominator. |
| T38 | refuted | The zero-coefficient combination of a standard normal has a unit atom and no density or positive-variance normal law. The two admissible correlation endpoints make both displayed denominators zero. These refute exactly the two specified printed assertions. |

For T36, the explicit function also satisfies the printed mixed-derivative interpretation; the disclosed omission is of formal witness details, not a failure of the example. In ordinary mathematics its lower-y slice integral is

    G(x,y) = exp(x) / (pi * (1+exp(x))^2)
               * (arctan(y*exp(x)) + pi/2).

This is continuous and bounded by the integrable logistic density in x. Setting F(x,y) to its integral from minus infinity to x gives the joint CDF; differentiating first in x and then in y yields f everywhere. For the reverse order, f(u,y) is bounded on u<=x by logistic(u)^2/pi, which is integrable there, permitting differentiation under the integral and then the fundamental theorem of calculus. Thus an everywhere mixed-derivative reading does not rescue the printed finite-marginal assertion. These observations are a referee check of the explicit example, not an assertion that the omitted CDF clauses have appeared in T36.

## Junk values and nonvacuity

The refreshed definitions preserve all earlier safeguards. Every real probability conversion is applied to a finite probability measure; conditional ratios and means have positive denominators on the cells used; integer and dyadic infinite sums are genuinely summable; and density predicates supply integrability. The fat-Cantor subtype inclusion is a measurable embedding of a closed set, so its comapped measure is not the zero fallback. Normalization excludes an empty probability space. The interval-free assertions quantify only over a<b.

T29's explicitly bounded densities are integrable despite the absence of an integrability conjunct in its closed statement. T34 asserts integrability and total mass one, so its unequal integral values are actual probability calculations. T36 uses an extended nonnegative integral for the divergent slice; it never assigns a finite real value to that divergence.

T38 retains a deliberately totalized extension of the printed endpoint expression, explicitly identified in `SAP/P001b/Defs/Part2.lean:49`. Its auxiliary zero function values and zero integrals are values of that extension, not of an ordinary expression with division by zero. The actual endpoint refutation is supplied separately by the zero-denominator assertions and survives deletion of every totalized-value assertion. Both endpoints meet the printed parameter bounds, and the normal combination uses a genuine standard normal probability law.

The following checks both passed against the refreshed compiled Defs:

- `/home/ubuntu/sap/tools/sap-lean scratch/Check.lean` — exit 0. Rechecks the earlier concrete normalized finite laws, positive-mass partition, integer summability, actual univariate and planar probability densities and marginals, selected positive finite slice, and analyticity.
- `/home/ubuntu/sap/tools/sap-lean scratch/DeltaCheck.lean` — exit 0. Checks that the retained predicates entail the refutation consequences for all eight revised refutation labels. In particular, it derives the failure of the universal integer formula, local flatness at non-jump points, endpoint differentiability, interval-containing actual range, triangular-region equality, and everywhere finite marginal slice integrals.

The second file proves implications from the retained predicates. It does not independently reprove those predicates. Neither file imports Challenge stubs, Solution, or Comparator, and neither contains a sorry proof. At most two Lean processes ran concurrently; no lake command was used. Concrete instances and mathematical nonvacuity explanations for all 19 targets are included in `findings2.json`.

There are no remaining findings requiring a fix. The architect's proof-credit and external-kernel claims were not independently audited; this review concerns the statements, their disclosed scope, and their mathematical refutations. The original `reading.md`, `claim-stage.json`, `findings.json`, and `REPORT.md` are preserved.
