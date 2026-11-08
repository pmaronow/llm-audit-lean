# P015a delta review

**12 targets accepted: 8 correct_whole and 4 correct_restricted; 0 outstanding issues.** All severities are `none`. The revised architect decisions are four `whole`, four `refuted`, and four `restricted`. Because the required findings schema has no `correct_refuted` value, the four complete, valid refutations receive `correct_whole`; this does not change their `refuted` architect labels.

## Earlier findings

| Earlier finding | Resolution | Evidence |
| --- | --- | --- |
| T6: incorrect whole refutation credit and missing disclosure | **Fixed** | `record2.json` says `restricted`. `SAP/P015a/Challenge/Part1.lean:69-74` retains the specified witness and explicitly disclaims refuting the necessary ML implication or supplying an actual probit ML maximizer with nonzero residual. |
| T12: alleged guard-scope mismatch | **Resolved; the original finding is withdrawn as a misreading** | The revised restriction is exact. More decisively, `scratch/DeltaReview.lean` reconstructs the old syntax and proves `Round1T12Statement = T12Statement` by `rfl`. Both guards already governed the entire conjunction; the added parentheses did not repair a semantic defect. |

No earlier defect remains partly fixed or not fixed. For T12, withdrawal is the accurate account rather than crediting a semantic repair that was unnecessary. The architect's rejection of my original scope allegation is correct.

The correction supersedes the T12 scope paragraph in `reading.md`, the guard-specific wording in `claim-stage.json`, and the T12 finding in `findings.json` and `REPORT.md`. Those round-1 artifacts are preserved unchanged. Their target coverage conclusion that T12 is narrower than the canonical claim remains correct because clause (iii) is absent.

## Correct T12 reading

After quantifying p,r,rho, assuming 0<p<1 and 0<=r<rho<sqrt(logOdds(p)^2+pi^2), and defining the complex inverse logit and its circle supremum M, the statement is:

`circle_image_nonempty -> circle_image_bounded_above -> (exact_radius_exists AND uniform_error_bound AND geometric_bound_tends_to_zero)`.

This is the reading of both revisions. Lean parses `A -> B -> C AND D AND E` as `A -> B -> (C AND D AND E)`. The original existential's own parentheses do not terminate the surrounding implication. Both this parsing identity and equality of the complete original/revised T12 propositions compile by reflexivity in `scratch/DeltaReview.lean:35-39`.

The revised docstring at `SAP/P015a/Challenge/Part1.lean:31-36` and its `record2.json` restriction accurately identify both guards, the real supremum with no separately asserted maximum attainment, and omission of the outside-domain dataset with a unique finite logistic ML estimate. This is `correct_restricted`.

## Complete delta and label review

All Defs and Challenge files were reread and compared with the saved blind reading and the previous source shown during the review. Apart from the explicit T12 grouping, the mathematical definitions and proposition bodies retain the previously audited contents. The T12 grouping is definitionally equal to the old source. The other substantive changes are the T6 restriction disclosure and the four refutation labels/prefixes; remaining docstring edits reflow the same descriptions. All twelve theorem names and universe quantifications are retained.

| Target | Revised decision | Verdict | Delta and coverage check |
| --- | --- | --- | --- |
| P015-T1 | refuted | correct_whole | Label/docstring changed to refuted; rare-law family, exact IPW moments and consistency, positivity, and OLS coefficient retain all counterexample facts. |
| P015-T2 | refuted | correct_whole | Label/docstring changed to refuted; positive effective profile mass with absent treatment endpoint directly falsifies pair-specific effective positivity. |
| P015-T3 | refuted | correct_whole | Label/docstring changed to refuted; an actual positive-probability sample has an entire zero fitted-weight profile despite positive population overlap. |
| P015-T13 | whole | correct_whole | Whole corrected derivative, affine Taylor polynomial, and printed-fraction evaluation retained. |
| P015-T12 | restricted | correct_restricted | Explicit conjunction parentheses and exact guard wording; definitionally unchanged proposition. Outside-domain dataset still omitted and disclosed. |
| P015-T8 | restricted | correct_restricted | Same correctly restricted scalar-score/Taylor content and disclosed omitted conclusions/hypotheses. |
| P015-T5 | restricted | correct_restricted | Same correctly restricted odds-link witness; no refutation of ML-implies-residual-zero is claimed. |
| P015-T6 | restricted | correct_restricted | Whole changed to restricted; added disclosure now exactly states converse failure and the missing actual-ML counterexample. |
| P015-T7 | refuted | correct_whole | Label/docstring changed to refuted; same genuine maximizing-branch derivatives 120/119 and 1 at the same mean, with causal model and OLS comparison. |
| P015-T16 | whole | correct_whole | Whole numerical conversion, fitted exponential ratio, and nonsingular spending/OLS example retained. |
| P015-T4 | whole | correct_whole | Whole discrete finite-second-moment positivity correction, effective-law formulas, and all three counterexamples retained. |
| P015-T19 | whole | correct_whole | Whole general-covariate conditional-variance identity and binary propensity formula retained. |

### Refutation directions

- **T1:** The family has strict binary positivity while its effective mass for X=0 is arbitrarily small. Its genuine IPW estimator is unbiased and consistent, with every-positive-sample-size bounds. These contradict the printed approximate-zero-weight implication, under the canonical effective-mass reading. The claim is not a uniform-precision assertion in epsilon.
- **T2:** The effective population gives X=1 positive mass but has conditional probability zero for D=1 there. This directly refutes the printed pair-specific positivity assertion. The arbitrary-potential-outcome section permits the nonlinear second world, and the observationally identical worlds have different effects. The claim is about the printed endpoint-specific display, not merely the existence of two treatment values in each profile.
- **T3:** Population conditional treatment probabilities are all 1/2, while an ordered sample of probability 1/256 has exactly zero fitted weights at X=0 and a nonsingular regression. This refutes the claimed inference from estimated profile weights to a population positivity failure under the canonical sample-weight interpretation.
- **T7:** The same square-link GLM and the same outcome mean 1/4 produce genuine ML treatment derivatives 120/119 and 1 in the two causal models. The first model's OLS treatment coefficient is exactly epsilon, and the link derivative at the center is 1. The first-order discrepancy refutes the printed extension to arbitrary GLMs of a scale depending solely on the outcome mean. Actual maximizing branches are conclusions, not assumed score roots.

T5 and T6 remain restricted for the correct reason: residual-root nonmaximality refutes sufficiency, whereas the printed estimating-equation assertion is necessary. Neither revised label wrongly claims the latter refutation.

### Whole and restricted coverage

T13 retains all four corrected derivative/Taylor/misprint-evaluation components. T16 retains all three formal components of the conversion and spending correction. T4 retains the distinct-endpoint and degeneracy assertions, binary equivalences, normalized effective-law cell formula and reversal, and all three converse counterexamples. T19 retains the identity for general measurable covariates with square-integrable treatment and its substantive almost-everywhere binary formula. Thus the four `whole` labels omit no canonical formal clause.

T8's disclosed restrictions remain exact: the normalized supported canonical-family hypotheses are explicit; the arbitrary-family response-mean identification, Appendix C/OLS linearization, derived equations and nonzero-multiplier/cancellation conclusions, and separate discrepancy examples are omitted. The retained first-Taylor-polynomial identity does not promise a quadratic remainder for the nonlinear score. T12, T5 and T6 accurately disclose their respective omissions as above. Every restricted docstring was checked programmatically against its full `record2.json` restriction after whitespace normalization.

## Junk values and nonvacuity

The label changes introduce no additional mathematical assumptions. The previous positive finite-law normalizers, positive conditioning cells, interior likelihood probabilities, nonzero design determinants, sample-size guards, integrability and L2 witnesses remain valid against the refreshed definitions. `scratch/Check.lean` was recompiled successfully against the revised Defs; it includes an actual infinite independent uniform sampling model for T2, so its estimator clause does not range over an impossible sampling setup.

For T12 a new independent check proves all the potentially disputed guards are jointly realizable. Take p=1/2, r=pi/8 and rho=pi/4. `scratch/DeltaReview.lean` proves the radius inequalities, a nonempty circle norm image, and boundedness above of that actual image. On the circle, |Im z|<=pi/4<pi/2 gives positive real part of exp(-z), so 1+exp(-z) is nonzero. The inverse-logit norm is continuous there and the circle is compact. Thus M is a genuine finite supremum and the entire guarded conjunction has a nonvacuous instance; r/rho=1/2. No empty set, unbounded supremum, or totalized inverse at a pole does any work.

T6 uses the same finite actual probit dataset, well-defined upper quartile, full-rank design and strictly interior fitted probabilities. Its newly disclosed restriction adds no hypothesis, much less a hypothesis assuming the desired conclusion. T7's positive square-link domain, finite mixture of independent uniform unit laws, and asserted actual unique maximizing branches retain their previous meaning. Nonvacuity details for every target are recorded in `findings2.json`.

## Validation

- `/home/ubuntu/sap/tools/sap-lean scratch/DeltaReview.lean`: exit 0. This imports only Defs and independently proves old/new T12 definitional equality, arrow scope, and the concrete circle/domain guards. Only harmless unused-simp-argument warnings were emitted.
- `/home/ubuntu/sap/tools/sap-lean scratch/Check.lean`: exit 0 with no diagnostics against the revised compiled definitions.
- `python3 scratch/exact_checks.py`: passed again; exact Fraction arithmetic confirms the finite cores. Probit and exponential numerical diagnostics remain diagnostics rather than formal analysis proofs.
- Restricted docstrings equal their recorded restrictions after whitespace normalization; all four `refuted` docstrings have the required prefix.
- `findings2.json` parses with Python, has the required schema, and contains exactly one entry for every target in `claims.json`.

No Challenge stub was used as a proof in the scratch checks. No Solution or external project source was read. No `lake` command was run, and no more than two Lean processes were active. The review concerns statement fidelity and does not rely on the architect's claims about external Comparator certification.
