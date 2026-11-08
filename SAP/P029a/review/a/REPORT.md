The statement audit accepts all 13 targets: **8 correct_whole and 5
correct_restricted**. There are no false, vacuous, unfaithful, inaccurately
restricted or omitted targets. Every severity is `none`.

| Verdict | Count |
|---|---:|
| correct_whole | 8 |
| correct_restricted | 5 |
| restriction_inaccurate | 0 |
| not_faithful | 0 |
| vacuous | 0 |
| false | 0 |
| omission_ok | 0 |
| omission_questionable | 0 |

The blind reading was saved in `reading.md` before opening `claims.json`.
The claim comparison was saved in `claim-stage.json` before opening
`record.json`. No step-2 classification was changed after reading the
record. Canonical statements, definitions_needed and standing assumptions
governed the comparison; notes and unused proof rows did not remove any
canonical clause. All 13 target IDs have exactly one theorem and one
finding.

| Target | Architect's decision | Audited verdict | Scope assessment |
|---|---|---|---|
| P029-T1 | whole | correct_whole | Complete six-atom counterexample to the receipt-ignorability-implies-latent-ignorability reading. |
| P029-T2 | restricted | correct_whole | Both witnesses and the general implication are covered; the extra premises are logically redundant, as explained below. |
| P029-T3 | whole | correct_whole | Both independence readings and their complete population-ratio counterexamples are covered. |
| P029-T4 | restricted | correct_restricted | All numbered population results are retained; sampling consistency from the corrected prose is explicitly dropped. |
| P029-T5 | whole | correct_whole | The admissible design, outcome cross-products, coefficient recovery, positive weights and both scoring signs are covered. |
| P029-T6 | whole | correct_whole | Constant effects, all positive replicate counts, benchmark moments and error identities are covered. |
| P029-T7 | restricted | correct_restricted | Objective invariance and numerical arrays are certified; fitted-probit and actual-refitting interpretations are explicitly dropped. |
| P029-T8 | restricted | correct_restricted | General and three concrete free-cell fits are certified; probit realization and distinct nonconstant-weight probit minimizers are explicitly dropped. |
| P029-T9 | restricted | correct_restricted | Both completions, compatible codes, outcomes, pooled counts, reverse comparisons and assignment support are retained; general sign algebra and independent raw-data summaries are explicitly dropped. |
| P029-T10 | restricted | correct_restricted | Count algebra, rate calculations, binary completions and group covariance are retained; empirical prose and raw-string preservation are explicitly dropped, and the positive-group premise is disclosed. |
| P029-T11 | whole | correct_whole | Both nondegenerate SEM counterexamples and their stated moments are covered. |
| P029-T12 | whole | correct_whole | Both noninclusions, the causal SEM constant-effect implication and heterogeneous IV law are covered. |
| P029-T13 | whole | correct_whole | Closed-domain maxima, boundary convention, score bias and five-per-arm enumeration are covered. |

T2's declaration accurately lists the extra clauses in its formal signature,
but calling them a restriction is conservative. In canonical part (c),
`D0=0` almost surely already rules out defiers. Positive profile mass and
positive conditional compliance imply
`P(C) >= P(C and X=x) = P(X=x) pi(x) > 0`. Independence of assignment
and the potential responses then gives
`E[D|Z=1]-E[D|Z=0] = E[D1-D0] = P(C) > 0`.
Every canonical instance therefore satisfies the complete IV bundle in
`OneSidedImplication`. No mathematical case is lost, so the audit retains
its step-2 `whole` assessment. This is a difference in scope classification,
not an undisclosed assumption or a required correction.

The five substantive restrictions are accurately stated in both the
Challenge docstrings and the record. T4 and T10 were compared against the
corrected prose as well as the numbered mathematical clauses. In
particular, the audit did not use their notes to erase the consistency or
empirical assertions. T7 and T8 do not certify that their prescribed score
arrays arise from the package's probit fitting procedure. T9's arbitrary
raw-code premise expresses compatibility with its recorded binary labels;
it is satisfiable and does not amount to validating an external data file.
No target is labelled `refuted` in the record. The counterexample
docstrings identify the implication or independence readings, or the
specific scoring/estimation assertion, without declaring broader printed
guidance false.

The expanded definitions use the paper's binary potential treatments,
outcome consistency/exclusion, compliance events, normalized arm means,
conditional effect means and observation likelihoods correctly. The
independence definitions were followed to Mathlib's generated sigma
algebras. All relevant conditional events and Wald denominators are
positive or nonzero under the hypotheses or in the concrete examples.
Finite covariate support makes the population weighting integrable; the
expected-error identity explicitly requires second moments. The apparent
absence of an integrability premise on Y0 in ConstantPopulationEffect is
harmless because its actual integrand is identically five. The EReal
objective explicitly handles zero-weight log contributions. Correlations
in the SEM witnesses have positive variance factors, matrix inverses have
nonzero determinants, and binomial exponents use indices k<=n. The closed
triangle and `0^0=1` in T13 are part of its canonical reading. No empty
index type or undefined-operation convention supplies a claimed result.

The retained record completions are finite potential-outcome populations
compatible with a realized assignment pattern. Their empirical
assignment/contact association is not assumed to be population random
assignment. `RecordedAssignmentSupport` instead supplies positive
probability of that particular pattern under an independent Bernoulli
assignment design, as required for compatibility.

Verification used only Mathlib and the audited definitions for Lean
checks. `/home/ubuntu/sap/tools/sap-lean scratch/Nonvacuity.lean` completed
successfully, with no Challenge import and no sorry. It constructs a fair
Boolean probability space with constant all-complier responses and checks
the full IV, one-sided, positive-profile, receipt-mean and joint-independence
premises. It also checks nonempty free-cell success/failure totals and a
nonconstant binary count instance. The independent Fraction calculations
in `scratch/arithmetic_check.py` passed for the finite laws, independence,
main weighted arm/Wald values, perturbations, SEM moments, record counts
and signs, noise Gram matrix/cross-products/determinant and binomial bias.
These checks support the statement audit; they do not replace the
Comparator's proof certification.

The supplied canonical transcriptions were the substantive paper source.
A paper-only web lookup confirmed the bibliographic reference at the
[publisher's article page](https://www.cambridge.org/core/journals/political-analysis/article/abs/beyond-late-estimation-of-the-average-treatment-effect-with-an-instrumental-variable/604E0803793175CF88329DB34DAA80B3).
The publisher page did not expose the full article in this session; no
claim of an independent raw-data, package-source or historical-simulation
audit is made. `findings.json` and `claim-stage.json` were parsed and
checked with Python for complete, unique target coverage and valid enum
values.
