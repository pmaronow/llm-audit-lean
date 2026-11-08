# P017 statement audit

All 16 targets are accounted for. The architect's decisions are supported:
10 complete positive statements, one complete advertised refutation, and five
correctly disclosed restrictions. No statement defect, inconsistent collection
of hypotheses, or unjustified target omission was found.

| Verdict | Count |
| --- | ---: |
| `correct_whole` | 11 |
| `correct_restricted` | 5 |
| `restriction_inaccurate` | 0 |
| `not_faithful` | 0 |
| `vacuous` | 0 |
| `false` | 0 |
| `omission_ok` | 0 |
| `omission_questionable` | 0 |

Severity counts: none 16, minor 0, major 0. There are no items outside
`correct_*` or `omission_ok` to report, and no fixes are required.

## Restricted targets

Each restriction below matches both `record.json` and the Challenge docstring.
The retained propositions have satisfiable hypotheses and are mathematically
correct on the stated domains.

| Target | Accurate, disclosed reduction |
| --- | --- |
| P017-T2 | Drops the prescribed normalized atom indicator and its bound, and the prescribed two-region mixture, conditional-mean/coefficient formulas and inequalities, boundedness and normalized mixture moments. Retains the complete attainability characterization and support consequences, an unspecified normalized atom witness and arbitrary admissible interior witnesses. |
| P017-T3 | Drops separate explicit comparisons of clipping endpoints with support bounds and the separately stated finite-valued-effect sufficient example. Retains the support-hull bound, exact representation criterion, strict-inside equality and representation, endpoint-mass and infinite-radius sufficient conditions, and both probability limits. |
| P017-T7 | Keeps root-n asymptotic normality for the combined theorem and drops a separate consistency-only formulation and the canonical sentence claiming consistency alone gives all of (a)-(c). That sentence includes root-n tightness, which consistency does not imply: the deterministic estimate mu+n^(-1/4) is a counterexample. The event bounds and every-positive-sequence conclusion are retained under the advertised stronger hypothesis. |
| P017-T11 | Drops the equivalent truncated Gaussian moment interpretation, standardized density integral identity and scale-s density/CDF expression. Retains the displayed Lebesgue integral identity, o(1/n), and every positive power decay limit. |
| P017-T12 | Drops the specified eventual formula p_n=sqrt(r_n) for the domination witness. Retains its existence, all arbitrary prescribed-failure-sequence constructions, exact events and moment bounds, logarithmic example and slow-rate conclusions. |

## Refutation and scope checks

P017-T9 is correctly recorded as `refuted`. Its Lean proposition negates the
printed universal representation assertion. Its final `correct_whole` verdict
means a correct, explicitly labeled refutation of that assertion; it does not
mean that the printed positive proposition is true. The stage-2 relation remains
`different` because the polarity is reversed. There was no post-record change
to that reading or any other stage-2 classification.

The negated universal specifies empirical-measure factorization and asymptotic
normality, but no IID data-law constraint or positive-mass requirement for the
bad realization. The canonical printed universal leaves the sampling scheme
unspecified. The concrete IPW construction in T1 also gives a genuine IID,
sampling-induced counterexample with positive-probability failure at each
positive sample size: each endpoint event has mass 4^(-n). Thus the refutation
does not depend on exploiting an unrelated sampling distribution or an
exceptional null sample.

T10's probability-zero implication remains under its support-bound hypothesis,
which already forces probability one. Its antecedent is therefore impossible
there. This is the canonical clause (c)'s explicit contradiction check on the
printed numeral, rather than an inconsistent hypothesis of the corollary. The
support-bound hypothesis itself is satisfiable. The support theorem and the
two separately quantified support remarks remain substantive.

The population and estimator supports are genuine closed pushforward supports.
Probability measures and measurable maps avoid empty-support and fallback-map
artifacts. Integrable effects make population expectations genuine; admissible
weights have finite positive denominators and integrable weighted effects.
Extended support bounds do not subtract one infinity from another because the
mean is finite. The infinite-radius clip explicitly returns its argument.
The positive-sample-size clauses prevent zero denominators. In the moment
statements, bounded concrete constructions or the square-integrable normal
decomposition ensure the required positive-n integrals are finite. The
identically zero infinite-radius residual is legitimately integrable, even
against an arbitrary measure.

## Evidence and validation

The required order was followed: `reading.md` was saved before `claims.json`
was opened, and `claim-stage.json` was saved and parsed before `record.json`
was opened. The blind reading's SHA256 is
`576ad550c768349482943fa5a236bab9c06f68e19c44e2a257685f0b4081eb2f`.
It expands all sixteen propositions and their SAP definitions to their
Mathlib measure, support, integral, probability and convergence meanings.
The architect's source-row names were used only as record metadata; no
Solution or Comparator was inspected.

The published paper's rendering confirms the named statements and locations;
the arXiv version has a different title and proposition numbering, so the
published text and the supplied canonical claims governed the comparison.
See the [published paper text](https://www.researchgate.net/publication/310050238_Data-Adaptive_Causal_Effects_and_Superefficiency)
and the [arXiv version](https://arxiv.org/pdf/1601.01413).

`scratch/Nonvacuity.lean` imports only `SAP.P017.Defs` and compiles successfully
with `/home/ubuntu/sap/tools/sap-lean scratch/Nonvacuity.lean`. It contains no
`sorry` and establishes a fair two-atom population with mean zero, support
{-1,1}, positive radius one and admissible constant weight; a measurable exact
normal/sqrt(n) estimator with nondegenerate asymptotic normality; a compatible
normal decomposition with zero square-integrable remainder satisfying the
required mean-square rate; and both stated numerical logarithmic probabilities.
The final compiler output contains only an unnecessary-`simpa` linter suggestion.
Additional per-target instances, including zero and infinite radius and both
support remarks, are given in `findings.json` with their mathematical reasons.

`claim-stage.json` and `findings.json` were parsed with Python 3. The final
validation checks unique coverage of all 16 canonical target IDs, theorem-name
agreement, allowed verdict and severity values, required fields, and the counts
reported here. No `lake` command was run, and Lean checks ran one process at a
time.
