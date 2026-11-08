# P061a statement audit

All 11 targets are accounted for: 10 Challenge theorems and one omission.

| Verdict | Count |
| --- | ---: |
| correct_whole | 7 |
| correct_restricted | 3 |
| restriction_inaccurate | 0 |
| not_faithful | 0 |
| vacuous | 0 |
| false | 0 |
| omission_ok | 1 |
| omission_questionable | 0 |

Severity: none 11, minor 0, major 0. There are no adverse findings requiring a statement or docstring fix.

`reading.md` was saved before reading the claims. `claim-stage.json` was saved and parsed before reading the record. No claim-stage judgment was changed after seeing the record. Claim statements, definitions_needed and standing assumptions determined the comparisons; notes, finite_lemmas and record row names were not treated as claim clauses or as mathematical evidence.

T1, T2, T3, T6, T8 and T9 cover their canonical claims. T11 is counted as correct_whole because its full refutation directly contradicts the canonical positivity-only ordinary-mean existence assertion. T1, T2 and T4 instead concern the specified readings of the closing comparison, which their docstrings correctly identify. Their labels do not purport to refute every possible interpretation of locality.

The three accepted restrictions are accurate and disclosed:

* T4 retains the explicit local pair design, moments, squared standardized divergence and coverage failure. Its docstring lists the omitted explicit graph assertions, alternative variance expression, unsquared limit and order classifications, and explains the finite-index domain and reindexing.
* T5 adds separate absolute moments for hybrid responses and everywhere-positive estimated scales, gives the ADE interval limit only at positive continuity endpoints, restricts the local inequality to a finite common alphabet on the full assignment space, and omits a separate AEED interval limit and the explicit T4 example. The docstring identifies each reduction. Results appearing only in finite_lemmas, such as the complete-randomization specialization, are not additional canonical obligations.
* T7 certifies divergence using exact weighted terms, finite partial sums and nonsummability of both sign parts. Its docstring identifies the ordinary-limit, derived-functional and extended-real conclusions that are not separately stated. It does not use Lean's default value for a divergent sum as an ordinary expectation.

T10's omission is justified: the supplied canonical content transcribes corrected rate hypotheses and does not assert a degree bound or theorem derived from stated assumptions. Creating those predicates alone would not establish a further mathematical claim.

The normalized atomic model matches the stipulated discrete power-set probability model. Positivity protects all exposure denominators in substantive mean assertions; finite populations are positive wherever their averages matter. Separate moment predicates protect ordinary infinite expectations. In T3, independence supplies feasible hybrids on positive-mass fibers; in T5, support feasibility is explicit. Bounded continuous test functions are integrable under the probability limit law. The local response ranges have finite, nonempty domains, including singleton function spaces for empty neighborhoods. The zero-size assignment spaces used only to define initial sequence terms are singletons, not empty types.

The [publisher PDF](https://www.cambridge.org/core/services/aop-cambridge-core/content/view/D47B6C466280143573F8BFC9C6B16EEA/S104719872610045Xa.pdf/on-the-foundations-of-the-design-based-approach.pdf) was consulted for the raw/exposure domains, positivity, stability and closing comparison. The supplementary rate wording was assessed from the supplied transcription.

Validation: `scratch/Check.lean`, importing only Defs, compiled successfully with `/home/ubuntu/sap/tools/sap-lean`; it constructs a positive fair-bit design, verifies finite targeted moments and a nonzero contrast, checks independence with a constant other variable, and checks key finite examples and nonempty index spaces. `scratch/exact_checks.py` passed exact rational checks for T1 at N=1–4, T2 at K=1–3, a nontrivial T3 instance, T4 pair moments at m=2,3,5,10, an attained T5 bound, T7 finite sign sums, and the complete T9 witness. These finite checks supplement the mathematical audit; they are not claimed as proofs of the general theorems. Findings include explicit mathematical nonvacuity instances for every theorem. No Solution or Comparator sources were read, and no `lake` command was run.
